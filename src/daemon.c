/*
 * daemon.c -- nfield persistent daemon with thread pool
 *
 * Listens on a TCP port, accepts commands as line-delimited JSON,
 * dispatches to a thread pool, returns output as JSON.
 *
 * Protocol:
 *   Client sends: {"cmd":"field 7"}\n
 *   Server sends: {"output":"n = 7, base = 10, ...\n"}\n
 *
 * Usage: nfield daemon [--port 9090] [--threads 4]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/time.h>
#include <signal.h>
#include <errno.h>
#include <stdint.h>

/* Forward declaration: dispatch a command string and capture output */
extern int nfield_dispatch(const char *cmdline, char *outbuf, size_t outbuf_size);
extern int nfield_dispatch_status(const char *cmdline, char *outbuf,
                                 size_t outbuf_size, int *truncated);

#define MAX_CMD_LEN 4096
#define MAX_OUTPUT  (1024 * 1024)
#define MAX_QUEUE   256

/* ── Work queue ──────────────────────────────────────── */

typedef struct {
    int client_fd;
} work_item_t;

typedef struct {
    work_item_t items[MAX_QUEUE];
    int head, tail, count;
    pthread_mutex_t lock;
    pthread_cond_t not_empty;
    pthread_cond_t not_full;
    int shutdown;
} work_queue_t;

static work_queue_t queue;

static int write_all(int fd, const char *buffer, size_t length) {
    while (length > 0) {
        ssize_t written = write(fd, buffer, length);
        if (written < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (written == 0) return -1;
        buffer += written;
        length -= (size_t)written;
    }
    return 0;
}

static void queue_init(void) {
    queue.head = queue.tail = queue.count = 0;
    queue.shutdown = 0;
    pthread_mutex_init(&queue.lock, NULL);
    pthread_cond_init(&queue.not_empty, NULL);
    pthread_cond_init(&queue.not_full, NULL);
}

static void queue_push(int fd) {
    pthread_mutex_lock(&queue.lock);
    while (queue.count == MAX_QUEUE && !queue.shutdown)
        pthread_cond_wait(&queue.not_full, &queue.lock);
    if (queue.shutdown) { pthread_mutex_unlock(&queue.lock); close(fd); return; }
    queue.items[queue.tail].client_fd = fd;
    queue.tail = (queue.tail + 1) % MAX_QUEUE;
    queue.count++;
    pthread_cond_signal(&queue.not_empty);
    pthread_mutex_unlock(&queue.lock);
}

static int queue_pop(int *fd) {
    pthread_mutex_lock(&queue.lock);
    while (queue.count == 0 && !queue.shutdown)
        pthread_cond_wait(&queue.not_empty, &queue.lock);
    if (queue.shutdown && queue.count == 0) {
        pthread_mutex_unlock(&queue.lock);
        return 0;
    }
    *fd = queue.items[queue.head].client_fd;
    queue.head = (queue.head + 1) % MAX_QUEUE;
    queue.count--;
    pthread_cond_signal(&queue.not_full);
    pthread_mutex_unlock(&queue.lock);
    return 1;
}

/* ── JSON helpers ────────────────────────────────────── */

static const char *json_extract_cmd(const char *json, char *cmd, size_t cmd_size) {
    /* Bounded extraction of the JSON string in {"cmd":"..."}. */
    const char *start = strstr(json, "\"cmd\"");
    if (!start) return NULL;
    start = strchr(start + 4, ':');
    if (!start) return NULL;
    start++;
    while (*start == ' ' || *start == '\t') start++;
    if (*start != '"') return NULL;
    start++;
    size_t i = 0;
    while (*start && *start != '"') {
        unsigned char decoded = (unsigned char)*start++;
        if (decoded == '\\') {
            unsigned char escaped = (unsigned char)*start++;
            if (escaped == '"' || escaped == '\\' || escaped == '/')
                decoded = escaped;
            else if (escaped == 'b') decoded = '\b';
            else if (escaped == 'f') decoded = '\f';
            else if (escaped == 'n') decoded = '\n';
            else if (escaped == 'r') decoded = '\r';
            else if (escaped == 't') decoded = '\t';
            else return NULL;
        }
        if (decoded < 32 || i >= cmd_size - 1) return NULL;
        cmd[i++] = (char)decoded;
    }
    if (*start != '"') return NULL;
    cmd[i] = '\0';
    return cmd;
}

static int json_escape(const char *src, char *dst, size_t dst_size) {
    static const char hex[] = "0123456789abcdef";
    size_t j = 0;
    if (!dst_size) return 0;
    for (size_t i = 0; src[i]; i++) {
        unsigned char c = (unsigned char)src[i];
        size_t needed = c == '"' || c == '\\' || c == '\n' || c == '\r' || c == '\t' ? 2 : c < 32 ? 6 : 1;
        if (needed >= dst_size - j) { dst[j] = '\0'; return 0; }
        if (c == '"' || c == '\\') { dst[j++] = '\\'; dst[j++] = (char)c; }
        else if (c == '\n' || c == '\r' || c == '\t') {
            dst[j++] = '\\'; dst[j++] = c == '\n' ? 'n' : c == '\r' ? 'r' : 't';
        } else if (c < 32) {
            dst[j++] = '\\'; dst[j++] = 'u'; dst[j++] = '0'; dst[j++] = '0';
            dst[j++] = hex[c >> 4]; dst[j++] = hex[c & 15];
        } else dst[j++] = (char)c;
    }
    dst[j] = '\0';
    return 1;
}

/* ── Worker thread ───────────────────────────────────── */

static void *worker_thread(void *arg) {
    (void)arg;
    while (1) {
        int fd;
        if (!queue_pop(&fd)) break;

        /* Read the command line */
        char buf[MAX_CMD_LEN];
        ssize_t n = 0;
        size_t total = 0;
        while (total < sizeof(buf) - 1) {
            n = read(fd, buf + total, sizeof(buf) - 1 - total);
            if (n <= 0) break;
            total += (size_t)n;
            if (memchr(buf, '\n', total)) break;
        }
        buf[total] = '\0';

        /* Strip trailing newline */
        char *nl = strchr(buf, '\n');
        if (nl) *nl = '\0';

        /* Extract command */
        char cmd[MAX_CMD_LEN];
        const char *extracted = json_extract_cmd(buf, cmd, sizeof(cmd));
        if (!extracted) {
            const char *err = "{\"error\":\"invalid request\"}\n";
            (void)write_all(fd, err, strlen(err));
            close(fd);
            continue;
        }

        /* Dispatch */
        char *outbuf = malloc(MAX_OUTPUT);
        if (!outbuf) {
            const char *err = "{\"error\":\"out of memory\"}\n";
            (void)write_all(fd, err, strlen(err));
            close(fd);
            continue;
        }

        int truncated = 0;
        int exit_code = nfield_dispatch_status(cmd, outbuf, MAX_OUTPUT, &truncated);

        /* JSON-escape the output */
        size_t escaped_size = 6 * strlen(outbuf) + 1;
        char *escaped = malloc(escaped_size);
        if (!escaped) {
            free(outbuf);
            const char *err = "{\"error\":\"out of memory\"}\n";
            (void)write_all(fd, err, strlen(err));
            close(fd);
            continue;
        }
        if (!json_escape(outbuf, escaped, escaped_size)) {
            truncated = 1;
            exit_code = 125;
        }

        /* Send response */
        size_t response_size = strlen(escaped) + 160;
        char *response = malloc(response_size);
        if (response) {
            int len = snprintf(response, response_size,
                "{\"output\":\"%s\",\"exit_code\":%d,\"truncated\":%s}\n",
                escaped, exit_code, truncated ? "true" : "false");
            if (len > 0 && (size_t)len < response_size)
                (void)write_all(fd, response, (size_t)len);
            free(response);
        } else {
            const char *err = "{\"error\":\"out of memory\"}\n";
            (void)write_all(fd, err, strlen(err));
        }

        free(escaped);
        free(outbuf);
        close(fd);
    }
    return NULL;
}

/* ── Main daemon loop ────────────────────────────────── */

static volatile int running = 1;

static void handle_signal(int sig) {
    (void)sig;
    running = 0;
}

int daemon_main(int port, int num_threads) {
    signal(SIGINT, handle_signal);
    signal(SIGTERM, handle_signal);
    signal(SIGPIPE, SIG_IGN);

    /* Create socket */
    int server_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (server_fd < 0) { perror("socket"); return 1; }

    int opt = 1;
    setsockopt(server_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK); /* localhost only */
    addr.sin_port = htons((uint16_t)port);

    if (bind(server_fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        perror("bind");
        close(server_fd);
        return 1;
    }

    if (listen(server_fd, 64) < 0) {
        perror("listen");
        close(server_fd);
        return 1;
    }

    printf("nfield daemon listening on 127.0.0.1:%d (%d threads)\n", port, num_threads);
    fflush(stdout);

    /* Init queue and start workers */
    queue_init();
    pthread_t *threads = malloc((size_t)num_threads * sizeof(*threads));
    if (!threads) {
        close(server_fd);
        fprintf(stderr, "unable to allocate daemon thread table\n");
        return 1;
    }
    int started_threads = 0;
    for (int i = 0; i < num_threads; i++) {
        if (pthread_create(&threads[i], NULL, worker_thread, NULL) != 0) {
            pthread_mutex_lock(&queue.lock);
            queue.shutdown = 1;
            pthread_cond_broadcast(&queue.not_empty);
            pthread_cond_broadcast(&queue.not_full);
            pthread_mutex_unlock(&queue.lock);
            for (int joined = 0; joined < started_threads; joined++)
                pthread_join(threads[joined], NULL);
            free(threads);
            close(server_fd);
            fprintf(stderr, "unable to start daemon worker thread\n");
            return 1;
        }
        started_threads++;
    }

    /* Accept loop */
    while (running) {
        struct sockaddr_in client_addr;
        socklen_t client_len = sizeof(client_addr);
        int client_fd = accept(server_fd, (struct sockaddr *)&client_addr, &client_len);
        if (client_fd < 0) {
            if (errno == EINTR) continue;
            perror("accept");
            break;
        }

        /* Set a read timeout per connection */
        struct timeval tv = { .tv_sec = 5, .tv_usec = 0 };
        setsockopt(client_fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

        queue_push(client_fd);
    }

    /* Shutdown */
    printf("nfield daemon shutting down...\n");
    pthread_mutex_lock(&queue.lock);
    queue.shutdown = 1;
    pthread_cond_broadcast(&queue.not_empty);
    pthread_cond_broadcast(&queue.not_full);
    pthread_mutex_unlock(&queue.lock);

    for (int i = 0; i < num_threads; i++)
        pthread_join(threads[i], NULL);

    free(threads);
    close(server_fd);
    return 0;
}
