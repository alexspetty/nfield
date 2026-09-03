/* Direct, shell-free command dispatch for daemon mode. */

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

#define DISPATCH_PATH_CAPACITY 4096
#define DISPATCH_COMMAND_CAPACITY 4096
#define DISPATCH_MAX_ARGUMENTS 128

static char self_path[DISPATCH_PATH_CAPACITY] = {0};

void dispatch_init(const char *argv0)
{
    ssize_t length = readlink(
        "/proc/self/exe", self_path, sizeof(self_path) - 1);
    if (length > 0) self_path[length] = '\0';
    else (void)snprintf(self_path, sizeof(self_path), "%s", argv0);
}

static int dispatch_starts_with(const char *command, const char *prefix)
{
    return strncmp(command, prefix, strlen(prefix)) == 0;
}

static int dispatch_timeout_seconds(const char *command)
{
    int timeout = 10;
    if (dispatch_starts_with(command, "verify") ||
        dispatch_starts_with(command, "neutrality") ||
        dispatch_starts_with(command, "spectral-structure verify") ||
        dispatch_starts_with(command, "phase-gate verify") ||
        dispatch_starts_with(command, "bin-derangements verify") ||
        dispatch_starts_with(command, "collision-characters verify") ||
        dispatch_starts_with(command, "collision-characters snapshot") ||
        dispatch_starts_with(command, "silent-primes verify") ||
        dispatch_starts_with(command, "silent-primes snapshot") ||
        dispatch_starts_with(command, "collision-fluctuation verify") ||
        dispatch_starts_with(command, "collision-fluctuation snapshot") ||
        dispatch_starts_with(command, "collision-centering verify") ||
        dispatch_starts_with(command, "collision-centering snapshot") ||
        dispatch_starts_with(command, "centered-collision verify") ||
        dispatch_starts_with(command, "centered-collision snapshot") ||
        dispatch_starts_with(command, "collision-table verify") ||
        dispatch_starts_with(command, "collision-periodic-table verify") ||
        dispatch_starts_with(command, "collision-transform verify") ||
        dispatch_starts_with(command, "collision-transform snapshot") ||
        dispatch_starts_with(command, "residue-three-neutrality verify") ||
        dispatch_starts_with(command, "residue-three-neutrality snapshot") ||
        dispatch_starts_with(command, "neutrality-theorem verify") ||
        dispatch_starts_with(command, "neutrality-theorem snapshot") ||
        dispatch_starts_with(command, "compatible-residue-channels") ||
        dispatch_starts_with(command, "general-neutrality"))
        timeout = 30;

    if (dispatch_starts_with(command, "finite-character-pairing") ||
        dispatch_starts_with(command, "coprime-base-orthogonality") ||
        dispatch_starts_with(command, "natural-prime-sum-window") ||
        dispatch_starts_with(command, "primitive-odd-sector") ||
        dispatch_starts_with(command, "conjugate-pair-relabeling") ||
        dispatch_starts_with(command, "additive-reflection-well") ||
        dispatch_starts_with(command, "reflected-prime-pair-sign") ||
        dispatch_starts_with(command, "goldbach-obstruction") ||
        dispatch_starts_with(command, "collision-spectrum-factorization") ||
        dispatch_starts_with(command, "special-value-moment") ||
        dispatch_starts_with(command, "base-five-cyclotomic-identity") ||
        dispatch_starts_with(command, "short-sum-bernoulli-correlation") ||
        dispatch_starts_with(command, "primitive-character-cancellation") ||
        dispatch_starts_with(command, "periodic-zeta-factorization") ||
        dispatch_starts_with(command, "collision-boundary-recovery") ||
        dispatch_starts_with(command, "active-collision-channel") ||
        dispatch_starts_with(command, "collision-coordinate") ||
        dispatch_starts_with(command, "finite-determination") ||
        dispatch_starts_with(command, "reflection-identity") ||
        dispatch_starts_with(command, "half-group") ||
        dispatch_starts_with(command, "all-prime-collision-label") ||
        dispatch_starts_with(command, "finite-spectral-quotient") ||
        dispatch_starts_with(command, "finite-prefix-slice") ||
        dispatch_starts_with(command, "oriented-digit-comparison") ||
        dispatch_starts_with(command, "boundary-bernoulli-factorization") ||
        dispatch_starts_with(command, "boundary-conductor-ledger") ||
        dispatch_starts_with(command, "finite-state-orbit-boundary") ||
        dispatch_starts_with(command, "full-orbit-energy") ||
        dispatch_starts_with(command, "quadratic-orbit-energy") ||
        dispatch_starts_with(command, "subgroup-jacobi-expansion") ||
        dispatch_starts_with(command, "prime-base-collision-energy") ||
        dispatch_starts_with(command, "arithmetic-boundary-defect") ||
        dispatch_starts_with(command, "carry-completed-carrier"))
        timeout = 60;
    if (strcmp(command, "verify") == 0 ||
        dispatch_starts_with(command, "verify "))
        timeout = 60;
    return timeout;
}

static int dispatch_forbidden_character(unsigned char character)
{
    if (character < 32 || character == 127) return 1;
    return strchr("\"'\\`$;&|<>(){}[]!*?", (int)character) != NULL;
}

static int dispatch_parse(
        const char *command, char *storage, size_t storage_size,
        char **arguments, int *argument_count)
{
    if (!command || !storage || storage_size == 0 || !arguments ||
        !argument_count)
        return 0;
    size_t length = strlen(command);
    if (length == 0 || length >= storage_size) return 0;
    for (size_t index = 0; index < length; index++) {
        unsigned char character = (unsigned char)command[index];
        if (character == ' ' || character == '\t') continue;
        if (dispatch_forbidden_character(character)) return 0;
    }
    memcpy(storage, command, length + 1);

    int count = 1;
    arguments[0] = self_path;
    char *cursor = storage;
    while (*cursor != '\0') {
        while (*cursor == ' ' || *cursor == '\t') cursor++;
        if (*cursor == '\0') break;
        if (count >= DISPATCH_MAX_ARGUMENTS) return 0;
        arguments[count++] = cursor;
        while (*cursor != '\0' && *cursor != ' ' && *cursor != '\t')
            cursor++;
        if (*cursor != '\0') *cursor++ = '\0';
    }
    if (count == 1) return 0;
    arguments[count] = NULL;
    *argument_count = count;
    return 1;
}

static long long dispatch_monotonic_milliseconds(void)
{
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    return (long long)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static void dispatch_append(
        char *output, size_t output_size, size_t *used,
        const char *source, size_t source_size)
{
    if (*used >= output_size - 1) return;
    size_t available = output_size - 1 - *used;
    size_t copied = source_size < available ? source_size : available;
    memcpy(output + *used, source, copied);
    *used += copied;
    output[*used] = '\0';
}

int nfield_dispatch(const char *command, char *output, size_t output_size)
{
    if (!output || output_size == 0) return -1;
    output[0] = '\0';
    if (!command || command[0] == '\0') {
        (void)snprintf(output, output_size, "Empty command\n");
        return 0;
    }

    char storage[DISPATCH_COMMAND_CAPACITY];
    char *arguments[DISPATCH_MAX_ARGUMENTS + 1];
    int argument_count = 0;
    if (!dispatch_parse(
            command, storage, sizeof(storage), arguments, &argument_count)) {
        (void)snprintf(
            output, output_size,
            "Invalid command syntax: use plain arguments without shell operators\n");
        return 0;
    }
    (void)argument_count;

    int descriptors[2];
    if (pipe(descriptors) != 0) {
        (void)snprintf(output, output_size, "Internal error: pipe failed\n");
        return -1;
    }
    posix_spawn_file_actions_t actions;
    int spawn_error = posix_spawn_file_actions_init(&actions);
    int actions_initialized = spawn_error == 0;
    if (spawn_error == 0)
        spawn_error = posix_spawn_file_actions_addclose(
            &actions, descriptors[0]);
    if (spawn_error == 0)
        spawn_error = posix_spawn_file_actions_adddup2(
            &actions, descriptors[1], STDOUT_FILENO);
    if (spawn_error == 0)
        spawn_error = posix_spawn_file_actions_adddup2(
            &actions, descriptors[1], STDERR_FILENO);
    if (spawn_error == 0)
        spawn_error = posix_spawn_file_actions_addclose(
            &actions, descriptors[1]);

    pid_t child = -1;
    if (spawn_error == 0)
        spawn_error = posix_spawn(
            &child, self_path, &actions, NULL, arguments, environ);
    if (actions_initialized)
        (void)posix_spawn_file_actions_destroy(&actions);
    if (spawn_error != 0) {
        close(descriptors[0]);
        close(descriptors[1]);
        (void)snprintf(output, output_size, "Internal error: spawn failed\n");
        return -1;
    }
    close(descriptors[1]);
    int flags = fcntl(descriptors[0], F_GETFL, 0);
    if (flags >= 0) (void)fcntl(descriptors[0], F_SETFL, flags | O_NONBLOCK);

    int timeout_seconds = dispatch_timeout_seconds(command);
    long long started = dispatch_monotonic_milliseconds();
    long long deadline = started < 0
        ? -1
        : started + (long long)timeout_seconds * 1000;
    size_t used = 0;
    int pipe_open = 1;
    int child_reaped = 0;
    int status = 0;
    int timed_out = 0;

    while (pipe_open || !child_reaped) {
        int wait_milliseconds = 100;
        if (deadline >= 0) {
            long long now = dispatch_monotonic_milliseconds();
            if (now >= deadline) {
                timed_out = 1;
                break;
            }
            long long remaining = deadline - now;
            if (remaining < wait_milliseconds)
                wait_milliseconds = (int)remaining;
        }

        if (pipe_open) {
            struct pollfd descriptor = {
                .fd = descriptors[0],
                .events = POLLIN | POLLHUP,
                .revents = 0
            };
            int poll_result;
            do {
                poll_result = poll(&descriptor, 1, wait_milliseconds);
            } while (poll_result < 0 && errno == EINTR);
            if (poll_result < 0) break;
            if (poll_result > 0 &&
                (descriptor.revents & (POLLIN | POLLHUP | POLLERR))) {
                for (;;) {
                    char chunk[4096];
                    ssize_t received = read(descriptors[0], chunk, sizeof(chunk));
                    if (received > 0) {
                        dispatch_append(
                            output, output_size, &used,
                            chunk, (size_t)received);
                        continue;
                    }
                    if (received == 0) {
                        close(descriptors[0]);
                        pipe_open = 0;
                    }
                    if (received < 0 && errno != EAGAIN && errno != EWOULDBLOCK) {
                        close(descriptors[0]);
                        pipe_open = 0;
                    }
                    break;
                }
            }
        }

        if (!child_reaped) {
            pid_t waited = waitpid(child, &status, WNOHANG);
            if (waited == child) child_reaped = 1;
            else if (waited < 0 && errno != EINTR) child_reaped = 1;
        }
    }

    if (timed_out) {
        (void)kill(child, SIGKILL);
        while (waitpid(child, &status, 0) < 0 && errno == EINTR) { }
        static const char timeout_message[] = "Command timed out\n";
        dispatch_append(
            output, output_size, &used,
            timeout_message, sizeof(timeout_message) - 1);
    } else if (!child_reaped) {
        while (waitpid(child, &status, 0) < 0 && errno == EINTR) { }
    }
    if (pipe_open) close(descriptors[0]);
    output[used] = '\0';
    return 0;
}
