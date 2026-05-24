/*
 * dispatch.c -- popen-based command dispatch for daemon mode
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static char self_path[4096] = {0};

void dispatch_init(const char *argv0) {
    ssize_t len = readlink("/proc/self/exe", self_path, sizeof(self_path) - 1);
    if (len > 0) self_path[len] = '\0';
    else strncpy(self_path, argv0, sizeof(self_path) - 1);
}

int nfield_dispatch(const char *cmdline, char *outbuf, size_t outbuf_size) {
    outbuf[0] = '\0';

    if (!cmdline || !cmdline[0]) {
        snprintf(outbuf, outbuf_size, "Empty command\n");
        return 0;
    }

    /* Build shell command: self_path + args, with timeout */
    int tmo = 10;
    if (strncmp(cmdline, "verify", 6) == 0 ||
        strncmp(cmdline, "neutrality", 10) == 0) tmo = 30;
    char shell_cmd[8192];
    snprintf(shell_cmd, sizeof(shell_cmd), "timeout %d %s %s 2>&1", tmo, self_path, cmdline);

    FILE *fp = popen(shell_cmd, "r");
    if (!fp) {
        snprintf(outbuf, outbuf_size, "Internal error: popen failed\n");
        return -1;
    }

    size_t total = 0;
    while (total < outbuf_size - 1) {
        size_t n = fread(outbuf + total, 1, outbuf_size - 1 - total, fp);
        if (n == 0) break;
        total += n;
    }
    outbuf[total] = '\0';

    pclose(fp);
    return 0;
}
