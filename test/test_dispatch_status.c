#define _POSIX_C_SOURCE 200809L
#include <signal.h>
#include <stdio.h>
#include <string.h>

extern void dispatch_init(const char *argv0);
extern int nfield_dispatch_status(const char *, char *, size_t, int *);

static int checks, failures;
static void check(int ok, const char *description)
{
    ++checks;
    if (!ok) { ++failures; fprintf(stderr, "FAIL: %s\n", description); }
}

int main(int argc, char **argv)
{
    if (argc > 1) {
        if (!strcmp(argv[1], "small")) { puts("usable result"); return 0; }
        if (!strcmp(argv[1], "failed")) { fputs("invalid input\n", stderr); return 3; }
        if (!strcmp(argv[1], "large")) {
            for (int i = 0; i < 512; ++i) putchar('x');
            return 0;
        }
        if (!strcmp(argv[1], "signal")) { raise(SIGTERM); return 1; }
        return 2;
    }
    dispatch_init(argv[0]);
    char output[64]; int truncated = -1;
    int status = nfield_dispatch_status("small", output, sizeof(output), &truncated);
    check(status == 0 && !strcmp(output, "usable result\n"), "successful result");
    check(truncated == 0, "complete result has no truncation");
    status = nfield_dispatch_status("failed", output, sizeof(output), &truncated);
    check(status == 3 && !strcmp(output, "invalid input\n"), "child error is retained");
    status = nfield_dispatch_status("large", output, sizeof(output), &truncated);
    check(status == 125 && truncated == 1, "overflow is an explicit failure");
    check(strlen(output) == sizeof(output) - 1, "overflow remains terminated and bounded");
    status = nfield_dispatch_status("small", output, sizeof(output), &truncated);
    check(status == 0 && truncated == 0, "next request resets overflow state");
    status = nfield_dispatch_status("signal", output, sizeof(output), &truncated);
    check(status == 128 + SIGTERM, "termination signal is retained");
    check(nfield_dispatch_status("", output, sizeof(output), &truncated) == 2,
          "empty request rejected");
    check(nfield_dispatch_status("small;large", output, sizeof(output), &truncated) == 2,
          "shell syntax rejected");
    printf("Dispatch contracts: %d/%d passed.\n", checks - failures, checks);
    return failures ? 1 : 0;
}
