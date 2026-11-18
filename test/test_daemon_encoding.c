/* Exercise the daemon's actual encoder, including control bytes. */
#include "../src/daemon.c"

void dispatch_init(const char *path) { (void)path; }
int nfield_dispatch_status(const char *cmd, char *out, size_t size, int *truncated)
{
    (void)cmd;
    if (size) out[0] = '\0';
    if (truncated) *truncated = 0;
    return 0;
}

int main(void)
{
    char output[256], small[2], exact[7];
    unsigned checks = 0;
    if (!json_escape("\"\\\n\r\t\001\b\f\033", output, sizeof(output)) ||
        strcmp(output, "\\\"\\\\\\n\\r\\t\\u0001\\u0008\\u000c\\u001b")) return 1;
    checks++;
    if (!json_escape("\001", exact, sizeof(exact)) || strcmp(exact, "\\u0001")) return 1;
    checks++;
    if (json_escape("\001", small, sizeof(small)) || small[0]) return 1;
    checks++;
    if (json_escape("a", small, 0)) return 1;
    checks++;
    for (unsigned c = 1; c < 32; ++c) {
        char input[2] = {(char)c, '\0'};
        if (!json_escape(input, output, sizeof(output))) return 1;
        for (size_t i = 0; output[i]; ++i) if ((unsigned char)output[i] < 32) return 1;
        checks++;
    }
    if (!json_escape("plain text", output, sizeof(output)) || strcmp(output, "plain text")) return 1;
    checks++;
    printf("Daemon JSON encoding: %u checks passed.\n", checks);
    return 0;
}
