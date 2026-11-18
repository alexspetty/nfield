#ifndef NFIELD_COMMAND_GUIDE_H
#define NFIELD_COMMAND_GUIDE_H

#include <stddef.h>

/* Research purpose and workflow, separate from syntax and calculation code. */
typedef struct {
    const char *name;
    const char *kind;
    const char *purpose;
    const char *inputs;
    const char *outputs;
    const char *example;
    const char *workflow;
    const char *limits;
} NfieldCommandGuide;

const NfieldCommandGuide *nfield_command_guide_lookup(const char *name);
const char *nfield_command_purpose(const char *name);
const char *nfield_command_canonical_name(const char *name);
int nfield_command_guide(const char *name);
/* Whether this action accepts the explicit --json or --csv format switch.
 * Verification checks use their mathematical family and check name. */
int nfield_command_format_supported(const char *family, const char *action,
                                   const char *format);
/* Full process argv. Return zero when valid, one after an error diagnostic. */
int nfield_command_format_guard(int argc, char **argv);

typedef struct {
    const char *family;
    const char *name;
    const char *kind;
    const char *purpose;
    const char *syntax;
    const char *inputs;
    const char *outputs;
    const char *example;
    const char *limits;
} NfieldActionGuide;

const NfieldActionGuide *nfield_action_guide_lookup(const char *family, const char *action);
const NfieldActionGuide *nfield_action_guide_at(const char *family, size_t index);
int nfield_action_guide(const char *family, const char *action);
const NfieldActionGuide *nfield_verify_action_guide_lookup(const char *family, const char *action);
int nfield_verify_action_guide(const char *family, const char *action);

#endif
