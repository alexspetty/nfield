#ifndef NFIELD_VERIFICATION_ROUTES_H
#define NFIELD_VERIFICATION_ROUTES_H

#include <stddef.h>

/* Arguments follow "nfield verify". -1 means this route is not owned here. */
int nfield_verify_route(int argc, char **argv);
/* Reject removed modes and registry flags before help or format dispatch. */
int nfield_verify_retired_request(int argc, char **argv);
int nfield_verify_action_is_fixed(const char *family, const char *action);
void nfield_verify_actions(const char *family);
void nfield_verify_routes_help(const char *family);
const char *nfield_verify_action_name(const char *family, size_t index);
const char *nfield_verify_action_legacy_name(const char *family, const char *action);
const char *nfield_verify_action_options(const char *family, const char *action);

#endif
