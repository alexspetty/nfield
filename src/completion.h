#ifndef NFIELD_COMPLETION_H
#define NFIELD_COMPLETION_H

int nfield_completion_command(int argc, char **argv);
int nfield_completion_candidates(int argc, char **argv);
void nfield_completion_help(void);
void nfield_commands_help(void);
void nfield_commands_json(void);
/* Arguments after "commands"; preserves the unfiltered text/JSON catalog. */
int nfield_commands_command(int argc, char **argv);
/* Print the metadata registry's ordinary names, or all names when requested. */
void nfield_command_names(int include_compatibility);

#endif
