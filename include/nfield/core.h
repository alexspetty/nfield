#ifndef NFIELD_PUBLIC_CORE_H
#define NFIELD_PUBLIC_CORE_H

/* libnfield C API. Library versions are separate from CLI build dates. */
#define NFIELD_VERSION "1.0.0"
#define NFIELD_API_VERSION 1u

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
    NFIELD_OK = 0,
    NFIELD_EINVAL = 1,       /* null argument, invalid selection or number */
    NFIELD_ERANGE = 2,      /* unsupported dimension or index */
    NFIELD_ESTATE = 3,      /* result has not been computed */
    NFIELD_ENODATA = 4,     /* requested quantity was not computed */
    NFIELD_ENOMEM = 5       /* result-object allocation failed */
} nfield_status;

const char *nfield_version(void);
unsigned nfield_api_version(void);
/* Returned strings are static and must not be freed. Unknown status is safe. */
const char *nfield_status_string(nfield_status status);

#ifdef __cplusplus
}
#endif
#endif
