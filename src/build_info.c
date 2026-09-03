#include "build_info.h"

#ifndef NFIELD_BUILD_VERSION
#define NFIELD_BUILD_VERSION "unknown"
#endif

const char *nfield_build_version(void)
{
    return NFIELD_BUILD_VERSION;
}
