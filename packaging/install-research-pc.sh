#!/bin/sh
# Write the optional research profile for the selected installation directories.
set -eu
if [ "$#" -ne 6 ]; then
    printf '%s\n' 'Usage: install-research-pc.sh FILE PREFIX LIBDIR INCLUDEDIR VERSION LIBRARIES' >&2
    exit 2
fi
target=$1
prefix=$2
library_dir=$3
include_dir=$4
version=$5
libraries=$6
if [ -z "$version" ] || [ -z "$libraries" ]; then
    printf '%s\n' 'The library version and research dependencies must not be empty.' >&2
    exit 2
fi
temporary=$(mktemp "${target}.XXXXXX")
trap 'rm -f "$temporary"' EXIT HUP INT TERM
{
    printf 'prefix=%s\n' "$prefix"
    printf 'libdir=%s\n' "$library_dir"
    printf 'includedir=%s\n\n' "$include_dir"
    printf '%s\n' 'Name: nfield-research'
    printf '%s\n' 'Description: Finite arithmetic, collision, spectral and weighted-remainder research interfaces'
    printf 'Version: %s\n' "$version"
    printf '%s\n' 'Libs: -L"${libdir}" -lnfield'
    printf 'Libs.private: %s\n' "$libraries"
    printf '%s\n' 'Cflags: -I"${includedir}"'
} > "$temporary"
chmod 644 "$temporary"
mv -f "$temporary" "$target"
trap - EXIT HUP INT TERM
