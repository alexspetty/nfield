#!/bin/sh
# Write pkg-config metadata for the selected installation directories.
set -eu

if [ "$#" -ne 5 ]; then
    printf '%s\n' 'Usage: install-pc.sh FILE PREFIX LIBDIR INCLUDEDIR VERSION' >&2
    exit 2
fi
target=$1
prefix=$2
library_dir=$3
include_dir=$4
version=$5
if [ -z "$version" ]; then
    printf '%s\n' 'The library version must not be empty.' >&2
    exit 2
fi

temporary=$(mktemp "${target}.XXXXXX")
trap 'rm -f "$temporary"' EXIT HUP INT TERM
{
    printf 'prefix=%s\n' "$prefix"
    printf 'libdir=%s\n' "$library_dir"
    printf 'includedir=%s\n\n' "$include_dir"
    printf '%s\n' 'Name: nfield'
    printf '%s\n' 'Description: Exact finite collision arithmetic and reset projections'
    printf 'Version: %s\n' "$version"
    printf '%s\n' 'Libs: -L"${libdir}" -lnfield'
    printf '%s\n' 'Libs.private: -lgmp'
    printf '%s\n' 'Cflags: -I"${includedir}"'
} > "$temporary"
chmod 644 "$temporary"
mv -f "$temporary" "$target"
trap - EXIT HUP INT TERM
