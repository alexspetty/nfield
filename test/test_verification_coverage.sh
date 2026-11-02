#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

LEDGER="${VERIFICATION_LEDGER:-VERIFICATION_COVERAGE.md}"

test -s "$LEDGER"

titles_file="$(mktemp)"
trap 'rm -f "$titles_file"' EXIT

awk -F '|' '
    /^\|/ {
        title=$2
        status=$4
        gsub(/^[[:space:]]+|[[:space:]]+$/, "", title)
        gsub(/^[[:space:]]+|[[:space:]]+$/, "", status)
        if (title != "" && title != "Title" && title != "---" && status != "")
            print title "\t" status
    }
' "$LEDGER" >"$titles_file"

expected="$(wc -l <"$titles_file" | tr -d ' ')"
if [ "$expected" -eq 0 ]; then
    printf 'no public titles found in verification ledger\n' >&2
    exit 1
fi

failures=0
ready=0
while IFS=$'\t' read -r title status; do
    if [ "$status" != "ready" ]; then
        printf 'coverage ledger title is not ready: %s (%s)\n' \
            "$title" "$status" >&2
        failures=$((failures + 1))
    else
        ready=$((ready + 1))
    fi
done <"$titles_file"

last_title="$(tail -n 1 "$titles_file" | cut -f 1)"
if [ "$last_title" != "Collision Calculus: Boundary Readings, Energy and Refinement" ]; then
    printf 'public ledger has an unexpected final title: %s\n' "$last_title" >&2
    failures=$((failures + 1))
fi


python3 test/test_conservation_coverage.py
python3 test/test_published_extensions.py

unpublished_title="The Arithmetic"" Scalar"
if grep -Fqi "$unpublished_title" "$LEDGER"; then
    printf 'unpublished title found in public verification ledger\n' >&2
    failures=$((failures + 1))
fi

if grep -R -Eqi --include='*.c' --include='*.h' \
       'paper[[:space:]_-]*#?[[:space:]_-]*[0-9]+' src ||
   grep -Eqi 'paper[[:space:]_-]*#?[[:space:]_-]*[0-9]+' \
       README.md VERIFICATION_COVERAGE.md; then
    printf 'numbered paper identifier found in public source, help, or coverage\n' >&2
    exit 1
fi

if find . -type f -print | grep -Eqi \
       '/(paper|manuscript)[_-]*#?[0-9]+'; then
    printf 'numbered paper or manuscript identifier found in public filename\n' >&2
    exit 1
fi

for source in src/*.c; do
    case "$source" in
        src/main.c|src/daemon.c|src/dispatch.c) continue ;;
    esac
    if ! grep -Fq -- "$source" Makefile; then
        printf 'public source is not compiled by the canonical Makefile: %s\n' \
            "$source" >&2
        exit 1
    fi
done

if [ "$failures" -ne 0 ]; then
    exit 1
fi

printf 'verification coverage: %s/%s titles ready; object naming and source inclusion PASS\n' \
    "$ready" "$expected"
