#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
BIN="${BIN:-./nfield}"
root="$(mktemp -d)"
trap 'rm -rf "$root"' EXIT

"$BIN" reset-forest 31 >"$root/work"
grep -Fxq 'Complementary resets: 17 23 29' "$root/work"
if grep -Eq 'PASS|FAIL|checks passed' "$root/work"; then
    printf 'The operation emitted a verification report\n' >&2; exit 1
fi
"$BIN" reset-forest 5 --divisor 1 --json >"$root/json"
grep -Fq '"corrected_defect":"-1/225"' "$root/json"
grep -Fq '"return_window":null' "$root/json"
"$BIN" reset-forest source 31 --csv >"$root/source"
grep -Fxq '17,1,1,0,1' "$root/source"
grep -Fxq '1,1,1,4,-3' "$root/source"
awk -F, 'NR>1 {n++; sum+=$4; if ($4+$5!=1) exit 1} END {if (n!=30 || sum!=30) exit 1}' "$root/source"
"$BIN" reset-forest 31 --divisor 1 --csv >"$root/incoming"
grep -Fq '7,7,0,4,0,' "$root/incoming"
"$BIN" reset-forest 251 --returns 31 --json >"$root/upper"
grep -Fq '"prime":251' "$root/upper"

for input in '0' '2' '9' '257' '31x' '31 --divisor 0' '31 --divisor -1' \
    '31 --divisor 1/2' '31 --returns 2' '31 --returns 32' 'source' \
    '31 --json --csv' '31 --returns 3 --divisor 1' '31 --unknown' '31 --divisor'; do
    # Intentionally split plain test arguments; no shell evaluation.
    if "$BIN" reset-forest $input >"$root/out" 2>"$root/error"; then
        printf 'Accepted invalid input: %s\n' "$input" >&2; exit 1
    fi
    test ! -s "$root/out"
    test -s "$root/error"
done
"$BIN" verify reset-forest
printf 'Reset forest CLI contracts passed.\n'
