#!/usr/bin/env bash
# Discovery, exact results and error contracts of the installed command surface.
set -euo pipefail
cd "$(dirname "$0")/.."
BIN="${BIN:-./nfield}"
root="$(mktemp -d)"
trap 'rm -rf "$root"' EXIT
checks=0
pass() { checks=$((checks+1)); }
fail() { printf 'command contract failed: %s\n' "$*" >&2; exit 1; }
reject() {
    local expected="$1" phrase="$2"; shift 2
    local status=0
    "$BIN" "$@" >"$root/out" 2>"$root/error" || status=$?
    [ "$status" = "$expected" ] || fail "exit $status instead of $expected: $*"
    [ ! -s "$root/out" ] || fail "unexpected stdout: $*"
    grep -Fq -- "$phrase" "$root/error" || fail "missing error $phrase: $*"
    pass
}
"$BIN" commands --json >"$root/catalog"
./test/test_json_contracts catalog --raw <"$root/catalog"
"$BIN" verify reset-forest contracts --json >"$root/contracts"
./test/test_json_contracts contracts --raw <"$root/contracts"
"$BIN" reset-forest 31 --json | ./test/test_json_contracts forest --raw
"$BIN" reset-forest source 31 --json | ./test/test_json_contracts source --raw
"$BIN" reset-forest project 4 --modulus 6 --weights 1,-2,3/2,1 --json | ./test/test_json_contracts weighted --raw
"$BIN" help reset-forest project | ./test/test_json_contracts help --raw
"$BIN" primitive-character-cancellation inspect 5 1 1 | ./test/test_json_contracts fiber --raw

# A wrong mathematical value, omitted check or malformed document must fail.
sed 's/"assertions":501493/"assertions":501492/' "$root/contracts" >"$root/bad"
if ./test/test_json_contracts contracts --raw <"$root/bad" >/dev/null 2>&1; then fail 'wrong assertion total accepted'; fi
pass
sed 's/"checks":75/"checks":74/' "$root/contracts" >"$root/bad"
if ./test/test_json_contracts contracts --raw <"$root/bad" >/dev/null 2>&1; then fail 'omitted check accepted'; fi
pass
for invalid in '{"x":1,"x":2}' '[1,]' '{"x":01}' '{"x":"\q"}' 'true false'; do
    if printf '%s' "$invalid" | ./test/test_json_contracts parse --raw >/dev/null 2>&1; then fail 'malformed JSON accepted'; fi
    pass
done
printf '%s' '{"text":"quote\" slash\\ newline\n unicode\u03c0","items":[true,false,null,-1.25e2]}' | ./test/test_json_contracts parse --raw

# Every registered family, including compatibility names, exposes useful help.
"$BIN" __complete >"$root/names"
"$BIN" __complete --legacy >>"$root/names"
sort -u "$root/names" >"$root/unique"
while IFS= read -r family; do
    case "$family" in --*|'') continue;; esac
    "$BIN" help "$family" >"$root/help"
    grep -Fxq 'Your inputs' "$root/help" || fail "missing inputs for $family"
    grep -Fxq 'Result' "$root/help" || fail "missing result for $family"
    grep -Fxq 'Start here' "$root/help" || fail "missing example for $family"
    "$BIN" "$family" --help >"$root/help"
    if [ "$family" != help ]; then grep -Fxq 'Your inputs' "$root/help" || fail "missing --help for $family"; fi
    pass
done <"$root/unique"
# The compatibility name runs the same finite numerical comparisons.
"$BIN" verify decomposition >"$root/decomposition"
grep -Fq 'Decomposition compatibility check' "$root/decomposition" || fail 'decomposition compatibility route missing'
grep -Fq 'population formula at every base; total=14372' "$root/decomposition" || fail 'decomposition population not checked'
grep -Fq 'maximum diagonal-reduction error' "$root/decomposition" || fail 'decomposition diagonal comparison missing'
grep -Fq 'maximum Bernoulli-factorization error' "$root/decomposition" || fail 'decomposition factorization comparison missing'
grep -Fq 'parameterized transforms=669, including base 73' "$root/decomposition" || fail 'decomposition transforms not checked'
grep -Fq '6/6 verification groups passed.' "$root/decomposition" || fail 'decomposition checks failed'
grep -Fq '1/1 verifications passed.' "$root/decomposition" || fail 'decomposition result not propagated'
if grep -Eq 'by construction|Parseval|base 10:' "$root/decomposition"; then fail 'decomposition scope overclaim'; fi
pass
"$BIN" commands spectrum --examples >"$root/search"
grep -Fq 'nfield collision-spectrum-factorization inspect' "$root/search" || fail 'spectrum search lacks runnable example'
pass
"$BIN" commands nonexistent-quantity >"$root/search"
grep -Fq 'No matching commands' "$root/search" || fail 'empty search message'
pass
for mode in all coverage list theorem work; do
    reject 2 'removed' verify "$mode"
    reject 2 'removed' verify "$mode" --help
done
reject 2 'retired' verify gate-width --require-complete
reject 2 'retired' verify gate-width --source-root /missing
reject 1 'not supported' field 7 --json
reject 2 'Invalid source selection' reset-forest project 2 --json --csv
reject 2 'Usage:' verify reset-forest contracts --json --json
reject 2 'Expected an integer' field 999999999999999999999999
printf 'Command contracts: %d checks passed.\n' "$checks"
