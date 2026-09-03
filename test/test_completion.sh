#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

BIN="${BIN:-./nfield}"
TEMP_ROOT="$(mktemp -d)"
trap 'rm -rf "$TEMP_ROOT"' EXIT

tests_run=0
tests_passed=0

pass() {
    tests_run=$((tests_run + 1))
    tests_passed=$((tests_passed + 1))
    printf '  %s: PASS\n' "$1"
}

fail() {
    tests_run=$((tests_run + 1))
    printf '  %s: FAIL\n' "$1" >&2
    exit 1
}

require_line() {
    local file="$1"
    local expected="$2"
    local label="$3"
    if grep -Fxq -- "$expected" "$file"; then
        pass "$label"
    else
        printf '    missing candidate: %s\n' "$expected" >&2
        fail "$label"
    fi
}

printf 'nfield completion and build-identity tests\n'
printf '==================================================\n\n'

top_level="$TEMP_ROOT/top-level"
"$BIN" __complete >"$top_level"
require_line "$top_level" "field" "core command candidate"
require_line "$top_level" "weighted-reference-profile" "tool-family candidate"
require_line "$top_level" "completion" "completion command candidate"
require_line "$top_level" "version" "version command candidate"
require_line "$top_level" "commands" "command-catalog candidate"
require_line "$top_level" "--help" "top-level help option"
require_line "$top_level" "--version" "top-level version option"

tool_candidates="$TEMP_ROOT/tool-candidates"
"$BIN" __complete weighted-reference-profile >"$tool_candidates"
for candidate in inspect branch torsion reflection-product oriented-words transport finite-orbit verify \
        --base --time --help; do
    require_line "$tool_candidates" "$candidate" \
        "weighted-reference-profile candidate $candidate"
done

help_candidates="$TEMP_ROOT/help-candidates"
"$BIN" __complete help >"$help_candidates"
for candidate in explore commands completion reading-map verification-map \
        tables weighted-reference-profile; do
    require_line "$help_candidates" "$candidate" "help topic $candidate"
done
if [ -z "$(sort "$help_candidates" | uniq -d)" ]; then
    pass "help candidates are unique"
else
    fail "help candidates are unique"
fi

verify_candidates="$TEMP_ROOT/verify-candidates"
"$BIN" __complete verify >"$verify_candidates"
for candidate in all digit-partition weighted-reference-profile antisymmetry; do
    require_line "$verify_candidates" "$candidate" "verifier candidate $candidate"
done

value_candidates="$TEMP_ROOT/value-candidates"
"$BIN" __complete digit-partition inspect 6 --base >"$value_candidates"
if [ ! -s "$value_candidates" ]; then
    pass "value-taking option suppresses command candidates"
else
    fail "value-taking option suppresses command candidates"
fi

dispatch_candidates="$TEMP_ROOT/dispatch-candidates"
sed -n 's/.*strcmp(cmd, "\([^"]*\)".*/\1/p' src/main.c | sort -u \
    >"$dispatch_candidates"
legacy_candidates="$TEMP_ROOT/legacy-candidates"
"$BIN" __complete --legacy >"$legacy_candidates"
all_registered="$TEMP_ROOT/all-registered"
sort -u "$top_level" "$legacy_candidates" >"$all_registered"
while IFS= read -r command; do
    [ -n "$command" ] || continue
    if ! grep -Fxq -- "$command" "$all_registered"; then
        printf '    dispatch command is absent from completion: %s\n' \
            "$command" >&2
        fail "dispatch registry coverage"
    fi
done <"$dispatch_candidates"
pass "dispatch registry coverage"

bash_completion="$TEMP_ROOT/nfield.bash"
"$BIN" completion bash >"$bash_completion"
if bash -n "$bash_completion"; then
    pass "generated Bash syntax"
else
    fail "generated Bash syntax"
fi

# shellcheck disable=SC1090
source "$bash_completion"
COMP_WORDS=("$BIN" "fi")
COMP_CWORD=1
_nfield_complete
if printf '%s\n' "${COMPREPLY[@]}" | grep -Fxq "field" &&
        printf '%s\n' "${COMPREPLY[@]}" | grep -Fxq \
            "finite-determination" &&
        ! printf '%s\n' "${COMPREPLY[@]}" | grep -Fxq "finite_det"; then
    pass "Bash nfield fi Tab choices"
else
    fail "Bash nfield fi Tab choices"
fi

COMP_WORDS=("$BIN" "weighted-ref")
COMP_CWORD=1
_nfield_complete
if printf '%s\n' "${COMPREPLY[@]}" | grep -Fxq \
        "weighted-reference-profile"; then
    pass "Bash top-level Tab completion"
else
    fail "Bash top-level Tab completion"
fi

COMP_WORDS=("$BIN" "weighted-reference-profile" "ref")
COMP_CWORD=2
_nfield_complete
if printf '%s\n' "${COMPREPLY[@]}" | grep -Fxq "reflection-product"; then
    pass "Bash action Tab completion"
else
    fail "Bash action Tab completion"
fi

for shell_name in zsh fish; do
    generated="$TEMP_ROOT/nfield.$shell_name"
    "$BIN" completion "$shell_name" >"$generated"
    if grep -Fq "nfield" "$generated" && grep -Fq "__complete" "$generated"; then
        pass "generated $shell_name completion"
    else
        fail "generated $shell_name completion"
    fi
done

invalid_out="$TEMP_ROOT/invalid-out"
invalid_err="$TEMP_ROOT/invalid-err"
if "$BIN" completion powershell >"$invalid_out" 2>"$invalid_err"; then
    fail "unsupported shell rejection"
elif grep -Fq "Unsupported shell: powershell" "$invalid_err"; then
    pass "unsupported shell rejection"
else
    fail "unsupported shell rejection"
fi

version_out="$TEMP_ROOT/version"
"$BIN" --version >"$version_out"
if grep -Eq '^nfield \.:\. [0-9]{4}\.[0-9]{4}\.[0-9]{6} \| A\. S\. Petty, 2020-2026$' \
        "$version_out"; then
    pass "numeric build version format"
else
    fail "numeric build version format"
fi

if [ "$("$BIN" --version)" = "$("$BIN" version)" ]; then
    pass "version command alias"
else
    fail "version command alias"
fi

timed_out="$TEMP_ROOT/timed"
"$BIN" field 7 --base 1222 --time >"$timed_out"
timed_line="$(tail -n 1 "$timed_out")"
if grep -Eq '^([0-9]+\.[0-9]{6} s|[0-9]+\.[0-9]{3} ms|[0-9]+\.[0-9]{3} us|[0-9]+ ns)$' \
        <<<"$timed_line"; then
    pass "adaptive high-resolution command timing"
else
    printf '    unexpected timing line: %s\n' "$timed_line" >&2
    fail "adaptive high-resolution command timing"
fi

printf '\n%d completion tests: %d passed, 0 failed\n' \
    "$tests_run" "$tests_passed"
