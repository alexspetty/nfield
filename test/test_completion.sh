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

moment_candidates="$TEMP_ROOT/moment-candidates"
"$BIN" __complete short-sum-bernoulli-correlation >"$moment_candidates"
require_line "$moment_candidates" "moments" "magnitude moment action candidate"
require_line "$moment_candidates" "ledger" "magnitude ledger action candidate"
require_line "$moment_candidates" "verify" "magnitude verifier action candidate"

remainder_candidates="$TEMP_ROOT/remainder-candidates"
"$BIN" __complete weighted-remainder-state >"$remainder_candidates"
require_line "$remainder_candidates" "inspect" "remainder inspect action"
require_line "$remainder_candidates" "conductor" "remainder conductor action"
require_line "$remainder_candidates" "boundary" "exact boundary action"
require_line "$remainder_candidates" "ramp" "exact ramp integral action"
require_line "$remainder_candidates" "floor" "exact prime-square floor action"
require_line "$remainder_candidates" "straighten" "exact midpoint straightening action"
require_line "$remainder_candidates" "clock" "exact finite clock action"
require_line "$remainder_candidates" "clock-law" "exact finite clock law action"
require_line "$remainder_candidates" "age-budget" "exact stationary-age budget action"
require_line "$remainder_candidates" "finite-weights" "exact supplied finite weights action"
require_line "$remainder_candidates" "rows" "exact primitive conductor rows action"
require_line "$remainder_candidates" "increment-covariance" "exact increment covariance action"
require_line "$remainder_candidates" "increment-recurrence" "certified increment recurrence action"
require_line "$remainder_candidates" "fourier" "certified primitive Fourier coefficient action"
require_line "$remainder_candidates" "amplitude-refinement" "certified full amplitude refinement action"
require_line "$remainder_candidates" "expansion-constants" "rational amplitude constants action"
require_line "$remainder_candidates" "harmonic-expansion" "harmonic seed expansion action"
require_line "$remainder_candidates" "amplitude-expansion" "uniform amplitude expansion action"
require_line "$remainder_candidates" "deficit-series" "positive Dirichlet deficit action"
require_line "$remainder_candidates" "deficit-diagnostic" "weighted deficit positivity action"
require_line "$remainder_candidates" "spectral-product" "spectral Euler constant action"
require_line "$remainder_candidates" "spectral-mean" "spectral signed floor mean action"
require_line "$remainder_candidates" "spectral-energy" "full conductor energy action"
require_line "$remainder_candidates" "spectral-tail" "full spectral tail action"
require_line "$remainder_candidates" "character-phase" "complex character phase action"
require_line "$remainder_candidates" "character-table" "full unit character table action"
require_line "$remainder_candidates" "character-l" "odd character L-value action"
require_line "$remainder_candidates" "mixed-moment" "full odd mixed moment action"
require_line "$remainder_candidates" "cotangent-sums" "cotangent series and descent action"
require_line "$remainder_candidates" "harmonic-polylog" "rational complex harmonic polylog action"
require_line "$remainder_candidates" "harmonic-root" "harmonic root identity action"
require_line "$remainder_candidates" "harmonic-root-average" "finite root average action"
require_line "$remainder_candidates" "sine-transform" "signed finite sine transform action"
require_line "$remainder_candidates" "small-amplitudes" "small conductor amplitude examples action"
require_line "$remainder_candidates" "mass-inverse" "finite multiple-amplitude inverse action"
require_line "$remainder_candidates" "mass-recovery" "certified full mass recovery action"
require_line "$remainder_candidates" "variance" "proved full variance enclosure action"
require_line "$remainder_candidates" "perturbation" "exact collision perturbation action"
require_line "$remainder_candidates" "cycle" "exact cycle probability action"
require_line "$remainder_candidates" "cycle-tv" "exact total variation enclosure action"
require_line "$remainder_candidates" "covariance" "exact remainder covariance action"
require_line "$remainder_candidates" "amplitude" "exact amplitude enclosure action"
require_line "$remainder_candidates" "tree" "exact primitive square frontier action"
require_line "$remainder_candidates" "tree-node" "exact pair-tree node action"
require_line "$remainder_candidates" "weight" "exact primitive weight and inverse action"
require_line "$remainder_candidates" "budget" "exact reciprocal-address budget action"
require_line "$remainder_candidates" "mass" "exact retained and omitted mass action"
require_line "$remainder_candidates" "sawtooth" "exact midpoint sawtooth action"
require_line "$remainder_candidates" "dedekind" "exact Dedekind sum action"
require_line "$remainder_candidates" "gram" "exact sawtooth Haar pairing action"
require_line "$remainder_candidates" "sawtooth-mean" "exact conditional sawtooth action"
require_line "$remainder_candidates" "reset" "exact boundary increment action"
require_line "$remainder_candidates" "pairing" "certified residue pairing action"
require_line "$remainder_candidates" "forcing" "full divisor forcing action"
require_line "$remainder_candidates" "block" "exact deficit block action"
require_line "$remainder_candidates" "crt" "joint CRT action"
require_line "$remainder_candidates" "moment" "empirical mixed moment action"
require_line "$remainder_candidates" "haar-moment" "cutoff Haar moment action"
require_line "$remainder_candidates" "cylinder" "exact Haar cylinder action"
require_line "$remainder_candidates" "position" "certified position probability action"
require_line "$remainder_candidates" "position-weight" "certified individual period weight action"
require_line "$remainder_candidates" "conductor-full" "full conductor enclosure action"
require_line "$remainder_candidates" "conductor-beta" "positive regrouped coefficient enclosure action"
require_line "$remainder_candidates" "conductor-prime" "exact CRT prime candidate action"
require_line "$remainder_candidates" "conductor-extrema" "restricted gap enclosure action"
require_line "$remainder_candidates" "conductor-minimizers" "possible minimizer enumeration action"
require_line "$remainder_candidates" "activation" "exact Bernoulli cube action"
require_line "$remainder_candidates" "verify" "remainder verifier action"

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
