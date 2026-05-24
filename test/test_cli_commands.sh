#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

BIN="${BIN:-./nfield}"
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-10}"
POST_ROOT="${POST_ROOT:-blog-site}"

tests_run=0
tests_passed=0
tests_failed=0

fail() {
    tests_failed=$((tests_failed + 1))
    printf '  FAIL: %s\n' "$1"
}

pass() {
    tests_passed=$((tests_passed + 1))
}

run_capture() {
    local cmd="$1"
    local outfile="$2"
    local errfile="$3"

    timeout "$TIMEOUT_SECONDS" "$BIN" $cmd >"$outfile" 2>"$errfile"
}

assert_command_contains() {
    local cmd="$1"
    shift
    local out err
    out="$(mktemp)"
    err="$(mktemp)"
    tests_run=$((tests_run + 1))

    if ! run_capture "$cmd" "$out" "$err"; then
        fail "$cmd exited nonzero: $(head -n 2 "$err" | tr '\n' ' ')"
        rm -f "$out" "$err"
        return
    fi

    local ok=1
    local marker
    for marker in "$@"; do
        if ! grep -Fq "$marker" "$out"; then
            printf '  FAIL: %s missing marker: %s\n' "$cmd" "$marker"
            ok=0
        fi
    done

    if grep -Eq 'Unknown command|Routed to|not implemented|placeholder|TODO|FIXME' "$out"; then
        printf '  FAIL: %s printed placeholder/fallback text\n' "$cmd"
        ok=0
    fi

    if [ "$ok" -eq 1 ]; then
        pass
    else
        tests_failed=$((tests_failed + 1))
    fi

    rm -f "$out" "$err"
}

assert_command_unknown() {
    local cmd="$1"
    local out err
    out="$(mktemp)"
    err="$(mktemp)"
    tests_run=$((tests_run + 1))

    if run_capture "$cmd" "$out" "$err"; then
        printf '  FAIL: %s unexpectedly succeeded\n' "$cmd"
        tests_failed=$((tests_failed + 1))
        rm -f "$out" "$err"
        return
    fi

    if grep -Fq "Unknown command" "$err"; then
        pass
    else
        printf '  FAIL: %s did not report Unknown command\n' "$cmd"
        tests_failed=$((tests_failed + 1))
    fi

    rm -f "$out" "$err"
}

is_public_command() {
    local cmd="$1"
    local name="${cmd%% *}"
    case "$name" in
        field|table|table1|tables|verify|spectral|align|decompose|survey|range|polar|div|equations|coherence|analytic|help|collision_table|spectrum|autocorrelation|derangements|silent_primes|gate_width|fluctuation_sum|character_components|class_bias|class_means|centered_sum|mertens_growth|neutrality|neutrality_sweep|finite_det|mod3_means|gate|polarity_field|scale)
            return 0
            ;;
        ''|*[!0-9]*)
            return 1
            ;;
        *)
            return 0
            ;;
    esac
}

assert_all_try_it_commands_run() {
    local commands_file out err cmd
    commands_file="$(mktemp)"
    out="$(mktemp)"
    err="$(mktemp)"

    if ! compgen -G "$POST_ROOT/posts/*.md" >/dev/null &&
       ! compgen -G "$POST_ROOT/posts/try-it-specs/*.md" >/dev/null; then
        rm -f "$commands_file" "$out" "$err"
        return
    fi

    awk '/\$ \.\/nfield/ {
        line=$0
        sub(/^.*\$ \.\/nfield /, "", line)
        sub(/#.*/, "", line)
        gsub(/[[:space:]]+$/, "", line)
        print line
    }' "$POST_ROOT"/posts/*.md "$POST_ROOT"/posts/try-it-specs/*.md | sort -u >"$commands_file"

    while IFS= read -r cmd; do
        [ -n "$cmd" ] || continue
        if ! is_public_command "$cmd"; then
            continue
        fi
        tests_run=$((tests_run + 1))
        if ! run_capture "$cmd" "$out" "$err"; then
            fail "$cmd exited nonzero: $(head -n 2 "$err" | tr '\n' ' ')"
            continue
        fi
        if grep -Eq 'Unknown command|Routed to|not implemented|placeholder|TODO|FIXME' "$out"; then
            fail "$cmd printed placeholder/fallback text"
            continue
        fi
        pass
    done <"$commands_file"

    rm -f "$commands_file" "$out" "$err"
}

printf 'nfield CLI regression tests\n'
printf '==================================================\n\n'

printf 'blog Try-It smoke:\n'
assert_all_try_it_commands_run
printf '\n'

printf 'named command output contracts:\n'
assert_command_contains "scale" "Alignment Deficit Lattice" "beta(m)"
assert_command_contains "scale --chromatic" "Just Chromatic Scale" "Exact in the limit"
assert_command_contains "collision_table 7" "Collision periodic table, base 7 (mod 49)" "S(49 - a) = -1"
assert_command_contains "collision_table 10 --pairs" "Complement pairs:" "100-a" "sum"
assert_command_contains "gate 7" "family: r = 7" "gate width 9"
assert_command_contains "derangements 13" "deranging multipliers (9)" "mean over constructive"
assert_command_contains "finite_det 10 --lag 1" "Finite Determination" "PASS"
assert_command_contains "fluctuation_sum 10 --lag 1 --primes 10000" "Fluctuation sum Phi_x" "sum / log log p_max"
assert_command_contains "class_bias 10 --lag 1" "Per-class collision bias" "mean deviation"
assert_command_contains "character_components 10 --lag 1" "Character components" "Pearson correlation"
assert_command_contains "spectrum 13" "Cross-alignment matrix eigenvalues" "eigenvalues:"
assert_command_contains "coherence 20 --base 10" "Spectral geometry of the collision invariant" "coherence Hamiltonian"
assert_command_contains "polarity_field 10" "Polarity field" "Centered collision invariant"
assert_command_unknown "__not_a_public_command__"
printf '\n'

printf '==================================================\n'
printf '%d CLI tests: %d passed, %d failed\n' "$tests_run" "$tests_passed" "$tests_failed"

if [ "$tests_failed" -ne 0 ]; then
    exit 1
fi
