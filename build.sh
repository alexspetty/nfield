#!/bin/bash
# Build, test, and compile the nfield project.
#
# Examples:
#   ./build.sh all                                    Build everything
#   ./build.sh code                                   Build engine + run tests
#   ./build.sh test                                   Build and run unit tests
#   ./build.sh verify                                 Build verification programs
#   ./build.sh research                               Build all research papers
#   ./build.sh publication                            Build publication papers
#   ./build.sh papers                                 Build all papers
#   ./build.sh golden_ratio_selects_prime_three.tex   Build one paper
#   ./build.sh research/alignment_limit.tex           Build one paper by path

set -e

# ── Code builds ──────────────────────────────────────

build_code() {
    echo "Building nfield engine..."
    make -s clean 2>/dev/null || true
    make -s
    echo "  nfield built."
    echo ""
}

run_tests() {
    echo "Running unit tests..."
    make -s test
    echo ""
}

build_verify() {
    echo "Building verification programs..."
    make -s verify
    echo "  verify programs built."
    echo ""
}

# ── Paper builds ─────────────────────────────────────

build_one() {
    local texfile="$1"
    local dir=$(dirname "$texfile")
    local base=$(basename "$texfile" .tex)

    echo "  $base"
    cd "$dir"
    pdflatex -interaction=nonstopmode "$base.tex" > /dev/null 2>&1
    pdflatex -interaction=nonstopmode "$base.tex" > /dev/null 2>&1
    pdflatex -interaction=nonstopmode "$base.tex" > /dev/null 2>&1

    # Check for errors
    if grep -q "^! " "$base.log" 2>/dev/null; then
        echo "    ERROR - check $dir/$base.log"
        cd - > /dev/null
        return 1
    fi

    # Report warnings worth knowing about
    overfull=$(grep -c "Overfull" "$base.log" 2>/dev/null || true)
    undef=$(grep -c "undefined" "$base.log" 2>/dev/null || true)
    if [ "$overfull" -gt 0 ]; then
        echo "    $overfull overfull boxes"
    fi
    if [ "$undef" -gt 0 ]; then
        echo "    $undef undefined references"
    fi

    # Clean build artifacts, keep only pdf
    rm -f "$base.aux" "$base.out" "$base.toc" "$base.bbl" "$base.blg" "$base.log"

    cd - > /dev/null
}

build_dir() {
    local dir="$1"
    local errors=0
    local count=0

    echo "Building $dir/"
    for f in "$dir"/*.tex; do
        [ -f "$f" ] || continue
        if ! build_one "$f"; then
            errors=$((errors + 1))
        fi
        count=$((count + 1))
    done
    echo "  $count papers, $errors errors"
    echo ""
    return $errors
}

# ── Main ─────────────────────────────────────────────

if [ $# -eq 0 ]; then
    echo "nfield build system"
    echo ""
    echo "Usage: ./build.sh <target>"
    echo ""
    echo "Targets:"
    echo "  all           Build engine, run tests, build all papers"
    echo "  code          Build engine and run tests"
    echo "  test          Run unit tests only"
    echo "  verify        Build verification programs"
    echo "  papers        Build all papers (research + publication)"
    echo "  research      Build research papers"
    echo "  publication   Build publication papers"
    echo "  <file.tex>    Build a single paper"
    exit 1
fi

case "$1" in
    all)
        build_code
        run_tests
        build_verify
        total_errors=0
        build_dir research || total_errors=$((total_errors + $?))
        build_dir publication || total_errors=$((total_errors + $?))
        if [ "$total_errors" -eq 0 ]; then
            echo "All clean."
        else
            echo "$total_errors papers with errors."
            exit 1
        fi
        ;;
    code)
        build_code
        run_tests
        ;;
    test)
        run_tests
        ;;
    verify)
        build_code
        build_verify
        ;;
    papers)
        total_errors=0
        build_dir research || total_errors=$((total_errors + $?))
        build_dir publication || total_errors=$((total_errors + $?))
        if [ "$total_errors" -eq 0 ]; then
            echo "All clean."
        else
            echo "$total_errors papers with errors."
            exit 1
        fi
        ;;
    research|publication)
        build_dir "$1"
        ;;
    *)
        if [ -f "$1" ]; then
            build_one "$1"
        elif [ -f "research/$1" ]; then
            build_one "research/$1"
        elif [ -f "publication/$1" ]; then
            build_one "publication/$1"
        else
            echo "File not found: $1"
            exit 1
        fi
        ;;
esac
