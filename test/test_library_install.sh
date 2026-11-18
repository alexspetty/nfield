#!/bin/sh
# Exercise an installed consumer without source-tree headers or private APIs.
set -eu

project=${1:-$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)}
project=$(CDPATH= cd -- "$project" && pwd)
stage=$(mktemp -d "${TMPDIR:-/tmp}/nfield-library-install.XXXXXX")
cleanup() {
    if [ "${NFIELD_INSTALL_TEST_KEEP:-0}" = 1 ]; then
        printf 'Installation test files retained at %s\n' "$stage"
    else
        rm -rf -- "$stage"
    fi
}
trap cleanup EXIT HUP INT TERM
fail() { printf 'library installation: %s\n' "$*" >&2; exit 1; }

destination="$stage/staging root"
prefix='/opt/nfield API test'
installed="$destination$prefix"
consumer="$stage/standalone consumer"
mkdir -p "$consumer"
make -C "$project" install-lib "DESTDIR=$destination" "PREFIX=$prefix" > "$stage/install.log" 2>&1 || {
    cat "$stage/install.log" >&2; fail 'install-lib failed';
}

test -f "$installed/lib/libnfield.a" || fail 'missing library'
test -f "$installed/lib/pkgconfig/nfield.pc" || fail 'missing pkg-config metadata'
for name in core collision nfield; do
    test -f "$installed/include/nfield/$name.h" || fail "missing $name.h"
done
test -f "$installed/share/doc/nfield/LIBRARY.md" || fail 'missing guide'
for name in forest_readings.c source_projection.c source_divisor.c Makefile; do
    test -f "$installed/share/doc/nfield/examples/$name" || fail "missing example $name"
done
# Compare the complete installed selection, including its separate core/research profiles.
(cd "$installed" && find . -type f | sed 's|^./||' | LC_ALL=C sort) > "$stage/installed-files.txt"
cat > "$stage/expected-files.txt" <<'FILES'
include/nfield/collision.h
include/nfield/core.h
include/nfield/nfield.h
include/nfield/research.h
include/nfield/research/arithmetic.h
include/nfield/research/boundary_spectrum.h
include/nfield/research/collision_capacity_generation.h
include/nfield/research/collision_capacity_transition.h
include/nfield/research/collision_kernel_readout.h
include/nfield/research/collision_magnitude_moments.h
include/nfield/research/collision_sampling.h
include/nfield/research/collision_spectrum_core.h
include/nfield/research/finite_character_core.h
include/nfield/research/native_arithmetic.h
include/nfield/research/native_directional.h
include/nfield/research/native_refinement.h
include/nfield/research/orbit_boundary_core.h
include/nfield/research/periodic_zeta_core.h
include/nfield/research/primitive_odd_sector_core.h
include/nfield/research/weighted_remainder_activation.h
include/nfield/research/weighted_remainder_alignment.h
include/nfield/research/weighted_remainder_alignment_growth.h
include/nfield/research/weighted_remainder_alignment_local.h
include/nfield/research/weighted_remainder_amplitude.h
include/nfield/research/weighted_remainder_character.h
include/nfield/research/weighted_remainder_clock.h
include/nfield/research/weighted_remainder_complex.h
include/nfield/research/weighted_remainder_conductor.h
include/nfield/research/weighted_remainder_constants.h
include/nfield/research/weighted_remainder_cotangent.h
include/nfield/research/weighted_remainder_cylinder.h
include/nfield/research/weighted_remainder_dirichlet.h
include/nfield/research/weighted_remainder_exact.h
include/nfield/research/weighted_remainder_expansion.h
include/nfield/research/weighted_remainder_floor.h
include/nfield/research/weighted_remainder_fourier.h
include/nfield/research/weighted_remainder_harmonic_root.h
include/nfield/research/weighted_remainder_increment.h
include/nfield/research/weighted_remainder_joint.h
include/nfield/research/weighted_remainder_law.h
include/nfield/research/weighted_remainder_pairing.h
include/nfield/research/weighted_remainder_power.h
include/nfield/research/weighted_remainder_primitive.h
include/nfield/research/weighted_remainder_rows.h
include/nfield/research/weighted_remainder_sawtooth.h
include/nfield/research/weighted_remainder_small_amplitude.h
include/nfield/research/weighted_remainder_spectral.h
include/nfield/research/weighted_remainder_state.h
include/nfield/research/weighted_remainder_weights.h
lib/libnfield.a
lib/pkgconfig/nfield-research.pc
lib/pkgconfig/nfield.pc
share/doc/nfield/LIBRARY.md
share/doc/nfield/RESEARCH_LIBRARY.md
share/doc/nfield/examples/Makefile
share/doc/nfield/examples/forest_readings.c
share/doc/nfield/examples/source_divisor.c
share/doc/nfield/examples/source_projection.c
FILES
cmp "$stage/installed-files.txt" "$stage/expected-files.txt" || fail 'unexpected installed file selection'
if grep -F "$destination" "$installed/lib/pkgconfig/nfield.pc" >/dev/null; then
    fail 'pkg-config metadata contains its staging directory'
fi
grep -Fx "prefix=$prefix" "$installed/lib/pkgconfig/nfield.pc" >/dev/null || fail 'incorrect prefix'
if grep -F "$destination" "$installed/lib/pkgconfig/nfield-research.pc" >/dev/null; then
    fail 'research pkg-config metadata contains its staging directory'
fi
grep -Fx "prefix=$prefix" "$installed/lib/pkgconfig/nfield-research.pc" >/dev/null || fail 'incorrect research prefix'

ar t "$installed/lib/libnfield.a" | LC_ALL=C sort > "$stage/members.txt"
cat > "$stage/expected-members.txt" <<'MEMBERS'
active_collision_channel.o
additive_reflection_well.o
alignment_limit.o
all_prime_collision_label.o
analytic.o
arithmetic_boundary_defect.o
autocorrelation_formula.o
base_five_cyclotomic_identity.o
bin_derangements.o
boundary_bernoulli_factorization.o
boundary_spectrum.o
boundary_spectrum_verify.o
carry_completed_carrier.o
centered_collision_sum.o
centered_collision_table.o
coherence.o
coherence_decomposition.o
collision_boundary_recovery.o
collision_capacity_generation.o
collision_capacity_generation_verify.o
collision_capacity_transition.o
collision_capacity_transition_verify.o
collision_character_structure.o
collision_coordinate.o
collision_fluctuation_sum.o
collision_kernel_readout.o
collision_magnitude_moments.o
collision_periodic_table.o
collision_sampling.o
collision_sampling_kernel.o
collision_sampling_verify.o
collision_spectrum_core.o
collision_spectrum_factorization.o
collision_table_core.o
collision_transform_strip.o
compatible_residue_channels.o
conjugate_pair_relabeling.o
coprime_base_orthogonality.o
cross_alignment.o
deficit_lattice.o
digit_partition.o
field.o
field_observation.o
finite_character_core.o
finite_character_pairing.o
finite_determination.o
finite_prefix_slice.o
finite_spectral_quotient.o
finite_state_orbit_boundary.o
full_orbit_energy.o
goldbach_obstruction.o
half_group.o
invariants.o
library.o
native_arithmetic.o
native_directional.o
native_refinement.o
natural_prime_sum_window.o
orbit_boundary_core.o
oriented_digit_comparison.o
output.o
periodic_zeta_core.o
periodic_zeta_factorization.o
phase_filtered_ramanujan.o
prime_base_collision_energy.o
primitive_character_cancellation.o
primitive_odd_sector.o
primitive_odd_sector_core.o
quadratic_orbit_energy.o
reciprocal_square_selection.o
reflection_identity.o
repetend.o
reset_forest.o
reset_source.o
residue_three_neutrality.o
scale.o
short_sum_bernoulli_correlation.o
silent_primes_variance.o
special_value_moment.o
spectral_power.o
spectral_structure.o
subgroup_jacobi_expansion.o
terminal_collision_conductor_ledger.o
terminal_collision_conductor_ledger_reference.o
three_tier.o
weighted_reference_profile.o
weighted_remainder_activation.o
weighted_remainder_alignment.o
weighted_remainder_alignment_growth.o
weighted_remainder_alignment_local.o
weighted_remainder_amplitude.o
weighted_remainder_character.o
weighted_remainder_clock.o
weighted_remainder_complex.o
weighted_remainder_conductor.o
weighted_remainder_constants.o
weighted_remainder_cotangent.o
weighted_remainder_cylinder.o
weighted_remainder_dirichlet.o
weighted_remainder_exact.o
weighted_remainder_expansion.o
weighted_remainder_floor.o
weighted_remainder_fourier.o
weighted_remainder_harmonic_root.o
weighted_remainder_increment.o
weighted_remainder_joint.o
weighted_remainder_law.o
weighted_remainder_pairing.o
weighted_remainder_power.o
weighted_remainder_primitive.o
weighted_remainder_rows.o
weighted_remainder_sawtooth.o
weighted_remainder_small_amplitude.o
weighted_remainder_spectral.o
weighted_remainder_spectral_tail.o
weighted_remainder_state.o
weighted_remainder_weights.o
MEMBERS
cmp "$stage/members.txt" "$stage/expected-members.txt" || fail 'unexpected archive members'
nm -g --defined-only "$installed/lib/libnfield.a" > "$stage/symbols.txt"
# Mixed mathematical objects retain their own render/check helpers. Exclude
# application entry points, service dispatch and proof-registry infrastructure.
if grep -E ' [TW] (main|verify_dispatch|verify_help|nfield_verification_.*|nfield_verify_route|nf_dispatch.*|nfield_daemon.*|daemon_start|completion_.*)$' "$stage/symbols.txt" >/dev/null; then
    fail 'application dispatch or registry in installed archive'
fi

# Clear incidental checkout flags. The test Makefile expands pkg-config output
# in recipe text, so the shell interprets its escaped installation-path spaces.
unset CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH LIBRARY_PATH LD_LIBRARY_PATH
unset CPPFLAGS CFLAGS CXXFLAGS LDFLAGS LDLIBS
PKG_CONFIG_PATH="$installed/lib/pkgconfig"
PKG_CONFIG_LIBDIR="$installed/lib/pkgconfig"
PKG_CONFIG_SYSROOT_DIR="$destination"
export PKG_CONFIG_PATH PKG_CONFIG_LIBDIR PKG_CONFIG_SYSROOT_DIR
pkg-config --exists nfield || fail 'pkg-config lookup failed'
pkg-config --exists nfield-research || fail 'research pkg-config lookup failed'
pkg-config --libs --static nfield > "$stage/link-flags.txt"
grep -F -- '-lgmp' "$stage/link-flags.txt" >/dev/null || fail 'static GMP dependency missing'
if grep -E -- '-l(m|mpfr|pthread|lapack|blas|openblas)( |$)' "$stage/link-flags.txt" >/dev/null; then
    fail 'core metadata acquired research-profile dependencies'
fi
if grep -F "$project" "$stage/link-flags.txt" >/dev/null; then fail 'source path in link flags'; fi
pkg-config --libs --static nfield-research > "$stage/research-link-flags.txt"
for dependency in -lm -lgmp -lmpfr; do
    grep -F -- "$dependency" "$stage/research-link-flags.txt" >/dev/null || fail "missing research dependency $dependency"
done
if grep -F "$project" "$stage/research-link-flags.txt" >/dev/null; then fail 'source path in research link flags'; fi

cp "$project/test/test_library.c" "$consumer/consumer.c"
cp "$project/test/test_research_library.c" "$consumer/research.c"
cp "$project/test/test_research_link.c" "$consumer/research_link.c"
cat > "$consumer/Makefile" <<'MAKEFILE'
CC ?= cc
CXX ?= c++
NFIELD_CFLAGS = $(shell pkg-config --cflags nfield)
NFIELD_LIBS = $(shell pkg-config --libs --static nfield)
RESEARCH_CFLAGS = $(shell pkg-config --cflags nfield-research)
RESEARCH_LIBS = $(shell pkg-config --libs --static nfield-research)
consumer: consumer.c
	$(CC) -std=c99 -O2 -Wall -Wextra -MMD -MF consumer.d $(NFIELD_CFLAGS) $< $(NFIELD_LIBS) -o $@
headers_cpp: headers.cpp
	$(CXX) -std=c++11 -Wall -Wextra -MMD -MF headers_cpp.d $(NFIELD_CFLAGS) $< $(NFIELD_LIBS) -o $@
research: research.c
	$(CC) -std=c99 -O2 -Wall -Wextra -MMD -MF research.d $(RESEARCH_CFLAGS) $< $(RESEARCH_LIBS) -o $@
research_link: research_link.c
	$(CC) -std=c99 -O2 -Wall -Wextra -Wno-cast-function-type -MMD -MF research_link.d $(RESEARCH_CFLAGS) $< $(RESEARCH_LIBS) -o $@
header: header.c
	$(CC) -std=c99 -Wall -Wextra -Werror -fsyntax-only -MMD -MF header.d $(RESEARCH_CFLAGS) $<
MAKEFILE
make -C "$consumer" consumer > "$stage/consumer-build.log" 2>&1 || {
    cat "$stage/consumer-build.log" >&2; fail 'installed C consumer failed to compile';
}
if grep -F "$project" "$consumer/consumer.d" >/dev/null; then fail 'source-tree header leaked into consumer'; fi
"$consumer/consumer" > "$stage/consumer.log" 2>&1 || {
    cat "$stage/consumer.log" >&2; fail 'installed C consumer failed';
}
cat "$stage/consumer.log"

make -C "$consumer" research > "$stage/research-build.log" 2>&1 || {
    cat "$stage/research-build.log" >&2; fail 'installed research consumer failed to compile';
}
if grep -F "$project" "$consumer/research.d" >/dev/null; then fail 'source-tree header leaked into research consumer'; fi
"$consumer/research" > "$stage/research.log" 2>&1 || {
    cat "$stage/research.log" >&2; fail 'installed research consumer failed';
}
cat "$stage/research.log"
make -C "$consumer" research_link > "$stage/research-link-build.log" 2>&1 || {
    cat "$stage/research-link-build.log" >&2; fail 'advertised research function link failed';
}
if grep -F "$project" "$consumer/research_link.d" >/dev/null; then fail 'source-tree header leaked into full research link'; fi
"$consumer/research_link" > "$stage/research-link.log" 2>&1 || {
    cat "$stage/research-link.log" >&2; fail 'advertised research function addresses missing';
}
cat "$stage/research-link.log"

# Every installed header must stand alone. This also follows transitive includes
# in the staged installation rather than silently falling back to src/ headers.
while IFS= read -r relative; do
    case "$relative" in
        include/nfield/*.h)
            printf '#include <%s>\nint main(void) { return 0; }\n' "${relative#include/}" > "$consumer/header.c"
            make -C "$consumer" header > "$stage/header-build.log" 2>&1 || {
                cat "$stage/header-build.log" >&2; fail "installed standalone header failed: $relative";
            }
            if grep -F "$project" "$consumer/header.d" >/dev/null; then fail "source-tree header leaked through $relative"; fi
            ;;
    esac
done < "$stage/expected-files.txt"

if command -v "${CXX:-c++}" >/dev/null 2>&1; then
    cat > "$consumer/headers.cpp" <<'CPP'
#include <nfield/core.h>
#include <nfield/collision.h>
#include <nfield/nfield.h>
int main()
{
    nfield_forest *forest = nullptr;
    mpz_t divisor; mpq_t value;
    mpz_init_set_ui(divisor, 1); mpq_init(value);
    bool ok = nfield_forest_create(&forest) == NFIELD_OK &&
        nfield_forest_compute(forest, 5, divisor) == NFIELD_OK &&
        nfield_forest_value(forest, NFIELD_FOREST_CONTINUOUS_ENERGY, value) == NFIELD_OK &&
        mpq_cmp_ui(value, 23, 9) == 0;
    nfield_forest_destroy(forest); mpq_clear(value); mpz_clear(divisor);
    return ok ? 0 : 1;
}
CPP
    make -C "$consumer" headers_cpp > "$stage/cpp-build.log" 2>&1 || {
        cat "$stage/cpp-build.log" >&2; fail 'installed C++ header check failed';
    }
    if grep -F "$project" "$consumer/headers_cpp.d" >/dev/null; then fail 'source-tree header leaked into C++ consumer'; fi
    "$consumer/headers_cpp" || fail 'C++ consumer execution failed'
    printf '%s\n' 'library installation: C++ headers and C linkage passed'
else
    printf '%s\n' 'library installation: C++ compiler unavailable, check skipped'
fi

examples="$stage/installed examples"
mkdir "$examples"
for name in forest_readings.c source_projection.c source_divisor.c Makefile; do
    cp "$installed/share/doc/nfield/examples/$name" "$examples/$name"
done
make -C "$examples" all > "$stage/examples-build.log" 2>&1 || {
    cat "$stage/examples-build.log" >&2; fail 'installed examples failed to compile';
}
for name in forest_readings source_projection source_divisor; do
    "$examples/$name" > "$stage/$name.log" 2>&1 || {
        cat "$stage/$name.log" >&2; fail "example $name failed";
    }
done
for value in 'continuous_energy=23/9' 'sampled_energy=48/25' 'defect=143/225' \
    'origin_contact=16/25' 'corrected_defect=-1/225'; do
    grep -Fx "$value" "$stage/forest_readings.log" >/dev/null || fail "missing exact forest reading: $value"
done
grep -F 'twice_mixed=-1/6 ' "$stage/source_projection.log" >/dev/null || fail 'continuous signed mixed value differs'
grep -F 'twice_mixed=-112/625 ' "$stage/source_projection.log" >/dev/null || fail 'sampled signed mixed value differs'
grep -Fx 'N=4 D=1 modulus=N^N*D=256 has_work=0' "$stage/source_divisor.log" >/dev/null || fail 'divisor example differs'
grep -Fx 'identity collapse M=0 Q=25 selected_continuous_energy=23/9' "$stage/source_divisor.log" >/dev/null || fail 'identity example differs'
if "$examples/forest_readings" 0 > "$stage/example-invalid.log" 2>&1; then fail 'example accepted a zero divisor'; fi
printf '%s\n' 'library installation: core and research consumers, exact 117-member/58-file boundary, 49 standalone headers, pkg-config, 3 examples, and paths with spaces passed'
