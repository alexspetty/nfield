CC      = gcc
CFLAGS  = -O2 -Wall -Wextra -std=c99
LDFLAGS ?=
LAPACK_LIBS ?= $(shell \
	lapack=$$($(CC) -print-file-name=liblapack.so); \
	blas=$$($(CC) -print-file-name=libblas.so); \
	if [ "$$lapack" != liblapack.so ] && [ "$$blas" != libblas.so ]; then \
		printf '%s' '-llapack -lblas'; \
	else \
		lapack=$$($(CC) -print-file-name=liblapack.so.3); \
		blas=$$($(CC) -print-file-name=libblas.so.3); \
		if [ "$$lapack" != liblapack.so.3 ] && [ "$$blas" != libblas.so.3 ]; then \
			printf '%s' '-l:liblapack.so.3 -l:libblas.so.3'; \
		else \
			printf '%s' '-llapack -lblas'; \
		fi; \
	fi)
LDLIBS  ?= -lm -lpthread $(LAPACK_LIBS) -lmpfr -lgmp
BUILD_VERSION ?= $(shell date -u '+%Y.%m%d.%H%M%S')

# Library foundations and stable mathematical verification objects.
FOUNDATION_SRC = src/native_arithmetic.c src/native_directional.c src/field_observation.c \
	src/repetend.c \
	src/native_refinement.c \
	src/field.c \
	src/invariants.c \
	src/output.c \
	src/coherence.c \
	src/analytic.c \
	src/scale.c \
	src/collision_table_core.c \
	src/finite_character_core.c \
	src/primitive_odd_sector_core.c \
	src/collision_spectrum_core.c \
	src/collision_magnitude_moments.c \
	src/periodic_zeta_core.c \
	src/orbit_boundary_core.c

VERIFICATION_OBJECT_SRC = \
	src/collision_sampling.c \
	src/collision_kernel_readout.c \
	verify/collision_sampling_verify.c \
	src/boundary_spectrum.c \
	verify/boundary_spectrum_verify.c \
	src/collision_capacity_transition.c \
	verify/collision_capacity_transition_verify.c \
	src/collision_capacity_generation.c \
	verify/collision_capacity_generation_verify.c \
	src/reciprocal_square_selection.c \
	src/weighted_reference_profile.c \
	src/digit_partition.c \
	src/alignment_limit.c \
	src/three_tier.c \
	src/deficit_lattice.c \
	src/coherence_decomposition.c \
	src/cross_alignment.c \
	src/spectral_structure.c \
	src/spectral_power.c \
	src/autocorrelation_formula.c \
	src/phase_filtered_ramanujan.c \
	src/bin_derangements.c \
	src/collision_character_structure.c \
	src/silent_primes_variance.c \
	src/collision_fluctuation_sum.c \
	src/centered_collision_sum.c \
	src/collision_periodic_table.c \
	src/collision_transform_strip.c \
	src/residue_three_neutrality.c \
	src/compatible_residue_channels.c \
	src/centered_collision_table.c \
	src/finite_character_pairing.c \
	src/coprime_base_orthogonality.c \
	src/natural_prime_sum_window.c \
	src/primitive_odd_sector.c \
	src/conjugate_pair_relabeling.c \
	src/additive_reflection_well.c \
	src/goldbach_obstruction.c \
	src/collision_spectrum_factorization.c \
	src/special_value_moment.c \
	src/base_five_cyclotomic_identity.c \
	src/short_sum_bernoulli_correlation.c \
	src/weighted_remainder_state.c \
	src/weighted_remainder_exact.c \
	src/weighted_remainder_floor.c \
	src/weighted_remainder_clock.c \
	src/weighted_remainder_weights.c \
	src/weighted_remainder_rows.c \
	src/weighted_remainder_increment.c \
	src/weighted_remainder_fourier.c \
	src/weighted_remainder_amplitude.c \
	src/weighted_remainder_constants.c \
	src/weighted_remainder_expansion.c \
	src/weighted_remainder_power.c \
	src/weighted_remainder_dirichlet.c \
	src/weighted_remainder_expansion_command.c \
	src/weighted_remainder_spectral.c \
	src/weighted_remainder_spectral_tail.c \
	src/weighted_remainder_spectral_command.c \
	src/weighted_remainder_complex.c \
	src/weighted_remainder_character.c \
	src/weighted_remainder_cotangent.c \
	src/weighted_remainder_harmonic_root.c \
	src/weighted_remainder_small_amplitude.c \
	src/weighted_remainder_mixed_command.c \
	src/weighted_remainder_alignment_local.c \
	src/weighted_remainder_alignment.c \
	src/weighted_remainder_alignment_growth.c \
	src/weighted_remainder_alignment_command.c \
	src/weighted_remainder_law.c \
	src/weighted_remainder_primitive.c \
	src/weighted_remainder_sawtooth.c \
	src/weighted_remainder_pairing.c \
	src/weighted_remainder_joint.c \
	src/weighted_remainder_cylinder.c \
	src/weighted_remainder_conductor.c \
	src/weighted_remainder_activation.c \
	src/primitive_character_cancellation.c \
	src/periodic_zeta_factorization.c \
	src/collision_boundary_recovery.c \
	src/active_collision_channel.c \
	src/collision_coordinate.c \
	src/finite_determination.c \
	src/reflection_identity.c \
	src/half_group.c \
	src/all_prime_collision_label.c \
	src/finite_spectral_quotient.c \
	src/finite_prefix_slice.c \
	src/oriented_digit_comparison.c \
	src/boundary_bernoulli_factorization.c \
	src/finite_state_orbit_boundary.c \
	src/full_orbit_energy.c \
	src/quadratic_orbit_energy.c \
	src/subgroup_jacobi_expansion.c \
	src/prime_base_collision_energy.c \
	src/arithmetic_boundary_defect.c \
	src/carry_completed_carrier.c \
	src/terminal_collision_conductor_ledger.c


LIB_SRC = $(FOUNDATION_SRC) $(VERIFICATION_OBJECT_SRC)
REFERENCE_AUDIT_OBJ = src/terminal_collision_conductor_ledger_reference.o
LIB_OBJ = $(LIB_SRC:.c=.o) $(REFERENCE_AUDIT_OBJ)
LIB     = libnfield.a

COLLISION_SPECTRUM_OBJ = \
	src/collision_spectrum_core.o \
	src/collision_magnitude_moments.o \
	src/collision_spectrum_factorization.o \
	src/special_value_moment.o \
	src/base_five_cyclotomic_identity.o \
	src/short_sum_bernoulli_correlation.o

PERIODIC_ZETA_OBJ = \
	src/periodic_zeta_core.o \
	src/primitive_character_cancellation.o \
	src/periodic_zeta_factorization.o \
	src/collision_boundary_recovery.o \
	src/active_collision_channel.o

# Main binary
BIN     = nfield

all: $(BIN)

src/native_refinement.o: src/native_refinement.h

src/weighted_remainder_state.o: src/weighted_remainder_state.h

src/collision_sampling.o verify/collision_sampling_verify.o: src/collision_sampling.h
src/collision_sampling.o: src/collision_capacity_transition.h
src/collision_kernel_readout.o src/collision_capacity_generation.o: src/collision_kernel_readout.h src/weighted_remainder_exact.h
src/boundary_spectrum.o verify/boundary_spectrum_verify.o: src/boundary_spectrum.h src/finite_character_core.h
src/finite_character_core.o: src/finite_character_core.h

src/weighted_remainder_exact.o: src/weighted_remainder_exact.h
src/weighted_remainder_floor.o: src/weighted_remainder_floor.h src/weighted_remainder_exact.h
src/weighted_remainder_clock.o: src/weighted_remainder_clock.h src/weighted_remainder_exact.h
src/weighted_remainder_weights.o: src/weighted_remainder_weights.h src/weighted_remainder_exact.h
src/weighted_remainder_rows.o: src/weighted_remainder_rows.h src/weighted_remainder_exact.h
src/weighted_remainder_increment.o: src/weighted_remainder_increment.h src/weighted_remainder_rows.h src/weighted_remainder_weights.h src/weighted_remainder_exact.h
src/weighted_remainder_fourier.o: src/weighted_remainder_fourier.h src/weighted_remainder_weights.h src/weighted_remainder_exact.h
src/weighted_remainder_primitive.o: src/weighted_remainder_primitive.h src/weighted_remainder_exact.h
src/weighted_remainder_sawtooth.o: src/weighted_remainder_sawtooth.h src/weighted_remainder_exact.h
src/weighted_remainder_pairing.o: src/weighted_remainder_pairing.h src/weighted_remainder_exact.h
src/weighted_remainder_joint.o: src/weighted_remainder_joint.h src/weighted_remainder_pairing.h src/weighted_remainder_exact.h
src/weighted_remainder_cylinder.o: src/weighted_remainder_cylinder.h src/weighted_remainder_exact.h
src/weighted_remainder_conductor.o: src/weighted_remainder_conductor.h src/weighted_remainder_exact.h
src/weighted_remainder_activation.o: src/weighted_remainder_activation.h

# Build static library from core sources
$(LIB): $(LIB_OBJ)
	ar rcs $@ $^

src/%.o: src/%.c src/nfield.h
	$(CC) $(CFLAGS) -c -o $@ $<

$(COLLISION_SPECTRUM_OBJ): src/collision_spectrum_core.h

src/collision_magnitude_moments.o src/short_sum_bernoulli_correlation.o: src/collision_magnitude_moments.h

$(PERIODIC_ZETA_OBJ): src/periodic_zeta_core.h

src/terminal_collision_conductor_ledger_reference.o: \
		src/terminal_collision_conductor_ledger_reference.c
	$(CC) $(CFLAGS) -DNFIELD_CLI_EMBEDDED -c -o $@ $<

# Main binary links against library + verify + daemon
$(BIN): src/main.o src/completion.o src/daemon.o src/dispatch.o \
		verify/verify.o $(LIB) src/build_info.c src/build_info.h
	$(CC) $(CFLAGS) -DNFIELD_BUILD_VERSION='"$(BUILD_VERSION)"' \
		-c -o src/build_info.o src/build_info.c
	$(CC) $(CFLAGS) -o $@ src/main.o src/completion.o src/daemon.o \
		src/dispatch.o verify/verify.o $(LIB) src/build_info.o \
		$(LDFLAGS) $(LDLIBS)

src/main.o: src/main.c src/nfield.h src/completion.h src/build_info.h
	$(CC) $(CFLAGS) -c -o $@ $<

src/completion.o: src/completion.c src/completion.h

src/daemon.o: src/daemon.c
	$(CC) $(CFLAGS) -c -o $@ $<

src/dispatch.o: src/dispatch.c
	$(CC) $(CFLAGS) -c -o $@ $<

verify/verify.o: verify/verify.c src/nfield.h
	$(CC) $(CFLAGS) -Isrc -c -o $@ $<

# Run every named verification through the supported CLI surface.
verify: $(BIN)
	./$(BIN) verify all

# Convenience targets
parallel: CFLAGS += -fopenmp -DNFIELD_PARALLEL
parallel: all

gmp: CFLAGS += -DNFIELD_GMP
gmp: LDLIBS += -lgmp
gmp: all

test: test-unit test-cli test-completion test-api test-capacity-generation test-sampling-spectrum-api test-weighted-remainder-exact test-weighted-remainder-primitive test-weighted-remainder-sawtooth test-weighted-remainder-pairing test-weighted-remainder-joint test-weighted-remainder-cylinder test-weighted-remainder-conductor test-weighted-remainder-activation

test/test_sampling_spectrum_api: test/test_sampling_spectrum_api.c $(LIB) src/collision_sampling.h src/boundary_spectrum.h src/collision_kernel_readout.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_sampling_spectrum_api.c $(LIB) $(LDLIBS)

test-sampling-spectrum-api: $(BIN) test/test_sampling_spectrum_api
	./test/test_sampling_spectrum_api

.PHONY: test-sampling-spectrum-api test-capacity-generation

test/test_weighted_remainder_exact: test/test_weighted_remainder_exact.c src/weighted_remainder_exact.o src/weighted_remainder_exact.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_exact.c src/weighted_remainder_exact.o -lgmp

test-weighted-remainder-exact: $(BIN) test/test_weighted_remainder_exact
	./test/test_weighted_remainder_exact < /dev/null > /dev/null

test/test_weighted_remainder_floor: test/test_weighted_remainder_floor.c src/weighted_remainder_floor.o src/weighted_remainder_exact.o src/weighted_remainder_floor.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_floor.c src/weighted_remainder_floor.o src/weighted_remainder_exact.o -lgmp

test-weighted-remainder-floor: $(BIN) test/test_weighted_remainder_floor
	./test/test_weighted_remainder_floor < /dev/null > /dev/null

test: test-weighted-remainder-floor
.PHONY: test-weighted-remainder-floor

test/test_weighted_remainder_clock: test/test_weighted_remainder_clock.c src/weighted_remainder_clock.o src/weighted_remainder_exact.o src/weighted_remainder_state.o src/weighted_remainder_clock.h src/weighted_remainder_state.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_clock.c src/weighted_remainder_clock.o src/weighted_remainder_exact.o src/weighted_remainder_state.o -lgmp -lm

test-weighted-remainder-clock: $(BIN) test/test_weighted_remainder_clock
	./test/test_weighted_remainder_clock < /dev/null > /dev/null

test: test-weighted-remainder-clock
.PHONY: test-weighted-remainder-clock

test/test_weighted_remainder_weights: test/test_weighted_remainder_weights.c src/weighted_remainder_weights.o src/weighted_remainder_exact.o src/weighted_remainder_state.o src/weighted_remainder_weights.h src/weighted_remainder_state.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_weights.c src/weighted_remainder_weights.o src/weighted_remainder_exact.o src/weighted_remainder_state.o -lgmp -lm

test-weighted-remainder-weights: $(BIN) test/test_weighted_remainder_weights
	./test/test_weighted_remainder_weights < /dev/null > /dev/null

test: test-weighted-remainder-weights
.PHONY: test-weighted-remainder-weights

test/test_weighted_remainder_rows: test/test_weighted_remainder_rows.c src/weighted_remainder_rows.o src/weighted_remainder_weights.o src/weighted_remainder_exact.o src/weighted_remainder_rows.h src/weighted_remainder_weights.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_rows.c src/weighted_remainder_rows.o src/weighted_remainder_weights.o src/weighted_remainder_exact.o -lgmp -lm

test-weighted-remainder-rows: $(BIN) test/test_weighted_remainder_rows
	./test/test_weighted_remainder_rows < /dev/null > /dev/null

test: test-weighted-remainder-rows
.PHONY: test-weighted-remainder-rows

test/test_weighted_remainder_increment: test/test_weighted_remainder_increment.c src/weighted_remainder_increment.o src/weighted_remainder_rows.o src/weighted_remainder_weights.o src/weighted_remainder_exact.o src/weighted_remainder_increment.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_increment.c src/weighted_remainder_increment.o src/weighted_remainder_rows.o src/weighted_remainder_weights.o src/weighted_remainder_exact.o -lgmp -lm

test-weighted-remainder-increment: $(BIN) test/test_weighted_remainder_increment
	./test/test_weighted_remainder_increment < /dev/null > /dev/null

test: test-weighted-remainder-increment
.PHONY: test-weighted-remainder-increment

test/test_weighted_remainder_fourier: test/test_weighted_remainder_fourier.c src/weighted_remainder_fourier.o src/weighted_remainder_weights.o src/weighted_remainder_rows.o src/weighted_remainder_exact.o src/weighted_remainder_fourier.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_fourier.c src/weighted_remainder_fourier.o src/weighted_remainder_weights.o src/weighted_remainder_rows.o src/weighted_remainder_exact.o -lgmp -lm

test-weighted-remainder-fourier: $(BIN) test/test_weighted_remainder_fourier
	./test/test_weighted_remainder_fourier < /dev/null > /dev/null

test: test-weighted-remainder-fourier
.PHONY: test-weighted-remainder-fourier

test/test_weighted_remainder_amplitude: test/test_weighted_remainder_amplitude.c src/weighted_remainder_amplitude.o src/weighted_remainder_exact.o src/weighted_remainder_amplitude.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_amplitude.c src/weighted_remainder_amplitude.o src/weighted_remainder_exact.o -lgmp -lm

test-weighted-remainder-amplitude: $(BIN) test/test_weighted_remainder_amplitude
	./test/test_weighted_remainder_amplitude < /dev/null > /dev/null

test: test-weighted-remainder-amplitude
.PHONY: test-weighted-remainder-amplitude

EXPANSION_CORE_OBJ = src/weighted_remainder_constants.o src/weighted_remainder_amplitude.o src/weighted_remainder_exact.o

test/test_weighted_remainder_constants: test/test_weighted_remainder_constants.c $(EXPANSION_CORE_OBJ) src/weighted_remainder_constants.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_constants.c $(EXPANSION_CORE_OBJ) -lgmp -lm

test-weighted-remainder-constants: $(BIN) test/test_weighted_remainder_constants
	./test/test_weighted_remainder_constants < /dev/null > /dev/null

test/test_weighted_remainder_expansion: test/test_weighted_remainder_expansion.c src/weighted_remainder_expansion.o $(EXPANSION_CORE_OBJ) src/weighted_remainder_expansion.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_expansion.c src/weighted_remainder_expansion.o $(EXPANSION_CORE_OBJ) -lgmp -lm

test-weighted-remainder-expansion: $(BIN) test/test_weighted_remainder_expansion
	./test/test_weighted_remainder_expansion < /dev/null > /dev/null

test/test_weighted_remainder_power: test/test_weighted_remainder_power.c src/weighted_remainder_power.o $(EXPANSION_CORE_OBJ) src/weighted_remainder_power.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_power.c src/weighted_remainder_power.o $(EXPANSION_CORE_OBJ) -lgmp -lm

test-weighted-remainder-power: test/test_weighted_remainder_power
	./test/test_weighted_remainder_power < /dev/null > /dev/null

test/test_weighted_remainder_dirichlet: test/test_weighted_remainder_dirichlet.c src/weighted_remainder_dirichlet.o src/weighted_remainder_power.o $(EXPANSION_CORE_OBJ) src/weighted_remainder_dirichlet.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_dirichlet.c src/weighted_remainder_dirichlet.o src/weighted_remainder_power.o $(EXPANSION_CORE_OBJ) -lgmp -lm

test-weighted-remainder-dirichlet: $(BIN) test/test_weighted_remainder_dirichlet
	./test/test_weighted_remainder_dirichlet < /dev/null > /dev/null

test: test-weighted-remainder-constants test-weighted-remainder-expansion test-weighted-remainder-power test-weighted-remainder-dirichlet
.PHONY: test-weighted-remainder-constants test-weighted-remainder-expansion test-weighted-remainder-power test-weighted-remainder-dirichlet

test/test_weighted_remainder_spectral: test/test_weighted_remainder_spectral.c src/weighted_remainder_spectral.o src/weighted_remainder_spectral_tail.o $(EXPANSION_CORE_OBJ) src/weighted_remainder_spectral.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_spectral.c src/weighted_remainder_spectral.o src/weighted_remainder_spectral_tail.o $(EXPANSION_CORE_OBJ) -lgmp -lm

test-weighted-remainder-spectral: $(BIN) test/test_weighted_remainder_spectral
	./test/test_weighted_remainder_spectral < /dev/null > /dev/null

test: test-weighted-remainder-spectral
.PHONY: test-weighted-remainder-spectral

MIXED_HEADERS = src/weighted_remainder_complex.h src/weighted_remainder_character.h \
	src/weighted_remainder_cotangent.h src/weighted_remainder_harmonic_root.h \
	src/weighted_remainder_small_amplitude.h src/weighted_remainder_rect_internal.h \
	src/finite_character_core.h
MIXED_DRIVERS = test/test_weighted_remainder_complex test/test_weighted_remainder_character \
	test/test_weighted_remainder_cotangent test/test_weighted_remainder_harmonic_root \
	test/test_weighted_remainder_small_amplitude
src/weighted_remainder_complex.o src/weighted_remainder_character.o \
src/weighted_remainder_cotangent.o src/weighted_remainder_harmonic_root.o \
src/weighted_remainder_small_amplitude.o src/weighted_remainder_mixed_command.o: $(MIXED_HEADERS)

$(MIXED_DRIVERS): %: %.c $(LIB) $(MIXED_HEADERS)
	$(CC) $(CFLAGS) $(LDFLAGS) -Isrc -o $@ $< $(LIB) $(LDLIBS)

test-weighted-remainder-mixed: $(BIN) $(MIXED_DRIVERS)
	./test/test_weighted_remainder_complex < /dev/null > /dev/null
	./test/test_weighted_remainder_character < /dev/null > /dev/null
	./test/test_weighted_remainder_cotangent < /dev/null > /dev/null
	./test/test_weighted_remainder_harmonic_root < /dev/null > /dev/null
	./test/test_weighted_remainder_small_amplitude < /dev/null > /dev/null

test: test-weighted-remainder-mixed
.PHONY: test-weighted-remainder-mixed

test/test_weighted_remainder_primitive: test/test_weighted_remainder_primitive.c src/weighted_remainder_primitive.o src/weighted_remainder_exact.o src/weighted_remainder_state.o src/weighted_remainder_primitive.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_primitive.c src/weighted_remainder_primitive.o src/weighted_remainder_exact.o src/weighted_remainder_state.o -lgmp -lm

test-weighted-remainder-primitive: $(BIN) test/test_weighted_remainder_primitive
	./test/test_weighted_remainder_primitive < /dev/null > /dev/null

test/test_weighted_remainder_sawtooth: test/test_weighted_remainder_sawtooth.c src/weighted_remainder_sawtooth.o src/weighted_remainder_sawtooth.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_sawtooth.c src/weighted_remainder_sawtooth.o -lgmp

test-weighted-remainder-sawtooth: $(BIN) test/test_weighted_remainder_sawtooth
	./test/test_weighted_remainder_sawtooth < /dev/null > /dev/null

test/test_weighted_remainder_pairing: test/test_weighted_remainder_pairing.c src/weighted_remainder_pairing.o src/weighted_remainder_exact.o src/weighted_remainder_pairing.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_pairing.c src/weighted_remainder_pairing.o src/weighted_remainder_exact.o -lgmp

test-weighted-remainder-pairing: $(BIN) test/test_weighted_remainder_pairing
	./test/test_weighted_remainder_pairing < /dev/null > /dev/null

test/test_weighted_remainder_joint: test/test_weighted_remainder_joint.c src/weighted_remainder_joint.o src/weighted_remainder_pairing.o src/weighted_remainder_exact.o src/weighted_remainder_joint.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_joint.c src/weighted_remainder_joint.o src/weighted_remainder_pairing.o src/weighted_remainder_exact.o -lgmp

test-weighted-remainder-joint: $(BIN) test/test_weighted_remainder_joint
	./test/test_weighted_remainder_joint --edges

test/test_weighted_remainder_cylinder: test/test_weighted_remainder_cylinder.c src/weighted_remainder_cylinder.o src/weighted_remainder_exact.o src/weighted_remainder_cylinder.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_cylinder.c src/weighted_remainder_cylinder.o src/weighted_remainder_exact.o -lgmp

test-weighted-remainder-cylinder: $(BIN) test/test_weighted_remainder_cylinder
	./test/test_weighted_remainder_cylinder < /dev/null > /dev/null

test/test_weighted_remainder_conductor: test/test_weighted_remainder_conductor.c src/weighted_remainder_conductor.o src/weighted_remainder_exact.o src/weighted_remainder_conductor.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_conductor.c src/weighted_remainder_conductor.o src/weighted_remainder_exact.o -lgmp

test-weighted-remainder-conductor: $(BIN) test/test_weighted_remainder_conductor
	./test/test_weighted_remainder_conductor --self-test

test/test_weighted_remainder_activation: test/test_weighted_remainder_activation.c src/weighted_remainder_activation.o src/weighted_remainder_activation.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_weighted_remainder_activation.c src/weighted_remainder_activation.o -lgmp

test-weighted-remainder-activation: $(BIN) test/test_weighted_remainder_activation
	./test/test_weighted_remainder_activation --self-test

test-unit: test/test_nfield.c src/collision_spectrum_core.h \
		           src/periodic_zeta_core.h $(LIB)
	$(CC) $(CFLAGS) -Isrc -o test/test_nfield $< $(LIB) \
		$(LDFLAGS) $(LDLIBS)
	./test/test_nfield

test-cli: $(BIN) test/test_cli_commands.sh
	bash test/test_cli_commands.sh

test-completion: $(BIN) test/test_completion.sh
	bash test/test_completion.sh

test-api: $(BIN) test/test_daemon_api.sh
	bash test/test_daemon_api.sh


test-sanitize:
	$(MAKE) clean
	$(MAKE) CFLAGS="-O1 -g -Wall -Wextra -std=c99 -fsanitize=address,undefined -fno-omit-frame-pointer" LDFLAGS="$(LDFLAGS) -fsanitize=address,undefined" test
	$(MAKE) clean
	$(MAKE) all

clean:
	rm -f test/test_weighted_remainder_transcendental
	rm -f test/test_native_api
	rm -f test/test_weighted_remainder_alignment_growth test/test_weighted_remainder_law
	rm -f test/test_weighted_remainder_floor
	rm -f test/test_weighted_remainder_clock
	rm -f test/test_weighted_remainder_weights
	rm -f test/test_weighted_remainder_rows
	rm -f test/test_weighted_remainder_increment
	rm -f test/test_weighted_remainder_fourier
	rm -f test/test_weighted_remainder_amplitude
	rm -f test/test_weighted_remainder_constants test/test_weighted_remainder_expansion test/test_weighted_remainder_power test/test_weighted_remainder_dirichlet
	rm -f test/test_weighted_remainder_spectral
	rm -f $(MIXED_DRIVERS)
	rm -f test/test_sampling_spectrum_api
	rm -f $(BIN) $(LIB) src/*.o verify/*.o test/test_nfield test/test_weighted_remainder_exact test/test_weighted_remainder_primitive test/test_weighted_remainder_sawtooth test/test_weighted_remainder_pairing test/test_weighted_remainder_joint test/test_weighted_remainder_cylinder test/test_weighted_remainder_conductor test/test_weighted_remainder_activation

.PHONY: all parallel gmp verify test test-unit test-cli test-rotation test-completion test-api test-weighted-remainder-exact test-weighted-remainder-primitive test-weighted-remainder-sawtooth test-weighted-remainder-pairing test-weighted-remainder-joint test-weighted-remainder-cylinder test-weighted-remainder-conductor test-weighted-remainder-activation test-sanitize clean



src/collision_capacity_transition.o verify/collision_capacity_transition_verify.o: src/collision_capacity_transition.h

src/collision_capacity_generation.o verify/collision_capacity_generation_verify.o: src/collision_capacity_generation.h src/collision_kernel_readout.h src/weighted_remainder_exact.h

.PHONY: test-capacity-generation
test-capacity-generation: nfield
	./$(BIN) verify capacity-generation

ALIGNMENT_HEADERS = src/weighted_remainder_alignment_local.h src/weighted_remainder_alignment.h src/weighted_remainder_alignment_growth.h src/weighted_remainder_alignment_command.h
src/weighted_remainder_alignment_local.o src/weighted_remainder_alignment.o src/weighted_remainder_alignment_growth.o src/weighted_remainder_alignment_command.o: $(ALIGNMENT_HEADERS) src/weighted_remainder_constants.h src/weighted_remainder_power.h src/weighted_remainder_exact.h

test/test_weighted_remainder_alignment_local: test/test_weighted_remainder_alignment_local.c $(LIB) $(ALIGNMENT_HEADERS)
	$(CC) $(CFLAGS) $(LDFLAGS) -Isrc -o $@ $< $(LIB) $(LDLIBS)
test/test_weighted_remainder_alignment: test/test_weighted_remainder_alignment.c $(LIB) $(ALIGNMENT_HEADERS)
	$(CC) $(CFLAGS) $(LDFLAGS) -Isrc -o $@ $< $(LIB) $(LDLIBS)
test/test_weighted_remainder_alignment_growth: test/test_weighted_remainder_alignment_growth.c $(LIB) $(ALIGNMENT_HEADERS)
	$(CC) $(CFLAGS) $(LDFLAGS) -Isrc -o $@ $< $(LIB) $(LDLIBS)
test-weighted-remainder-alignment: $(BIN) test/test_weighted_remainder_alignment_local test/test_weighted_remainder_alignment test/test_weighted_remainder_alignment_growth
	./test/test_weighted_remainder_alignment_local < /dev/null
	./test/test_weighted_remainder_alignment < /dev/null
	./test/test_weighted_remainder_alignment_growth
test: test-weighted-remainder-alignment
.PHONY: test-weighted-remainder-alignment

src/weighted_remainder_law.o: src/weighted_remainder_law.h src/weighted_remainder_clock.h src/weighted_remainder_weights.h src/weighted_remainder_cylinder.h

test/test_weighted_remainder_law: test/test_weighted_remainder_law.c $(LIB) src/weighted_remainder_law.h
	$(CC) $(CFLAGS) $(LDFLAGS) -Isrc -o $@ $< $(LIB) $(LDLIBS)
test-weighted-remainder-law: $(BIN) test/test_weighted_remainder_law
	./test/test_weighted_remainder_law
test: test-weighted-remainder-law

src/collision_sampling.o: src/collision_sampling_source.inc







.PHONY: test-weighted-remainder-law

src/native_refinement.o: src/native_refinement_detector.inc src/native_probe_transport.inc
src/collision_sampling.o: src/collision_sampling_prefix.inc
src/field_observation.o: src/field_observation_matrix.inc

src/field_observation.o: src/field_observation_segments.inc

test/test_native_api: test/test_native_api.c $(LIB) src/native_arithmetic.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $< $(LIB) $(LDLIBS)
test-native-api: test/test_native_api
	./test/test_native_api
test: test-native-api
.PHONY: test-native-api



test/test_weighted_remainder_transcendental: test/test_weighted_remainder_transcendental.c $(LIB) src/weighted_remainder_power.h
	$(CC) $(CFLAGS) $(LDFLAGS) -Isrc -o $@ $< $(LIB) $(LDLIBS)

test-weighted-remainder-transcendental: test/test_weighted_remainder_transcendental
	./test/test_weighted_remainder_transcendental < /dev/null

test: test-weighted-remainder-transcendental
.PHONY: test-weighted-remainder-transcendental
