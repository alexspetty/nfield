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
LDLIBS  ?= -lm -lpthread $(LAPACK_LIBS)
BUILD_VERSION ?= $(shell date -u '+%Y.%m%d.%H%M%S')

# Library foundations and stable mathematical verification objects.
FOUNDATION_SRC = \
	src/repetend.c \
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
	src/periodic_zeta_core.c \
	src/orbit_boundary_core.c

VERIFICATION_OBJECT_SRC = \
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

# Build static library from core sources
$(LIB): $(LIB_OBJ)
	ar rcs $@ $^

src/%.o: src/%.c src/nfield.h
	$(CC) $(CFLAGS) -c -o $@ $<

$(COLLISION_SPECTRUM_OBJ): src/collision_spectrum_core.h

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

test: test-unit test-cli test-completion test-api test-coverage

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

test-coverage: test/test_verification_coverage.sh VERIFICATION_COVERAGE.md
	bash test/test_verification_coverage.sh

test-sanitize:
	$(MAKE) clean
	$(MAKE) CFLAGS="-O1 -g -Wall -Wextra -std=c99 -fsanitize=address,undefined -fno-omit-frame-pointer" LDFLAGS="$(LDFLAGS) -fsanitize=address,undefined" test
	$(MAKE) clean
	$(MAKE) all

clean:
	rm -f $(BIN) $(LIB) src/*.o verify/*.o test/test_nfield

.PHONY: all parallel gmp verify test test-unit test-cli test-completion test-api test-coverage test-sanitize clean
