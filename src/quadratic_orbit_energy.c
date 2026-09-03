/* Exact off-resonance energy of the quadratic-residue orbit boundary. */

#include <stdio.h>

#include "nfield.h"
#include "orbit_boundary_core.h"

static int qoe_primitive_root(int prime)
{
    int phi = prime - 1;
    for (int candidate = 2; candidate < prime; candidate++)
        if (orbit_boundary_multiplicative_order(candidate, prime) == phi)
            return candidate;
    return 0;
}

static long long qoe_closed_form(int prime)
{
    switch (prime % 8) {
        case 1:
            return (long long)(prime - 1) * (prime + 3) / 8;
        case 3:
            return (long long)(prime - 3) * (prime + 3) / 8;
        case 5:
            return (long long)(prime - 1) * (prime - 1) / 8;
        case 7:
            return (long long)(prime - 5) * (prime + 1) / 8;
        default:
            return -1;
    }
}

int quadratic_orbit_energy_values(
        int prime, long long *full_odd_energy,
        long long *resonant_energy, long long *off_resonance_energy,
        long long *closed_energy, int *off_resonance_characters)
{
    if (!full_odd_energy || !resonant_energy || !off_resonance_energy ||
        !closed_energy || !off_resonance_characters || prime == 2 ||
        !orbit_boundary_is_prime(prime))
        return 0;
    int generator = qoe_primitive_root(prime);
    if (generator == 0) return 0;
    int subgroup_generator = orbit_boundary_modular_power(
        generator, 2, prime);
    OrbitBoundary orbit = {0};
    if (!orbit_boundary_build_subgroup(
            subgroup_generator, prime, &orbit))
        return 0;
    long long diagonal = 0;
    long long antipodal = 0;
    long long full = 0;
    if (!orbit_boundary_odd_energy(
            &orbit, prime - 1, &diagonal, &antipodal, &full)) {
        orbit_boundary_free(&orbit);
        return 0;
    }
    long long resonant = 0;
    if (prime % 4 == 3) {
        long long flux = 0;
        for (int residue = 1; residue < prime; residue++)
            flux += (long long)orbit.boundary[residue] *
                    orbit_boundary_legendre(residue, prime);
        resonant = flux * flux;
    }
    long long off = full - resonant;
    long long closed = qoe_closed_form(prime);
    int count = prime % 4 == 1 ? (prime - 1) / 2 : (prime - 3) / 2;
    int subgroup_size = orbit.support_size;
    *full_odd_energy = full;
    *resonant_energy = resonant;
    *off_resonance_energy = off;
    *closed_energy = closed;
    *off_resonance_characters = count;
    orbit_boundary_free(&orbit);
    return off == closed && subgroup_size == (prime - 1) / 2;
}

int quadratic_orbit_energy_inspect(int prime)
{
    long long full = 0;
    long long resonant = 0;
    long long off = 0;
    long long closed = 0;
    int character_count = 0;
    if (prime == 2 || !orbit_boundary_is_prime(prime)) {
        fprintf(stderr, "q must be an odd prime\n");
        return 1;
    }
    int ok = quadratic_orbit_energy_values(
        prime, &full, &resonant, &off, &closed, &character_count);
    int legendre_minus_two = orbit_boundary_legendre(-2, prime);
    long long sigma = -(long long)(prime - 1) * legendre_minus_two / 2 +
                      (prime % 4 == 3 ? 1 : 0);
    printf("Quadratic-orbit off-resonance energy\n\n");
    printf("  prime=%d; residue class modulo 8=%d\n", prime, prime % 8);
    printf("  quadratic value (-2|p)=%d\n", legendre_minus_two);
    printf("  off-resonance odd characters N=%d\n", character_count);
    printf("  Jacobi-sum aggregate Sigma=%lld\n", sigma);
    printf("  exact full odd-kernel energy=%lld\n", full);
    printf("  exact resonant quadratic-channel energy=%lld\n", resonant);
    printf("  exact off-resonance energy=%lld\n", off);
    printf("  closed mod-eight law=%lld  %s\n",
           closed, off == closed ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int quadratic_orbit_energy_verify(void)
{
    int exhaustive_ok = 1;
    int class_ok[4] = {1, 1, 1, 1};
    int class_seen[4] = {0, 0, 0, 0};
    int example_ok = 0;
    int domain_ok = 0;
    int prime_models = 0;
    long long full = 0;
    long long resonant = 0;
    long long off = 0;
    long long closed = 0;
    int character_count = 0;

    for (int prime = 3; prime < 600; prime += 2) {
        if (!orbit_boundary_is_prime(prime)) continue;
        prime_models++;
        int ok = quadratic_orbit_energy_values(
            prime, &full, &resonant, &off, &closed, &character_count);
        if (!ok) exhaustive_ok = 0;
        int class_index = (prime % 8 - 1) / 2;
        class_seen[class_index]++;
        if (off != closed) class_ok[class_index] = 0;
        if (prime == 7)
            example_ok = ok && full - resonant == 2 && off == 2 &&
                         character_count == 2;
    }
    int all_classes = 1;
    for (int index = 0; index < 4; index++)
        if (!class_ok[index] || class_seen[index] == 0) all_classes = 0;
    domain_ok = !quadratic_orbit_energy_values(
                    9, &full, &resonant, &off, &closed, &character_count) &&
                !quadratic_orbit_energy_values(
                    2, &full, &resonant, &off, &closed, &character_count);

    int passed = exhaustive_ok + all_classes + example_ok + domain_ok;
    printf("Quadratic-orbit energy verification\n\n");
    printf("  every odd prime below 600: %d models           %s\n",
           prime_models, exhaustive_ok ? "PASS" : "FAIL");
    printf("  all four prime residue classes modulo eight    %s\n",
           all_classes ? "PASS" : "FAIL");
    printf("  prime-seven off-resonance energy equals two    %s\n",
           example_ok ? "PASS" : "FAIL");
    printf("  odd-prime domain rejection                     %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("\n%d/4 verification groups passed.\n", passed);
    printf("Computed  the quadratic subgroup, additive boundary, full odd kernel,\n");
    printf("resonant subtraction, and closed law use exact integer arithmetic.\n");
    printf("Proof status  the four mod-eight formulas are algebraic; this audit\n");
    printf("reproduces the declared exhaustive range with no complex rounding.\n");
    return passed == 4;
}

void quadratic_orbit_energy_help(void)
{
    printf(
        "Quadratic-orbit off-resonance energy\n\n"
        "Commands\n"
        "  nfield quadratic-orbit-energy inspect <odd-prime>\n"
        "      Build the quadratic-residue subgroup, subtract its resonant odd\n"
        "      channel, and compare the exact energy with the mod-eight law.\n"
        "  nfield quadratic-orbit-energy verify\n"
        "  nfield verify quadratic-orbit-energy\n\n"
        "Example\n"
        "  nfield quadratic-orbit-energy inspect 7\n\n"
        "Scope\n"
        "  proved       the off-resonance energy has one closed formula in each\n"
        "               odd-prime residue class modulo eight.\n"
        "  exact        subgroup, additive boundary, odd kernel, quadratic\n"
        "               resonance, Legendre value, and energy use integers.\n"
        "  verifier     every odd prime below 600, exactly the stated range.\n"
        "  boundary     this is the index-two subgroup law at prime modulus; it\n"
        "               does not claim a higher-index closed form.\n"
    );
}
