/* Exact odd-character energy for a full prime-power remainder orbit. */

#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"
#include "orbit_boundary_core.h"

#define FOE_MAX_MODULUS 200000

static const BoundaryConductorEnergyRow *foe_energy_row(
        const BoundaryConductorLedgerSummary *summary, int conductor)
{
    for (int index = 0; index < summary->energy_count; index++)
        if (summary->energy[index].conductor == conductor)
            return &summary->energy[index];
    return NULL;
}

static int foe_exact_conductor_spectrum(
        int base, int prime, int depth,
        BoundaryConductorLedgerSummary *summary)
{
    int modulus = 0;
    int phi = 0;
    if (!summary || prime == 2 ||
        !orbit_boundary_prime_power(
            prime, depth, FOE_MAX_MODULUS, &modulus) ||
        !orbit_boundary_phi_prime_power(prime, depth, &phi) ||
        orbit_boundary_multiplicative_order(base, modulus) != phi)
        return 0;

    OrbitBoundary orbit = {0};
    if (!orbit_boundary_build_subgroup(base, modulus, &orbit)) return 0;
    int *weights = calloc((size_t)modulus, sizeof(*weights));
    if (!weights) {
        orbit_boundary_free(&orbit);
        return 0;
    }
    for (int residue = 0; residue < modulus; residue++)
        weights[residue] = orbit.support[residue] ? 1 : 0;

    int ok = orbit.support_size == phi &&
             boundary_conductor_ledger_compute(
                 modulus, weights, modulus, summary);
    if (ok) {
        const BoundaryConductorEnergyRow *prime_level =
            foe_energy_row(summary, prime);
        int thickness = modulus / prime;
        long long expected =
            (long long)(prime - 1) / 2 * thickness * thickness;
        int nonzero_levels = 0;
        for (int index = 0; index < summary->energy_count; index++) {
            const BoundaryConductorEnergyRow *row = &summary->energy[index];
            if (row->energy == 0) continue;
            nonzero_levels++;
            if (row->conductor != prime) ok = 0;
        }
        ok = ok && prime_level && prime_level->energy == expected &&
             summary->full_odd_energy == expected && nonzero_levels == 1;
    }
    free(weights);
    orbit_boundary_free(&orbit);
    return ok;
}

int full_orbit_energy_values(
        int base, int prime, int depth,
        long long *kernel_energy, long long *closed_energy,
        int *orbit_size, int *thickness)
{
    int modulus = 0;
    int phi = 0;
    if (!kernel_energy || !closed_energy || !orbit_size || !thickness ||
        prime == 2 ||
        !orbit_boundary_prime_power(
            prime, depth, FOE_MAX_MODULUS, &modulus) ||
        !orbit_boundary_phi_prime_power(prime, depth, &phi) ||
        orbit_boundary_multiplicative_order(base, modulus) != phi)
        return 0;
    OrbitBoundary orbit = {0};
    if (!orbit_boundary_build_subgroup(base, modulus, &orbit)) return 0;
    long long diagonal = 0;
    long long antipodal = 0;
    long long energy = 0;
    int ok = orbit.support_size == phi &&
             orbit_boundary_odd_energy(
                 &orbit, phi, &diagonal, &antipodal, &energy);
    int local_thickness = modulus / prime;
    long long formula = (long long)phi * local_thickness / 2;
    BoundaryConductorLedgerSummary spectrum = {0};
    if (ok) {
        *kernel_energy = energy;
        *closed_energy = formula;
        *orbit_size = orbit.support_size;
        *thickness = local_thickness;
        ok = energy == formula && diagonal - antipodal == local_thickness &&
             foe_exact_conductor_spectrum(
                 base, prime, depth, &spectrum) &&
             spectrum.full_odd_energy == energy;
    }
    orbit_boundary_free(&orbit);
    return ok;
}

int full_orbit_energy_inspect(int base, int prime, int depth)
{
    int modulus = 0;
    int phi = 0;
    long long kernel = 0;
    long long closed = 0;
    int orbit_size = 0;
    int thickness = 0;
    BoundaryConductorLedgerSummary spectrum = {0};
    if (!orbit_boundary_prime_power(
            prime, depth, FOE_MAX_MODULUS, &modulus) || prime == 2 ||
        !orbit_boundary_phi_prime_power(prime, depth, &phi)) {
        fprintf(stderr,
                "require an odd prime p, depth>=1, and p^depth<=200000\n");
        return 1;
    }
    int order = orbit_boundary_multiplicative_order(base, modulus);
    if (order != phi) {
        fprintf(stderr,
                "base must be a primitive root modulo the odd prime power (order=%d, phi=%d)\n",
                order, phi);
        return 1;
    }
    int ok = full_orbit_energy_values(
                 base, prime, depth,
                 &kernel, &closed, &orbit_size, &thickness) &&
             foe_exact_conductor_spectrum(
                 base, prime, depth, &spectrum);
    const BoundaryConductorEnergyRow *prime_level =
        foe_energy_row(&spectrum, prime);
    printf("Full-orbit energy law\n\n");
    printf("  base=%d prime=%d depth=%d modulus=%d\n",
           base, prime, depth, modulus);
    printf("  multiplicative order=%d; phi=%d; orbit size=%d  %s\n",
           order, phi, orbit_size,
           order == phi && orbit_size == phi ? "PASS" : "FAIL");
    printf("  local prime-power thickness p^(depth-1)=%d\n", thickness);
    printf("  exact odd-kernel boundary energy=%lld\n", kernel);
    printf("  phi(p^depth)*p^(depth-1)/2=%lld  %s\n",
           closed, kernel == closed ? "PASS" : "FAIL");
    printf("  exact conductor p=%d energy=%lld\n",
           prime, prime_level ? prime_level->energy : 0);
    printf("  all other exact-conductor energies vanish  %s\n",
           ok ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int foe_smallest_primitive_root(int modulus, int phi)
{
    for (int base = 2; base < modulus; base++)
        if (orbit_boundary_multiplicative_order(base, modulus) == phi)
            return base;
    return 0;
}

int full_orbit_energy_verify(void)
{
    int nine_ok = 0;
    int family_ok = 1;
    int thickness_ok = 1;
    int prime_ok = 1;
    int conductor_support_ok = 1;
    int domain_ok = 1;
    int prime_power_models = 0;

    long long kernel = 0;
    long long closed = 0;
    int orbit_size = 0;
    int thickness = 0;
    nine_ok = full_orbit_energy_values(
        2, 3, 2, &kernel, &closed, &orbit_size, &thickness) &&
        kernel == 9 && closed == 9 && orbit_size == 6 && thickness == 3;

    for (int prime = 3; prime <= 101; prime += 2) {
        if (!orbit_boundary_is_prime(prime)) continue;
        for (int depth = 1; depth <= 4; depth++) {
            int modulus = 0;
            int phi = 0;
            if (!orbit_boundary_prime_power(
                    prime, depth, 20000, &modulus) ||
                !orbit_boundary_phi_prime_power(prime, depth, &phi))
                continue;
            int representative = foe_smallest_primitive_root(modulus, phi);
            if (representative == 0) {
                family_ok = 0;
                continue;
            }
            prime_power_models++;
            if (!full_orbit_energy_values(
                    representative, prime, depth,
                    &kernel, &closed, &orbit_size, &thickness))
                family_ok = 0;
            if (thickness != modulus / prime ||
                kernel != (long long)phi * thickness / 2)
                thickness_ok = 0;
            if (depth == 1 && kernel != (prime - 1) / 2)
                prime_ok = 0;
            BoundaryConductorLedgerSummary spectrum = {0};
            if (!foe_exact_conductor_spectrum(
                    representative, prime, depth, &spectrum))
                conductor_support_ok = 0;
        }
    }
    domain_ok = !full_orbit_energy_values(
                    4, 3, 2, &kernel, &closed,
                    &orbit_size, &thickness) &&
                !full_orbit_energy_values(
                    2, 2, 2, &kernel, &closed,
                    &orbit_size, &thickness);

    int passed = nine_ok + family_ok + thickness_ok + prime_ok +
                 conductor_support_ok + domain_ok;
    printf("Full-orbit energy verification\n\n");
    printf("  base-two orbit modulo nine has exact energy nine  %s\n",
           nine_ok ? "PASS" : "FAIL");
    printf("  representative primitive-root prime-power models=%d  %s\n",
           prime_power_models, family_ok ? "PASS" : "FAIL");
    printf("  every kernel difference equals local thickness   %s\n",
           thickness_ok ? "PASS" : "FAIL");
    printf("  every prime-level value equals (p-1)/2           %s\n",
           prime_ok ? "PASS" : "FAIL");
    printf("  only exact conductor p carries orbit energy      %s\n",
           conductor_support_ok ? "PASS" : "FAIL");
    printf("  nonprimitive and even-prime domain rejection     %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("\n%d/6 verification groups passed.\n", passed);
    printf("Computed  orbit membership, additive boundary, kernel diagonal,\n");
    printf("antipodal term, exact-conductor spectrum, and energy all use exact\n");
    printf("integer arithmetic.\n");
    printf("Proof status  the universal full-orbit law is algebraic; this bounded\n");
    printf("audit checks one complete unit orbit per declared model.\n");
    return passed == 6;
}

void full_orbit_energy_help(void)
{
    printf(
        "Full-orbit energy law\n\n"
        "Commands\n"
        "  nfield full-orbit-energy inspect <base> <p> <depth>\n"
        "      Require the base to generate every unit modulo p^depth, then\n"
        "      compare the exact odd-character kernel with the closed law.\n"
        "  nfield full-orbit-energy verify\n"
        "  nfield verify full-orbit-energy\n\n"
        "Example\n"
        "  nfield full-orbit-energy inspect 2 3 2\n\n"
        "Scope\n"
        "  proved       E(b,p^e)=phi(p^e)*p^(e-1)/2 for a primitive-root base.\n"
        "  exact        multiplicative order, orbit support, additive boundary,\n"
        "               odd kernel, thickness, exact-conductor spectrum, and\n"
        "               energy use integers only. Only conductor p is nonzero.\n"
        "  boundary     p must be odd, p^e<=200000, and b must generate the\n"
        "               complete unit group; coset energies are not inferred.\n"
    );
}
