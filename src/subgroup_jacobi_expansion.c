/* Jacobi-type expansion of an additive subgroup-orbit boundary flux. */

#include <complex.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"
#include "orbit_boundary_core.h"

#define SJE_TOLERANCE 5.0e-11L

typedef struct {
    int prime;
    int phi;
    int generator;
    int *discrete_log;
    unsigned char *is_unit;
} SjeContext;

static int sje_primitive_root(int prime)
{
    for (int candidate = 2; candidate < prime; candidate++)
        if (orbit_boundary_multiplicative_order(candidate, prime) == prime - 1)
            return candidate;
    return 0;
}

static void sje_context_free(SjeContext *context)
{
    if (!context) return;
    free(context->discrete_log);
    free(context->is_unit);
    *context = (SjeContext){0};
}

static int sje_context_build(int prime, SjeContext *context)
{
    if (!context || prime == 2 || !orbit_boundary_is_prime(prime)) return 0;
    *context = (SjeContext){
        .prime = prime,
        .phi = prime - 1,
        .generator = sje_primitive_root(prime)
    };
    if (context->generator == 0) return 0;
    context->discrete_log = malloc(
        (size_t)prime * sizeof(*context->discrete_log));
    context->is_unit = calloc((size_t)prime, sizeof(*context->is_unit));
    if (!context->discrete_log || !context->is_unit) {
        sje_context_free(context);
        return 0;
    }
    for (int residue = 0; residue < prime; residue++)
        context->discrete_log[residue] = -1;
    int residue = 1;
    for (int exponent = 0; exponent < context->phi; exponent++) {
        context->discrete_log[residue] = exponent;
        context->is_unit[residue] = 1;
        residue = (int)((long long)residue * context->generator % prime);
    }
    if (residue != 1) {
        sje_context_free(context);
        return 0;
    }
    return 1;
}

static long double complex sje_character(
        const SjeContext *context, int exponent, int residue)
{
    residue %= context->prime;
    if (residue < 0) residue += context->prime;
    if (!context->is_unit[residue]) return 0.0L + 0.0L * I;
    long double angle = 2.0L * acosl(-1.0L) *
        (long double)((long long)exponent *
                      context->discrete_log[residue] % context->phi) /
        (long double)context->phi;
    return cosl(angle) + I * sinl(angle);
}

static int sje_compare(
        const SjeContext *context, int base, int character_exponent,
        long double complex *direct_flux,
        long double complex *expanded_flux,
        int *order, int *index, int *resonant)
{
    if (!context || !direct_flux || !expanded_flux || !order || !index ||
        !resonant || character_exponent <= 0 ||
        character_exponent >= context->phi || character_exponent % 2 == 0)
        return 0;
    int subgroup_order = orbit_boundary_multiplicative_order(
        base, context->prime);
    if (subgroup_order <= 0 || context->phi % subgroup_order != 0) return 0;
    int subgroup_index = context->phi / subgroup_order;
    OrbitBoundary orbit = {0};
    if (!orbit_boundary_build_subgroup(base, context->prime, &orbit)) return 0;
    long double complex direct = 0.0L + 0.0L * I;
    for (int residue = 0; residue < context->prime; residue++)
        direct += (long double)orbit.boundary[residue] *
                  sje_character(context, character_exponent, residue);

    long double complex expansion = 0.0L + 0.0L * I;
    for (int quotient_index = 0;
         quotient_index < subgroup_index; quotient_index++) {
        int rho_exponent = quotient_index * subgroup_order;
        long double complex jacobi = 0.0L + 0.0L * I;
        for (int residue = 0; residue < context->prime; residue++)
            jacobi += sje_character(context, rho_exponent, residue) *
                      sje_character(
                          context, character_exponent, residue + 1);
        if ((rho_exponent + character_exponent) % context->phi == 0)
            jacobi -= (long double)context->phi;
        expansion += jacobi;
    }
    expansion /= (long double)subgroup_index;
    *direct_flux = direct;
    *expanded_flux = expansion;
    *order = subgroup_order;
    *index = subgroup_index;
    *resonant = character_exponent % subgroup_order == 0;
    orbit_boundary_free(&orbit);
    return cabsl(direct - expansion) <=
           SJE_TOLERANCE * (1.0L + cabsl(direct) + cabsl(expansion));
}

int subgroup_jacobi_expansion_compare(
        int prime, int base, int character_exponent,
        long double *error, int *order, int *index, int *resonant)
{
    if (!error || !order || !index || !resonant) return 0;
    SjeContext context = {0};
    if (!sje_context_build(prime, &context)) return 0;
    long double complex direct = 0.0L;
    long double complex expansion = 0.0L;
    int ok = sje_compare(
        &context, base, character_exponent,
        &direct, &expansion, order, index, resonant);
    if (ok) *error = cabsl(direct - expansion);
    sje_context_free(&context);
    return ok;
}

static void sje_print_complex(const char *label, long double complex value)
{
    printf("  %-27s %+.12Lf %+.12Lfi\n",
           label, creall(value), cimagl(value));
}

int subgroup_jacobi_expansion_inspect(
        int prime, int base, int character_exponent)
{
    SjeContext context = {0};
    if (!sje_context_build(prime, &context)) {
        fprintf(stderr, "p must be an odd prime\n");
        return 1;
    }
    if (character_exponent <= 0 || character_exponent >= context.phi ||
        character_exponent % 2 == 0) {
        fprintf(stderr,
                "character exponent must be odd and lie in [1,p-2]\n");
        sje_context_free(&context);
        return 1;
    }
    long double complex direct = 0.0L;
    long double complex expansion = 0.0L;
    int order = 0;
    int index = 0;
    int resonant = 0;
    int ok = sje_compare(
        &context, base, character_exponent,
        &direct, &expansion, &order, &index, &resonant);
    if (order == 0) {
        fprintf(stderr, "base must be nonzero modulo p\n");
        sje_context_free(&context);
        return 1;
    }
    printf("Subgroup Jacobi expansion\n\n");
    printf("  prime=%d base=%d primitive-root coordinate=%d\n",
           prime, base, context.generator);
    printf("  subgroup order=%d; index=%d\n", order, index);
    printf("  odd character exponent=%d; classification=%s\n",
           character_exponent, resonant ? "resonant" : "off-resonance");
    sje_print_complex("direct boundary flux", direct);
    sje_print_complex("quotient-character expansion", expansion);
    printf("  numerical expansion error %.3Le  %s\n",
           cabsl(direct - expansion), ok ? "PASS" : "FAIL");
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    sje_context_free(&context);
    return ok ? 0 : 1;
}

int subgroup_jacobi_expansion_verify(void)
{
    int expansion_ok = 1;
    int resonance_ok = 1;
    int index_two_ok = 1;
    int domain_ok = 1;
    int models = 0;
    int resonant_models = 0;
    int off_models = 0;
    int index_two_models = 0;
    long double maximum_error = 0.0L;

    for (int prime = 3; prime <= 97; prime += 2) {
        if (!orbit_boundary_is_prime(prime)) continue;
        SjeContext context = {0};
        if (!sje_context_build(prime, &context)) return 0;
        int maximum_base = prime - 1 < 12 ? prime - 1 : 12;
        for (int base = 2; base <= maximum_base; base++) {
            int order = orbit_boundary_multiplicative_order(base, prime);
            if (order == 0) continue;
            int expected_index = (prime - 1) / order;
            for (int exponent = 1; exponent < prime - 1; exponent += 2) {
                long double complex direct = 0.0L;
                long double complex expansion = 0.0L;
                int observed_order = 0;
                int observed_index = 0;
                int resonant = 0;
                models++;
                if (!sje_compare(
                        &context, base, exponent,
                        &direct, &expansion, &observed_order,
                        &observed_index, &resonant))
                    expansion_ok = 0;
                long double error = cabsl(direct - expansion);
                if (error > maximum_error) maximum_error = error;
                if (observed_order != order ||
                    observed_index != expected_index ||
                    resonant != (exponent % order == 0))
                    resonance_ok = 0;
                if (resonant) resonant_models++;
                else off_models++;

                if (expected_index == 2 && !resonant) {
                    int quadratic_exponent = (prime - 1) / 2;
                    long double complex jacobi = 0.0L;
                    for (int residue = 0; residue < prime; residue++)
                        jacobi += sje_character(
                                      &context, quadratic_exponent, residue) *
                                  sje_character(
                                      &context, exponent, residue + 1);
                    long double complex endpoint = (jacobi - 1.0L) / 2.0L;
                    index_two_models++;
                    if (cabsl(direct - endpoint) > SJE_TOLERANCE)
                        index_two_ok = 0;
                }
            }
        }
        sje_context_free(&context);
    }
    long double error = 0.0L;
    int order = 0;
    int index = 0;
    int resonant = 0;
    domain_ok = !subgroup_jacobi_expansion_compare(
                    9, 2, 1, &error, &order, &index, &resonant) &&
                !subgroup_jacobi_expansion_compare(
                    7, 2, 2, &error, &order, &index, &resonant);

    int coverage_ok = models > 0 && resonant_models > 0 && off_models > 0;
    int passed = expansion_ok + resonance_ok + index_two_ok +
                 coverage_ok + domain_ok;
    printf("Subgroup Jacobi-expansion verification\n\n");
    printf("  subgroup/odd-character models=%d                 %s\n",
           models, expansion_ok ? "PASS" : "FAIL");
    printf("  resonant=%d; off-resonance=%d classifications    %s\n",
           resonant_models, off_models,
           resonance_ok && coverage_ok ? "PASS" : "FAIL");
    printf("  index-two endpoint reductions=%d                 %s\n",
           index_two_models, index_two_ok ? "PASS" : "FAIL");
    printf("  declared family covers both spectral branches    %s\n",
           coverage_ok ? "PASS" : "FAIL");
    printf("  prime and odd-character domain rejection         %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("  maximum numerical expansion error %.3Le\n", maximum_error);
    printf("\n%d/5 verification groups passed.\n", passed);
    printf("Exact boundary  subgroup order, index, orbit support, additive boundary,\n");
    printf("annihilator exponents, and resonance labels use integer arithmetic.\n");
    printf("Numerical boundary  roots of unity and Jacobi-type sums use long-double\n");
    printf("complex arithmetic. No higher-index closed form is asserted.\n");
    printf("Proof status  the quotient-character expansion and index-two endpoint\n");
    printf("reduction are algebraic identities.\n");
    return passed == 5;
}

void subgroup_jacobi_expansion_help(void)
{
    printf(
        "Subgroup Jacobi expansion\n\n"
        "Commands\n"
        "  nfield subgroup-jacobi-expansion inspect <p> <base> <odd-exponent>\n"
        "      Build H=<base>, classify the character against H's annihilator,\n"
        "      and compare direct boundary flux with the quotient-character sum.\n"
        "  nfield subgroup-jacobi-expansion verify\n"
        "  nfield verify subgroup-jacobi-expansion\n\n"
        "Example\n"
        "  nfield subgroup-jacobi-expansion inspect 7 2 1\n\n"
        "Scope\n"
        "  proved       every prime-modulus subgroup boundary flux has the exact\n"
        "               quotient-character Jacobi expansion.\n"
        "  exact        subgroup order and index, additive boundary, annihilator,\n"
        "               and resonant/off-resonance classification.\n"
        "  numerical    roots of unity, direct flux, and Jacobi-type sums.\n"
        "  boundary     prime modulus only; higher-index fluxes are expanded but\n"
        "               no unproved higher-index closed energy law is claimed.\n"
    );
}
