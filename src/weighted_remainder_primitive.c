/* Exact primitive weights, reciprocal budgets and the finite pair tree. */
#include "weighted_remainder_primitive.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void set_potential(mpq_t out, unsigned a, unsigned b)
{
    mpz_set_ui(mpq_numref(out), a + b);
    mpz_set_ui(mpq_denref(out), a);
    mpz_mul_ui(mpq_denref(out), mpq_denref(out), a);
    mpz_mul_ui(mpq_denref(out), mpq_denref(out), b);
    mpz_mul_ui(mpq_denref(out), mpq_denref(out), b);
    mpq_canonicalize(out);
}

static void set_pair_mass(mpq_t out, unsigned a, unsigned b)
{
    mpz_set_ui(mpq_numref(out), 1);
    mpz_set_ui(mpq_denref(out), a);
    mpz_mul_ui(mpq_denref(out), mpq_denref(out), b);
    mpz_mul_ui(mpq_denref(out), mpq_denref(out), a + b);
    mpq_canonicalize(out);
}

int weighted_remainder_tree_node_q(mpq_t potential, mpq_t left, mpq_t right,
                                   mpq_t loss, unsigned a, unsigned b)
{
    if (!a || !b || a > WEIGHTED_REMAINDER_EXACT_MAX ||
        b > WEIGHTED_REMAINDER_EXACT_MAX || potential == left ||
        potential == right || potential == loss || left == right ||
        left == loss || right == loss) return 0;
    set_potential(potential, a, b);
    set_potential(left, a, a + b);
    set_potential(right, a + b, b);
    set_pair_mass(loss, a, b);
    return 1;
}

int weighted_remainder_tree_address_q(mpq_t out, unsigned a, unsigned b)
{
    if (!a || !b || a > WEIGHTED_REMAINDER_EXACT_MAX ||
        b > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpz_set_ui(mpq_numref(out), 1);
    mpz_set_ui(mpq_denref(out), a);
    mpz_mul_ui(mpq_denref(out), mpq_denref(out), a + b);
    mpz_mul_ui(mpq_denref(out), mpq_denref(out), a + b);
    mpq_canonicalize(out);
    return 1;
}

static void accumulate_tree(unsigned a, unsigned b, unsigned cutoff,
                            mpq_t mass, mpq_t frontier, mpq_t term,
                            unsigned *nodes)
{
    ++*nodes;
    set_pair_mass(term, a, b);
    mpq_add(mass, mass, term);
    unsigned sum = a + b;
    if (sum <= cutoff) {
        /* The coordinate sum strictly increases. With cutoff<=240 the
         * recursion depth is at most 2*cutoff-1. Each primitive node has
         * one parent, proved by the finite child bijections in Lean. */
        accumulate_tree(a, sum, cutoff, mass, frontier, term, nodes);
        accumulate_tree(sum, b, cutoff, mass, frontier, term, nodes);
    } else {
        set_potential(term, a, sum);
        mpq_add(frontier, frontier, term);
        set_potential(term, sum, b);
        mpq_add(frontier, frontier, term);
    }
}

int weighted_remainder_tree_box_q(mpq_t mass, mpq_t frontier, mpq_t upper,
                                  unsigned cutoff, unsigned *node_count)
{
    if (!cutoff || cutoff > WEIGHTED_REMAINDER_EXACT_MAX ||
        mass == frontier || mass == upper || frontier == upper) return 0;
    mpq_t total, outgoing, bound, term;
    mpq_inits(total, outgoing, bound, term, NULL);
    unsigned nodes = 0;
    accumulate_tree(1, 1, cutoff, total, outgoing, term, &nodes);
    mpq_set_ui(bound, 1, 1);
    for (unsigned k = 1; k <= cutoff; ++k) {
        mpq_set_ui(term, 1, k);
        mpq_add(bound, bound, term);
    }
    mpq_set_ui(term, 2, cutoff);
    mpq_canonicalize(term);
    mpq_mul(bound, bound, term);
    mpq_set(mass, total);
    mpq_set(frontier, outgoing);
    mpq_set(upper, bound);
    if (node_count) *node_count = nodes;
    mpq_clears(total, outgoing, bound, term, NULL);
    return 1;
}

int weighted_remainder_budget_q(mpq_t out, unsigned n)
{
    if (!n || n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t sum, term;
    mpq_inits(sum, term, NULL);
    for (unsigned k = 1; k <= n; ++k) if (n % k == 0) {
        weighted_remainder_weight_q(term, k);
        for (unsigned j = 0; j < 3; ++j)
            mpz_mul_ui(mpq_numref(term), mpq_numref(term), k);
        mpq_canonicalize(term);
        mpq_add(sum, sum, term);
    }
    mpq_set(out, sum);
    mpq_clears(sum, term, NULL);
    return 1;
}

static int primitive_mobius(unsigned n)
{
    int sign = 1;
    for (unsigned p = 2; p <= n / p; ++p) if (n % p == 0) {
        n /= p;
        if (n % p == 0) return 0;
        sign = -sign;
    }
    return n > 1 ? -sign : sign;
}

int weighted_remainder_weight_inverse_q(mpq_t out, unsigned n)
{
    if (n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t sum, harmonic, term;
    mpq_inits(sum, harmonic, term, NULL);
    for (unsigned d = 1; d <= n; ++d) if (n % d == 0) {
        int mu = primitive_mobius(n / d);
        if (!mu) continue;
        mpq_set_ui(harmonic, 0, 1);
        for (unsigned j = 1; j < d; ++j) {
            mpq_set_ui(term, 1, j);
            mpq_add(harmonic, harmonic, term);
        }
        mpz_mul_ui(mpq_numref(harmonic), mpq_numref(harmonic), d);
        mpq_canonicalize(harmonic);
        if (mu > 0) mpq_add(sum, sum, harmonic);
        else mpq_sub(sum, sum, harmonic);
    }
    if (n) {
        for (unsigned j = 0; j < 3; ++j)
            mpz_mul_ui(mpq_denref(sum), mpq_denref(sum), n);
        mpq_canonicalize(sum);
    }
    mpq_set(out, sum);
    mpq_clears(sum, harmonic, term, NULL);
    return 1;
}

int weighted_remainder_mass_q(mpq_t retained, mpq_t omitted, unsigned cutoff)
{
    if (cutoff > WEIGHTED_REMAINDER_EXACT_MAX || retained == omitted) return 0;
    mpq_t mass, tail, term;
    mpq_inits(mass, tail, term, NULL);
    for (unsigned k = 2; k <= cutoff; ++k) {
        weighted_remainder_weight_q(term, k);
        mpq_add(mass, mass, term);
    }
    mpq_set_ui(tail, 1, 1);
    mpq_sub(tail, tail, mass);
    mpq_set(retained, mass);
    mpq_set(omitted, tail);
    mpq_clears(mass, tail, term, NULL);
    return 1;
}

int weighted_remainder_mass_budget_q(mpq_t retained, mpq_t omitted,
                                     mpq_t weighted_mass, mpq_t deficit_upper,
                                     unsigned cutoff)
{
    if (cutoff > WEIGHTED_REMAINDER_EXACT_MAX || retained == omitted ||
        retained == weighted_mass || retained == deficit_upper ||
        omitted == weighted_mass || omitted == deficit_upper ||
        weighted_mass == deficit_upper) return 0;
    mpq_t mass, tail, moment, bound, term;
    mpq_inits(mass, tail, moment, bound, term, NULL);
    weighted_remainder_mass_q(mass, tail, cutoff);
    for (unsigned k = 2; k <= cutoff; ++k) {
        weighted_remainder_weight_q(term, k);
        mpz_mul_ui(mpq_numref(term), mpq_numref(term), k);
        mpq_canonicalize(term);
        mpq_add(moment, moment, term);
    }
    mpq_set_ui(term, cutoff, 1);
    mpq_mul(bound, tail, term);
    mpq_add(bound, bound, moment);
    mpq_set_ui(term, 2, 3);
    mpq_mul(bound, bound, term);
    mpq_set(retained, mass);
    mpq_set(omitted, tail);
    mpq_set(weighted_mass, moment);
    mpq_set(deficit_upper, bound);
    mpq_clears(mass, tail, moment, bound, term, NULL);
    return 1;
}

static int primitive_index(const char *text, unsigned minimum, unsigned *out)
{
    if (!text || !*text) return 0;
    for (const char *p = text; *p; ++p) if (*p < '0' || *p > '9') return 0;
    char *end;
    errno = 0;
    unsigned long n = strtoul(text, &end, 10);
    if (errno || *end || n < minimum || n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    *out = (unsigned)n;
    return 1;
}

int weighted_remainder_primitive_command(int argc, char **argv)
{
    unsigned a, b, nodes;
    mpq_t x, y, z, t;
    if (argc == 5 && strcmp(argv[2], "tree-node") == 0 &&
        primitive_index(argv[3], 1, &a) && primitive_index(argv[4], 1, &b)) {
        mpq_inits(x, y, z, t, NULL);
        weighted_remainder_tree_node_q(x, y, z, t, a, b);
        printf("Exact pair-tree node\ncoordinates %u %u\n", a, b);
        gmp_printf("potential %Qd\nleft_child %Qd\nright_child %Qd\nloss %Qd\n", x, y, z, t);
        weighted_remainder_tree_address_q(x, a, b);
        gmp_printf("address_mass %Qd\n", x);
        mpq_clears(x, y, z, t, NULL);
        return 0;
    }
    if (argc == 4 && strcmp(argv[2], "tree") == 0 && primitive_index(argv[3], 1, &a)) {
        mpq_inits(x, y, z, t, NULL);
        weighted_remainder_tree_box_q(x, y, z, a, &nodes);
        printf("Exact primitive square tree\ncutoff %u\nnodes %u\n", a, nodes);
        gmp_printf("primitive_pair_mass %Qd\noutgoing_mass %Qd\nharmonic_upper_bound %Qd\n", x, y, z);
        mpq_set_ui(t, 1, 2);
        mpq_mul(t, t, x);
        gmp_printf("primitive_address_mass %Qd\n", t);
        puts("The finite pair mass and outgoing mass sum to two.");
        mpq_clears(x, y, z, t, NULL);
        return 0;
    }
    if (argc == 4 && strcmp(argv[2], "weight") == 0 && primitive_index(argv[3], 0, &a)) {
        mpq_inits(x, y, z, NULL);
        weighted_remainder_weight_q(x, a);
        weighted_remainder_weight_inverse_q(y, a);
        mpq_set_ui(z, a, 1);
        mpq_mul(z, z, x);
        printf("Exact primitive harmonic weight\nperiod %u\n", a);
        gmp_printf("weight %Qd\nbudget_inverse %Qd\nforcing_coefficient %Qd\n", x, y, z);
        mpq_clears(x, y, z, NULL);
        return 0;
    }
    if (argc == 4 && strcmp(argv[2], "budget") == 0 && primitive_index(argv[3], 1, &a)) {
        mpq_init(x);
        weighted_remainder_budget_q(x, a);
        printf("Exact reciprocal-address budget\nresolution %u\n", a);
        gmp_printf("budget %Qd\n", x);
        puts("The divisor sum k^3*w_k equals n*H_(n-1).");
        mpq_clear(x);
        return 0;
    }
    if (argc == 4 && strcmp(argv[2], "mass") == 0 && primitive_index(argv[3], 0, &a)) {
        mpq_inits(x, y, z, t, NULL);
        weighted_remainder_mass_budget_q(x, y, z, t, a);
        printf("Exact retained and omitted unit mass\ncutoff %u\n", a);
        gmp_printf("retained_mass %Qd\nomitted_mass %Qd\n", x, y);
        gmp_printf("weighted_mass %Qd\ndeficit_upper_bound %Qd\n", z, t);
        puts("The omitted mass uses the proved infinite unit normalization.");
        mpq_clears(x, y, z, t, NULL);
        return 0;
    }
    fputs("Use tree <M 1..240>, tree-node <a 1..240> <b 1..240>, weight <k 0..240>, budget <n 1..240>, or mass <M 0..240>.\n", stderr);
    return 1;
}
