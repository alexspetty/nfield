#include "reset_source.h"
#include <string.h>

static unsigned rs_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned t = a % b; a = b; b = t; }
    return a;
}

static int rs_mobius(unsigned n)
{
    int sign = 1;
    for (unsigned p = 2; p <= n / p; ++p) {
        if (n % p) continue;
        n /= p;
        sign = -sign;
        if (n % p == 0) return 0;
    }
    return n > 1 ? -sign : sign;
}

static void rs_scale(mpq_t out, const mpq_t in, long numerator,
                     unsigned long denominator)
{
    mpq_t factor;
    mpq_init(factor);
    mpq_set_si(factor, numerator, denominator);
    mpq_canonicalize(factor);
    mpq_mul(out, in, factor);
    mpq_clear(factor);
}

void reset_source_init(ResetSource *out)
{
    out->cutoff = out->grid = 0;
    out->saturated = out->has_work = 0;
    memset(out->mask, 0, sizeof(out->mask));
    memset(out->destination, 0, sizeof(out->destination));
    mpz_init(out->modulus);
    for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) {
        mpq_inits(out->total[c], out->ordered_work[c], out->reset_work[c], NULL);
        for (unsigned j = 0; j <= RESET_SOURCE_MAX_CUTOFF; ++j)
            mpq_inits(out->coefficient[c][j], out->mass[c][j], NULL);
        for (unsigned f = 0; f < RS_FORM_COUNT; ++f)
            mpq_init(out->energy[f][c]);
    }
    for (unsigned j = 0; j <= RESET_SOURCE_MAX_CUTOFF; ++j)
        mpq_inits(out->primitive_work[j], out->clock_work[j], NULL);
    for (unsigned f = 0; f < RS_FORM_COUNT; ++f) mpq_init(out->mixed[f]);
}

void reset_source_clear(ResetSource *out)
{
    mpz_clear(out->modulus);
    for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) {
        mpq_clears(out->total[c], out->ordered_work[c], out->reset_work[c], NULL);
        for (unsigned j = 0; j <= RESET_SOURCE_MAX_CUTOFF; ++j)
            mpq_clears(out->coefficient[c][j], out->mass[c][j], NULL);
        for (unsigned f = 0; f < RS_FORM_COUNT; ++f)
            mpq_clear(out->energy[f][c]);
    }
    for (unsigned j = 0; j <= RESET_SOURCE_MAX_CUTOFF; ++j)
        mpq_clears(out->primitive_work[j], out->clock_work[j], NULL);
    for (unsigned f = 0; f < RS_FORM_COUNT; ++f) mpq_clear(out->mixed[f]);
}

void reset_source_mass(mpq_t out, const mpq_t *coefficient,
                       unsigned cutoff, unsigned reset)
{
    mpq_t sum;
    mpq_init(sum);
    if (reset && reset <= cutoff && coefficient)
        for (unsigned j = reset; j <= cutoff; j += reset)
            mpq_add(sum, sum, coefficient[j]);
    mpq_set(out, sum);
    mpq_clear(sum);
}

static void rs_field(mpq_t out, const mpq_t *c, unsigned n,
                     unsigned a, unsigned q)
{
    mpq_t term, value;
    mpq_inits(term, value, NULL);
    for (unsigned j = 1; j <= n; ++j) {
        unsigned residue = (j * a) % q;
        if (!residue || mpq_sgn(c[j]) == 0) continue;
        mpq_set_si(term, 2L * residue - (long)q, q);
        mpq_canonicalize(term);
        mpq_mul(term, term, c[j]);
        mpq_add(value, value, term);
    }
    mpq_set(out, value);
    mpq_clears(term, value, NULL);
}

static void rs_pairing(mpq_t out, const mpq_t *c, const mpq_t *e,
                       unsigned n)
{
    mpq_t term, kernel;
    mpq_inits(term, kernel, NULL);
    mpq_set_ui(out, 0, 1);
    for (unsigned i = 1; i <= n; ++i) {
        if (mpq_sgn(c[i]) == 0) continue;
        for (unsigned j = 1; j <= n; ++j) {
            if (mpq_sgn(e[j]) == 0) continue;
            unsigned g = rs_gcd(i, j);
            mpq_set_ui(kernel, g * g, 3UL * i * j);
            mpq_canonicalize(kernel);
            mpq_mul(term, c[i], e[j]);
            mpq_mul(term, term, kernel);
            mpq_add(out, out, term);
        }
    }
    mpq_clears(term, kernel, NULL);
}

static void rs_work(ResetSource *out)
{
    unsigned n = out->cutoff, q = out->grid;
    mpq_t field[RS_COMPONENT_COUNT], term, phase;
    for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) mpq_init(field[c]);
    mpq_inits(term, phase, NULL);
    for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c)
        rs_pairing(out->energy[RS_CONTINUOUS][c], out->coefficient[c],
                   out->coefficient[c], n);
    rs_pairing(out->mixed[RS_CONTINUOUS], out->coefficient[RS_SELECTED],
               out->coefficient[RS_COMPLEMENT], n);
    rs_scale(out->mixed[RS_CONTINUOUS], out->mixed[RS_CONTINUOUS], 2, 1);
    for (unsigned a = 1; a < q; ++a) {
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) {
            rs_field(field[c], out->coefficient[c], n, a, q);
            mpq_mul(term, field[c], field[c]);
            mpq_add(out->energy[RS_SAMPLED][c], out->energy[RS_SAMPLED][c], term);
        }
        mpq_mul(term, field[RS_SELECTED], field[RS_COMPLEMENT]);
        mpq_add(out->mixed[RS_SAMPLED], out->mixed[RS_SAMPLED], term);
    }
    for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c)
        rs_scale(out->energy[RS_SAMPLED][c], out->energy[RS_SAMPLED][c], 1, q);
    rs_scale(out->mixed[RS_SAMPLED], out->mixed[RS_SAMPLED], 2, q);

    for (unsigned k = 2; k <= n; ++k) {
        for (unsigned a = 1; a < k; ++a) {
            unsigned residue = (q * a) % k;
            if (!residue) continue;
            rs_field(field[0], out->coefficient[RS_ORIGINAL], n, a, k);
            mpq_set_si(phase, 2L * residue - (long)k, 2UL * k);
            mpq_canonicalize(phase);
            mpq_mul(term, field[0], phase);
            mpq_add(out->clock_work[k], out->clock_work[k], term);
            if (rs_gcd(a, k) == 1)
                mpq_add(out->primitive_work[k], out->primitive_work[k], term);
        }
        /* W_k = sum (B_c/2) psi(Qa/k); the primitive reading uses B_c. */
        rs_scale(out->clock_work[k], out->clock_work[k], 1, 2);
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) {
            mpq_mul(term, out->coefficient[c][k], out->clock_work[k]);
            rs_scale(term, term, 2, 1);
            mpq_add(out->ordered_work[c], out->ordered_work[c], term);
            mpq_mul(term, out->mass[c][k], out->primitive_work[k]);
            mpq_add(out->reset_work[c], out->reset_work[c], term);
        }
    }
    for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) mpq_clear(field[c]);
    mpq_clears(term, phase, NULL);
    out->has_work = 1;
}

int reset_source_project(ResetSource *out, unsigned n, const mpq_t *coefficient,
                         const unsigned char *mask, unsigned grid)
{
    if (!out || n > RESET_SOURCE_MAX_CUTOFF || grid > RESET_SOURCE_MAX_GRID ||
        (n && (!coefficient || !mask))) return 0;
    for (unsigned j = 1; j <= n; ++j) if (mask[j] > 1) return 0;

    /* Copy inputs before resetting the output, so reprojecting a returned
     * component in the same object is well-defined. */
    mpq_t input[RESET_SOURCE_MAX_CUTOFF + 1];
    unsigned char selection[RESET_SOURCE_MAX_CUTOFF + 1] = {0};
    for (unsigned j = 0; j <= n; ++j) {
        mpq_init(input[j]);
        if (j) { mpq_set(input[j], coefficient[j]); selection[j] = mask[j]; }
    }
    reset_source_clear(out);
    reset_source_init(out);
    out->cutoff = n;
    out->grid = grid;
    for (unsigned j = 1; j <= n; ++j) {
        mpq_set(out->coefficient[RS_ORIGINAL][j], input[j]);
        out->mask[j] = selection[j];
    }
    for (unsigned j = 0; j <= n; ++j) mpq_clear(input[j]);
    for (unsigned k = 1; k <= n; ++k) {
        reset_source_mass(out->mass[RS_ORIGINAL][k], out->coefficient[RS_ORIGINAL], n, k);
        if (selection[k]) mpq_set(out->mass[RS_SELECTED][k], out->mass[RS_ORIGINAL][k]);
        mpq_sub(out->mass[RS_COMPLEMENT][k], out->mass[RS_ORIGINAL][k], out->mass[RS_SELECTED][k]);
    }
    for (unsigned d = 1; d <= n; ++d) {
        for (unsigned j = 1; j <= n / d; ++j) {
            int mu = rs_mobius(j);
            if (mu > 0) mpq_add(out->coefficient[RS_SELECTED][d], out->coefficient[RS_SELECTED][d], out->mass[RS_SELECTED][d*j]);
            if (mu < 0) mpq_sub(out->coefficient[RS_SELECTED][d], out->coefficient[RS_SELECTED][d], out->mass[RS_SELECTED][d*j]);
        }
        mpq_sub(out->coefficient[RS_COMPLEMENT][d], out->coefficient[RS_ORIGINAL][d], out->coefficient[RS_SELECTED][d]);
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c)
            mpq_add(out->total[c], out->total[c], out->coefficient[c][d]);
    }
    if (grid) rs_work(out);
    return 1;
}

int reset_source_collapse(ResetSource *out, unsigned n, const mpq_t *coefficient,
                          const mpz_t modulus, unsigned grid)
{
    if (!out || !modulus || mpz_sgn(modulus) < 0 || n > RESET_SOURCE_MAX_CUTOFF)
        return 0;
    unsigned char mask[RESET_SOURCE_MAX_CUTOFF + 1] = {0};
    for (unsigned k = 1; k <= n; ++k) mask[k] = mpz_divisible_ui_p(modulus, k) != 0;
    mpz_t carrier;
    mpz_init_set(carrier, modulus);
    int ok = reset_source_project(out, n, coefficient, mask, grid);
    if (ok) {
        out->saturated = 1;
        mpz_set(out->modulus, carrier);
        for (unsigned j = 1; j <= n; ++j)
            out->destination[j] = rs_gcd(j, (unsigned)mpz_fdiv_ui(carrier, j));
    }
    mpz_clear(carrier);
    return ok;
}
