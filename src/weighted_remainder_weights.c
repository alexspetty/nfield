#include "weighted_remainder_weights.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned weights_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned r = a % b; a = b; b = r; }
    return a;
}

static unsigned weights_jordan_two(unsigned n)
{
    unsigned value = n * n;
    for (unsigned p = 2; p <= n / p; ++p) if (n % p == 0) {
        value = value / (p * p) * (p * p - 1);
        do { n /= p; } while (n % p == 0);
    }
    if (n > 1) value = value / (n * n) * (n * n - 1);
    return value;
}

static int weights_rational_valid(const mpq_t value)
{
    if (mpz_sgn(mpq_denref(value)) <= 0) return 0;
    mpz_t g;
    mpz_init(g);
    mpz_gcd(g, mpq_numref(value), mpq_denref(value));
    int ok = mpz_cmp_ui(g, 1) == 0;
    mpz_clear(g);
    return ok;
}

static int weights_valid(const mpq_t *v, unsigned m)
{
    if (!v || m < 2 || m > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    for (unsigned k = 0; k <= m; ++k)
        if (!weights_rational_valid(v[k])) return 0;
    return mpq_sgn(v[0]) == 0 && mpq_sgn(v[1]) == 0;
}

static int weights_epsilon_valid(const mpq_t epsilon)
{
    if (!weights_rational_valid(epsilon) || !mpq_sgn(epsilon)) return 0;
    mpq_t value, bound;
    mpq_inits(value, bound, NULL);
    mpq_abs(value, epsilon);
    mpq_set_ui(bound, 1, 24);
    int ok = mpq_cmp(value, bound) < 0;
    mpq_clears(value, bound, NULL);
    return ok;
}

void weighted_remainder_weights_init(WeightedRemainderWeights *s)
{
    s->cutoff = 0;
    s->nonnegative = s->unit_mass = 0;
    mpq_inits(s->mass, s->first_moment, s->raw_age, s->stationary_age,
               s->centered_age, s->divisor_forcing, s->increment,
               s->gram_variance, s->jordan_variance, NULL);
}

void weighted_remainder_weights_clear(WeightedRemainderWeights *s)
{
    mpq_clears(s->mass, s->first_moment, s->raw_age, s->stationary_age,
                s->centered_age, s->divisor_forcing, s->increment,
                s->gram_variance, s->jordan_variance, NULL);
}

int weighted_remainder_weights_compute(WeightedRemainderWeights *out,
                                       const mpq_t *v, unsigned m,
                                       const mpz_t address)
{
    if (!out || !weights_valid(v, m)) return 0;
    WeightedRemainderWeights s;
    weighted_remainder_weights_init(&s);
    s.nonnegative = 1;
    mpq_t factor, term, xi;
    mpq_inits(factor, term, xi, NULL);
    for (unsigned k = 2; k <= m; ++k) {
        if (mpq_sgn(v[k]) < 0) s.nonnegative = 0;
        if (!mpq_sgn(v[k])) continue;
        unsigned r = (unsigned)mpz_fdiv_ui(address, k);
        mpq_add(s.mass, s.mass, v[k]);
        mpq_set_ui(factor, k, 1);
        mpq_mul(term, factor, v[k]);
        mpq_add(s.first_moment, s.first_moment, term);
        if (!r) mpq_add(s.divisor_forcing, s.divisor_forcing, term);
        mpq_set_ui(factor, 2 * r, 3);
        mpq_canonicalize(factor);
        mpq_mul(term, factor, v[k]);
        mpq_add(s.raw_age, s.raw_age, term);
        for (unsigned ell = 2; ell <= k; ++ell) {
            if (!mpq_sgn(v[ell])) continue;
            unsigned g = weights_gcd(k, ell);
            mpq_set_ui(factor, (g * g - 1) * (ell == k ? 1 : 2), 27);
            mpq_canonicalize(factor);
            mpq_mul(term, v[k], v[ell]);
            mpq_mul(term, term, factor);
            mpq_add(s.gram_variance, s.gram_variance, term);
        }
    }
    for (unsigned q = 2; q <= m; ++q) {
        mpq_set_ui(xi, 0, 1);
        for (unsigned k = q; k <= m; k += q) mpq_add(xi, xi, v[k]);
        mpq_mul(term, xi, xi);
        mpq_set_ui(factor, weights_jordan_two(q), 27);
        mpq_canonicalize(factor);
        mpq_mul(term, term, factor);
        mpq_add(s.jordan_variance, s.jordan_variance, term);
    }
    mpq_sub(s.stationary_age, s.first_moment, s.mass);
    mpq_set_ui(factor, 1, 3);
    mpq_mul(s.stationary_age, s.stationary_age, factor);
    mpq_sub(s.centered_age, s.raw_age, s.stationary_age);
    mpq_sub(s.increment, s.mass, s.divisor_forcing);
    mpq_set_ui(factor, 2, 3);
    mpq_mul(s.increment, s.increment, factor);
    out->cutoff = m;
    out->nonnegative = s.nonnegative;
    out->unit_mass = mpq_cmp_ui(s.mass, 1, 1) == 0;
    mpq_set(out->mass, s.mass);
    mpq_set(out->first_moment, s.first_moment);
    mpq_set(out->raw_age, s.raw_age);
    mpq_set(out->stationary_age, s.stationary_age);
    mpq_set(out->centered_age, s.centered_age);
    mpq_set(out->divisor_forcing, s.divisor_forcing);
    mpq_set(out->increment, s.increment);
    mpq_set(out->gram_variance, s.gram_variance);
    mpq_set(out->jordan_variance, s.jordan_variance);
    mpq_clears(factor, term, xi, NULL);
    weighted_remainder_weights_clear(&s);
    return 1;
}

int weighted_remainder_weights_amplitude_q(mpq_t out, const mpq_t *v,
                                           unsigned m, unsigned q)
{
    if (!weights_valid(v, m) || q < 2 || q > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    mpq_t sum;
    mpq_init(sum);
    for (unsigned k = q; k <= m; k += q) mpq_add(sum, sum, v[k]);
    mpq_set(out, sum);
    mpq_clear(sum);
    return 1;
}

int weighted_remainder_weights_energy_q(mpq_t out, const mpq_t *v,
                                        unsigned m, const mpz_t n)
{
    if (!weights_valid(v, m) || mpz_sgn(n) < 0) return 0;
    mpq_t mass, energy, factor, term;
    mpq_inits(mass, energy, factor, term, NULL);
    int ok = 1;
    for (unsigned k = 2; k <= m; ++k) {
        if (mpq_sgn(v[k]) < 0) ok = 0;
        mpq_add(mass, mass, v[k]);
    }
    ok = ok && mpq_cmp_ui(mass, 1, 1) == 0;
    if (ok) {
        mpz_set(mpq_numref(energy), n);
        mpz_set_ui(mpq_denref(energy), 3);
        mpq_canonicalize(energy);
        for (unsigned k = 2; k <= m; ++k) {
            if (!mpq_sgn(v[k])) continue;
            mpz_fdiv_q_ui(mpq_numref(factor), n, k);
            mpz_mul_ui(mpq_numref(factor), mpq_numref(factor), 2 * k);
            mpz_set_ui(mpq_denref(factor), 3);
            mpq_canonicalize(factor);
            mpq_mul(term, factor, v[k]);
            mpq_add(energy, energy, term);
        }
        mpq_set(out, energy);
    }
    mpq_clears(mass, energy, factor, term, NULL);
    return ok;
}

int weighted_remainder_perturbed_weights_q(mpq_t *out, unsigned m,
                                          const mpq_t epsilon)
{
    if (!out || m < 4 || m > WEIGHTED_REMAINDER_EXACT_MAX ||
        !weights_epsilon_valid(epsilon)) return 0;
    mpq_t e, bound;
    mpq_inits(e, bound, NULL);
    mpq_set(e, epsilon);
    for (unsigned k = 0; k <= m; ++k) weighted_remainder_weight_q(out[k], k);
    mpq_add(out[2], out[2], e);
    mpq_mul_2exp(bound, e, 1);
    mpq_sub(out[3], out[3], bound);
    mpq_add(out[4], out[4], e);
    mpq_clears(e, bound, NULL);
    return 1;
}

int weighted_remainder_perturbed_deficit_q(mpq_t original, mpq_t perturbed,
                                          unsigned n, const mpq_t epsilon)
{
    if (original == perturbed || n > WEIGHTED_REMAINDER_EXACT_MAX ||
        !weights_epsilon_valid(epsilon)) return 0;
    mpq_t e, base, shift, value;
    mpq_inits(e, base, shift, value, NULL);
    mpq_set(e, epsilon);
    weighted_remainder_capacity_q(base, n);
    mpq_set_ui(value, n, 1);
    mpq_sub(base, value, base);
    long numerator = 2L * ((long)(n % 2) - 2L * (n % 3) + (long)(n % 4));
    mpq_set_si(shift, numerator, 3);
    mpq_canonicalize(shift);
    mpq_mul(shift, shift, e);
    mpq_add(value, base, shift);
    mpq_set(original, base);
    mpq_set(perturbed, value);
    mpq_clears(e, base, shift, value, NULL);
    return 1;
}

int weighted_remainder_collision_variance_q(mpq_t finite, mpq_t squared_error,
                                           mpq_t cross_upper, mpq_t full_upper,
                                           unsigned *binary_exponent, unsigned m)
{
    mpq_ptr outputs[] = {finite, squared_error, cross_upper, full_upper};
    if (!binary_exponent || m < 2 || m > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    for (unsigned i = 0; i < 4; ++i)
        for (unsigned j = i + 1; j < 4; ++j) if (outputs[i] == outputs[j]) return 0;
    mpq_t v[WEIGHTED_REMAINDER_EXACT_MAX + 1], error, product, cross, upper;
    mpq_inits(error, product, cross, upper, NULL);
    for (unsigned k = 0; k <= m; ++k) {
        mpq_init(v[k]); weighted_remainder_weight_q(v[k], k);
    }
    mpz_t zero, scaled, quotient, root, square;
    mpz_inits(zero, scaled, quotient, root, square, NULL);
    WeightedRemainderWeights state;
    weighted_remainder_weights_init(&state);
    weighted_remainder_weights_compute(&state, v, m, zero);
    unsigned b = 0, power = 1;
    while (power < 2 * m) { power *= 2; ++b; }
    mpq_set_ui(error, 256 * (b + 1) * (b + 1), m);
    mpq_canonicalize(error);
    mpq_mul(product, state.gram_variance, error);
    unsigned grid = m * m;
    mpz_mul_ui(scaled, mpq_numref(product), grid);
    mpz_mul_ui(scaled, scaled, grid);
    mpz_fdiv_q(quotient, scaled, mpq_denref(product));
    mpz_sqrt(root, quotient);
    mpz_mul(square, root, root);
    mpz_mul(square, square, mpq_denref(product));
    if (mpz_cmp(square, scaled) < 0) mpz_add_ui(root, root, 1);
    mpz_set(mpq_numref(cross), root);
    mpz_set_ui(mpq_denref(cross), grid);
    mpq_canonicalize(cross);
    mpq_mul_2exp(upper, cross, 1);
    mpq_add(upper, upper, state.gram_variance);
    mpq_add(upper, upper, error);
    mpq_set(finite, state.gram_variance);
    mpq_set(squared_error, error);
    mpq_set(cross_upper, cross);
    mpq_set(full_upper, upper);
    *binary_exponent = b;
    weighted_remainder_weights_clear(&state);
    mpz_clears(zero, scaled, quotient, root, square, NULL);
    mpq_clears(error, product, cross, upper, NULL);
    for (unsigned k = 0; k <= m; ++k) mpq_clear(v[k]);
    return 1;
}

static int weights_parse_index(const char *text, unsigned *out)
{
    if (!text || !*text) return 0;
    unsigned n = 0;
    for (const char *p = text; *p; ++p) {
        if (*p < '0' || *p > '9') return 0;
        n = 10 * n + (unsigned)(*p - '0');
        if (n > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    }
    *out = n;
    return 1;
}

static int weights_parse_address(mpz_t out, const char *text)
{
    if (!text || !*text) return 0;
    const char *p = text;
    if (*p == '-' || *p == '+') ++p;
    if (!*p) return 0;
    for (; *p; ++p) if (*p < '0' || *p > '9') return 0;
    return mpz_set_str(out, *text == '+' ? text + 1 : text, 10) == 0;
}

static int weights_parse_rational(mpq_t out, const char *text)
{
    if (!text || !*text) return 0;
    const char *p = text;
    if (*p == '-' || *p == '+') ++p;
    if (*p < '0' || *p > '9') return 0;
    while (*p >= '0' && *p <= '9') ++p;
    if (*p == '/') {
        ++p;
        if (*p < '0' || *p > '9') return 0;
        while (*p >= '0' && *p <= '9') ++p;
    }
    if (*p || mpq_set_str(out, *text == '+' ? text + 1 : text, 10) ||
        mpz_sgn(mpq_denref(out)) <= 0) return 0;
    mpq_canonicalize(out);
    return 1;
}

static void weights_print_state(const WeightedRemainderWeights *s,
                                 const mpz_t address)
{
    printf("cutoff %u\nnonnegative %d\nunit_mass %d\nadmissible_probability_mass %d\n",
           s->cutoff, s->nonnegative, s->unit_mass, s->nonnegative && s->unit_mass);
    gmp_printf("address %Zd\nmass %Qd\nfirst_moment %Qd\nraw_age %Qd\n"
               "stationary_age %Qd\ncentered_age %Qd\ndivisor_forcing %Qd\n"
               "finite_increment %Qd\ngram_variance %Qd\njordan_variance %Qd\n",
               address, s->mass, s->first_moment, s->raw_age, s->stationary_age,
               s->centered_age, s->divisor_forcing, s->increment,
               s->gram_variance, s->jordan_variance);
}

int weighted_remainder_weights_command(int argc, char **argv)
{
    int ok = 0;
    unsigned m = 2;
    mpq_t v[WEIGHTED_REMAINDER_EXACT_MAX + 1], base[WEIGHTED_REMAINDER_EXACT_MAX + 1];
    for (unsigned k = 0; k <= WEIGHTED_REMAINDER_EXACT_MAX; ++k) {
        mpq_init(v[k]); mpq_init(base[k]);
    }
    mpq_t epsilon, value, delta, error, cross;
    mpq_inits(epsilon, value, delta, error, cross, NULL);
    mpz_t address;
    mpz_init(address);
    WeightedRemainderWeights state, original, z;
    weighted_remainder_weights_init(&state);
    weighted_remainder_weights_init(&original);
    weighted_remainder_weights_init(&z);
    if (argc == 4 && !strcmp(argv[2], "variance") && weights_parse_index(argv[3], &m)) {
        unsigned bits;
        ok = weighted_remainder_collision_variance_q(delta, error, cross, value, &bits, m);
        if (ok) {
            printf("Exact bounds for the collision Haar variance\ncutoff %u\nbinary_exponent %u\n"
                   "cross_grid_denominator %u\n", m, bits, m * m);
            gmp_printf("finite_variance %Qd\npotential_error_squared_upper %Qd\n"
                       "cross_upper %Qd\nfull_variance_upper %Qd\n", delta, error, cross, value);
            mpz_set_ui(address, 1);
            for (unsigned k = 2; k <= m; ++k) mpz_lcm_ui(address, address, k);
            gmp_printf("cutoff_cylinder_modulus %Zd\ncutoff_cylinder_error_squared_upper %Qd\n",
                       address, error);
        }
    } else if (argc >= 4 && !strcmp(argv[2], "finite-weights") &&
        argc <= WEIGHTED_REMAINDER_EXACT_MAX + 3 &&
        weights_parse_address(address, argv[3])) {
        unsigned char seen[WEIGHTED_REMAINDER_EXACT_MAX + 1] = {0};
        ok = 1;
        for (int j = 4; j < argc && ok; ++j) {
            char *token = malloc(strlen(argv[j]) + 1);
            if (!token) { ok = 0; break; }
            strcpy(token, argv[j]);
            char *colon = strchr(token, ':');
            unsigned k = 0;
            if (colon) *colon++ = '\0';
            ok = colon && weights_parse_index(token, &k) && k >= 2 && !seen[k] &&
                weights_parse_rational(v[k], colon);
            if (ok) { seen[k] = 1; if (k > m) m = k; }
            free(token);
        }
        if (ok) ok = weighted_remainder_weights_compute(&state, v, m, address);
        if (ok) {
            puts("Exact finite supplied-weight system");
            weights_print_state(&state, address);
            int energy_ok = weighted_remainder_weights_energy_q(value, v, m, address);
            printf("unit_energy_available %d\n", energy_ok);
            if (energy_ok) gmp_printf("unit_energy %Qd\n", value);
            for (unsigned q = 2; q <= m; ++q) {
                weighted_remainder_weights_amplitude_q(value, v, m, q);
                if (mpq_sgn(value)) gmp_printf("amplitude %u %Qd\n", q, value);
            }
        }
    } else if (argc == 6 && !strcmp(argv[2], "perturbation") &&
               weights_parse_index(argv[3], &m) && weights_parse_address(address, argv[4]) &&
               weights_parse_rational(epsilon, argv[5])) {
        ok = weighted_remainder_perturbed_weights_q(v, m, epsilon);
        if (ok) {
            weighted_remainder_weights_compute(&state, v, m, address);
            for (unsigned k = 0; k <= m; ++k) weighted_remainder_weight_q(base[k], k);
            weighted_remainder_weights_compute(&original, base, m, address);
            for (unsigned k = 0; k <= m; ++k) mpq_set_ui(base[k], 0, 1);
            mpq_set_ui(base[2], 1, 1); mpq_set_si(base[3], -2, 1); mpq_set_ui(base[4], 1, 1);
            weighted_remainder_weights_compute(&z, base, 4, address);
            puts("Exact finite collision-mass perturbation");
            weights_print_state(&state, address);
            gmp_printf("epsilon %Qd\nweight_two %Qd\nweight_three %Qd\nweight_four %Qd\n",
                       epsilon, v[2], v[3], v[4]);
            mpq_sub(delta, state.mass, original.mass);
            gmp_printf("mass_change %Qd\n", delta);
            mpq_set_ui(value, 1, 1);
            mpq_sub(value, value, state.mass);
            gmp_printf("omitted_mass %Qd\n", value);
            mpq_sub(delta, state.stationary_age, original.stationary_age);
            gmp_printf("stationary_age_change %Qd\n", delta);
            mpq_sub(delta, state.centered_age, original.centered_age);
            gmp_printf("centered_age_change %Qd\nperturbation_value %Qd\n"
                       "perturbation_norm_sq %Qd\n", delta, z.centered_age, z.gram_variance);
            mpq_mul(value, epsilon, z.centered_age);
            mpq_sub(delta, delta, value);
            gmp_printf("change_identity_error %Qd\n", delta);
            if (mpz_sgn(address) >= 0) gmp_printf("full_deficit_change %Qd\n", value);
            if (mpz_sgn(address) >= 0 && mpz_cmp_ui(address, WEIGHTED_REMAINDER_EXACT_MAX) <= 0) {
                weighted_remainder_perturbed_deficit_q(error, cross,
                    (unsigned)mpz_get_ui(address), epsilon);
                gmp_printf("original_full_deficit %Qd\nperturbed_full_deficit %Qd\n", error, cross);
            }
        }
    }
    weighted_remainder_weights_clear(&state);
    weighted_remainder_weights_clear(&original);
    weighted_remainder_weights_clear(&z);
    mpq_clears(epsilon, value, delta, error, cross, NULL);
    mpz_clear(address);
    for (unsigned k = 0; k <= WEIGHTED_REMAINDER_EXACT_MAX; ++k) {
        mpq_clear(v[k]); mpq_clear(base[k]);
    }
    if (!ok) fputs("Use finite-weights <address> [period:weight ...] or "
                   "perturbation <cutoff> <address> <epsilon>, or variance <cutoff>. "
                   "Variance cutoff is 2..240. Supplied periods are "
                   "distinct integers 2..240; weights are signed rationals with positive "
                   "denominators and are never normalized. Address is any signed GMP "
                   "integer. Perturbation cutoff is 4..240 with 0<abs(epsilon)<1/24.\n", stderr);
    return ok ? 0 : 1;
}
