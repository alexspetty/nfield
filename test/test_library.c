#include <nfield/nfield.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned checks, failures;
#define CHECK(e) do { ++checks; if (!(e)) { ++failures; \
    if (failures < 25) fprintf(stderr, "line %d: %s\n", __LINE__, #e); } } while (0)
#define OK(e) CHECK((e) == NFIELD_OK)

static void qset(mpq_t q, long n, unsigned long d)
{ mpq_set_si(q, n, d); mpq_canonicalize(q); }

static unsigned gcd_u(unsigned a, unsigned b)
{ while (b) { unsigned t = a % b; a = b; b = t; } return a; }

static void equal_q(const mpq_t actual, const mpq_t expected)
{
    CHECK(mpq_equal(actual, expected));
    if (!mpq_equal(actual, expected) && failures < 25)
        gmp_fprintf(stderr, "  got %Qd, expected %Qd\n", actual, expected);
}

static void equal_literal(const mpq_t actual, const char *literal)
{
    mpq_t expected; mpq_init(expected);
    CHECK(mpq_set_str(expected, literal, 10) == 0);
    mpq_canonicalize(expected); equal_q(actual, expected); mpq_clear(expected);
}

/* The reference field uses rational floor arithmetic. Integer arguments have
 * the assigned midpoint value zero, including sampled reset points. */
static void psi(mpq_t out, const mpq_t x)
{
    mpz_t floor; mpz_init(floor);
    mpz_fdiv_q(floor, mpq_numref(x), mpq_denref(x));
    mpq_t q; mpq_init(q); mpq_set_z(q, floor); mpq_sub(out, x, q);
    if (mpq_sgn(out)) { qset(q, 1, 2); mpq_sub(out, out, q); }
    mpq_clear(q); mpz_clear(floor);
}

static void field(mpq_t out, const mpq_t *c, unsigned n, const mpq_t x)
{
    mpq_t t, w; mpq_inits(t, w, NULL); qset(out, 0, 1);
    for (unsigned j = 1; j <= n; ++j) {
        qset(w, j, 1); mpq_mul(t, x, w); psi(t, t);
        mpq_mul(t, t, c[j - 1]); mpq_mul_2exp(t, t, 1);
        mpq_add(out, out, t);
    }
    mpq_clears(t, w, NULL);
}

/* Exact integration of affine pieces on the common rational partition.
 * This does not use the library's gcd Gram matrix formula. */
static void continuous_pair(mpq_t out, const mpq_t *a, const mpq_t *b, unsigned n)
{
    unsigned cells = 1;
    for (unsigned j = 1; j <= n; ++j) cells = cells / gcd_u(cells, j) * j;
    mpq_t x, fa, fb, sa, sb, t, width;
    mpq_inits(x, fa, fb, sa, sb, t, width, NULL);
    qset(out, 0, 1); qset(width, 1, cells);
    for (unsigned j = 1; j <= n; ++j) {
        qset(t, 2 * j, 1); mpq_mul(x, t, a[j - 1]); mpq_add(sa, sa, x);
        mpq_mul(x, t, b[j - 1]); mpq_add(sb, sb, x);
    }
    for (unsigned k = 0; k < cells; ++k) {
        qset(x, 2 * k + 1, 2 * cells);
        field(fa, a, n, x); field(fb, b, n, x);
        mpq_mul(t, fa, fb); mpq_mul(t, t, width); mpq_add(out, out, t);
    }
    /* There are cells equal intervals: total slope correction = sa*sb/(12*cells^2). */
    mpq_mul(t, sa, sb); qset(x, 1, 12UL * cells * cells);
    mpq_mul(t, t, x); mpq_add(out, out, t);
    mpq_clears(x, fa, fb, sa, sb, t, width, NULL);
}

static void sampled_pair(mpq_t out, const mpq_t *a, const mpq_t *b,
                         unsigned n, unsigned grid)
{
    mpq_t x, fa, fb, t; mpq_inits(x, fa, fb, t, NULL); qset(out, 0, 1);
    for (unsigned k = 0; k < grid; ++k) {
        qset(x, k, grid); field(fa, a, n, x); field(fb, b, n, x);
        mpq_mul(t, fa, fb); mpq_add(out, out, t);
    }
    qset(t, 1, grid); mpq_mul(out, out, t); mpq_clears(x, fa, fb, t, NULL);
}

static void clock_pair(mpq_t clock, mpq_t primitive, mpq_t absolute,
                       const mpq_t *c, unsigned n, unsigned grid, unsigned k)
{
    mpq_t x, f, t, v; mpq_inits(x, f, t, v, NULL);
    qset(clock, 0, 1); qset(primitive, 0, 1); qset(absolute, 0, 1);
    for (unsigned a = 1; a < k; ++a) {
        qset(x, a, k); field(f, c, n, x);
        qset(t, grid, 1); mpq_mul(t, t, x); psi(t, t); mpq_mul(t, t, f);
        mpq_add(clock, clock, t);
        if (gcd_u(a, k) == 1) {
            mpq_add(primitive, primitive, t); mpq_abs(v, t); mpq_add(absolute, absolute, v);
        }
    }
    mpq_div_2exp(clock, clock, 1); mpq_clears(x, f, t, v, NULL);
}

static void check_source_result(nfield_source *source, unsigned n,
    const mpq_t *weights, const unsigned char *mask, unsigned grid,
    const mpz_t modulus)
{
    mpq_t c[3][NFIELD_SOURCE_MAX_CUTOFF], mass[3][NFIELD_SOURCE_MAX_CUTOFF];
    mpq_t total, expected, actual, t, clock, primitive, absolute, ordered, reset;
    mpq_inits(total, expected, actual, t, clock, primitive, absolute, ordered, reset, NULL);
    for (unsigned s = 0; s < 3; ++s) for (unsigned j = 0; j < n; ++j) {
        mpq_init(c[s][j]); mpq_init(mass[s][j]);
    }
    for (unsigned j = 0; j < n; ++j) {
        mpz_set(mpq_numref(c[0][j]), mpq_numref(weights[j]));
        mpz_set(mpq_denref(c[0][j]), mpq_denref(weights[j]));
        mpq_canonicalize(c[0][j]);
    }
    for (unsigned k = 1; k <= n; ++k) {
        for (unsigned j = 1; j <= n; ++j) if (j % k == 0)
            mpq_add(mass[0][k - 1], mass[0][k - 1], c[0][j - 1]);
        if (mask[k - 1]) mpq_set(mass[1][k - 1], mass[0][k - 1]);
        mpq_sub(mass[2][k - 1], mass[0][k - 1], mass[1][k - 1]);
    }
    /* Descending triangular inversion, independently of Mobius evaluation. */
    for (unsigned k = n; k > 0; --k) {
        mpq_set(c[1][k - 1], mass[1][k - 1]);
        for (unsigned j = k + 1; j <= n; ++j) if (j % k == 0)
            mpq_sub(c[1][k - 1], c[1][k - 1], c[1][j - 1]);
        mpq_sub(c[2][k - 1], c[0][k - 1], c[1][k - 1]);
    }
    nfield_source_info info = {999, 999, -1, -1};
    OK(nfield_source_get_info(source, &info));
    CHECK(info.cutoff == n && info.grid == grid && info.has_work == (grid != 0));
    CHECK(info.has_modulus == (modulus != NULL));
    mpz_t z, g; mpz_inits(z, g, NULL); mpz_set_ui(z, 777);
    if (modulus) { OK(nfield_source_modulus(source, z)); CHECK(mpz_cmp(z, modulus) == 0); }
    else { CHECK(nfield_source_modulus(source, z) == NFIELD_ENODATA); CHECK(mpz_cmp_ui(z, 777) == 0); }
    for (unsigned k = 1; k <= n; ++k) {
        unsigned value = 999;
        OK(nfield_source_mask(source, k, &value)); CHECK(value == mask[k - 1]);
        value = 999;
        if (modulus) {
            OK(nfield_source_destination(source, k, &value));
            CHECK(value == mpz_gcd_ui(g, modulus, k));
        } else {
            CHECK(nfield_source_destination(source, k, &value) == NFIELD_ENODATA);
            CHECK(value == 999);
        }
    }
    for (unsigned s = 0; s < 3; ++s) {
        qset(total, 0, 1); qset(ordered, 0, 1); qset(reset, 0, 1);
        for (unsigned k = 1; k <= n; ++k) {
            OK(nfield_source_coefficient(source, (nfield_component)s, k, actual));
            equal_q(actual, c[s][k - 1]);
            OK(nfield_source_mass(source, (nfield_component)s, k, actual));
            equal_q(actual, mass[s][k - 1]); mpq_add(total, total, c[s][k - 1]);
            if (grid) {
                clock_pair(clock, primitive, absolute, c[0], n, grid, k);
                OK(nfield_source_clock_work(source, k, actual)); equal_q(actual, clock);
                OK(nfield_source_primitive_work(source, k, actual)); equal_q(actual, primitive);
                qset(t, 2, 1); mpq_mul(t, t, c[s][k - 1]);
                mpq_mul(t, t, clock); mpq_add(ordered, ordered, t);
                mpq_mul(t, mass[s][k - 1], primitive); mpq_add(reset, reset, t);
            }
        }
        OK(nfield_source_total(source, (nfield_component)s, actual)); equal_q(actual, total);
        for (unsigned form = 0; form < 2; ++form) {
            qset(actual, 99, 7);
            if (!grid) {
                CHECK(nfield_source_energy(source, (nfield_form)form,
                    (nfield_component)s, actual) == NFIELD_ENODATA);
                equal_literal(actual, "99/7");
            } else {
                if (form) sampled_pair(expected, c[s], c[s], n, grid);
                else continuous_pair(expected, c[s], c[s], n);
                OK(nfield_source_energy(source, (nfield_form)form, (nfield_component)s, actual));
                equal_q(actual, expected);
            }
        }
        qset(actual, 99, 7);
        if (grid) { OK(nfield_source_ordered_work(source, (nfield_component)s, actual)); equal_q(actual, ordered); }
        else { CHECK(nfield_source_ordered_work(source, (nfield_component)s, actual) == NFIELD_ENODATA); equal_literal(actual, "99/7"); }
        qset(actual, 99, 7);
        if (grid) { OK(nfield_source_reset_work(source, (nfield_component)s, actual)); equal_q(actual, reset); }
        else { CHECK(nfield_source_reset_work(source, (nfield_component)s, actual) == NFIELD_ENODATA); equal_literal(actual, "99/7"); }
    }
    for (unsigned form = 0; form < 2; ++form) {
        qset(actual, 99, 7);
        if (grid) {
            if (form) sampled_pair(expected, c[1], c[2], n, grid);
            else continuous_pair(expected, c[1], c[2], n);
            mpq_mul_2exp(expected, expected, 1);
            OK(nfield_source_mixed(source, (nfield_form)form, actual)); equal_q(actual, expected);
        } else { CHECK(nfield_source_mixed(source, (nfield_form)form, actual) == NFIELD_ENODATA); equal_literal(actual, "99/7"); }
    }
    if (!grid && n) {
        qset(actual, 99, 7); CHECK(nfield_source_clock_work(source, 1, actual) == NFIELD_ENODATA); equal_literal(actual, "99/7");
        CHECK(nfield_source_primitive_work(source, 1, actual) == NFIELD_ENODATA); equal_literal(actual, "99/7");
    }
    for (unsigned s = 0; s < 3; ++s) for (unsigned j = 0; j < n; ++j) {
        mpq_clear(c[s][j]); mpq_clear(mass[s][j]);
    }
    mpz_clears(z, g, NULL);
    mpq_clears(total, expected, actual, t, clock, primitive, absolute, ordered, reset, NULL);
}

static void source_panels(void)
{
    nfield_source *source = NULL; OK(nfield_source_create(&source));
    mpq_t weights[NFIELD_SOURCE_MAX_CUTOFF]; unsigned char mask[NFIELD_SOURCE_MAX_CUTOFF];
    for (unsigned j = 0; j < NFIELD_SOURCE_MAX_CUTOFF; ++j) mpq_init(weights[j]);
    const unsigned grids[] = {0, 1, 2, 5, 12};
    for (unsigned n = 0; n <= 4; ++n) for (unsigned pattern = 0; pattern < 4; ++pattern) {
        for (unsigned j = 0; j < n; ++j) {
            long numerator = pattern == 0 ? 0 : pattern == 1 ? 1 :
                pattern == 2 ? ((j & 1) ? -(long)(j + 2) : (long)(j + 2)) : (j == 0 ? -3 : 5);
            qset(weights[j], numerator, pattern < 2 ? 1 : j + 2);
        }
        for (unsigned bits = 0; bits < (1u << n); ++bits) {
            for (unsigned j = 0; j < n; ++j) mask[j] = (bits >> j) & 1u;
            for (unsigned gi = 0; gi < sizeof(grids) / sizeof(grids[0]); ++gi) {
                OK(nfield_source_project(source, n, n ? weights : NULL, n ? mask : NULL, grids[gi]));
                check_source_result(source, n, weights, mask, grids[gi], NULL);
            }
        }
    }
    mpz_t modulus, divisor; mpz_inits(modulus, divisor, NULL);
    for (unsigned j = 0; j < 4; ++j) qset(weights[j], (j & 1) ? -5 : 3, j + 2);
    const unsigned moduli[] = {0, 1, 2, 3, 6, 12};
    for (unsigned i = 0; i < sizeof(moduli) / sizeof(moduli[0]); ++i) {
        mpz_set_ui(modulus, moduli[i]);
        for (unsigned k = 1; k <= 4; ++k) mask[k - 1] = mpz_divisible_ui_p(modulus, k);
        OK(nfield_source_collapse(source, 4, weights, modulus, 5));
        check_source_result(source, 4, weights, mask, 5, modulus);
    }
    mpz_set_ui(divisor, 3); mpz_ui_pow_ui(modulus, 4, 4); mpz_mul(modulus, modulus, divisor);
    for (unsigned k = 1; k <= 4; ++k) mask[k - 1] = mpz_divisible_ui_p(modulus, k);
    OK(nfield_source_divisor(source, 4, weights, divisor, 7));
    check_source_result(source, 4, weights, mask, 7, modulus);
    OK(nfield_source_divisor(source, 0, NULL, divisor, 0));
    check_source_result(source, 0, weights, mask, 0, divisor);

    /* Large rational inputs remain exact, and borrowed noncanonical values
     * retain their numerator and denominator after normalization of copies. */
    mpz_ui_pow_ui(mpq_numref(weights[0]), 2, 521); mpz_add_ui(mpq_numref(weights[0]), mpq_numref(weights[0]), 17);
    mpz_ui_pow_ui(mpq_denref(weights[0]), 2, 257); mpz_add_ui(mpq_denref(weights[0]), mpq_denref(weights[0]), 25);
    mpz_mul_ui(mpq_numref(weights[0]), mpq_numref(weights[0]), 6);
    mpz_mul_si(mpq_denref(weights[0]), mpq_denref(weights[0]), -6);
    mpz_set_si(mpq_numref(weights[1]), -18); mpz_set_si(mpq_denref(weights[1]), -42);
    mpz_t before[4]; for (unsigned j = 0; j < 4; ++j) mpz_init(before[j]);
    for (unsigned j = 0; j < 2; ++j) { mpz_set(before[2*j], mpq_numref(weights[j])); mpz_set(before[2*j+1], mpq_denref(weights[j])); }
    mask[0] = 0; mask[1] = 1;
    OK(nfield_source_project(source, 2, weights, mask, 5));
    check_source_result(source, 2, weights, mask, 5, NULL);
    for (unsigned j = 0; j < 2; ++j) { CHECK(mpz_cmp(before[2*j], mpq_numref(weights[j])) == 0); CHECK(mpz_cmp(before[2*j+1], mpq_denref(weights[j])) == 0); }
    mpz_ui_pow_ui(modulus, 2, 1024); mpz_add_ui(modulus, modulus, 1);
    mask[0] = 1; mask[1] = 0;
    OK(nfield_source_collapse(source, 2, weights, modulus, 3));
    check_source_result(source, 2, weights, mask, 3, modulus);
    for (unsigned j = 0; j < 2; ++j) { CHECK(mpz_cmp(before[2*j], mpq_numref(weights[j])) == 0); CHECK(mpz_cmp(before[2*j+1], mpq_denref(weights[j])) == 0); }
    for (unsigned j = 0; j < 4; ++j) mpz_clear(before[j]);
    for (unsigned j = 0; j < NFIELD_SOURCE_MAX_CUTOFF; ++j) { qset(weights[j], 1, 1); mask[j] = 1; }
    OK(nfield_source_project(source, NFIELD_SOURCE_MAX_CUTOFF, weights, mask, 0));
    /* Coordinate-only upper cutoff has no large common-partition integral. */
    check_source_result(source, NFIELD_SOURCE_MAX_CUTOFF, weights, mask, 0, NULL);
    OK(nfield_source_project(source, 0, NULL, NULL, NFIELD_SOURCE_MAX_GRID));
    check_source_result(source, 0, weights, mask, NFIELD_SOURCE_MAX_GRID, NULL);
    mpz_clears(modulus, divisor, NULL);
    for (unsigned j = 0; j < NFIELD_SOURCE_MAX_CUTOFF; ++j) mpq_clear(weights[j]);
    nfield_source_destroy(source);
}

/* Every rational getter must reject bad handles/output pointers and preserve
 * initialized caller outputs on recoverable failures. */
static void source_errors(void)
{
    nfield_source *source = NULL; OK(nfield_source_create(&source));
    nfield_source *saved = source;
    CHECK(nfield_source_create(NULL) == NFIELD_EINVAL);
    CHECK(nfield_source_create(&source) == NFIELD_EINVAL); CHECK(source == saved);
    nfield_source_destroy(NULL);
    mpq_t out, weight; mpq_inits(out, weight, NULL); qset(out, 99, 7); qset(weight, 3, 2);
    mpz_t z; mpz_init_set_ui(z, 777);
    unsigned u = 777; unsigned char mask = 1;
    nfield_source_info info = {777, 777, 777, 777};
#define QERROR(call, code) do { qset(out, 99, 7); CHECK((call) == (code)); equal_literal(out, "99/7"); } while (0)
    QERROR(nfield_source_coefficient(source, NFIELD_ORIGINAL, 1, out), NFIELD_ESTATE);
    QERROR(nfield_source_mass(source, NFIELD_ORIGINAL, 1, out), NFIELD_ESTATE);
    QERROR(nfield_source_total(source, NFIELD_ORIGINAL, out), NFIELD_ESTATE);
    QERROR(nfield_source_energy(source, NFIELD_CONTINUOUS, NFIELD_ORIGINAL, out), NFIELD_ESTATE);
    QERROR(nfield_source_mixed(source, NFIELD_CONTINUOUS, out), NFIELD_ESTATE);
    QERROR(nfield_source_ordered_work(source, NFIELD_ORIGINAL, out), NFIELD_ESTATE);
    QERROR(nfield_source_reset_work(source, NFIELD_ORIGINAL, out), NFIELD_ESTATE);
    QERROR(nfield_source_clock_work(source, 1, out), NFIELD_ESTATE);
    QERROR(nfield_source_primitive_work(source, 1, out), NFIELD_ESTATE);
    CHECK(nfield_source_get_info(source, &info) == NFIELD_ESTATE); CHECK(info.cutoff == 777 && info.grid == 777 && info.has_work == 777 && info.has_modulus == 777);
    CHECK(nfield_source_mask(source, 1, &u) == NFIELD_ESTATE); CHECK(u == 777);
    CHECK(nfield_source_destination(source, 1, &u) == NFIELD_ESTATE); CHECK(u == 777);
    CHECK(nfield_source_modulus(source, z) == NFIELD_ESTATE); CHECK(mpz_cmp_ui(z, 777) == 0);
    OK(nfield_source_project(source, 1, &weight, &mask, 5));
    CHECK(nfield_source_project(NULL, 1, &weight, &mask, 5) == NFIELD_EINVAL);
    CHECK(nfield_source_project(source, 65, NULL, NULL, 0) == NFIELD_ERANGE);
    CHECK(nfield_source_project(source, 1, &weight, &mask, 65537) == NFIELD_ERANGE);
    CHECK(nfield_source_project(source, UINT_MAX, NULL, NULL, 0) == NFIELD_ERANGE);
    CHECK(nfield_source_project(source, 1, NULL, &mask, 5) == NFIELD_EINVAL);
    CHECK(nfield_source_project(source, 1, &weight, NULL, 5) == NFIELD_EINVAL);
    mask = 2; CHECK(nfield_source_project(source, 1, &weight, &mask, 5) == NFIELD_EINVAL); mask = 1;
    mpz_set_ui(mpq_denref(weight), 0);
    CHECK(nfield_source_project(source, 1, &weight, &mask, 5) == NFIELD_EINVAL);
    CHECK(nfield_source_collapse(source, 1, &weight, z, 5) == NFIELD_EINVAL);
    CHECK(nfield_source_divisor(source, 1, &weight, z, 5) == NFIELD_EINVAL);
    qset(weight, 3, 2);
    CHECK(nfield_source_collapse(source, 1, &weight, NULL, 5) == NFIELD_EINVAL);
    CHECK(nfield_source_divisor(source, 1, &weight, NULL, 5) == NFIELD_EINVAL);
    mpz_set_si(z, -1); CHECK(nfield_source_collapse(source, 1, &weight, z, 5) == NFIELD_EINVAL);
    CHECK(nfield_source_divisor(source, 1, &weight, z, 5) == NFIELD_EINVAL);
    mpz_set_ui(z, 0); CHECK(nfield_source_divisor(source, 1, &weight, z, 5) == NFIELD_EINVAL);
    check_source_result(source, 1, &weight, &mask, 5, NULL);
    for (unsigned which = 0; which < 2; ++which) {
        nfield_component bad = (nfield_component)(which ? -1 : 3);
        QERROR(nfield_source_coefficient(source, bad, 1, out), NFIELD_EINVAL);
        QERROR(nfield_source_mass(source, bad, 1, out), NFIELD_EINVAL);
        QERROR(nfield_source_total(source, bad, out), NFIELD_EINVAL);
        QERROR(nfield_source_energy(source, NFIELD_CONTINUOUS, bad, out), NFIELD_EINVAL);
        QERROR(nfield_source_ordered_work(source, bad, out), NFIELD_EINVAL);
        QERROR(nfield_source_reset_work(source, bad, out), NFIELD_EINVAL);
        nfield_form form = (nfield_form)(which ? -1 : 2);
        QERROR(nfield_source_energy(source, form, NFIELD_ORIGINAL, out), NFIELD_EINVAL);
        QERROR(nfield_source_mixed(source, form, out), NFIELD_EINVAL);
    }
    const unsigned bad_indices[] = {0, 2, UINT_MAX};
    for (unsigned i = 0; i < 3; ++i) {
        unsigned k = bad_indices[i];
        QERROR(nfield_source_coefficient(source, NFIELD_ORIGINAL, k, out), NFIELD_ERANGE);
        QERROR(nfield_source_mass(source, NFIELD_ORIGINAL, k, out), NFIELD_ERANGE);
        QERROR(nfield_source_clock_work(source, k, out), NFIELD_ERANGE);
        QERROR(nfield_source_primitive_work(source, k, out), NFIELD_ERANGE);
        u = 777; CHECK(nfield_source_mask(source, k, &u) == NFIELD_ERANGE); CHECK(u == 777);
        CHECK(nfield_source_destination(source, k, &u) == NFIELD_ERANGE); CHECK(u == 777);
    }
#define SOURCE_NULL(call) CHECK((call) == NFIELD_EINVAL)
    SOURCE_NULL(nfield_source_get_info(NULL, &info)); SOURCE_NULL(nfield_source_get_info(source, NULL));
    SOURCE_NULL(nfield_source_coefficient(NULL, NFIELD_ORIGINAL, 1, out)); SOURCE_NULL(nfield_source_coefficient(source, NFIELD_ORIGINAL, 1, NULL));
    SOURCE_NULL(nfield_source_mass(NULL, NFIELD_ORIGINAL, 1, out)); SOURCE_NULL(nfield_source_mass(source, NFIELD_ORIGINAL, 1, NULL));
    SOURCE_NULL(nfield_source_total(NULL, NFIELD_ORIGINAL, out)); SOURCE_NULL(nfield_source_total(source, NFIELD_ORIGINAL, NULL));
    SOURCE_NULL(nfield_source_energy(NULL, NFIELD_CONTINUOUS, NFIELD_ORIGINAL, out)); SOURCE_NULL(nfield_source_energy(source, NFIELD_CONTINUOUS, NFIELD_ORIGINAL, NULL));
    SOURCE_NULL(nfield_source_mixed(NULL, NFIELD_CONTINUOUS, out)); SOURCE_NULL(nfield_source_mixed(source, NFIELD_CONTINUOUS, NULL));
    SOURCE_NULL(nfield_source_ordered_work(NULL, NFIELD_ORIGINAL, out)); SOURCE_NULL(nfield_source_ordered_work(source, NFIELD_ORIGINAL, NULL));
    SOURCE_NULL(nfield_source_reset_work(NULL, NFIELD_ORIGINAL, out)); SOURCE_NULL(nfield_source_reset_work(source, NFIELD_ORIGINAL, NULL));
    SOURCE_NULL(nfield_source_clock_work(NULL, 1, out)); SOURCE_NULL(nfield_source_clock_work(source, 1, NULL));
    SOURCE_NULL(nfield_source_primitive_work(NULL, 1, out)); SOURCE_NULL(nfield_source_primitive_work(source, 1, NULL));
    SOURCE_NULL(nfield_source_mask(NULL, 1, &u)); SOURCE_NULL(nfield_source_mask(source, 1, NULL));
    SOURCE_NULL(nfield_source_destination(NULL, 1, &u)); SOURCE_NULL(nfield_source_destination(source, 1, NULL));
    SOURCE_NULL(nfield_source_modulus(NULL, z)); SOURCE_NULL(nfield_source_modulus(source, NULL));
    /* Getter storage is caller-owned; later calls cannot change this copy. */
    OK(nfield_source_coefficient(source, NFIELD_ORIGINAL, 1, out));
    OK(nfield_source_total(source, NFIELD_COMPLEMENT, weight));
    equal_literal(weight, "0");
    OK(nfield_source_coefficient(source, NFIELD_ORIGINAL, 1, weight));
    equal_literal(weight, "3/2");
    qset(weight, -11, 7); mask = 0; OK(nfield_source_project(source, 1, &weight, &mask, 0));
    equal_literal(out, "3/2"); check_source_result(source, 1, &weight, &mask, 0, NULL);
    OK(nfield_source_project(source, 0, NULL, NULL, 0));
    QERROR(nfield_source_coefficient(source, NFIELD_ORIGINAL, 1, out), NFIELD_ERANGE);
    check_source_result(source, 0, NULL, NULL, 0, NULL);
    nfield_source_destroy(source); mpq_clears(out, weight, NULL); mpz_clear(z);
}

static void check_forest(nfield_forest *forest, unsigned p, const mpz_t divisor)
{
    const unsigned n = p - 1, grid = p * p;
    nfield_forest_info info; OK(nfield_forest_get_info(forest, &info));
    CHECK(info.prime == p && info.cutoff == n && info.grid == grid);
    mpq_t c[10], expected[12], actual, clock, primitive, absolute, t, h;
    for (unsigned j = 0; j < n; ++j) { mpq_init(c[j]); qset(c[j], 1, 1); }
    for (unsigned j = 0; j < 12; ++j) mpq_init(expected[j]);
    mpq_inits(actual, clock, primitive, absolute, t, h, NULL);
    mpz_t modulus, z; mpz_inits(modulus, z, NULL);
    mpz_ui_pow_ui(modulus, n, n); mpz_mul(modulus, modulus, divisor);
    OK(nfield_forest_divisor(forest, z)); CHECK(mpz_cmp(z, divisor) == 0);
    unsigned population[11] = {0}, destinations[11], selected = 0;
    for (unsigned k = 1; k <= n; ++k) { destinations[k] = mpz_gcd_ui(z, modulus, k); ++population[destinations[k]]; }
    for (unsigned k = 1; k <= n; ++k) {
        unsigned rough = k;
        for (unsigned d = 2; d <= n; ++d) if (n % d == 0)
            while (rough % d == 0) rough /= d;
        unsigned keep = mpz_divisible_ui_p(divisor, rough);
        if (k >= 2 && keep) ++selected;
        nfield_forest_clock_info ci;
        OK(nfield_forest_get_clock_info(forest, k, &ci));
        CHECK(ci.rough == rough && ci.selected == keep && ci.destination == destinations[k] && ci.population == population[k]);
        clock_pair(clock, primitive, absolute, c, n, grid, k);
        qset(t, n / k, 1); mpq_mul(primitive, primitive, t); mpq_mul(absolute, absolute, t);
        OK(nfield_forest_clock_work(forest, NFIELD_CLOCK_SIGNED_WORK, k, actual)); equal_q(actual, primitive);
        OK(nfield_forest_clock_work(forest, NFIELD_CLOCK_ABSOLUTE_WORK, k, actual)); equal_q(actual, absolute);
        OK(nfield_forest_clock_work(forest, NFIELD_CLOCK_ORDERED_WORK, k, actual)); equal_q(actual, clock);
        if (k >= 2) {
            mpq_add(expected[keep ? 5 : 6], expected[keep ? 5 : 6], primitive);
            if (keep) {
                mpq_add(expected[7], expected[7], absolute);
                qset(t, 2 * (1L - (long)population[k]), 1); mpq_mul(t, t, clock); mpq_add(expected[8], expected[8], t);
                qset(h, 0, 1);
                for (unsigned j = 1; j <= k / 2; ++j) { qset(t, 1, j); mpq_add(h, h, t); }
                mpq_mul(h, h, h); qset(t, n, 2); mpq_mul(h, h, t); mpq_add(expected[11], expected[11], h);
            } else { mpq_mul_2exp(t, clock, 1); mpq_add(expected[9], expected[9], t); }
        }
    }
    CHECK(info.selected_count == selected);
    continuous_pair(expected[0], c, c, n); sampled_pair(expected[1], c, c, n, grid);
    mpq_sub(expected[2], expected[0], expected[1]); qset(expected[3], n * n, grid);
    mpq_sub(expected[4], expected[2], expected[3]); qset(h, 0, 1);
    for (unsigned k = 1; k <= n; ++k) { qset(t, 1, k); mpq_add(h, h, t); }
    qset(t, -(long)n, 3UL * p * p * p); mpq_mul(expected[10], h, t);
    for (unsigned j = 0; j < 12; ++j) { OK(nfield_forest_value(forest, (nfield_forest_quantity)j, actual)); equal_q(actual, expected[j]); }
    for (unsigned j = 0; j < n; ++j) mpq_clear(c[j]);
    for (unsigned j = 0; j < 12; ++j) mpq_clear(expected[j]);
    mpq_clears(actual, clock, primitive, absolute, t, h, NULL); mpz_clears(modulus, z, NULL);
}

static void forest_cases(void)
{
    nfield_forest *forest = NULL; OK(nfield_forest_create(&forest));
    nfield_forest *saved = forest;
    CHECK(nfield_forest_create(NULL) == NFIELD_EINVAL);
    CHECK(nfield_forest_create(&forest) == NFIELD_EINVAL); CHECK(forest == saved);
    nfield_forest_destroy(NULL);
    mpq_t out; mpq_init(out); mpz_t divisor, z; mpz_inits(divisor, z, NULL);
    mpz_set_ui(divisor, 1); mpz_set_ui(z, 777);
    nfield_forest_info info = {777, 777, 777, 777};
    nfield_forest_clock_info ci = {777, 777, 777, 777};
    CHECK(nfield_forest_get_info(forest, &info) == NFIELD_ESTATE); CHECK(info.prime == 777 && info.cutoff == 777 && info.grid == 777 && info.selected_count == 777);
    CHECK(nfield_forest_get_clock_info(forest, 1, &ci) == NFIELD_ESTATE); CHECK(ci.rough == 777 && ci.selected == 777 && ci.destination == 777 && ci.population == 777);
    QERROR(nfield_forest_value(forest, NFIELD_FOREST_DEFECT, out), NFIELD_ESTATE);
    QERROR(nfield_forest_clock_work(forest, NFIELD_CLOCK_SIGNED_WORK, 1, out), NFIELD_ESTATE);
    CHECK(nfield_forest_divisor(forest, z) == NFIELD_ESTATE); CHECK(mpz_cmp_ui(z, 777) == 0);
    const unsigned primes[] = {3, 5, 7, 11};
    for (unsigned i = 0; i < 4; ++i) for (unsigned d = 0; d < 3; ++d) {
        mpz_set_ui(divisor, d == 0 ? 1 : 3);
        if (d == 2) { mpz_ui_pow_ui(divisor, 2, 1024); mpz_add_ui(divisor, divisor, 17); }
        OK(nfield_forest_compute(forest, primes[i], divisor)); check_forest(forest, primes[i], divisor);
    }
    mpz_set_ui(divisor, 1); OK(nfield_forest_compute(forest, 5, divisor));
    const char *p5[] = {"23/9", "48/25", "143/225", "16/25", "-1/225"};
    for (unsigned j = 0; j < 5; ++j) { OK(nfield_forest_value(forest, (nfield_forest_quantity)j, out)); equal_literal(out, p5[j]); }
    CHECK(nfield_forest_compute(NULL, 5, divisor) == NFIELD_EINVAL);
    CHECK(nfield_forest_compute(forest, 5, NULL) == NFIELD_EINVAL);
    mpz_set_ui(divisor, 0); CHECK(nfield_forest_compute(forest, 5, divisor) == NFIELD_EINVAL);
    mpz_set_si(divisor, -1); CHECK(nfield_forest_compute(forest, 5, divisor) == NFIELD_EINVAL); mpz_set_ui(divisor, 1);
    const unsigned bad_primes[] = {0, 1, 2, 252, UINT_MAX, 4, 9, 15, 25};
    for (unsigned j = 0; j < sizeof(bad_primes) / sizeof(bad_primes[0]); ++j) {
        nfield_status status = j < 5 ? NFIELD_ERANGE : NFIELD_EINVAL;
        CHECK(nfield_forest_compute(forest, bad_primes[j], divisor) == status);
        mpz_set_ui(z, 777); CHECK(nfield_forest_return_divisor(z, bad_primes[j], 3) == status); CHECK(mpz_cmp_ui(z, 777) == 0);
    }
    check_forest(forest, 5, divisor);
    const unsigned bad_windows[] = {0, 1, 2, 32, UINT_MAX};
    for (unsigned j = 0; j < 5; ++j) { mpz_set_ui(z, 777); CHECK(nfield_forest_return_divisor(z, 5, bad_windows[j]) == NFIELD_ERANGE); CHECK(mpz_cmp_ui(z, 777) == 0); }
    CHECK(nfield_forest_return_divisor(NULL, 5, 3) == NFIELD_EINVAL);
    OK(nfield_forest_return_divisor(z, 5, 3));
    /* 15*101*11*(25-4)*(25^3-4^3). */
    CHECK(mpz_cmp_ui(z, 5445805365UL) == 0);
    OK(nfield_forest_return_divisor(z, 251, 31)); CHECK(mpz_sizeinbase(z, 2) > 3000);
    const unsigned bad_indices[] = {0, 5, UINT_MAX};
    for (unsigned j = 0; j < 3; ++j) {
        QERROR(nfield_forest_clock_work(forest, NFIELD_CLOCK_SIGNED_WORK, bad_indices[j], out), NFIELD_ERANGE);
        ci = (nfield_forest_clock_info){777, 777, 777, 777};
        CHECK(nfield_forest_get_clock_info(forest, bad_indices[j], &ci) == NFIELD_ERANGE); CHECK(ci.rough == 777 && ci.selected == 777 && ci.destination == 777 && ci.population == 777);
    }
    QERROR(nfield_forest_value(forest, (nfield_forest_quantity)-1, out), NFIELD_EINVAL);
    QERROR(nfield_forest_value(forest, (nfield_forest_quantity)12, out), NFIELD_EINVAL);
    QERROR(nfield_forest_clock_work(forest, (nfield_clock_quantity)-1, 1, out), NFIELD_EINVAL);
    QERROR(nfield_forest_clock_work(forest, (nfield_clock_quantity)3, 1, out), NFIELD_EINVAL);
    SOURCE_NULL(nfield_forest_get_info(NULL, &info)); SOURCE_NULL(nfield_forest_get_info(forest, NULL));
    SOURCE_NULL(nfield_forest_get_clock_info(NULL, 1, &ci)); SOURCE_NULL(nfield_forest_get_clock_info(forest, 1, NULL));
    SOURCE_NULL(nfield_forest_divisor(NULL, z)); SOURCE_NULL(nfield_forest_divisor(forest, NULL));
    SOURCE_NULL(nfield_forest_value(NULL, NFIELD_FOREST_DEFECT, out)); SOURCE_NULL(nfield_forest_value(forest, NFIELD_FOREST_DEFECT, NULL));
    SOURCE_NULL(nfield_forest_clock_work(NULL, NFIELD_CLOCK_SIGNED_WORK, 1, out)); SOURCE_NULL(nfield_forest_clock_work(forest, NFIELD_CLOCK_SIGNED_WORK, 1, NULL));
    OK(nfield_forest_value(forest, NFIELD_FOREST_CONTINUOUS_ENERGY, out));
    OK(nfield_forest_compute(forest, NFIELD_FOREST_MAX_PRIME, divisor));
    equal_literal(out, "23/9");
    OK(nfield_forest_get_info(forest, &info)); CHECK(info.prime == 251 && info.cutoff == 250 && info.grid == 63001);
    OK(nfield_forest_get_clock_info(forest, 250, &ci)); CHECK(ci.rough == 1 && ci.destination == 250);
    OK(nfield_forest_compute(forest, 3, divisor)); check_forest(forest, 3, divisor);
    QERROR(nfield_forest_clock_work(forest, NFIELD_CLOCK_SIGNED_WORK, 250, out), NFIELD_ERANGE);
    CHECK(nfield_forest_get_clock_info(forest, 250, &ci) == NFIELD_ERANGE);
    nfield_forest_destroy(forest); mpq_clear(out); mpz_clears(divisor, z, NULL);
}

int main(void)
{
    CHECK(strcmp(nfield_version(), NFIELD_VERSION) == 0);
    CHECK(nfield_api_version() == NFIELD_API_VERSION);
    for (int i = 0; i <= 5; ++i) CHECK(nfield_status_string((nfield_status)i)[0] != '\0');
    CHECK(strcmp(nfield_status_string((nfield_status)-1), "unknown status") == 0);
    CHECK(strcmp(nfield_status_string((nfield_status)INT_MAX), "unknown status") == 0);
    source_errors(); source_panels(); forest_cases();
    printf("library: %u checks, %u failures\n", checks, failures);
    return failures ? EXIT_FAILURE : EXIT_SUCCESS;
}
