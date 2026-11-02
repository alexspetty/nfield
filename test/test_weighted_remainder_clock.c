#include "../src/weighted_remainder_clock.h"
#include "../src/weighted_remainder_state.h"
#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>

static unsigned edges;
#define CHECK(c) do { assert(c); ++edges; } while (0)

static void clock_record(unsigned m, const char *text)
{
    mpz_t a;
    mpz_init(a);
    assert(mpz_set_str(a, text, 10) == 0);
    WeightedRemainderClock c;
    weighted_remainder_clock_init(&c);
    assert(weighted_remainder_clock_compute(&c, m, a));
    gmp_printf("clock %u %Zd %Qd %Qd %Qd %Qd %Qd %Qd\n", m, a,
               c.retained_mass, c.omitted_mass, c.raw_age,
               c.stationary_age, c.centered_age, c.increment);
    if (mpz_sgn(a) >= 0 && mpz_cmp_ui(a, 1000000000) <= 0) {
        WeightedRemainderState old;
        assert(weighted_remainder_state_compute((int)mpz_get_ui(a), (int)m, &old));
        gmp_printf("floating %u %Zd ", m, a);
        printf("%.21Lg %.21Lg %.21Lg %.21Lg\n", old.mass,
               old.stationary_age, old.centered_age, old.finite_increment);
    }
    weighted_remainder_clock_clear(&c);
    mpz_clear(a);
}

static void cycle_record(unsigned k, unsigned r, const char *address, const char *last)
{
    mpz_t a, n;
    mpz_inits(a, n, NULL);
    assert(mpz_set_str(a, address, 10) == 0 && mpz_set_str(n, last, 10) == 0);
    mpq_t orbit, stationary, average;
    mpq_inits(orbit, stationary, average, NULL);
    assert(weighted_remainder_cycle_q(orbit, stationary, average, k, r, a, n));
    gmp_printf("cycle %u %u %Zd %Zd %Qd %Qd %Qd\n", k, r, a, n, orbit, stationary, average);
    mpq_clears(orbit, stationary, average, NULL);
    mpz_clears(a, n, NULL);
}

static void tv_record(unsigned m, const char *last)
{
    mpz_t n;
    mpz_init(n);
    assert(mpz_set_str(n, last, 10) == 0);
    mpq_t lower, upper, tail;
    mpq_inits(lower, upper, tail, NULL);
    assert(weighted_remainder_cycle_tv_q(lower, upper, tail, m, n));
    gmp_printf("tv %u %Zd %Qd %Qd %Qd\n", m, n, lower, upper, tail);
    mpq_clears(lower, upper, tail, NULL);
    mpz_clear(n);
}

static int law_record(const mpq_t value, unsigned multiplicity, void *context)
{
    unsigned m = *(unsigned *)context;
    gmp_printf("atom %u %Qd %u\n", m, value, multiplicity);
    return 1;
}

static int abort_law(const mpq_t value, unsigned multiplicity, void *context)
{
    (void)value; (void)multiplicity;
    unsigned *calls = context;
    ++*calls;
    return *calls < 3;
}

static void covariance_record(unsigned k, unsigned l)
{
    mpq_t out;
    mpq_init(out);
    assert(weighted_remainder_clock_covariance_q(out, k, l));
    gmp_printf("covariance %u %u %Qd ", k, l, out);
    printf("%.21Lg\n", weighted_remainder_covariance((int)k, (int)l));
    mpq_clear(out);
}

int main(void)
{
    mpz_t address, last;
    mpz_inits(address, last, NULL);
    mpz_set_si(address, -13);
    mpq_t a, b, c;
    mpq_inits(a, b, c, NULL);
    mpq_set_ui(a, 13, 17); mpq_set_ui(b, 19, 23); mpq_set_ui(c, 29, 31);
    WeightedRemainderClock clock;
    weighted_remainder_clock_init(&clock);
    clock.cutoff = 7;
    mpq_set_ui(clock.centered_age, 13, 17);
    const unsigned bad[] = {0, 1, 241, UINT_MAX};
    for (unsigned i = 0; i < sizeof bad / sizeof *bad; ++i) {
        CHECK(!weighted_remainder_clock_compute(&clock, bad[i], address));
        CHECK(clock.cutoff == 7 && mpq_cmp_ui(clock.centered_age, 13, 17) == 0);
        CHECK(!weighted_remainder_cycle_q(a, b, c, bad[i], 0, address, last));
        CHECK(mpq_cmp_ui(a, 13, 17) == 0 && mpq_cmp_ui(b, 19, 23) == 0 && mpq_cmp_ui(c, 29, 31) == 0);
        CHECK(!weighted_remainder_cycle_tv_q(a, b, c, bad[i], last));
        CHECK(mpq_cmp_ui(a, 13, 17) == 0 && mpq_cmp_ui(b, 19, 23) == 0 && mpq_cmp_ui(c, 29, 31) == 0);
    }
    CHECK(!weighted_remainder_clock_compute(NULL, 2, address));
    CHECK(!weighted_remainder_age_budget_q(a, b, 241));
    CHECK(!weighted_remainder_age_budget_q(a, b, UINT_MAX));
    CHECK(!weighted_remainder_age_budget_q(a, a, 2));
    CHECK(mpq_cmp_ui(a, 13, 17) == 0 && mpq_cmp_ui(b, 19, 23) == 0);
    CHECK(!weighted_remainder_cycle_q(a, b, c, 3, 3, address, last));
    CHECK(!weighted_remainder_cycle_q(a, a, c, 3, 1, address, last));
    CHECK(!weighted_remainder_cycle_q(a, b, a, 3, 1, address, last));
    CHECK(!weighted_remainder_cycle_q(a, b, b, 3, 1, address, last));
    CHECK(!weighted_remainder_cycle_tv_q(a, a, c, 3, last));
    CHECK(!weighted_remainder_cycle_tv_q(a, b, a, 3, last));
    CHECK(!weighted_remainder_cycle_tv_q(a, b, b, 3, last));
    mpz_set_si(last, -1);
    CHECK(!weighted_remainder_cycle_q(a, b, c, 3, 1, address, last));
    CHECK(!weighted_remainder_cycle_tv_q(a, b, c, 3, last));
    CHECK(mpq_cmp_ui(a, 13, 17) == 0 && mpq_cmp_ui(b, 19, 23) == 0 && mpq_cmp_ui(c, 29, 31) == 0);
    unsigned period = 77, distinct = 88, calls = 0;
    CHECK(!weighted_remainder_clock_law(&period, &distinct, 13, NULL, NULL));
    CHECK(period == 77 && distinct == 88);
    CHECK(!weighted_remainder_clock_law(&period, &period, 2, NULL, NULL));
    CHECK(period == 77);
    CHECK(!weighted_remainder_clock_law(NULL, &distinct, 2, NULL, NULL));
    CHECK(!weighted_remainder_clock_law(&period, NULL, 2, NULL, NULL));
    CHECK(!weighted_remainder_clock_law(&period, &distinct, 4, abort_law, &calls));
    CHECK(period == 77 && distinct == 88 && calls == 3);
    for (unsigned m = 0; m <= 240; ++m) if (m < 2 || m > 12) {
        CHECK(!weighted_remainder_clock_law(&period, &distinct, m, NULL, NULL));
        CHECK(period == 77 && distinct == 88);
    }
    const int bad_periods[] = {-1, 0, 241, INT_MIN, INT_MAX};
    for (unsigned i = 0; i < sizeof bad_periods / sizeof *bad_periods; ++i) {
        CHECK(isnan(weighted_remainder_covariance(bad_periods[i], 3)));
        CHECK(isnan(weighted_remainder_covariance(3, bad_periods[i])));
        CHECK(!weighted_remainder_clock_covariance_q(a, (unsigned)bad_periods[i], 3));
        CHECK(!weighted_remainder_clock_covariance_q(a, 3, (unsigned)bad_periods[i]));
        CHECK(mpq_cmp_ui(a, 13, 17) == 0);
    }
    /* Consume GMP inputs before writing overlapping outputs. */
    mpq_set_si(clock.increment, -13, 1);
    CHECK(weighted_remainder_clock_compute(&clock, 7, mpq_numref(clock.increment)));
    WeightedRemainderClock reference;
    weighted_remainder_clock_init(&reference);
    CHECK(weighted_remainder_clock_compute(&reference, 7, address));
    CHECK(mpq_equal(clock.centered_age, reference.centered_age));
    mpq_set_si(a, -13, 1); mpq_set_ui(b, 100, 1);
    CHECK(weighted_remainder_cycle_q(a, b, c, 7, 1, mpq_numref(a), mpq_numref(b)));
    gmp_printf("cycle 7 1 -13 100 %Qd %Qd %Qd\n", a, b, c);
    mpq_set_ui(a, 100, 1);
    CHECK(weighted_remainder_cycle_tv_q(a, b, c, 7, mpq_numref(a)));
    gmp_printf("tv 7 100 %Qd %Qd %Qd\n", a, b, c);
    weighted_remainder_clock_clear(&clock);
    weighted_remainder_clock_clear(&reference);
    for (unsigned m = 0; m <= 240; ++m) {
        assert(weighted_remainder_age_budget_q(a, b, m));
        gmp_printf("budget %u %Qd %Qd\n", m, a, b);
    }
    mpq_clears(a, b, c, NULL);
    mpz_clears(address, last, NULL);
    printf("edge_checks %u\n", edges);

    const char *addresses[] = {"0", "1", "-1", "6", "-13", "1000000000",
        "-9223372036854775808", "9223372036854775807",
        "-123456789012345678901234567890123456789012345678901234567890"};
    const char *windows[] = {"0", "1", "6", "12", "100", "1000000000000000000000000000000"};
    for (unsigned m = 2; m <= 240; ++m) {
        for (unsigned i = 0; i < sizeof addresses / sizeof *addresses; ++i) clock_record(m, addresses[i]);
        for (unsigned i = 0; i < sizeof windows / sizeof *windows; ++i) tv_record(m, windows[i]);
    }
    for (unsigned k = 2; k <= 240; ++k) {
        unsigned residues[] = {0, 1, k / 2, k - 1};
        for (unsigned i = 0; i < 4; ++i)
            for (unsigned j = 0; j < sizeof windows / sizeof *windows; ++j)
                cycle_record(k, residues[i], addresses[(i + j) % 9], windows[j]);
    }
    for (unsigned k = 2; k <= 12; ++k) for (unsigned r = 0; r < k; ++r)
        for (unsigned n = 0; n <= 2 * k; ++n) {
            char value[32]; snprintf(value, sizeof value, "%u", n);
            cycle_record(k, r, "-13", value);
        }
    for (unsigned m = 2; m <= 12; ++m) {
        assert(weighted_remainder_clock_law(&period, &distinct, m, law_record, &m));
        printf("law %u %u %u\n", m, period, distinct);
    }
    for (unsigned k = 1; k <= 48; ++k) for (unsigned l = 1; l <= 48; ++l)
        covariance_record(k, l);
    for (unsigned k = 1; k <= 240; ++k) {
        covariance_record(k, 1); covariance_record(k, 2);
        covariance_record(k, k); covariance_record(k, 240);
    }
    return 0;
}
