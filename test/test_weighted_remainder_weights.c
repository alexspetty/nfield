#include "../src/weighted_remainder_weights.h"
#include "../src/weighted_remainder_state.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static unsigned edges, profiles;
#define CHECK(x) do { assert(x); ++edges; } while (0)

static void variance_checks(void)
{
    mpq_t a, b, c, d;
    mpq_inits(a, b, c, d, NULL);
    mpq_set_ui(a, 13, 17); mpq_set_ui(b, 19, 23);
    mpq_set_ui(c, 29, 31); mpq_set_ui(d, 37, 41);
    unsigned bits = 7;
    const unsigned invalid[] = {0, 1, 241, UINT_MAX};
    for (unsigned j = 0; j < sizeof invalid / sizeof *invalid; ++j) {
        CHECK(!weighted_remainder_collision_variance_q(a, b, c, d, &bits, invalid[j]));
        CHECK(bits == 7 && mpq_cmp_ui(a, 13, 17) == 0 && mpq_cmp_ui(b, 19, 23) == 0 &&
              mpq_cmp_ui(c, 29, 31) == 0 && mpq_cmp_ui(d, 37, 41) == 0);
    }
    CHECK(!weighted_remainder_collision_variance_q(a, b, c, d, NULL, 2));
    for (unsigned i = 0; i < 4; ++i) for (unsigned j = i + 1; j < 4; ++j) {
        mpq_ptr outputs[] = {a,b,c,d};
        outputs[j] = outputs[i];
        CHECK(!weighted_remainder_collision_variance_q(outputs[0], outputs[1], outputs[2], outputs[3], &bits, 2));
        CHECK(bits == 7 && mpq_cmp_ui(a, 13, 17) == 0 && mpq_cmp_ui(b, 19, 23) == 0 &&
              mpq_cmp_ui(c, 29, 31) == 0 && mpq_cmp_ui(d, 37, 41) == 0);
    }
    for (unsigned m = 2; m <= 240; ++m) {
        assert(weighted_remainder_collision_variance_q(a, b, c, d, &bits, m));
        WeightedRemainderState old;
        assert(weighted_remainder_state_compute(0, (int)m, &old));
        gmp_printf("variance %u %u %Qd %Qd %Qd %Qd ", m, bits, a, b, c, d);
        printf("%.21Lg\n", old.variance);
    }
    mpq_clears(a, b, c, d, NULL);
}

static void rational(mpq_t q, long n, unsigned d)
{
    mpq_set_si(q, n, d);
    mpq_canonicalize(q);
}

static void zero_weights(mpq_t *v)
{
    for (unsigned k = 0; k <= 240; ++k) mpq_set_ui(v[k], 0, 1);
}

static void profile(mpq_t *v, unsigned m, const mpq_t epsilon, int perturbed)
{
    unsigned id = profiles++;
    printf("profile %u %u\n", id, m);
    if (perturbed) gmp_printf("perturbed %u %Qd\n", id, epsilon);
    for (unsigned k = 2; k <= m; ++k)
        if (mpq_sgn(v[k])) gmp_printf("weight %u %u %Qd\n", id, k, v[k]);
    WeightedRemainderWeights s;
    weighted_remainder_weights_init(&s);
    mpz_t n;
    mpz_init(n);
    mpq_t q;
    mpq_init(q);
    const char *addresses[] = {"0", "1", "-1", "6", "-13", "1000000000",
        "123456789012345678901234567890123456789012345678901234567890",
        "-123456789012345678901234567890123456789012345678901234567890"};
    for (unsigned j = 0; j < sizeof addresses / sizeof *addresses; ++j) {
        assert(mpz_set_str(n, addresses[j], 10) == 0);
        assert(weighted_remainder_weights_compute(&s, v, m, n));
        gmp_printf("state %u %Zd %d %d %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd %Qd\n",
                   id, n, s.nonnegative, s.unit_mass, s.mass, s.first_moment,
                   s.raw_age, s.stationary_age, s.centered_age, s.divisor_forcing,
                   s.increment, s.gram_variance, s.jordan_variance);
        rational(q, 13, 17);
        int ok = weighted_remainder_weights_energy_q(q, v, m, n);
        gmp_printf("energy %u %Zd %d %Qd\n", id, n, ok, q);
    }
    for (unsigned k = 2; k <= 240; ++k) {
        assert(weighted_remainder_weights_amplitude_q(q, v, m, k));
        gmp_printf("amplitude %u %u %Qd\n", id, k, q);
    }
    /* Address contained in an output must be read before the output changes. */
    rational(s.mass, -13, 1);
    CHECK(weighted_remainder_weights_compute(&s, v, m, mpq_numref(s.mass)));
    gmp_printf("alias_center %u %Qd\n", id, s.centered_age);
    mpq_clear(q);
    mpz_clear(n);
    weighted_remainder_weights_clear(&s);
}

/* Independent reference: visit literal paired residues over their complete
 * period. The period is found by repeated addition, not production's gcd,
 * and no covariance or Jordan formula is used. Integer products fit int64. */
static void complete_cycle_references(void)
{
    for (unsigned k = 2; k <= 240; ++k) for (unsigned ell = 2; ell <= k; ++ell) {
        unsigned period = k;
        while (period % ell) period += k;
        long long sum = 0;
        for (unsigned n = 0; n < period; ++n) {
            long long a = 2LL * (n % k) - (long long)k + 1;
            long long b = 2LL * (n % ell) - (long long)ell + 1;
            sum += a * b;
        }
        printf("cycle_reference %u %u %lld %u\n", k, ell, sum, period);
    }
}

int main(void)
{
    mpq_t v[241], q, e;
    for (unsigned k = 0; k <= 240; ++k) mpq_init(v[k]);
    mpq_inits(q, e, NULL);
    rational(q, 13, 17);
    mpz_t n;
    mpz_init_set_ui(n, 1);
    WeightedRemainderWeights s;
    weighted_remainder_weights_init(&s);
    s.cutoff = 7;
    rational(s.mass, 13, 17);
    const unsigned bad[] = {0, 1, 241, UINT_MAX};
    for (unsigned j = 0; j < sizeof bad / sizeof *bad; ++j) {
        CHECK(!weighted_remainder_weights_compute(&s, v, bad[j], n));
        CHECK(s.cutoff == 7 && mpq_cmp_ui(s.mass, 13, 17) == 0);
        CHECK(!weighted_remainder_weights_amplitude_q(q, v, bad[j], 2));
        CHECK(!weighted_remainder_weights_amplitude_q(q, v, 2, bad[j]));
        CHECK(!weighted_remainder_weights_energy_q(q, v, bad[j], n));
        CHECK(mpq_cmp_ui(q, 13, 17) == 0);
    }
    CHECK(!weighted_remainder_weights_compute(NULL, v, 2, n));
    CHECK(!weighted_remainder_weights_compute(&s, NULL, 2, n));
    CHECK(!weighted_remainder_weights_amplitude_q(q, NULL, 2, 2));
    CHECK(!weighted_remainder_weights_energy_q(q, NULL, 2, n));
    for (unsigned k = 0; k <= 1; ++k) {
        rational(v[k], 1, 1);
        CHECK(!weighted_remainder_weights_compute(&s, v, 2, n));
        CHECK(!weighted_remainder_weights_amplitude_q(q, v, 2, 2));
        CHECK(!weighted_remainder_weights_energy_q(q, v, 2, n));
        rational(v[k], 0, 1);
    }
    /* Noncanonical, zero and negative denominators are rejected safely. */
    for (int d = -1; d <= 2; ++d) {
        mpz_set_ui(mpq_numref(v[2]), d == 2 ? 2 : 1);
        mpz_set_si(mpq_denref(v[2]), d);
        if (d == 1) continue;
        CHECK(!weighted_remainder_weights_compute(&s, v, 2, n));
        CHECK(!weighted_remainder_weights_amplitude_q(q, v, 2, 2));
        CHECK(!weighted_remainder_weights_energy_q(q, v, 2, n));
        CHECK(mpq_cmp_ui(q, 13, 17) == 0 && mpq_cmp_ui(s.mass, 13, 17) == 0);
    }
    rational(v[2], 1, 1);
    mpz_set_si(n, -1);
    CHECK(!weighted_remainder_weights_energy_q(q, v, 2, n));
    CHECK(mpq_cmp_ui(q, 13, 17) == 0);
    rational(q, 13, 17);
    CHECK(weighted_remainder_weights_energy_q(q, v, 2, mpq_numref(q)));
    CHECK(mpq_cmp_ui(q, 37, 3) == 0);
    CHECK(weighted_remainder_weights_amplitude_q(v[2], v, 2, 3));
    CHECK(mpq_sgn(v[2]) == 0);

    const long bad_eps[] = {0, 1, -1, 2, -2};
    for (unsigned j = 0; j < sizeof bad_eps / sizeof *bad_eps; ++j) {
        rational(e, bad_eps[j], 24);
        rational(v[2], 13, 17);
        CHECK(!weighted_remainder_perturbed_weights_q(v, 4, e));
        CHECK(mpq_cmp_ui(v[2], 13, 17) == 0);
    }
    rational(e, 1, 48);
    CHECK(!weighted_remainder_perturbed_weights_q(NULL, 4, e));
    const unsigned bad_perturbed[] = {0, 1, 2, 3, 241, UINT_MAX};
    for (unsigned j = 0; j < sizeof bad_perturbed / sizeof *bad_perturbed; ++j) {
        CHECK(!weighted_remainder_perturbed_weights_q(v, bad_perturbed[j], e));
        CHECK(mpq_cmp_ui(v[2], 13, 17) == 0);
    }
    rational(v[2], 1, 48);
    CHECK(weighted_remainder_perturbed_weights_q(v, 4, v[2]));
    CHECK(mpq_cmp_ui(v[2], 13, 48) == 0);
    rational(q, 13, 17);
    rational(e, 1, 48);
    CHECK(!weighted_remainder_perturbed_deficit_q(q, v[0], 241, e));
    CHECK(!weighted_remainder_perturbed_deficit_q(q, v[0], UINT_MAX, e));
    CHECK(!weighted_remainder_perturbed_deficit_q(q, q, 6, e));
    CHECK(mpq_cmp_ui(q, 13, 17) == 0 && mpq_sgn(v[0]) == 0);
    for (unsigned j = 0; j < sizeof bad_eps / sizeof *bad_eps; ++j) {
        rational(e, bad_eps[j], 24);
        CHECK(!weighted_remainder_perturbed_deficit_q(q, v[0], 6, e));
        CHECK(mpq_cmp_ui(q, 13, 17) == 0 && mpq_sgn(v[0]) == 0);
    }
    for (unsigned denominator = 25; denominator <= 48; denominator += 23)
        for (int sign = -1; sign <= 1; sign += 2) {
            rational(e, sign, denominator);
            for (unsigned resolution = 0; resolution <= 240; ++resolution)
                if (resolution <= 24 || resolution >= 239) {
                    CHECK(weighted_remainder_perturbed_deficit_q(q, v[0], resolution, e));
                    gmp_printf("perturbed_deficit %u %Qd %Qd %Qd\n", resolution, e, q, v[0]);
                }
        }
    rational(q, 1, 48);
    CHECK(weighted_remainder_perturbed_deficit_q(q, v[0], 6, q));
    gmp_printf("perturbed_deficit 6 1/48 %Qd %Qd\n", q, v[0]);
    for (unsigned k = 2; k <= 12; ++k) {
        zero_weights(v); rational(v[k], 1, 1); profile(v, k, e, 0);
    }
    zero_weights(v); profile(v, 2, e, 0);
    const unsigned pairs[][2] = {{2,3},{4,6},{6,10},{8,12},{239,240},{120,240}};
    for (unsigned j = 0; j < sizeof pairs / sizeof *pairs; ++j)
        for (int sign = -1; sign <= 1; sign += 2) {
            zero_weights(v);
            rational(v[pairs[j][0]], sign, 3);
            rational(v[pairs[j][1]], 3 - sign, 3);
            profile(v, pairs[j][1], e, 0);
        }
    for (unsigned m = 4; m <= 40; m += 6) {
        zero_weights(v);
        for (unsigned k = 2; k <= m; ++k) rational(v[k], k % 2 ? -1 : 1, k + 1);
        profile(v, m, e, 0);
    }
    const unsigned cutoffs[] = {4,5,12,40,240};
    for (unsigned j = 0; j < sizeof cutoffs / sizeof *cutoffs; ++j)
        for (int sign = -1; sign <= 1; sign += 2) {
            rational(e, sign, 25);
            CHECK(weighted_remainder_perturbed_weights_q(v, cutoffs[j], e));
            profile(v, cutoffs[j], e, 1);
        }
    variance_checks();
    complete_cycle_references();
    printf("edge_checks %u profiles %u\n", edges, profiles);
    weighted_remainder_weights_clear(&s);
    mpq_clears(q, e, NULL);
    mpz_clear(n);
    for (unsigned k = 0; k <= 240; ++k) mpq_clear(v[k]);
    return 0;
}
