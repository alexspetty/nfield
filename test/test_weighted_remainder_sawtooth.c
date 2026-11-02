#include "../src/weighted_remainder_sawtooth.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static unsigned edge_checks;
#define CHECK(condition) do { assert(condition); ++edge_checks; } while (0)

static unsigned test_gcd(unsigned a, unsigned b)
{
    while (b) { unsigned r = a % b; a = b; b = r; }
    return a;
}

static int unit(unsigned d, long long a)
{
    long long r = a % (long long)d;
    return test_gcd((unsigned)(r < 0 ? r + d : r), d) == 1;
}

static void gram_record(mpq_t out, unsigned d, long long a, unsigned e, long long b)
{
    assert(weighted_remainder_sawtooth_gram_q(out, d, a, e, b));
    gmp_printf("gram %u %lld %u %lld %Qd\n", d, a, e, b, out);
}

int main(void)
{
    mpq_t out;
    mpq_init(out);
    mpq_set_ui(out, 13, 17);
    const unsigned bad[] = {0, 241, UINT_MAX};
    for (unsigned i = 0; i < sizeof bad / sizeof *bad; ++i) {
        CHECK(!weighted_remainder_sawtooth_q(out, bad[i], 1, 0));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_dedekind_q(out, bad[i], 1));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_sawtooth_gram_q(out, bad[i], 1, 5, 1));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_sawtooth_gram_q(out, 5, 1, bad[i], 1));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_sawtooth_mean_q(out, bad[i], 1, 1, 0));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_sawtooth_mean_q(out, 5, 1, bad[i], 0));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
    }
    for (unsigned d = 2; d <= 240; ++d) {
        CHECK(!weighted_remainder_sawtooth_q(out, d, 0, 1));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_dedekind_q(out, d, -(long long)d));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_sawtooth_gram_q(out, d, d, 1, 1));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_sawtooth_gram_q(out, 1, 1, d, -(long long)d));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
        CHECK(!weighted_remainder_sawtooth_mean_q(out, d, d, 1, 0));
        CHECK(mpq_cmp_ui(out, 13, 17) == 0);
    }
    CHECK(!weighted_remainder_sawtooth_gram_q(out, 6, 2, 5, 1));
    CHECK(mpq_cmp_ui(out, 13, 17) == 0);
    CHECK(!weighted_remainder_sawtooth_mean_q(out, 6, 2, 1, 0));
    CHECK(mpq_cmp_ui(out, 13, 17) == 0);
    CHECK(!weighted_remainder_sawtooth_mean_q(out, 5, 1, 3, 0));
    CHECK(mpq_cmp_ui(out, 13, 17) == 0);
    printf("edge_checks %u\n", edge_checks);

    for (unsigned d = 1; d <= 240; ++d) {
        const long long slopes[] = {1, -1, d + 1, -(long long)d - 1, LLONG_MIN, LLONG_MAX};
        const long long residues[] = {0, 1, -1, d, (long long)d - 1,
                                      d + 1, LLONG_MIN, LLONG_MAX, 3LL * d + 7};
        for (unsigned i = 0; i < sizeof slopes / sizeof *slopes; ++i) {
            long long a = slopes[i];
            if (!unit(d, a)) continue;
            for (unsigned j = 0; j < sizeof residues / sizeof *residues; ++j) {
                long long r = residues[j];
                assert(weighted_remainder_sawtooth_q(out, d, a, r));
                gmp_printf("row %u %lld %lld %Qd\n", d, a, r, out);
            }
            for (unsigned q = 1; q <= d; ++q) if (d % q == 0) {
                const long long fibers[] = {0, 1, -1, (long long)q - 1, LLONG_MIN, LLONG_MAX};
                for (unsigned j = 0; j < sizeof fibers / sizeof *fibers; ++j) {
                    long long t = fibers[j];
                    assert(weighted_remainder_sawtooth_mean_q(out, d, a, q, t));
                    gmp_printf("mean %u %lld %u %lld %Qd\n", d, a, q, t, out);
                }
            }
        }
        for (unsigned a = 0; a < d; ++a) if (unit(d, a)) {
            assert(weighted_remainder_dedekind_q(out, d, a));
            gmp_printf("dedekind %u %u %Qd\n", d, a, out);
            assert(weighted_remainder_dedekind_q(out, d, -(long long)a - 2 * d));
            gmp_printf("dedekind %u %lld %Qd\n", d, -(long long)a - 2 * d, out);
        }
    }
    for (unsigned d = 1; d <= 16; ++d) for (unsigned e = 1; e <= 16; ++e)
        for (unsigned a = 0; a < d; ++a) if (unit(d, a))
            for (unsigned b = 0; b < e; ++b) if (unit(e, b))
                gram_record(out, d, a, e, b);
    const unsigned large[] = {1, 2, 119, 120, 127, 128, 179, 180, 239, 240};
    for (unsigned i = 0; i < sizeof large / sizeof *large; ++i)
        for (unsigned j = 0; j < sizeof large / sizeof *large; ++j) {
            unsigned d = large[i], e = large[j];
            const long long first[] = {1, -1, LLONG_MIN, LLONG_MAX};
            const long long second[] = {1, -1, LLONG_MAX};
            for (unsigned u = 0; u < sizeof first / sizeof *first; ++u) if (unit(d, first[u]))
                for (unsigned v = 0; v < sizeof second / sizeof *second; ++v) if (unit(e, second[v]))
                    gram_record(out, d, first[u], e, second[v]);
        }
    mpq_clear(out);
    return 0;
}
