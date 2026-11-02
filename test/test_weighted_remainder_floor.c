#include "../src/weighted_remainder_floor.h"
#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>

static unsigned edge_checks;
#define CHECK(c) do { assert(c); ++edge_checks; } while (0)

static int prime(unsigned p)
{
    if (p < 2) return 0;
    for (unsigned d = 2; d * d <= p; ++d) if (p % d == 0) return 0;
    return 1;
}

static void record(unsigned p, long long a)
{
    mpq_t raw, left, right;
    mpq_inits(raw, left, right, NULL);
    assert(weighted_remainder_floor_q(raw, p, a));
    assert(weighted_remainder_straightening_q(left, right, p, a));
    gmp_printf("sample %u %lld %Qd %Qd %Qd\n", p, a, raw, left, right);
    mpq_clears(raw, left, right, NULL);
}

static void reject(unsigned p)
{
    mpq_t left, right;
    mpq_inits(left, right, NULL);
    mpq_set_ui(left, 13, 17);
    mpq_set_ui(right, 19, 23);
    CHECK(!weighted_remainder_floor_q(left, p, LLONG_MIN));
    CHECK(mpq_cmp_ui(left, 13, 17) == 0);
    CHECK(!weighted_remainder_straightening_q(left, right, p, LLONG_MAX));
    CHECK(mpq_cmp_ui(left, 13, 17) == 0);
    CHECK(mpq_cmp_ui(right, 19, 23) == 0);
    mpq_clears(left, right, NULL);
}

int main(void)
{
    for (unsigned p = 0; p <= 240; ++p) if (!prime(p)) reject(p);
    reject(241);
    reject(UINT_MAX);
    mpq_t same;
    mpq_init(same);
    mpq_set_ui(same, 13, 17);
    CHECK(!weighted_remainder_straightening_q(same, same, 2, 1));
    CHECK(mpq_cmp_ui(same, 13, 17) == 0);
    CHECK(!weighted_remainder_straightening_q(same, same, 239, LLONG_MIN));
    CHECK(mpq_cmp_ui(same, 13, 17) == 0);
    mpq_clear(same);
    printf("edge_checks %u\n", edge_checks);

    uint32_t state = 0x612f43u;
    for (unsigned p = 2; p <= 239; ++p) if (prime(p)) {
        unsigned modulus = p * p;
        if (p <= 43) for (unsigned a = 0; a < modulus; ++a) record(p, a);
        /* Every nonunit address at every admitted prime. */
        for (unsigned k = 0; k < p; ++k) record(p, (long long)k * p);
        const long long addresses[] = {0, 1, -1, p - 1, p, p + 1,
            (long long)modulus - 1, modulus, (long long)modulus + 1,
            -(long long)modulus - 1, LLONG_MIN, LLONG_MAX};
        for (unsigned i = 0; i < sizeof addresses / sizeof *addresses; ++i)
            record(p, addresses[i]);
        for (unsigned i = 0; i < 64; ++i) {
            state = state * UINT32_C(1664525) + UINT32_C(1013904223);
            long long a = (long long)(state % modulus) +
                          ((int)(i % 3) - 1) * (long long)modulus;
            record(p, a);
        }
    }
    return 0;
}
