#include "../src/weighted_remainder_exact.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static int stop_atom(unsigned a, unsigned k, unsigned copies, void *context)
{
    (void)a; (void)k; (void)copies;
    ++*(unsigned *)context;
    return 0;
}

int main(void)
{
    mpq_t value, phase, high;
    mpq_inits(value, phase, high, NULL);
    mpq_set_ui(value, 9, 7);
    mpq_set_ui(high, 11, 13);
    assert(!weighted_remainder_amplitude_interval_q(value, high, 1, 2));
    assert(!weighted_remainder_amplitude_interval_q(value, high, 2, 1));
    assert(!weighted_remainder_amplitude_interval_q(value, high, UINT_MAX, 2));
    assert(!weighted_remainder_amplitude_interval_q(value, high, 2, 241));
    assert(!weighted_remainder_amplitude_interval_q(value, value, 2, 2));
    assert(mpq_cmp_ui(high, 11, 13) == 0);
    assert(!weighted_remainder_weight_q(value, UINT_MAX));
    assert(!weighted_remainder_capacity_q(value, 241));
    assert(!weighted_remainder_ramp_overlap_q(value, 0, 1));
    assert(!weighted_remainder_ramp_overlap_q(value, 1, 241));
    assert(!weighted_remainder_midpoint_q(value, 241, phase));
    assert(!weighted_remainder_response_q(value, 241, phase));
    assert(mpq_cmp_ui(value, 9, 7) == 0);
    assert(!weighted_remainder_boundary_visit(1, NULL, NULL));
    unsigned visits = 0;
    assert(weighted_remainder_boundary_visit(0, stop_atom, &visits));
    assert(visits == 0);
    assert(!weighted_remainder_boundary_visit(240, stop_atom, &visits));
    assert(visits == 1);
    assert(!weighted_remainder_boundary_visit(241, stop_atom, &visits));
    mpz_set_ui(mpq_denref(phase), 0);
    assert(!weighted_remainder_midpoint_q(value, 1, phase));
    assert(!weighted_remainder_response_q(value, 1, phase));
    assert(mpq_cmp_ui(value, 9, 7) == 0);
    mpq_set_ui(phase, 0, 1);

    for (unsigned k = 0; k <= 240; ++k) {
        assert(weighted_remainder_weight_q(value, k));
        gmp_printf("weight %u %Qd\n", k, value);
    }
    for (unsigned n = 0; n <= 24; ++n) {
        assert(weighted_remainder_capacity_q(value, n));
        gmp_printf("capacity %u %Qd\n", n, value);
    }
    for (unsigned r = 1; r <= 32; ++r) for (unsigned s = 1; s <= 32; ++s) {
        assert(weighted_remainder_ramp_overlap_q(value, r, s));
        gmp_printf("ramp %u %u %Qd\n", r, s, value);
    }
    assert(weighted_remainder_ramp_overlap_q(value, 239, 240));
    gmp_printf("ramp 239 240 %Qd\n", value);
    for (unsigned q = 2; q <= 32; ++q) for (unsigned m = 2; m <= 32; ++m) {
        assert(weighted_remainder_amplitude_interval_q(value, high, q, m));
        gmp_printf("amplitude_lower %u %u %Qd\n", q, m, value);
        gmp_printf("amplitude_upper %u %u %Qd\n", q, m, high);
    }
    const unsigned conductors[] = {2, 3, 7, 31, 239, 240};
    const unsigned cutoffs[] = {2, 3, 6, 12, 32, 240};
    for (unsigned i = 0; i < sizeof conductors / sizeof *conductors; ++i)
        for (unsigned j = 0; j < sizeof cutoffs / sizeof *cutoffs; ++j) {
            unsigned q = conductors[i], m = cutoffs[j];
            assert(weighted_remainder_amplitude_interval_q(value, high, q, m));
            gmp_printf("amplitude_lower %u %u %Qd\n", q, m, value);
            gmp_printf("amplitude_upper %u %u %Qd\n", q, m, high);
        }
    for (unsigned r = 0; r <= 12; ++r) for (unsigned d = 1; d <= 13; ++d)
        for (long a = -13; a <= 13; ++a) {
            mpq_set_si(phase, a, d);
            mpq_canonicalize(phase);
            assert(weighted_remainder_midpoint_q(value, r, phase));
            gmp_printf("midpoint %u %ld %u %Qd\n", r, a, d, value);
            assert(weighted_remainder_response_q(value, r, phase));
            gmp_printf("response %u %ld %u %Qd\n", r, a, d, value);
        }
    /* In-place rational output must not corrupt the input phase. */
    mpq_set_si(phase, -1, 6);
    assert(weighted_remainder_response_q(phase, 6, phase));
    gmp_printf("response 6 -1 6 %Qd\n", phase);
    mpq_clears(value, phase, high, NULL);
    puts("invalid-input-and-alias-checks PASS");
    return 0;
}
