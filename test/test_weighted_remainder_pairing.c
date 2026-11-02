#include "../src/weighted_remainder_pairing.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static void table(mpq_t *real, mpq_t *imag, unsigned period, unsigned kind)
{
    for (unsigned j = 0; j < period; ++j) {
        if (kind == 0) {
            mpq_set_ui(real[j], 0, 1);
            mpq_set_ui(imag[j], 0, 1);
        } else if (kind == 1) {
            mpq_set_si(real[j], -2, 3);
            mpq_set_ui(imag[j], 5, 7);
        } else if (kind == 2) {
            mpq_set_si(real[j], (long)((7*j+period)%13)-6, j%5+1);
            mpq_set_si(imag[j], (long)((5*j+3*period)%11)-5, j%7+1);
        } else {
            mpq_set_ui(real[j], j == period/2, 1);
            mpq_set_si(imag[j], j == period-1 ? -7 : 0, 4);
        }
        mpq_canonicalize(real[j]);
        mpq_canonicalize(imag[j]);
    }
}

int main(void)
{
    mpq_t real_values[240], imag_values[240], real, imag, re_radius, im_radius;
    mpq_inits(real, imag, re_radius, im_radius, NULL);
    for (unsigned j = 0; j < 240; ++j) {
        mpq_init(real_values[j]);
        mpq_init(imag_values[j]);
    }
    table(real_values, imag_values, 240, 2);
    mpq_set_ui(real, 9, 7); mpq_set_ui(imag, 11, 13);
    mpq_set_ui(re_radius, 17, 19); mpq_set_ui(im_radius, 23, 29);
    assert(!weighted_remainder_reset_q(real, 0));
    assert(!weighted_remainder_reset_q(real, UINT_MAX));
    assert(!weighted_remainder_boundary_test_q(real, imag, 0, 2, real_values, imag_values));
    assert(!weighted_remainder_boundary_test_q(real, imag, 241, 2, real_values, imag_values));
    assert(!weighted_remainder_boundary_test_q(real, imag, 2, 0, real_values, imag_values));
    assert(!weighted_remainder_boundary_test_q(real, imag, 2, UINT_MAX, real_values, imag_values));
    assert(!weighted_remainder_boundary_test_q(real, imag, 2, 2, NULL, imag_values));
    assert(!weighted_remainder_boundary_test_q(real, imag, 2, 2, real_values, NULL));
    assert(!weighted_remainder_boundary_test_q(real, real, 2, 2, real_values, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 0, 2, real_values, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 241, 2, real_values, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 2, 1, real_values, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 2, UINT_MAX, real_values, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 2, 2, NULL, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 2, 2, real_values, NULL));
    mpq_ptr outputs[] = {real, imag, re_radius, im_radius};
    for (unsigned i = 0; i < 4; ++i) for (unsigned j = i+1; j < 4; ++j) {
        mpq_ptr alias[] = {real, imag, re_radius, im_radius};
        alias[j] = outputs[i];
        assert(!weighted_remainder_haar_test_q(alias[0], alias[1], alias[2], alias[3],
                                               2, 2, real_values, imag_values));
    }
    /* Validate the entire table, including entries the finite window misses. */
    mpz_set_ui(mpq_denref(real_values[239]), 0);
    assert(!weighted_remainder_boundary_test_q(real, imag, 1, 240, real_values, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 240, 2, real_values, imag_values));
    table(real_values, imag_values, 240, 2);
    mpz_neg(mpq_denref(imag_values[239]), mpq_denref(imag_values[239]));
    assert(!weighted_remainder_boundary_test_q(real, imag, 1, 240, real_values, imag_values));
    assert(!weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 240, 2, real_values, imag_values));
    table(real_values, imag_values, 240, 2);
    assert(mpq_cmp_ui(real, 9, 7) == 0 && mpq_cmp_ui(imag, 11, 13) == 0);
    assert(mpq_cmp_ui(re_radius, 17, 19) == 0 && mpq_cmp_ui(im_radius, 23, 29) == 0);

    for (unsigned n = 1; n <= 240; ++n) {
        assert(weighted_remainder_reset_q(real, n));
        gmp_printf("reset %u %Qd\n", n, real);
    }
    const unsigned periods[] = {1, 2, 3, 4, 6, 7, 12, 31, 239, 240};
    const unsigned lengths[] = {1, 2, 6, 13, 24, 31, 239, 240};
    const unsigned cutoffs[] = {2, 3, 6, 12, 24, 31, 239, 240};
    for (unsigned t = 0; t < 4; ++t) for (unsigned p = 0; p < 10; ++p) {
        unsigned period = periods[p];
        table(real_values, imag_values, period, t);
        for (unsigned j = 0; j < 8; ++j) {
            assert(weighted_remainder_boundary_test_q(real, imag, lengths[j], period, real_values, imag_values));
            gmp_printf("finite %u %u %u %Qd %Qd\n", t, period, lengths[j], real, imag);
            assert(weighted_remainder_haar_test_q(real, imag, re_radius, im_radius,
                                                 period, cutoffs[j], real_values, imag_values));
            gmp_printf("haar %u %u %u %Qd %Qd %Qd %Qd\n", t, period, cutoffs[j],
                       real, imag, re_radius, im_radius);
        }
    }
    /* Read every input before writing any output, including four table aliases. */
    table(real_values, imag_values, 7, 2);
    assert(weighted_remainder_boundary_test_q(real, imag, 24, 7, real_values, imag_values));
    assert(weighted_remainder_boundary_test_q(real_values[0], imag_values[0], 24, 7, real_values, imag_values));
    assert(mpq_equal(real, real_values[0]) && mpq_equal(imag, imag_values[0]));
    table(real_values, imag_values, 7, 2);
    assert(weighted_remainder_haar_test_q(real, imag, re_radius, im_radius, 7, 24, real_values, imag_values));
    assert(weighted_remainder_haar_test_q(real_values[0], real_values[1], imag_values[0], imag_values[1],
                                         7, 24, real_values, imag_values));
    assert(mpq_equal(real, real_values[0]) && mpq_equal(imag, real_values[1]));
    assert(mpq_equal(re_radius, imag_values[0]) && mpq_equal(im_radius, imag_values[1]));
    for (unsigned j = 0; j < 240; ++j) {
        mpq_clear(real_values[j]);
        mpq_clear(imag_values[j]);
    }
    mpq_clears(real, imag, re_radius, im_radius, NULL);
    puts("invalid-input-and-alias-checks PASS");
    return 0;
}
