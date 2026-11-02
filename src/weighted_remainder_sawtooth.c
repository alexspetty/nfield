#include "weighted_remainder_sawtooth.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned saw_gcd(unsigned a, unsigned b)
{
    while (b) {
        unsigned r = a % b;
        a = b;
        b = r;
    }
    return a;
}

static int saw_period(unsigned d)
{
    return d >= 1 && d <= WEIGHTED_REMAINDER_EXACT_MAX;
}

static unsigned saw_residue(long long a, unsigned d)
{
    long long r = a % (long long)d;
    return (unsigned)(r < 0 ? r + d : r);
}

static int saw_unit(unsigned d, long long a)
{
    return saw_period(d) && saw_gcd(saw_residue(a, d), d) == 1;
}

/* Call only after reducing r and checking 1<=d<=240. */
static void saw_value(mpq_t out, unsigned d, unsigned r)
{
    if (!r) mpq_set_ui(out, 0, 1);
    else {
        mpq_set_si(out, 2L * r - (long)d, 2UL * d);
        mpq_canonicalize(out);
    }
}

int weighted_remainder_sawtooth_q(mpq_t out, unsigned d,
                                  long long a, long long r)
{
    if (!saw_unit(d, a)) return 0;
    saw_value(out, d, (saw_residue(a, d) * saw_residue(r, d)) % d);
    return 1;
}

int weighted_remainder_dedekind_q(mpq_t out, unsigned d, long long a)
{
    if (!saw_unit(d, a)) return 0;
    unsigned h = saw_residue(a, d);
    long numerator = 0;
    /* Every nonzero residue has a nonzero image because h is a unit.
     * There are at most 239 products, each of magnitude <=238^2, so
     * their signed sum fits even a 32-bit long. The zero term vanishes. */
    for (unsigned t = 1; t < d; ++t)
        numerator += (2L * t - (long)d) * (2L * ((h * t) % d) - (long)d);
    mpq_set_si(out, numerator, 4UL * d * d);
    mpq_canonicalize(out);
    return 1;
}

/* Euclidean inverse at a positive modulus; modulus one is the zero ring. */
static unsigned saw_inverse(unsigned a, unsigned d)
{
    if (d == 1) return 0;
    long r = d, next_r = a, t = 0, next_t = 1;
    while (next_r) {
        long quotient = r / next_r;
        long saved = r - quotient * next_r;
        r = next_r;
        next_r = saved;
        saved = t - quotient * next_t;
        t = next_t;
        next_t = saved;
    }
    t %= (long)d;
    return (unsigned)(t < 0 ? t + d : t);
}

int weighted_remainder_sawtooth_gram_q(mpq_t out, unsigned d, long long a,
                                       unsigned e, long long b)
{
    if (!saw_unit(d, a) || !saw_unit(e, b)) return 0;
    unsigned g = saw_gcd(d, e);
    unsigned ratio = (saw_residue(b, g) * saw_inverse(saw_residue(a, g), g)) % g;
    mpq_t sum, factor;
    mpq_inits(sum, factor, NULL);
    int ok = weighted_remainder_dedekind_q(sum, g, ratio);
    if (ok) {
        mpq_set_ui(factor, g, (unsigned long)d * e);
        mpq_canonicalize(factor);
        mpq_mul(out, sum, factor);
    }
    mpq_clears(sum, factor, NULL);
    return ok;
}

int weighted_remainder_sawtooth_mean_q(mpq_t out, unsigned d, long long a,
                                       unsigned q, long long r)
{
    if (!saw_unit(d, a) || !saw_period(q) || d % q) return 0;
    mpq_t value, factor;
    mpq_inits(value, factor, NULL);
    saw_value(value, q, (saw_residue(a, q) * saw_residue(r, q)) % q);
    mpq_set_ui(factor, q, d);
    mpq_canonicalize(factor);
    mpq_mul(out, value, factor);
    mpq_clears(value, factor, NULL);
    return 1;
}

static int saw_parse_period(const char *s, unsigned *out)
{
    if (!s || !*s) return 0;
    for (const char *p = s; *p; ++p) if (*p < '0' || *p > '9') return 0;
    char *end;
    errno = 0;
    unsigned long d = strtoul(s, &end, 10);
    if (errno || *end || d < 1 || d > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    *out = (unsigned)d;
    return 1;
}

static int saw_parse_integer(const char *s, long long *out)
{
    if (!s || !*s) return 0;
    const char *p = s;
    if (*p == '-') ++p;
    if (!*p) return 0;
    for (; *p; ++p) if (*p < '0' || *p > '9') return 0;
    char *end;
    errno = 0;
    long long a = strtoll(s, &end, 10);
    if (errno || *end) return 0;
    *out = a;
    return 1;
}

int weighted_remainder_sawtooth_command(int argc, char **argv)
{
    unsigned d, e;
    long long a, b;
    mpq_t value;
    mpq_init(value);
    int ok = 0;
    if (argc == 6 && strcmp(argv[2], "sawtooth") == 0 &&
        saw_parse_period(argv[3], &d) && saw_parse_integer(argv[4], &a) &&
        saw_parse_integer(argv[5], &b)) {
        ok = weighted_remainder_sawtooth_q(value, d, a, b);
        if (ok) {
            printf("Exact midpoint sawtooth\nperiod %u\nslope %lld\nresidue %lld\n", d, a, b);
            gmp_printf("value %Qd\n", value);
        }
    } else if (argc == 5 && strcmp(argv[2], "dedekind") == 0 &&
               saw_parse_period(argv[3], &d) && saw_parse_integer(argv[4], &a)) {
        ok = weighted_remainder_dedekind_q(value, d, a);
        if (ok) {
            printf("Exact Dedekind sum\nperiod %u\nslope %lld\n", d, a);
            gmp_printf("dedekind_sum %Qd\n", value);
        }
    } else if (argc == 7 && strcmp(argv[2], "gram") == 0 &&
               saw_parse_period(argv[3], &d) && saw_parse_integer(argv[4], &a) &&
               saw_parse_period(argv[5], &e) && saw_parse_integer(argv[6], &b)) {
        ok = weighted_remainder_sawtooth_gram_q(value, d, a, e, b);
        if (ok) {
            printf("Exact sawtooth Haar pairing\nfirst_period %u\nfirst_slope %lld\n", d, a);
            printf("second_period %u\nsecond_slope %lld\ngcd %u\n", e, b, saw_gcd(d, e));
            gmp_printf("haar_pairing %Qd\n", value);
        }
    } else if (argc == 7 && strcmp(argv[2], "sawtooth-mean") == 0 &&
               saw_parse_period(argv[3], &d) && saw_parse_integer(argv[4], &a) &&
               saw_parse_period(argv[5], &e) && saw_parse_integer(argv[6], &b)) {
        ok = weighted_remainder_sawtooth_mean_q(value, d, a, e, b);
        if (ok) {
            printf("Exact conditional sawtooth mean\nperiod %u\nslope %lld\n", d, a);
            printf("cylinder_period %u\ncylinder_residue %lld\n", e, b);
            gmp_printf("conditional_mean %Qd\n", value);
        }
    }
    mpq_clear(value);
    if (!ok)
        fputs("Use sawtooth <d> <a> <r>, dedekind <d> <a>, gram <d> <a> <e> <b>, or sawtooth-mean <d> <a> <q> <t>. Periods 1..240; slopes must be units; q divides d.\n", stderr);
    return ok ? 0 : 1;
}
