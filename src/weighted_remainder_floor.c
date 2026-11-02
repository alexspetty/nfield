#include "weighted_remainder_floor.h"
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int floor_prime(unsigned p)
{
    if (p < 2 || p > WEIGHTED_REMAINDER_EXACT_MAX) return 0;
    for (unsigned d = 2; d <= p / d; ++d) if (p % d == 0) return 0;
    return 1;
}

static unsigned floor_residue(long long a, unsigned modulus)
{
    long long r = a % (long long)modulus;
    return (unsigned)(r < 0 ? r + modulus : r);
}

static unsigned floor_transformed(unsigned p, unsigned a)
{
    unsigned modulus = p * p;
    return (unsigned)(((uint64_t)(modulus + 1 - p) * a) % modulus);
}

int weighted_remainder_floor_q(mpq_t out, unsigned p, long long address)
{
    if (!floor_prime(p)) return 0;
    unsigned modulus = p * p, a = floor_residue(address, modulus), count = 0;
    for (unsigned d = 0; d < p; ++d) {
        uint64_t lower = (uint64_t)d * (p + 1) * a;
        uint64_t upper = lower + a;
        /* 0<=a<p^2, so each floor difference is zero or one. Products
         * are formed only after reduction and in unsigned 64-bit space. */
        count += (unsigned)(upper / modulus - lower / modulus);
    }
    mpq_set_si(out, (long)p * count - (long)a, p);
    mpq_canonicalize(out);
    return 1;
}

int weighted_remainder_straightening_q(mpq_t left, mpq_t right,
                                       unsigned p, long long address)
{
    if (left == right || !floor_prime(p)) return 0;
    unsigned modulus = p * p, a = floor_residue(address, modulus);
    mpq_t floor_value, midpoint_value, phase;
    mpq_inits(floor_value, midpoint_value, phase, NULL);
    mpq_set_ui(phase, a, modulus);
    mpq_canonicalize(phase);
    int ok = weighted_remainder_floor_q(floor_value, p, floor_transformed(p, a)) &&
             weighted_remainder_response_q(midpoint_value, p - 1, phase);
    if (ok) {
        mpq_set(left, floor_value);
        mpq_set(right, midpoint_value);
    }
    mpq_clears(floor_value, midpoint_value, phase, NULL);
    return ok;
}

static int floor_parse_prime(const char *s, unsigned *out)
{
    if (!s || !*s) return 0;
    for (const char *t = s; *t; ++t) if (*t < '0' || *t > '9') return 0;
    errno = 0;
    char *end;
    unsigned long p = strtoul(s, &end, 10);
    if (errno || *end || p > WEIGHTED_REMAINDER_EXACT_MAX || !floor_prime((unsigned)p))
        return 0;
    *out = (unsigned)p;
    return 1;
}

static int floor_parse_address(const char *s, long long *out)
{
    if (!s || !*s) return 0;
    const char *t = s;
    if (*t == '-') ++t;
    if (!*t) return 0;
    for (; *t; ++t) if (*t < '0' || *t > '9') return 0;
    errno = 0;
    char *end;
    long long a = strtoll(s, &end, 10);
    if (errno || *end) return 0;
    *out = a;
    return 1;
}

int weighted_remainder_floor_command(int argc, char **argv)
{
    unsigned p;
    long long address;
    if (argc != 5 || !floor_parse_prime(argv[3], &p) ||
        !floor_parse_address(argv[4], &address) ||
        (strcmp(argv[2], "floor") && strcmp(argv[2], "straighten"))) {
        fputs("Use floor <prime> <address> or straighten <prime> <address>. "
              "Prime is 2..239; address is a signed 64-bit integer.\n", stderr);
        return 1;
    }
    mpq_t left, right;
    mpq_inits(left, right, NULL);
    unsigned modulus = p * p, a = floor_residue(address, modulus);
    printf("Exact prime-square floor response\nprime %u\nmodulus %u\n", p, modulus);
    printf("address %lld\ncanonical_address %u\n", address, a);
    int ok;
    if (strcmp(argv[2], "floor") == 0) {
        ok = weighted_remainder_floor_q(left, p, address);
        if (ok) gmp_printf("floor_response %Qd\n", left);
    } else {
        ok = weighted_remainder_straightening_q(left, right, p, address);
        if (ok) {
            printf("transformed_address %u\n", floor_transformed(p, a));
            gmp_printf("floor_response %Qd\nmidpoint_response %Qd\n", left, right);
            mpq_sub(right, left, right);
            gmp_printf("difference %Qd\n", right);
        }
    }
    mpq_clears(left, right, NULL);
    return ok ? 0 : 1;
}
