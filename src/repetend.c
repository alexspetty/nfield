/*
 * repetend.c: Compute the periodic decimal (or base-b) expansion of k/n.
 *
 * Tracks remainders during long division. When a remainder recurs,
 * the cycle start and length are identified.
 *
 * Uses long long by default. Compile with -DNFIELD_GMP for arbitrary
 * precision (requires libgmp).
 */

#include <stdlib.h>
#include <string.h>
#include "nfield.h"

#ifdef NFIELD_GMP

/* ── GMP implementation ──────────────────────────────────── */

Repetend repetend_compute(int k, int n, int base)
{
    Repetend r = {0};
    if (n == 0) return r;

    /* remainder tracking via hash table (linear probe) */
    typedef struct { mpz_t rem; int pos; int used; } Slot;
    int cap = n < 1024 ? 1024 : n + 1;
    Slot *tbl = calloc(cap, sizeof(Slot));
    for (int i = 0; i < cap; i++) {
        mpz_init(tbl[i].rem);
        tbl[i].used = 0;
    }

    mpz_t rem, mpn, mpb, q;
    mpz_init_set_si(rem, (long)k);
    mpz_init_set_si(mpn, (long)n);
    mpz_init_set_si(mpb, (long)base);
    mpz_init(q);

    mpz_mod(rem, rem, mpn);

    int d_cap = 64, d_len = 0;
    int *digits = malloc(sizeof(int) * d_cap);

    while (mpz_cmp_ui(rem, 0) != 0) {
        /* check if remainder seen */
        unsigned long h = mpz_fdiv_ui(rem, cap);
        while (tbl[h].used) {
            if (mpz_cmp(tbl[h].rem, rem) == 0) {
                r.digits      = digits;
                r.len         = d_len;
                r.cycle_start = tbl[h].pos;
                r.cycle_len   = d_len - tbl[h].pos;
                goto done;
            }
            h = (h + 1) % cap;
        }

        /* record remainder */
        mpz_set(tbl[h].rem, rem);
        tbl[h].pos  = d_len;
        tbl[h].used = 1;

        /* long division step */
        mpz_mul(rem, rem, mpb);
        mpz_tdiv_qr(q, rem, rem, mpn);
        int digit = (int)mpz_get_si(q);

        if (d_len == d_cap) {
            d_cap *= 2;
            digits = realloc(digits, sizeof(int) * d_cap);
        }
        digits[d_len++] = digit;
    }

    /* terminates */
    r.digits      = digits;
    r.len         = d_len;
    r.cycle_start = d_len;
    r.cycle_len   = 0;

done:
    for (int i = 0; i < cap; i++)
        mpz_clear(tbl[i].rem);
    free(tbl);
    mpz_clear(rem);
    mpz_clear(mpn);
    mpz_clear(mpb);
    mpz_clear(q);
    return r;
}

#else

/* ── Native long long implementation ─────────────────────── */

Repetend repetend_compute(int k, int n, int base)
{
    Repetend r = {0};

    if (n == 0)
        return r;

    long long kk = (long long)k % n;
    if (kk < 0)
        kk += n;

    /* track remainders: seen[remainder] = position */
    int cap  = n + 1;
    int *pos = malloc(sizeof(int) * cap);
    memset(pos, -1, sizeof(int) * cap);

    int  d_cap = 64;
    int  d_len = 0;
    int *digits = malloc(sizeof(int) * d_cap);

    while (kk != 0) {
        if (pos[kk] >= 0) {
            /* found cycle */
            r.digits      = digits;
            r.len         = d_len;
            r.cycle_start = pos[kk];
            r.cycle_len   = d_len - pos[kk];
            free(pos);
            return r;
        }

        pos[kk] = d_len;

        kk *= base;
        int digit = (int)(kk / n);
        kk = kk % n;

        if (d_len == d_cap) {
            d_cap *= 2;
            digits = realloc(digits, sizeof(int) * d_cap);
        }
        digits[d_len++] = digit;
    }

    /* terminates */
    r.digits      = digits;
    r.len         = d_len;
    r.cycle_start = d_len;
    r.cycle_len   = 0;

    free(pos);
    return r;
}

#endif /* NFIELD_GMP */

void repetend_free(Repetend *r)
{
    free(r->digits);
    r->digits      = NULL;
    r->len         = 0;
    r->cycle_start = 0;
    r->cycle_len   = 0;
}
