/*
 * scale.c — The just major scale and chromatic scale in the deficit lattice.
 *
 * Shows that the alignment deficit lattice in base 30 (smooth primes 2, 3, 5)
 * reproduces the just intonation intervals.
 *
 * The stable coordinate is the alignment deficit
 *   delta(m) = 2/p - alpha(pm) = (p-2)/(p(pm-1)),
 * and the beta ratio delta(m0)/delta(m) converges to the interval m/m0.
 *
 * A. S. Petty, 2026
 */

#include <stdio.h>
#include <string.h>
#include <math.h>

#include "nfield.h"

typedef struct {
    const char *name;
    int num;
    int den;
} Interval;

static const Interval major_scale[] = {
    {"Do  (C)",   1,  1},
    {"Re  (D)",   9,  8},
    {"Mi  (E)",   5,  4},
    {"Fa  (F)",   4,  3},
    {"Sol (G)",   3,  2},
    {"La  (A)",   5,  3},
    {"Ti  (B)",  15,  8},
    {"Do  (C)",   2,  1},
};

static const Interval chromatic[] = {
    {"C ",   1,  1},
    {"C#",  16, 15},
    {"D ",   9,  8},
    {"Eb",   6,  5},
    {"E ",   5,  4},
    {"F ",   4,  3},
    {"F#",  45, 32},
    {"G ",   3,  2},
    {"Ab",   8,  5},
    {"A ",   5,  3},
    {"Bb",   9,  5},
    {"B ",  15,  8},
    {"C ",   2,  1},
};

typedef struct {
    const char *name;
    int num;
    int den;
    long long m;
    int supported;
    double alpha;
    double deficit;
    double beta;
    double lattice;
    double error;
} ScaleRow;

static int is_smooth(long long m, int b) {
    long long t = m;
    for (int p = 2; p * p <= b; p++) {
        if (b % p == 0) {
            while (t % p == 0) t /= p;
        }
    }
    if (b > 1) {
        /* remaining prime factor of b */
        int rem = b;
        for (int p = 2; p * p <= b; p++)
            while (rem % p == 0) rem /= p;
        if (rem > 1)
            while (t % rem == 0) t /= rem;
    }
    return t == 1;
}

double alignment_limit_for_prime(int p) {
    return 2.0 / (double)p;
}

double deficit_alignment(int m, int p) {
    return (double)(p - 2) / ((double)p * ((double)p * (double)m - 1.0));
}

static double alpha_from_pm(int m, int p) {
    return (2.0 * (double)m - 1.0) / ((double)p * (double)m - 1.0);
}

static void build_rows(const Interval *scale, int n, long long m0, int p,
                       ScaleRow *rows) {
    double d0 = deficit_alignment((int)m0, p);
    for (int i = 0; i < n; i++) {
        long long m = m0 * scale[i].num / scale[i].den;
        double d = deficit_alignment((int)m, p);
        rows[i].name = scale[i].name;
        rows[i].num = scale[i].num;
        rows[i].den = scale[i].den;
        rows[i].m = m;
        rows[i].supported = is_smooth(m, 30);
        rows[i].alpha = alpha_from_pm((int)m, p);
        rows[i].deficit = d;
        rows[i].beta = d0 / d;
        rows[i].lattice = (double)scale[i].num / scale[i].den;
        rows[i].error = fabs(rows[i].beta - rows[i].lattice) / rows[i].lattice;
    }
}

static void show_scale_beta(const ScaleRow *rows, int n, long long m0, int p,
                            const char *label) {
    printf("\n%s (base 30, p = %d, m0 = %lld)\n\n", label, p, m0);
    printf("  %-8s %6s  %10s  %6s  %12s  %10s  %10s\n",
           "Note", "m/m0", "m", "P-sup", "beta", "lattice", "error");
    printf("  %-8s %6s  %10s  %6s  %12s  %10s  %10s\n",
           "--------", "------", "----------", "------",
           "------------", "----------", "----------");

    for (int i = 0; i < n; i++) {
        printf("  %-8s %2d/%-3d  %10lld  %4s    %12.6f  %10.6f  %10.2e\n",
               rows[i].name, rows[i].num, rows[i].den, rows[i].m,
               rows[i].supported ? "yes" : "NO",
               rows[i].beta, rows[i].lattice, rows[i].error);
    }
}

static void show_scale_alpha(const ScaleRow *rows, int n, long long m0, int p,
                             const char *label) {
    double limit = alignment_limit_for_prime(p);
    printf("\n%s (alpha form, base 30, p = %d, m0 = %lld)\n\n", label, p, m0);
    printf("  %-8s %6s  %10s  %6s  %10s  %12s  %10s\n",
           "Note", "m/m0", "m", "P-sup", "alpha", "delta", "beta");
    printf("  %-8s %6s  %10s  %6s  %10s  %12s  %10s\n",
           "--------", "------", "----------", "------",
           "----------", "------------", "----------");

    for (int i = 0; i < n; i++) {
        printf("  %-8s %2d/%-3d  %10lld  %4s    %10.6f  %12.6e  %10.6f\n",
               rows[i].name, rows[i].num, rows[i].den, rows[i].m,
               rows[i].supported ? "yes" : "NO",
               rows[i].alpha, limit - rows[i].alpha, rows[i].beta);
    }
}

static void show_scale_csv(const ScaleRow *rows, int n, long long m0, int p,
                           const char *label) {
    const char *form = strstr(label, "Chromatic") ? "chromatic" : "major";
    for (int i = 0; i < n; i++) {
        printf("%s,%lld,%d,%s,%s,%d,%d,%lld,%d,%.10f,%.10e,%.10f,%.10f,%.10e\n",
               form, m0, p, rows[i].name, rows[i].supported ? "yes" : "no",
               rows[i].num, rows[i].den, rows[i].m, 30, rows[i].alpha,
               rows[i].deficit, rows[i].beta, rows[i].lattice, rows[i].error);
    }
}

static void show_scale(const Interval *scale, int n, long long m0, int p,
                       const char *label, int alpha_form, int csv) {
    ScaleRow rows[16];
    build_rows(scale, n, m0, p, rows);

    if (csv) {
        show_scale_csv(rows, n, m0, p, label);
        return;
    }

    if (alpha_form)
        show_scale_alpha(rows, n, m0, p, label);
    else
        show_scale_beta(rows, n, m0, p, label);
}

void scale_print(int chromatic_flag, int alpha_form, int csv) {
    int p = 29;  /* 30 ≡ 1 mod 29 */

    if (csv) {
        printf("form,m0,p,note,supported,num,den,m,base30,alpha,deficit,beta,lattice,error\n");
    } else {
        printf("The Alignment Deficit Lattice — Musical Intervals\n");
        printf("Base 30 = 2 × 3 × 5.  Prime p = 29 (since 30 ≡ 1 mod 29).\n");
        printf("Stable beta form uses the residual lattice coordinate\n");
        printf("  beta(m) = delta(m0)/delta(m)\n");
        printf("with delta(m) = (p-2)/(p(pm-1)).\n");
        if (alpha_form) {
            printf("Alpha form is shown for comparison only:\n");
            printf("  alpha(pm) = (2m-1)/(pm-1),  limit = 2/p.\n");
        }
    }

    /* Major scale: m0 = 24 works for all denominators */
    show_scale(major_scale, 8, 24, p, "Just Major Scale (8 tones)", alpha_form, csv);

    if (chromatic_flag) {
        /* Chromatic: need m0 divisible by lcm(1..32) = 480 */
        show_scale(chromatic, 13, 480, p, "Just Chromatic Scale (12 tones)", alpha_form, csv);
    }

    if (csv)
        return;

    /* Show convergence */
    printf("\nConvergence (perfect fifth, ratio 3/2):\n\n");
    printf("  %10s  %16s  %10s\n", "m0", "beta ratio", "error");
    long long m0s[] = {24, 240, 2400, 24000, 240000, 2400000};
    for (int i = 0; i < 6; i++) {
        long long m0 = m0s[i];
        long long m1 = m0 * 3 / 2;
        double d0 = deficit_alignment((int)m0, p);
        double d1 = deficit_alignment((int)m1, p);
        double ratio = d0 / d1;
        double err = fabs(ratio - 1.5) / 1.5;
        printf("  %10lld  %16.10f  %10.2e\n", m0, ratio, err);
    }
    printf("\n  Exact in the limit.\n");
    printf("  The beta coordinate is the lattice readout used by the scale table.\n");
}
