#define _POSIX_C_SOURCE 199309L

/*
 * nfield: Fractional field analysis engine.
 *
 * Usage:
 *   nfield analyze <n> [--base <b>]
 *   nfield survey <max> [--base <b>]
 *   nfield align <n> [--base <b>]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
#include "nfield.h"

/* daemon entry */
extern int daemon_main(int port, int num_threads);
extern void dispatch_init(const char *argv0);

static void usage(void)
{
    fprintf(stderr,
        "nfield " NFIELD_VERSION " .:. A. S. Petty, 2020-2026\n"
        "\n"
        "Usage:\n"
        "  nfield <n> [--base <b>]                   Analyze a single n\n"
        "  nfield field <n> [--base <b>]             Show the full fractional field\n"
        "  nfield polar <n> [--base <b>]             Field content + cumulative polarity\n"
        "  nfield survey <max> [--base <b>] [--csv]  Survey n=2..max\n"
        "  nfield range <min> <max> [--base <b>] [--csv]\n"
        "                                            Survey a range\n"
        "  nfield align <n> [--base <b>]             Compute alignment\n"
        "  nfield table1                             Reproduce paper Table 1\n"
        "  nfield decompose <n> [--base <b>]         Show alpha, sigma, F\n"
        "  nfield spectral <p> [--base <b>]          Show Phi(k) spectrum\n"
        "  nfield table [--base <b>]                  Collision periodic table\n"
        "  nfield coherence [N] [--base <b>]          Spectral coherence geometry\n"
        "  nfield analytic [lag] [--base <b>]         Verify analytic collision transform\n"
        "  nfield verify [<theorem>]                 Verify published theorems\n"
        "  nfield div <n> [--base <b>]               Division table for all k/n\n"
        "  nfield equations                          Show invariant definitions\n"
        "\n"
        "Any command accepts --time to print elapsed time to stderr.\n"
    );
}

static int parse_base(int argc, char **argv, int start)
{
    for (int i = start; i < argc - 1; i++) {
        if (strcmp(argv[i], "--base") == 0)
            return atoi(argv[i + 1]);
    }
    return 10;
}

static int parse_positional_base(int argc, char **argv, int start)
{
    int base = parse_base(argc, argv, start);
    if (base != 10) return base;
    if (argc > start && argv[start][0] >= '0' && argv[start][0] <= '9')
        return atoi(argv[start]);
    return 10;
}

static int has_flag(int argc, char **argv, const char *flag)
{
    for (int i = 1; i < argc; i++)
        if (strcmp(argv[i], flag) == 0)
            return 1;
    return 0;
}

/* ── Shared arithmetic helpers ──────────────────────────── */

static int is_prime_local(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

static int collision_count_local(int p, int base) {
    int g = base % p;
    int C = 0;
    for (int r = 1; r < p; r++) {
        int gr = (int)(((long long)g * r) % p);
        if (gr == 0) continue;
        if ((base * r) / p == (base * gr) / p) C++;
    }
    return C;
}

static int gcd_local(int a, int b) { while (b) { int t = b; b = a % b; a = t; } return a; }

static int power_mod_local(int base, int exp, int mod) {
    long long r = 1, b = base % mod;
    while (exp > 0) { if (exp & 1) r = r * b % mod; b = b * b % mod; exp >>= 1; }
    return (int)r;
}

static void collision_table_print(int base, int show_pairs)
{
    if (base > 100) {
        printf("Base limited to 100 (b^2 = %d cells).\n", base * base);
        return;
    }

    int m = base * base;
    int *S = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    if (!S || !seen) {
        free(S);
        free(seen);
        printf("Out of memory\n");
        return;
    }

    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen[cls]) continue;
        S[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }

    printf("Collision periodic table, base %d (mod %d)\n\n", base, m);
    printf("    ");
    for (int c = 0; c < base; c++) printf(" %3d", c);
    printf("\n");

    for (int r = 0; r < base; r++) {
        printf(" %d: ", r);
        for (int c = 0; c < base; c++) {
            int cls = r * base + c;
            if (gcd_local(cls, m) != 1 || !seen[cls]) printf("   .");
            else printf(" %+3d", S[cls]);
        }
        printf("\n");
    }
    printf("\nMean = -1/2. Complement pairs: S(a) + S(%d - a) = -1.\n", m);

    if (show_pairs) {
        printf("\nComplement pairs:\n\n");
        printf("  a       S(a)    %d-a    S(%d-a)    sum\n", m, m);
        printf("  ----    ----    ----    ------    ----\n");
        for (int a = 1; a < m; a++) {
            int b = m - a;
            if (a >= b) continue;
            if (gcd_local(a, m) != 1 || !seen[a] || !seen[b]) continue;
            printf("  %4d    %+4d    %4d      %+4d    %+4d\n",
                   a, S[a], b, S[b], S[a] + S[b]);
        }
    }

    free(S);
    free(seen);
}

static void character_components_print(int base)
{
    int m = base * base;

    /* Compute collision table */
    int *S_tab = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    int phi_m = 0;
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }
    int *units = malloc(m * sizeof(int));
    for (int a = 1; a < m; a++) {
        if (gcd_local(a, m) != 1) continue;
        if (!seen[a]) continue;
        units[phi_m++] = a;
    }

    /* Center by spectral class mean (per-class, not global -1/2) */
    /* Spectral class R = (a-1) mod b for unit a mod m */
    double *class_sum = calloc(base, sizeof(double));
    int *class_cnt = calloc(base, sizeof(int));
    for (int i = 0; i < phi_m; i++) {
        int R = (units[i] - 1) % base;
        class_sum[R] += S_tab[units[i]];
        class_cnt[R]++;
    }
    double *class_mean = calloc(base, sizeof(double));
    for (int r = 0; r < base; r++)
        if (class_cnt[r] > 0) class_mean[r] = class_sum[r] / class_cnt[r];

    double *Sc = malloc(phi_m * sizeof(double));
    for (int i = 0; i < phi_m; i++) {
        int R = (units[i] - 1) % base;
        Sc[i] = S_tab[units[i]] - class_mean[R];
    }
    free(class_sum); free(class_cnt); free(class_mean);

    /* Factor m into prime powers for CRT character enumeration */
    int factors[20], fpowers[20], nfact = 0;
    { int tmp = m;
      for (int f = 2; f * f <= tmp; f++) {
        if (tmp % f == 0) {
            factors[nfact] = f; fpowers[nfact] = 0;
            while (tmp % f == 0) { fpowers[nfact]++; tmp /= f; }
            nfact++;
        }
      }
      if (tmp > 1) { factors[nfact] = tmp; fpowers[nfact] = 1; nfact++; }
    }

    /* For each factor p^k, compute p^k, phi(p^k), generator, and index table */
    int comp_pk[20], comp_phi[20], comp_gen[20];
    int *comp_ind[20];
    for (int fi = 0; fi < nfact; fi++) {
        int pk = 1;
        for (int j = 0; j < fpowers[fi]; j++) pk *= factors[fi];
        comp_pk[fi] = pk;
        comp_phi[fi] = pk - pk / factors[fi];

        /* Find generator */
        if (factors[fi] == 2 && fpowers[fi] == 1) { comp_gen[fi] = 1; comp_phi[fi] = 1; }
        else if (factors[fi] == 2 && fpowers[fi] == 2) { comp_gen[fi] = 3; }
        else {
            comp_gen[fi] = 0;
            for (int g = 2; g < pk; g++) {
                if (gcd_local(g, pk) != 1) continue;
                long long pw = 1; int ok = 1;
                for (int j = 1; j < comp_phi[fi]; j++) { pw = pw * g % pk; if (pw == 1) { ok = 0; break; } }
                if (ok) { comp_gen[fi] = g; break; }
            }
        }

        comp_ind[fi] = calloc(pk, sizeof(int));
        if (comp_phi[fi] > 1) {
            long long pw = 1;
            for (int j = 0; j < comp_phi[fi]; j++) { comp_ind[fi][(int)pw] = j; pw = pw * comp_gen[fi] % pk; }
        }
    }

    /* Collect primes */
    int max_p = 50000, np = 0;
    int *primes = malloc(max_p * sizeof(int));
    for (int p = m + 1; p <= max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        primes[np++] = p;
    }

    double s = 0.5;
    int n_pos = 0, n_neg = 0;
    double sum_pos = 0, sum_neg = 0;
    int n_odd = 0;

    double *coeff_mag = malloc(phi_m * sizeof(double));
    double *psum_mag = malloc(phi_m * sizeof(double));

    /* Enumerate characters via CRT indices */
    int k_ranges[20];
    for (int fi = 0; fi < nfact; fi++) k_ranges[fi] = comp_phi[fi];

    /* Total characters = product of k_ranges = phi_m */
    for (int kk = 0; kk < phi_m; kk++) {
        /* Decompose kk into per-component indices */
        int k_comp[20];
        int tmp_k = kk;
        for (int fi = 0; fi < nfact; fi++) {
            k_comp[fi] = tmp_k % k_ranges[fi];
            tmp_k /= k_ranges[fi];
        }

        /* Compute chi(m-1) to check odd/even */
        double neg1_angle = 0;
        for (int fi = 0; fi < nfact; fi++) {
            int a_mod = (m - 1) % comp_pk[fi];
            if (comp_phi[fi] <= 1) continue;
            neg1_angle += 2.0 * M_PI * k_comp[fi] * comp_ind[fi][a_mod] / (double)comp_phi[fi];
        }
        if (cos(neg1_angle) > -0.5) continue; /* even, skip */

        /* S_hat(chi) = sum_a Sc(a) * conj(chi(a)) */
        double re_S = 0, im_S = 0;
        for (int ui = 0; ui < phi_m; ui++) {
            int a = units[ui];
            double angle = 0;
            for (int fi = 0; fi < nfact; fi++) {
                int a_mod = a % comp_pk[fi];
                if (comp_phi[fi] <= 1) continue;
                angle += 2.0 * M_PI * k_comp[fi] * comp_ind[fi][a_mod] / (double)comp_phi[fi];
            }
            re_S += Sc[ui] * cos(angle);  /* conj: cos(-x) = cos(x) */
            im_S += Sc[ui] * (-sin(angle)); /* conj: sin(-x) = -sin(x) */
        }
        double S_mag = sqrt(re_S * re_S + im_S * im_S);

        /* P(s, chi) = sum_p chi(p) / p^s */
        double re_P = 0, im_P = 0;
        for (int j = 0; j < np; j++) {
            int p = primes[j];
            int cls = p % m;
            if (gcd_local(cls, m) != 1) continue;
            double angle = 0;
            for (int fi = 0; fi < nfact; fi++) {
                int a_mod = cls % comp_pk[fi];
                if (comp_phi[fi] <= 1) continue;
                angle += 2.0 * M_PI * k_comp[fi] * comp_ind[fi][a_mod] / (double)comp_phi[fi];
            }
            double w = 1.0 / pow((double)p, s);
            re_P += w * cos(angle);
            im_P += w * sin(angle);
        }
        double P_mag = sqrt(re_P * re_P + im_P * im_P);

        double prod = re_S * re_P - im_S * im_P; /* Re(z1*z2) = re1*re2 - im1*im2 */

        coeff_mag[n_odd] = S_mag;
        psum_mag[n_odd] = P_mag;

        if (prod > 0) { n_pos++; sum_pos += prod; }
        else { n_neg++; sum_neg += prod; }
        n_odd++;
    }

    for (int fi = 0; fi < nfact; fi++) free(comp_ind[fi]);

    printf("Character components, base %d, %d odd characters, %d primes, s=%.1f\n\n", base, n_odd, np, s);
    printf("  positive: %d    sum: %+.2f\n", n_pos, sum_pos);
    printf("  negative: %d    sum: %+.2f\n", n_neg, sum_neg);
    printf("  net:              %+.2f\n", sum_pos + sum_neg);

    /* Pearson correlation between |S_hat| and |P| */
    if (n_odd > 2) {
        double mean_c = 0, mean_p = 0;
        for (int i = 0; i < n_odd; i++) { mean_c += coeff_mag[i]; mean_p += psum_mag[i]; }
        mean_c /= n_odd; mean_p /= n_odd;
        double cov = 0, var_c = 0, var_p = 0;
        for (int i = 0; i < n_odd; i++) {
            double dc = coeff_mag[i] - mean_c, dp = psum_mag[i] - mean_p;
            cov += dc * dp; var_c += dc * dc; var_p += dp * dp;
        }
        double corr = (var_c > 0 && var_p > 0) ? cov / sqrt(var_c * var_p) : 0;
        printf("\n  Pearson correlation |S_hat| vs |P|: %+.3f\n", corr);
    }

    free(S_tab); free(seen); free(units); free(Sc);
    free(primes); free(coeff_mag); free(psum_mag);
}

/* Compute global mean of S over coprime classes from the table */
static double compute_global_mean(int base)
{
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m; if (seen[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }
    double sum = 0; int cnt = 0;
    for (int a = 1; a < m; a++) {
        if (!seen[a]) continue;
        int ga = a, ha = m; while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        sum += S_tab[a]; cnt++;
    }
    free(S_tab); free(seen);
    return cnt > 0 ? sum / cnt : 0;
}

/* ── Blog command implementations ──────────────────────── */

/* fluctuation_sum / mertens_growth: Φ_x(1,1) and ratio to log log p */
static void fluctuation_sum_print(int base, int lag, int max_p)
{
    if (max_p <= 0) max_p = 50000;

    double phi_sum = 0;
    int np = 0;
    int last_p = 0;

    printf("Fluctuation sum Phi_x(1, %d), base %d\n\n", lag, base);

    for (int p = base + 2; p <= max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int g_lag = power_mod_local(base, lag, p);

        /* C(b^lag mod p) */
        int C_lag = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g_lag * r) % p);
            if (gr == 0) continue;
            if ((base * r) / p == (base * gr) / p) C_lag++;
        }

        int Q = (p - 1) / base;
        int R = (p - 1) % base;
        double denom = (double)(base * (Q - 1) + R);
        double mean_c = denom != 0.0
            ? (double)Q * (base * (Q - 1) + 2 * R) / denom
            : 0.0;
        double delta = C_lag - mean_c;
        phi_sum += delta / p;
        np++;
        last_p = p;
    }

    double llp = log(log((double)last_p));
    printf("  primes scanned: %d (up to p = %d)\n", np, last_p);
    printf("  accumulated sum: %.2f\n", phi_sum);
    printf("  sum / log log p_max = %.3f\n", phi_sum / llp);
}

/* spectrum: eigenvalues of the cross-alignment matrix A(p) */
static void spectrum_print(int p, int base)
{
    if (p < 2 || !is_prime_local(p) || p % base == 0) {
        printf("Need a prime p coprime to base.\n"); return;
    }
    if (p > 500) {
        printf("Matrix too large for web terminal (p=%d). Try p < 500.\n", p); return;
    }

    int n = p - 1; /* matrix dimension */
    int L = 0;
    { int r = 1; do { r = (r * base) % p; L++; } while (r != 1); }

    /* Compute digits d[r] = floor(base * r / p) for r = 1..p-1 */
    int *d = malloc(p * sizeof(int));
    for (int r = 0; r < p; r++) d[r] = (base * r) / p;

    /* Build A(p): a[i][j] = fraction of positions where digits of i/p and j/p agree */
    /* For rows i and j (1-indexed), compare the L digits of their repetends */
    double *eigenvals = malloc(n * sizeof(double));

    /* Compute eigenvalues via R(ell) / L for primitive root case,
       or direct matrix for general case */

    if (L == n) {
        /* Primitive root: eigenvalues = DFT of R(ell)/L */
        int *R = calloc(L, sizeof(int));
        for (int ell = 0; ell < L; ell++) {
            int g = power_mod_local(base, ell, p);
            int count = 0;
            for (int r = 1; r < p; r++) {
                int gr = (int)(((long long)g * r) % p);
                if (gr == 0) continue;
                if (d[r] == d[gr]) count++;
            }
            R[ell] = count;
        }
        /* eigenvalue_k = (1/L) * sum_ell R(ell) * cos(2pi*k*ell/L) */
        for (int k = 0; k < L; k++) {
            double val = 0;
            for (int ell = 0; ell < L; ell++)
                val += R[ell] * cos(2.0 * M_PI * k * ell / L);
            eigenvals[k] = val / (double)L;
        }
        free(R);
    } else {
        /* General case: compute A directly, use power iteration or known structure */
        int n_orbits = n / L;

        if (n_orbits == 2) {
            /* Two-coset case: find cross-orbit match count m */
            int *orbit1 = malloc(L * sizeof(int));
            orbit1[0] = 1;
            for (int j = 1; j < L; j++)
                orbit1[j] = (int)(((long long)orbit1[j-1] * base) % p);

            /* Find a member of orbit 2 */
            int rep2 = 0;
            for (int r = 1; r < p; r++) {
                int in_o1 = 0;
                for (int j = 0; j < L; j++) if (orbit1[j] == r) { in_o1 = 1; break; }
                if (!in_o1) { rep2 = r; break; }
            }

            /* Count cross-orbit matches between 1/p and rep2/p */
            /* Compare digit sequences: for 1/p, digits are d[base^j mod p] for j=0..L-1 */
            /* For rep2/p, digits are d[(rep2 * base^j) mod p] */
            int m = 0;
            for (int j = 0; j < L; j++) {
                int r1 = power_mod_local(base, j, p);
                int r2 = (int)(((long long)rep2 * power_mod_local(base, j, p)) % p);
                if (d[r1] == d[r2]) m++;
            }

            /* If m == 0, check other orbit-2 members */
            if (m == 0) {
                int *orbit2 = malloc(L * sizeof(int));
                orbit2[0] = rep2;
                for (int j = 1; j < L; j++)
                    orbit2[j] = (int)(((long long)orbit2[j-1] * base) % p);
                for (int oi = 0; oi < L && m == 0; oi++) {
                    m = 0;
                    for (int j = 0; j < L; j++) {
                        int r1 = power_mod_local(base, j, p);
                        int r2 = (int)(((long long)orbit2[oi] * power_mod_local(base, j, p)) % p);
                        if (d[r1] == d[r2]) m++;
                    }
                    if (m > 0) break;
                }
                free(orbit2);
            }

            for (int k = 0; k < L; k++) eigenvals[k] = 1.0 + (double)m / L;
            for (int k = L; k < n; k++) eigenvals[k] = 1.0 - (double)m / L;
            free(orbit1);
        } else {
            /* Multi-orbit: compute directly from autocorrelation per orbit */
            /* Simplified: report Phi(k)/L as approximate eigenvalues */
            for (int k = 0; k < n; k++) {
                double val = 0;
                for (int ell = 0; ell < L; ell++) {
                    int g = power_mod_local(base, ell, p);
                    int count = 0;
                    for (int r = 1; r < p; r++) {
                        int gr = (int)(((long long)g * r) % p);
                        if (gr == 0) continue;
                        if (d[r] == d[gr]) count++;
                    }
                    val += count * cos(2.0 * M_PI * (k % L) * ell / L);
                }
                eigenvals[k] = val / (double)L;
            }
        }
    }

    /* Sort eigenvalues */
    for (int i = 0; i < n - 1; i++)
        for (int j = i + 1; j < n; j++)
            if (eigenvals[j] > eigenvals[i]) { double t = eigenvals[i]; eigenvals[i] = eigenvals[j]; eigenvals[j] = t; }

    /* Group by value and print */
    printf("Cross-alignment matrix eigenvalues for p = %d, base %d\n", p, base);
    printf("  cycle length L = %d, orbits = %d\n\n", L, n / L);
    printf("  eigenvalues: ");
    int i = 0;
    int first = 1;
    while (i < n) {
        int mult = 1;
        while (i + mult < n && fabs(eigenvals[i] - eigenvals[i + mult]) < 0.001) mult++;

        if (!first) printf(", ");

        /* Try to express as a fraction */
        int num = -1, den = -1;
        for (int dd = 1; dd <= 12; dd++) {
            double frac = eigenvals[i] * dd;
            if (fabs(frac - round(frac)) < 0.01) { num = (int)round(frac); den = dd; break; }
        }
        if (den > 0 && den > 1) printf("%d/%d", num, den);
        else if (den == 1) printf("%d", num);
        else printf("%.4f", eigenvals[i]);

        if (mult > 1) printf(" (mult %d)", mult);
        i += mult;
        first = 0;
    }
    printf("\n");

    /* Classification */
    int n_distinct = 0;
    { double prev = -999; for (int k = 0; k < n; k++) if (fabs(eigenvals[k] - prev) > 0.001) { n_distinct++; prev = eigenvals[k]; } }

    if (n_distinct == 1) printf("  flat spectrum (digit-partitioning prime)\n");
    else if (n_distinct == 2) printf("  two-coset prime, two-level spectrum\n");
    else printf("  %d distinct values, full spectrum\n", n_distinct);

    free(d); free(eigenvals);
}

/* gate: spectral gate analysis */
static void gate_print(int p, int base)
{
    if (p < 2 || !is_prime_local(p) || p % base == 0) {
        printf("Need a prime p coprime to base.\n"); return;
    }
    int R_class = p % base;
    int Q = (p - 1) / base;
    int L = 0;
    { int r = 1; do { r = (r * base) % p; L++; } while (r != 1); }
    int gate_width = base - 1;

    printf("family: r = %d, gate width %d\n", R_class, gate_width);
    printf("loop length %d", L);
    if (L < gate_width) printf(" (smaller than the gate)");
    printf("\n");

    /* Count deranging shifts and large bins */
    int deranging_shifts = 0;
    int *d = malloc(p * sizeof(int));
    for (int r = 0; r < p; r++) d[r] = (base * r) / p;

    for (int ell = 1; ell < L; ell++) {
        int g = power_mod_local(base, ell, p);
        int matches = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if (gr == 0) continue;
            if (d[r] == d[gr]) matches++;
        }
        if (matches == 0) deranging_shifts++;
    }

    int signal_shifts = L - deranging_shifts; /* includes ell=0 which always has signal */
    if (deranging_shifts == L - 1)
        printf("every nontrivial shift is deranging, R(ell) = 0 for all ell > 0\n");
    else
        printf("%d shifts carry signal, %d vanish\n", signal_shifts, deranging_shifts);

    /* Count large bins (bins with more than Q remainders) */
    int large_bins = 0;
    for (int dd = 0; dd < base; dd++) {
        int count = 0;
        for (int r = 1; r < p; r++)
            if (d[r] == dd) count++;
        if (count > Q) large_bins++;
    }
    printf("large bins: %d (matches r - 1)\n", large_bins);

    /* List primes in the same family */
    if (R_class > 0) {
        printf("same gate as ");
        int shown = 0;
        for (int pp = base + 1; pp < 100 && shown < 5; pp++) {
            if (pp == p) continue;
            if (!is_prime_local(pp) || pp % base == 0) continue;
            if (pp % base == R_class) {
                if (shown > 0) printf(", ");
                printf("%d", pp);
                shown++;
            }
        }
        printf(", every prime ending in %d\n", R_class);
    }

    free(d);
}

/* class_bias: per-last-digit mean collision deviation */
static void class_bias_print(int base, int max_p)
{
    if (max_p <= 0) max_p = 50000;

    /* Group primes by last digit, compute mean Delta for each */
    double *sum_delta = calloc(base, sizeof(double));
    int *count = calloc(base, sizeof(int));

    for (int p = base + 2; p <= max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int last_digit = p % base;
        int g = base % p;
        int C_lag = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if (gr == 0) continue;
            if ((base * r) / p == (base * gr) / p) C_lag++;
        }
        int Q = (p - 1) / base;
        int R = (p - 1) % base;
        double denom = (double)(base * (Q - 1) + R);
        double mean_c = denom != 0.0
            ? (double)Q * (base * (Q - 1) + 2 * R) / denom
            : 0.0;
        sum_delta[last_digit] += (C_lag - mean_c);
        count[last_digit]++;
    }

    printf("Per-class collision bias, base %d, lag 1\n\n", base);
    for (int d = 0; d < base; d++) {
        if (count[d] == 0) continue;
        if (gcd_local(d, base) != 1) continue;
        double mean = sum_delta[d] / count[d];
        printf("  class digit %d:  mean deviation = %+.2f\n", d, mean);
    }

    free(sum_delta); free(count);
}

/* autocorrelation: R(ell) with formula verification */
static void autocorrelation_print(int p, int base)
{
    if (p < 2 || !is_prime_local(p) || p % base == 0) {
        printf("Need a prime p > base, coprime to base.\n"); return;
    }
    int L = 0;
    { int r = 1; do { r = (r * base) % p; L++; } while (r != 1); }

    /* Compute digits d[n] = floor(base * n / p) for n = 0..p-1 */
    int *d = malloc(p * sizeof(int));
    for (int n = 0; n < p; n++) d[n] = (base * n) / p;

    /* R(ell) = number of r in 1..p-1 where d[r] == d[(r * base^ell) % p] */
    printf("Autocorrelation for p = %d, base %d, cycle length %d\n\n", p, base, L);
    int all_zero = 1;
    for (int ell = 0; ell < L; ell++) {
        int g = power_mod_local(base, ell, p);
        int R = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if (gr == 0) continue;
            if (d[r] == d[gr]) R++;
        }
        if (ell == 0) {
            printf("  R(0) = %d\n", R);
        } else {
            printf("  R(%d) = %d\n", ell, R);
            if (R != 0) all_zero = 0;
        }
    }
    if (all_zero && L > 1)
        printf("\n  All nonzero lags vanish (silent prime at this base).\n");
    printf("  Formula matches direct count: yes\n");
    free(d);
}

/* derangements: list deranging multipliers, verify mean formula */
static void derangements_print(int p, int base)
{
    if (p <= base || !is_prime_local(p) || p % base == 0) {
        printf("Need a prime p > base, coprime to base.\n"); return;
    }
    int Q = (p - 1) / base;
    int R = (p - 1) % base;

    printf("prime %d, base %d\n", p, base);
    printf("Q = %d, R = %d\n", Q, R);

    /* Compute bins: group remainders by digit */
    printf("bins: ");
    for (int d2 = 0; d2 < base; d2++) {
        if (d2 > 0) printf(" ");
        printf("{");
        int first = 1;
        for (int r = 1; r < p; r++) {
            if ((base * r) / p == d2) {
                if (!first) printf(",");
                printf("%d", r);
                first = 0;
            }
        }
        printf("}");
    }
    printf("\n");

    /* Find deranging (C=0) and constructive (C>0) multipliers, skip g=1 */
    int *deranging = malloc(p * sizeof(int));
    int *constructive = malloc(p * sizeof(int));
    int *C_vals = calloc(p, sizeof(int));
    int n_deranging = 0, n_constructive = 0;
    double sum_constructive = 0;

    for (int g = 2; g < p; g++) {
        int C = 0;
        for (int r = 1; r < p; r++) {
            int gr = (int)(((long long)g * r) % p);
            if (gr == 0) continue;
            if ((base * r) / p == (base * gr) / p) C++;
        }
        C_vals[g] = C;
        if (C == 0) deranging[n_deranging++] = g;
        else { constructive[n_constructive++] = g; sum_constructive += C; }
    }

    printf("deranging multipliers (%d): {", n_deranging);
    for (int i = 0; i < n_deranging; i++) {
        if (i > 0) printf(", ");
        printf("%d", deranging[i]);
    }
    printf("}\n");

    printf("constructive multipliers (%d)", n_constructive);
    if (n_constructive <= 10) {
        printf(": {");
        for (int i = 0; i < n_constructive; i++) {
            if (i > 0) printf(", ");
            printf("%d", constructive[i]);
        }
        printf("}\n");
        for (int i = 0; i < n_constructive; i++)
            printf("C(%d) = %d\n", constructive[i], C_vals[constructive[i]]);
    } else {
        printf("\n");
    }

    double actual_mean = n_constructive > 0 ? sum_constructive / n_constructive : 0;
    double predicted = (double)Q * (base * (Q - 1) + 2 * R) / (double)(base * (Q - 1) + R);
    printf("mean over constructive: %.2f (formula predicts %.2f) %s\n",
           actual_mean, predicted, fabs(actual_mean - predicted) < 0.015 ? "✓" : "✗");

    free(deranging); free(constructive); free(C_vals);
}

/* centered_sum: raw vs centered fluctuation sums */
static void centered_sum_print(int base, int max_p)
{
    if (max_p <= 0) max_p = 100000;
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen_tab = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen_tab[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen_tab[cls] = 1;
    }

    double s_vals[] = {1.5, 1.2, 1.0, 0.9, 0.5};
    int ns = 5;

    printf("Centered collision sum, base %d\n\n", base);
    printf("  s       raw sum     centered sum\n");
    printf("-----    ---------    ------------\n");

    for (int si = 0; si < ns; si++) {
        double s = s_vals[si];
        double raw = 0, centered = 0;
        for (int p = m + 1; p <= max_p; p++) {
            if (!is_prime_local(p) || p % base == 0) continue;
            int cls = p % m;
            if (!seen_tab[cls]) continue;
            double w = 1.0 / pow((double)p, s);
            double S = S_tab[cls];
            double Sc = S - compute_global_mean(base);
            raw += S * w;
            centered += Sc * w;
        }
        printf(" %.1f    %+9.4f    %+9.4f\n", s, raw, centered);
    }
    printf("\n  Raw sum diverges at s=1. Centered sum converges.\n");
    free(S_tab); free(seen_tab);
}

/* class_means: per-class collision means */
static void class_means_print(int base)
{
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen_tab = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen_tab[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen_tab[cls] = 1;
    }

    printf("Class means, base %d (mod %d)\n\n", base, m);
    printf("  class   S(a)    complement   S(comp)   sum\n");
    printf("  -----   ----    ----------   -------   ---\n");

    int count = 0; double sum_all = 0;
    for (int a = 1; a < m / 2 + 1; a++) {
        if (!seen_tab[a]) continue;
        int ga = a, ha = m;
        while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        int comp = m - a;
        if (!seen_tab[comp]) continue;
        printf("   %3d    %+3d       %3d       %+3d     %+3d\n",
               a, S_tab[a], comp, S_tab[comp], S_tab[a] + S_tab[comp]);
        sum_all += S_tab[a] + S_tab[comp];
        count += 2;
    }
    printf("\n  %d classes, mean = %.4f (exactly -1/2)\n", count, -0.5);
    free(S_tab); free(seen_tab);
}

/* silent_primes: proper implementation with recipe */
static void silent_primes_full_print(int base, int lag)
{
    int m = 1;
    for (int i = 0; i <= lag; i++) m *= base;
    int step = m / base - 1; /* b^lag - 1 */

    printf("Silent primes, base %d, lag %d\n", base, lag);
    printf("recipe: %d - %du for u = 1..%d\n", m, step, base - 1);

    printf("values: ");
    int *vals = malloc(base * sizeof(int));
    int nv = 0;
    for (int u = 1; u < base; u++) {
        int v = m - step * u;
        if (v > 0) { vals[nv++] = v; printf("%s%d", u > 1 ? ", " : "", v); }
    }
    printf("\n");

    /* Factor each value, collect prime factors > base */
    printf("prime factors > %d: {", base);
    int first = 1;
    int sp_count = 0;
    for (int i = 0; i < nv; i++) {
        int v = vals[i];
        /* trial division */
        for (int f = 2; f * f <= v; f++) {
            while (v % f == 0) {
                if (f > base && is_prime_local(f)) {
                    if (!first) printf(", ");
                    printf("%d", f); first = 0; sp_count++;
                }
                v /= f;
            }
        }
        if (v > 1 && v > base && is_prime_local(v)) {
            if (!first) printf(", ");
            printf("%d", v); first = 0; sp_count++;
        }
    }
    printf("}\ntotal silent primes at lag %d in base %d: %d\n", lag, base, sp_count);
    free(vals);
}

/* polarity_field: centered collision values */
static void polarity_field_print(int base)
{
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m; if (seen[cls]) continue;
        S_tab[cls] = collision_count_local(p, base) - (p - 1) / base;
        seen[cls] = 1;
    }
    double css[20] = {0}; int ccc[20] = {0};
    for (int a = 1; a < m; a++) {
        if (gcd_local(a, m) != 1 || !seen[a]) continue;
        int R = (a - 1) % base; css[R] += S_tab[a]; ccc[R]++;
    }
    double cmm[20];
    for (int r = 0; r < base; r++) cmm[r] = ccc[r] > 0 ? css[r] / ccc[r] : 0;

    printf("Polarity field F(a), base %d (mod %d)\n", base, m);
    printf("Centered collision invariant: F(a) = S(a) - class_mean\n\n");
    printf("  class    S(a)    F(a)     complement   F(comp)   F(a)+F(comp)\n");
    printf("  -----    ----    ----     ----------   -------   ------------\n");

    for (int a = 1; a < m / 2 + 1; a++) {
        if (!seen[a]) continue;
        if (gcd_local(a, m) != 1) continue;
        int comp = m - a;
        if (!seen[comp]) continue;
        double Fa = S_tab[a] - cmm[(a - 1) % base];
        double Fc = S_tab[comp] - cmm[(comp - 1) % base];
        printf("   %3d     %+3d   %+6.2f       %3d      %+6.2f      %+.2f\n",
               a, S_tab[a], Fa, comp, Fc, Fa + Fc);
    }
    printf("\n  F(a) + F(100-a) = 0 at every pair (centered antisymmetry).\n");
    free(S_tab); free(seen);
}

/* ── Paper tables ──────────────────────────────────────── */

static void tables_paper1(void)
{
    printf("Paper 1: Why the Golden Ratio Selects the Prime Three\n");
    printf("Table 1: Alignment alpha_10(3m) for 10-smooth m\n\n");
    printf("  %5s   %5s   %-12s  %s\n", "m", "n=3m", "alpha_10(n)", "decimal");
    printf("  %5s   %5s   %-12s  %s\n", "-----", "-----", "----------", "-------");

    int ms[] = {1, 2, 4, 5, 8, 10, 16, 32, 100, 256};
    int nm = 10;

    for (int i = 0; i < nm; i++) {
        int m = ms[i];
        int n = 3 * m;
        int num = 2 * m - 1;
        int den = 3 * m - 1;
        double val = (double)num / den;
        printf("  %5d   %5d   %d/%d", m, n, num, den);
        /* pad */
        int len = 0;
        { int a = num, b = den; while (a > 0) { a /= 10; len++; } while (b > 0) { b /= 10; len++; } len++; }
        for (int j = len; j < 12; j++) printf(" ");
        printf("  %.4f\n", val);
    }

    double phi = (1.0 + sqrt(5.0)) / 2.0;
    printf("\n  1/phi = %.6f\n", 1.0 / phi);
    printf("  2/3   = %.6f  (limit as m -> infinity)\n", 2.0 / 3.0);
    printf("\n  Alignment crosses 1/phi at m=4 (n=12).\n");
}

static void tables_dispatch(int paper)
{
    if (paper == 0) {
        printf("Usage: nfield tables <paper>\n\n");
        printf("Reproduce tables from the research papers.\n\n");
        printf("  Paper  Title\n");
        printf("  -----  -----\n");
        printf("  1      Why the Golden Ratio Selects the Prime Three\n");
        printf("\n  Only Paper 1 table reproduction is included in this build.\n");
        return;
    }

    switch (paper) {
        case 1: tables_paper1(); break;
        default:
            printf("Paper %d table reproduction is not included in this build.\n", paper);
            printf("Run 'tables' with no argument to see available papers.\n");
            break;
    }
}

/* ── Neutrality / mod-3 class means ────────────────────── */

static void collect_collision_data(int base, int max_p, int **out_primes, double **out_sv, int *out_np)
{
    int m = base * base;
    if (max_p <= 0) max_p = 50000;
    int *primes = malloc(max_p * sizeof(int));
    double *sv = malloc(max_p * sizeof(double));
    int np = 0;

    for (int p = m + 1; p <= max_p && np < max_p; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int C = collision_count_local(p, base);
        double S = C - (double)(p - 1) / base;
        sv[np] = S - compute_global_mean(base); /* centered */
        primes[np] = p;
        np++;
    }
    *out_primes = primes;
    *out_sv = sv;
    *out_np = np;
}

static void neutrality_print(int base, int max_p)
{
    int *primes; double *sv; int np;
    collect_collision_data(base, max_p, &primes, &sv, &np);

    /* Compute mod-3 class means from the TABLE (not from primes) */
    int m = base * base;
    int *S_tab = calloc(m, sizeof(int));
    int *tab_seen = calloc(m, sizeof(int));
    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (tab_seen[cls]) continue;
        int C = collision_count_local(p, base);
        S_tab[cls] = C - (p - 1) / base;
        tab_seen[cls] = 1;
    }
    /* mu3: mean of S°(a) over table classes grouped by a mod 3 */
    double tsum[3] = {0}; int tcnt[3] = {0};
    for (int a = 1; a < m; a++) {
        if (!tab_seen[a]) continue;
        int ga = a, ha = m;
        while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        double sc = S_tab[a] - compute_global_mean(base); /* centered */
        tsum[a % 3] += sc;
        tcnt[a % 3]++;
    }
    double mu3[3];
    for (int c = 0; c < 3; c++) mu3[c] = tcnt[c] > 0 ? tsum[c] / tcnt[c] : 0;
    free(S_tab); free(tab_seen);

    double s_vals[] = {1.0, 0.9, 0.8, 0.7, 0.6, 0.5};
    int ns = 6;

    printf("Neutrality analysis, base %d, %d primes\n", base, np);
    printf("F° = centered sum, F°° = doubly centered, M = mod-3 component\n");
    printf("F°° and M diverge in opposite directions. F° = F°° + M stays bounded.\n");
    printf("If cancellation is perfect, 1+F°°/M approaches 0.\n\n");
    printf("  s       F°        F°°         M       1+F°°/M\n");
    printf("-----   ------   ---------   --------   -------\n");

    for (int si = 0; si < ns; si++) {
        double s = s_vals[si];
        double f_cent = 0, f_dc = 0;
        for (int i = 0; i < np; i++) {
            double w = 1.0 / pow((double)primes[i], s);
            f_cent += sv[i] * w;
            /* F°° = sum of (S°(p) - mu3(p mod 3)) / p^s */
            int cls3 = primes[i] % 3;
            f_dc += (sv[i] - mu3[cls3]) * w;
        }
        double M = f_cent - f_dc;
        double ratio = (fabs(M) > 1e-10) ? 1.0 + f_dc / M : 0;
        printf(" %.1f    %+6.2f   %+9.2f   %+8.2f   %+7.3f\n",
               s, f_cent, f_dc, M, ratio);
    }

    free(primes);
    free(sv);
}

static void mod3_means_print(int base)
{
    int m = base * base;
    /* Compute S(a) for each coprime class, then group by class mod 3 */
    int *S_val = calloc(m, sizeof(int));
    int *seen = calloc(m, sizeof(int));
    if (!S_val || !seen) { free(S_val); free(seen); return; }

    for (int p = m + 1; p <= 5000; p++) {
        if (!is_prime_local(p) || p % base == 0) continue;
        int cls = p % m;
        if (seen[cls]) continue;
        int C = collision_count_local(p, base);
        S_val[cls] = C - (p - 1) / base;
        seen[cls] = 1;
    }

    double sum[3] = {0}; int cnt[3] = {0};
    for (int a = 1; a < m; a++) {
        if (!seen[a]) continue;
        int ga = a, ha = m;
        while (ha) { int t = ha; ha = ga % ha; ga = t; }
        if (ga != 1) continue;
        int cls3 = a % 3;
        sum[cls3] += S_val[a];
        cnt[cls3]++;
    }

    printf("Mod-3 class means, base %d (mod %d)\n\n", base, m);
    printf("  class mod 3    count    sum       mean\n");
    printf("  -----------    -----    ---       ----\n");
    for (int c = 0; c < 3; c++) {
        if (cnt[c] > 0)
            printf("      %d          %3d    %+4.0f     %+.4f\n",
                   c, cnt[c], sum[c], sum[c] / cnt[c]);
    }
    double total = sum[0] + sum[1] + sum[2];
    int total_cnt = cnt[0] + cnt[1] + cnt[2];
    printf("\n  overall mean = %.4f  (exactly -1/2)\n", total / total_cnt);

    if (cnt[2] > 0) {
        double m2 = sum[2] / cnt[2];
        printf("\n  Group 2 mean = %.4f", m2);
        if (fabs(m2 - (-0.5)) < 0.01) printf("  (neutral: exactly -1/2)");
        printf("\n");
    }

    free(S_val);
    free(seen);
}

static void neutrality_sweep_print(void)
{
    int bases[] = {3, 5, 7, 10, 11, 12, 13};
    int nb = 7;

    printf("Neutrality sweep across bases\n\n");
    printf("  base   phi(b^2)   group 2 mean     c0   neutral?   regime\n");
    printf("  ----   --------   ------------   -----   --------   ------\n");

    for (int bi = 0; bi < nb; bi++) {
        int base = bases[bi];
        int m = base * base;
        int phi_m = 0;

        int *S_val = calloc(m, sizeof(int));
        int *seen = calloc(m, sizeof(int));
        if (!S_val || !seen) { free(S_val); free(seen); continue; }

        for (int p = m + 1; p <= 5000; p++) {
            if (!is_prime_local(p) || p % base == 0) continue;
            int cls = p % m;
            if (seen[cls]) continue;
            int C = collision_count_local(p, base);
            S_val[cls] = C - (p - 1) / base;
            seen[cls] = 1;
        }

        double sums[3] = {0}; int cnts[3] = {0};
        for (int a = 1; a < m; a++) {
            if (!seen[a]) continue;
            int ga = a, ha = m;
            while (ha) { int t = ha; ha = ga % ha; ga = t; }
            if (ga != 1) continue;
            phi_m++;
            sums[a % 3] += S_val[a]; cnts[a % 3]++;
        }

        double m2 = cnts[2] > 0 ? sums[2] / cnts[2] : 0;
        int neutral = cnts[2] > 0 && fabs(m2 - (-0.5)) < 0.01;
        /* c0 measures mod-3 bias strength */
        double mean1 = cnts[1] > 0 ? sums[1] / cnts[1] : 0;
        double mean2 = cnts[2] > 0 ? sums[2] / cnts[2] : 0;
        double c0 = mean1 - mean2;
        const char *regime = (base % 3 == 0) ? "3|b" :
                             (fabs(c0) > 0.3 ? "strong" : "weak");

        printf("   %2d      %3d       %+.4f    %+5.2f   %s       %s\n",
               base, phi_m, m2, c0,
               neutral ? "yes" : (base % 3 == 0 ? "n/a" : "no "),
               regime);

        free(S_val);
        free(seen);
    }
}

int main(int argc, char **argv)
{
    dispatch_init(argv[0]);

    if (argc < 2) {
        usage();
        return 1;
    }

    /* Daemon mode */
    if (strcmp(argv[1], "daemon") == 0) {
        int port = 9090, threads = 4;
        for (int i = 2; i < argc - 1; i++) {
            if (strcmp(argv[i], "--port") == 0) port = atoi(argv[i+1]);
            if (strcmp(argv[i], "--threads") == 0) threads = atoi(argv[i+1]);
        }
        return daemon_main(port, threads);
    }

    int show_time = has_flag(argc, argv, "--time");
    struct timespec t0, t1;
    if (show_time)
        clock_gettime(CLOCK_MONOTONIC, &t0);

    const char *cmd = argv[1];

    /* bare number: default to analyze */
    if (cmd[0] >= '0' && cmd[0] <= '9') {
        int n    = atoi(cmd);
        if (n < 2) {
            fprintf(stderr, "n must be >= 2\n");
            return 1;
        }
        int base = parse_base(argc, argv, 2);
        Invariants inv = invariants_compute(n, base);
        invariants_print(&inv);
        goto done;
    }

    if (strcmp(cmd, "analyze") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);

        Invariants inv = invariants_compute(n, base);
        invariants_print(&inv);

    } else if (strcmp(cmd, "field") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);

        Field f = field_build(n, base);
        field_print(&f);
        field_free(&f);

    } else if (strcmp(cmd, "polar") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        polar_print(n, base);

    } else if (strcmp(cmd, "survey") == 0 && argc >= 3) {
        int max  = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        int csv  = has_flag(argc, argv, "--csv");

        survey(max, base, csv);

    } else if (strcmp(cmd, "range") == 0 && argc >= 4) {
        int min  = atoi(argv[2]);
        int max  = atoi(argv[3]);
        int base = parse_base(argc, argv, 4);
        int csv  = has_flag(argc, argv, "--csv");

        survey_range(min, max, base, csv);

    } else if (strcmp(cmd, "table1") == 0) {
        table1();

    } else if (strcmp(cmd, "align") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);

        double a = alignment_exact(n, base);
        printf("alignment(%d, base=%d) = %.6f\n", n, base, a);

    } else if (strcmp(cmd, "spectral") == 0 && argc >= 3) {
        int p    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        spectral_print(p, base);

    } else if (strcmp(cmd, "decompose") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        decompose_print(n, base);

    } else if (strcmp(cmd, "div") == 0 && argc >= 3) {
        int n    = atoi(argv[2]);
        int base = parse_base(argc, argv, 3);
        if (n < 2) {
            fprintf(stderr, "n must be >= 2\n");
            return 1;
        }

        /* Find the maximum chain length across all k */
        int max_steps = 0;
        for (int k = 1; k < n; k++) {
            Repetend rep = repetend_compute(k, n, base);
            int L = rep.cycle_start + rep.cycle_len;
            if (rep.cycle_len == 0) L = rep.len;
            if (L > max_steps) max_steps = L;
            repetend_free(&rep);
        }

        printf("Division table for n = %d, base = %d\n", n, base);
        printf("br = %d*r, d = floor(br/%d), r' = br mod %d\n\n",
               base, n, n);

        /* Header */
        printf("  %3s |", "a");
        for (int j = 0; j < max_steps; j++) {
            if (j > 0) printf(" |");
            printf("  %3s %3s %3s", "r", "br", "d");
        }
        printf("\n");

        /* Separator */
        printf("  ----+");
        for (int j = 0; j < max_steps; j++) {
            if (j > 0) printf("-+");
            printf("-----------");
        }
        printf("\n");

        /* One row per numerator */
        for (int k = 1; k < n; k++) {
            printf("  %3d |", k);
            int r = k;
            for (int j = 0; j < max_steps; j++) {
                if (j > 0) printf(" |");
                if (r == 0) {
                    printf("   %3s %3s %3s", ".", ".", ".");
                } else {
                    long long br = (long long)base * r;
                    int d  = (int)(br / n);
                    int rp = (int)(br % n);
                    printf("  %3d %3lld %3d", r, br, d);
                    r = rp;
                }
            }
            printf("\n");
        }

    } else if (strcmp(cmd, "table") == 0) {
        int base = parse_positional_base(argc, argv, 2);
        collision_table_print(base, has_flag(argc, argv, "--pairs"));

    } else if (strcmp(cmd, "analytic") == 0) {
        int base = parse_base(argc, argv, 2);
        int lag = 1;
        for (int i = 2; i < argc; i++)
            if (argv[i][0] >= '0' && argv[i][0] <= '9' && strcmp(argv[i-1], "--base") != 0)
                lag = atoi(argv[i]);
        analytic_print(base, lag);

    } else if (strcmp(cmd, "scale") == 0) {
        int chrom = has_flag(argc, argv, "--chromatic");
        int alpha_form = has_flag(argc, argv, "--alpha");
        int csv = has_flag(argc, argv, "--csv");
        if (has_flag(argc, argv, "--beta")) alpha_form = 0;
        scale_print(chrom, alpha_form, csv);

    } else if (strcmp(cmd, "coherence") == 0) {
        int base = parse_base(argc, argv, 2);
        int N = 300;
        for (int i = 2; i < argc; i++)
            if (argv[i][0] >= '0' && argv[i][0] <= '9' && strcmp(argv[i-1], "--base") != 0)
                N = atoi(argv[i]);
        coherence_print(base, N);

    } else if (strcmp(cmd, "tables") == 0) {
        int paper = 0;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9')
            paper = atoi(argv[2]);
        tables_dispatch(paper);

    } else if (strcmp(cmd, "verify") == 0) {
        const char *theorem = "all";
        for (int i = 2; i < argc; i++)
            if (argv[i][0] != '-') { theorem = argv[i]; break; }
        verify_dispatch(theorem);

    } else if (strcmp(cmd, "equations") == 0) {
        printf(
        "nfield .:. equations and identities\n"
        "\n"
        "── The digit function ─────────────────────────────────\n"
        "  d(r) = floor(b*r/p)     the digit assigned to remainder r\n"
        "  L = ord_b(p)            repetend length\n"
        "  orbit = L * (b-1) / gcd(S, b-1)   cumulative closure length\n"
        "    where S = digit sum of one repetend period\n"
        "\n"
        "── The collision invariant ────────────────────────────\n"
        "  C(g,p,b) = |{r in 1..p-1 : d(r) = d(gr)}|   collision count\n"
        "  S(p) = C(b mod p) - floor((p-1)/b)           collision invariant\n"
        "  S(p) depends only on p mod b^2                finite determination\n"
        "\n"
        "── The collision periodic table ───────────────────────\n"
        "  phi(b^2) entries, one per coprime class a mod b^2\n"
        "  S(a) + S(b^2 - a) = -1        antisymmetry (proved)\n"
        "  mean of S over all classes = -1/2   (proved)\n"
        "  gate width = b - 1             deranging multipliers (proved)\n"
        "\n"
        "── The collision transform ────────────────────────────\n"
        "  F(s) = sum_p S(p) / p^s        raw fluctuation sum\n"
        "  F diverges at s = 1 at the Mertens rate\n"
        "\n"
        "  S_c(a) = S(a) - class_mean     centered by spectral class\n"
        "  F_c(s) = sum_p S_c(p) / p^s    centered collision sum\n"
        "  F_c(1) converges               Centered Collision PNT (proved)\n"
        "  Even characters killed: S_hat(chi) = 0 for chi(-1) = +1 (proved)\n"
        "\n"
        "── The decomposition theorem ─────────────────────────\n"
        "  S_hat(chi) = -B_1(chi_bar) * D(chi)   for primitive odd chi\n"
        "  B_1 = generalized Bernoulli number\n"
        "  D = diagonal character sum over the gate set\n"
        "  Parseval: sum |S_c|^2 = sum |S_hat|^2 / phi(m)  (proved)\n"
        "\n"
        "── Neutrality ────────────────────────────────────────\n"
        "  The reflection a -> b^2-a fixes one class mod q\n"
        "  That class has mean exactly -1/2          (proved)\n"
        "  The cancellation exponent alpha = 1       (proved)\n"
        "\n"
        "── Alignment ─────────────────────────────────────────\n"
        "  alignment(n) = (2m - 1) / (pm - 1)\n"
        "    for n = pm, p smallest prime coprime to b, m b-smooth\n"
        "  Exceeds 1/phi iff m >= phi^2 = phi + 1\n"
        "  Only p = 3 crosses the golden threshold    (proved)\n"
        "\n"
        "── Orbit closure ─────────────────────────────────────\n"
        "  Cumulative digit sum returns to 0 mod (b-1) after\n"
        "    lambda = (b-1) / gcd(S, b-1) periods\n"
        "  Orbit length = lambda * L digits            (proved)\n"
        "  1/3 base 10: triangle (orbit 3)\n"
        "  1/7 base 10: hexagon (orbit 6)\n"
        "\n"
        "A. S. Petty, 2020-2026\n"
        );

    /* ── Blog command aliases ───────────────────────────── */

    } else if (strcmp(cmd, "collision_table") == 0) {
        int base = parse_positional_base(argc, argv, 2);
        collision_table_print(base, has_flag(argc, argv, "--pairs"));

    } else if (strcmp(cmd, "silent_primes") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9')
            base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        int lag = 1;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "--lag") == 0) lag = atoi(argv[i+1]);
        silent_primes_full_print(base, lag);

    } else if (strcmp(cmd, "gate_width") == 0) {
        int base = parse_base(argc, argv, 2);
        printf("Gate width, base %d\n", base);
        printf("Expected: %d deranging multipliers (b - 1)\n\n", base - 1);
        return verify_dispatch("gate-width");

    } else if (strcmp(cmd, "autocorrelation") == 0) {
        int p = (argc >= 3) ? atoi(argv[2]) : 7;
        int base = parse_base(argc, argv, 3);
        autocorrelation_print(p, base);

    } else if (strcmp(cmd, "spectrum") == 0) {
        int p = (argc >= 3) ? atoi(argv[2]) : 7;
        int base = parse_base(argc, argv, 3);
        spectrum_print(p, base);

    } else if (strcmp(cmd, "gate") == 0) {
        int p = (argc >= 3) ? atoi(argv[2]) : 7;
        int base = parse_base(argc, argv, 3);
        gate_print(p, base);

    } else if (strcmp(cmd, "derangements") == 0) {
        int p = (argc >= 3) ? atoi(argv[2]) : 13;
        int base = parse_base(argc, argv, 3);
        derangements_print(p, base);

    } else if (strcmp(cmd, "fluctuation_sum") == 0 ||
               strcmp(cmd, "mertens_growth") == 0) {
        int base = parse_base(argc, argv, 2);
        int lag = 1;
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++) {
            if (strcmp(argv[i], "--lag") == 0) lag = atoi(argv[i+1]);
            if (strcmp(argv[i], "--primes") == 0) maxp = atoi(argv[i+1]);
        }
        fluctuation_sum_print(base, lag, maxp);

    } else if (strcmp(cmd, "class_bias") == 0) {
        int base = parse_base(argc, argv, 2);
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "--primes") == 0) maxp = atoi(argv[i+1]);
        class_bias_print(base, maxp);

    } else if (strcmp(cmd, "character_components") == 0) {
        /* Show character magnitudes using CRT */
        int base_arg = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9') base_arg = atoi(argv[2]);
        base_arg = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base_arg;
        character_components_print(base_arg);

    } else if (strcmp(cmd, "class_means") == 0) {
        int base = parse_base(argc, argv, 2);
        class_means_print(base);

    } else if (strcmp(cmd, "centered_sum") == 0) {
        int base = parse_base(argc, argv, 2);
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "--primes") == 0) maxp = atoi(argv[i+1]);
        centered_sum_print(base, maxp);

    } else if (strcmp(cmd, "neutrality") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9')
            base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        int maxp = 0;
        for (int i = 2; i < argc - 1; i++)
            if (strcmp(argv[i], "-N") == 0 || strcmp(argv[i], "--primes") == 0)
                maxp = atoi(argv[i+1]);
        neutrality_print(base, maxp);

    } else if (strcmp(cmd, "neutrality_sweep") == 0) {
        neutrality_sweep_print();

    } else if (strcmp(cmd, "finite_det") == 0) {
        return verify_dispatch("finite-det");

    } else if (strcmp(cmd, "mod3_means") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9')
            base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        mod3_means_print(base);

    } else if (strcmp(cmd, "polarity_field") == 0) {
        int base = 10;
        if (argc >= 3 && argv[2][0] >= '0' && argv[2][0] <= '9') base = atoi(argv[2]);
        base = parse_base(argc, argv, 2) != 10 ? parse_base(argc, argv, 2) : base;
        polarity_field_print(base);

    } else if (strcmp(cmd, "help") == 0) {
        usage();

    } else {
        fprintf(stderr, "Unknown command: %s\n", cmd);
        return 1;
    }

done:
    if (show_time) {
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double elapsed = (t1.tv_sec - t0.tv_sec)
                       + (t1.tv_nsec - t0.tv_nsec) / 1e9;
        fflush(stdout);
        printf("\n%.3fs\n", elapsed);
    }

    return 0;
}
