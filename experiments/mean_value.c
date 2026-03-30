/*
 * mean_value.c - Mean-value analysis of |P|^2 vs |L|^alpha.
 *
 * Compute: M(alpha) = (1/n) sum_chi |P(chi)|^2 / |L(1,chi)|^alpha
 *
 * If M(alpha) is constant across bases for some alpha,
 * that alpha is the correct exponent relating |P| to |L|.
 *
 * Also: compute the joint moments
 * <|P|^a |L|^b> for various (a,b) to find the relationship.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_PRIME 2000000

static int is_prime(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    return 1;
}

static int gcd(int a, int b) {
    while (b) { int t = b; b = a % b; a = t; }
    return a;
}

void run_base(int b) {
    int m = b * b;
    int units[m], n_units = 0;
    for (int a = 1; a < m; a++)
        if (gcd(a, m) == 1) units[n_units++] = a;

    int g = -1;
    for (int c = 2; c < m; c++) {
        if (gcd(c, m) != 1) continue;
        int v = 1, o = 0;
        do { v=(int)((long long)v*c%m); o++; } while (v!=1);
        if (o == n_units) { g = c; break; }
    }
    if (g < 0) return;

    int dlog[m];
    memset(dlog, -1, sizeof(int)*m);
    { int v=1; for(int k=0;k<n_units;k++){dlog[v]=k;v=(int)((long long)v*g%m);} }

    int dl_m1 = dlog[m-1];
    int odd_j[1000]; int n_odd = 0;
    for (int j = 0; j < n_units && n_odd < 1000; j++) {
        long long t = 2LL * j * dl_m1;
        if ((int)(t%(2*n_units)) != n_units) continue;
        odd_j[n_odd++] = j;
    }

    /* |P| for each odd character */
    double P_mag[1000];
    for (int c = 0; c < n_odd; c++) {
        int j = odd_j[c];
        double re=0, im=0;
        for (int k=1; k<=b-1; k++) {
            if (dlog[k]<0) continue;
            double angle = -2*M_PI*j*dlog[k]/(double)n_units;
            re += cos(angle); im += sin(angle);
        }
        P_mag[c] = sqrt(re*re + im*im);
    }

    /* |L(1)| for each odd character */
    double L_mag[1000];
    memset(L_mag, 0, sizeof(double)*n_odd);
    for (int p = 2; p < MAX_PRIME; p++) {
        if (!is_prime(p) || p == b) continue;
        int dl = dlog[p%m]; if (dl<0) continue;
        for (int c = 0; c < n_odd; c++) {
            double angle = 2*M_PI*odd_j[c]*dl/(double)n_units;
            double re = 1 - cos(angle)/p, im = -sin(angle)/p;
            double mag2 = re*re + im*im;
            if (mag2 > 1e-30) L_mag[c] -= 0.5*log(mag2);
        }
    }
    for (int c = 0; c < n_odd; c++) L_mag[c] = exp(L_mag[c]);

    /* Compute mean values for various alpha */
    /* M(alpha) = mean of |P|^2 / |L|^alpha */
    printf("%5d %4d", b, n_odd);

    int cnt = 0;
    for (int c = 0; c < n_odd; c++)
        if (P_mag[c] > 1e-6 && L_mag[c] > 0.01) cnt++;

    double alphas[] = {0.0, 0.5, 1.0, 1.5, 1.6, 1.7, 1.8, 2.0};
    int na = 8;

    for (int ai = 0; ai < na; ai++) {
        double alpha = alphas[ai];
        double sum = 0;
        int n = 0;
        for (int c = 0; c < n_odd; c++) {
            if (P_mag[c] < 1e-6 || L_mag[c] < 0.01) continue;
            sum += P_mag[c]*P_mag[c] / pow(L_mag[c], alpha);
            n++;
        }
        printf(" %8.3f", sum/n);
    }

    /* Also: best-fit alpha where CV of |P|^2/|L|^alpha is minimized */
    double best_alpha = 0, best_cv = 1e30;
    for (double alpha = 0; alpha <= 3.0; alpha += 0.01) {
        double sum=0, sum2=0; int n=0;
        for (int c=0; c<n_odd; c++) {
            if (P_mag[c]<1e-6||L_mag[c]<0.01) continue;
            double r = P_mag[c]*P_mag[c] / pow(L_mag[c], alpha);
            sum+=r; sum2+=r*r; n++;
        }
        double mean = sum/n;
        double var = sum2/n - mean*mean;
        double cv = sqrt(var>0?var:0)/mean;
        if (cv < best_cv) { best_cv = cv; best_alpha = alpha; }
    }
    printf(" | best=%.2f cv=%.3f\n", best_alpha, best_cv);
}

int main(void) {
    printf("%5s %4s", "base", "n");
    printf(" %8s %8s %8s %8s %8s %8s %8s %8s | %s\n",
           "a=0.0", "a=0.5", "a=1.0", "a=1.5", "a=1.6", "a=1.7", "a=1.8", "a=2.0",
           "best alpha");

    int bases[] = {5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < 10; i++)
        run_base(bases[i]);

    return 0;
}
