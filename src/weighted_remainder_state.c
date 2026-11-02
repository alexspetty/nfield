/* Conserved period weights, centered clocks, and finite additive conductors. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include "weighted_remainder_state.h"

enum { MAX_PERIOD = 240 };

static int residue_gcd(int a, int b)
{
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int residue_mobius(int n)
{
    int sign = 1;
    for (int p = 2; p <= n / p; ++p) {
        if (n % p) continue;
        n /= p;
        sign = -sign;
        if (n % p == 0) return 0;
    }
    return n > 1 ? -sign : sign;
}

static long double harmonic(int n)
{
    long double result = 0;
    for (int k = 1; k <= n; ++k) result += 1.0L / k;
    return result;
}

long double weighted_remainder_weight(int k)
{
    if (k < 0 || k > MAX_PERIOD) return NAN;
    if (k < 2) return 0;
    long double result = 0;
    for (int a = 1; a < k; ++a)
        if (residue_gcd(a, k) == 1) result += 1.0L / a;
    return result / ((long double)k * k);
}

long double weighted_remainder_covariance(int k, int l)
{
    if (k <= 0 || l <= 0 || k > MAX_PERIOD || l > MAX_PERIOD) return NAN;
    int d = residue_gcd(k, l);
    return ((long double)d * d - 1) / 12;
}

static int64_t row_twice(int q, int n, int odd)
{
    int64_t total = 0;
    for (int d = 1; d <= q; ++d) if (q % d == 0) {
        int r = n % d;
        int term = odd ? (r == 0 ? 0 : 2 * r - d) : 2 * r - d + 1;
        total += (int64_t)residue_mobius(q / d) * term;
    }
    return total;
}

static int64_t ramanujan(int q, int n)
{
    int64_t total = 0;
    for (int d = 1; d <= q; ++d)
        if (q % d == 0 && n % d == 0)
            total += (int64_t)d * residue_mobius(q / d);
    return total;
}

static int64_t jordan_two(int q)
{
    int64_t result = 0;
    for (int d = 1; d <= q; ++d) if (q % d == 0)
        result += (int64_t)d * d * residue_mobius(q / d);
    return result;
}

static int totient(int q)
{
    int result = 0;
    for (int a = 1; a <= q; ++a) result += residue_gcd(a, q) == 1;
    return result;
}

static long double centered_age(const long double *w, int M, int n)
{
    long double result = 0;
    for (int k = 2; k <= M; ++k)
        result += w[k] * (2 * (n % k) - k + 1) / 3;
    return result;
}

static long double finite_increment(const long double *w, int M, int n)
{
    long double result = 0;
    for (int k = 2; k <= M; ++k)
        result += (2.0L / 3) * w[k] * (1 - (n % k == 0 ? k : 0));
    return result;
}

static long double finite_eta(const long double *w, int q, int M)
{
    long double result = 0;
    for (int k = q; k <= M; k += q) result += w[k];
    return result;
}

int weighted_remainder_state_compute(int n, int M, WeightedRemainderState *s)
{
    if (!s || n < 0 || n > 1000000000 || M < 2 || M > MAX_PERIOD) return 0;
    long double w[MAX_PERIOD + 1] = {0};
    *s = (WeightedRemainderState){.resolution = n, .cutoff = M};
    for (int k = 2; k <= M; ++k) {
        w[k] = weighted_remainder_weight(k);
        s->mass += w[k];
        s->stationary_age += w[k] * (k - 1) / 3;
    }
    s->centered_age = centered_age(w, M, n);
    s->finite_increment = finite_increment(w, M, n);
    for (int q = 2; q <= M; ++q) {
        long double eta = finite_eta(w, q, M);
        s->variance += jordan_two(q) * eta * eta / 27;
    }
    return 1;
}

int weighted_remainder_state_inspect(int n, int M)
{
    WeightedRemainderState s;
    if (!weighted_remainder_state_compute(n, M, &s)) return 1;
    printf("Weighted remainder state\n\nResolution %d; period cutoff %d\n", n, M);
    printf("retained mass          %.15Lf\n", s.mass);
    printf("complementary mass     %.15Lf\n", 1 - s.mass);
    printf("stationary mean        %.15Lf\n", s.stationary_age);
    printf("centered age           %.15Lf\n", s.centered_age);
    printf("finite reset increment %.15Lf\n", s.finite_increment);
    printf("finite Haar variance   %.15Lf\n", s.variance);
    if (n <= M) {
        long double deficit = s.centered_age + s.stationary_age +
            (2.0L / 3) * n * (1 - s.mass);
        printf("completed deficit      %.15Lf\n", deficit);
        printf("continuous capacity    %.15Lf\n", n - deficit);
    }
    puts("\nFinite cutoff, with omitted mass retained in the deficit completion.");
    puts("The finite increment uses retained mass, not the infinite unit advance.");
    puts("Long-double evaluation; no limit distribution or asymptotic is inferred.");
    return 0;
}

int weighted_remainder_state_conductor(int q, int M)
{
    if (q < 2 || q > M || M > MAX_PERIOD) return 1;
    long double w[MAX_PERIOD + 1] = {0};
    for (int k = 2; k <= M; ++k) w[k] = weighted_remainder_weight(k);
    printf("Finite additive conductor\n\nConductor %d; period cutoff %d\n", q, M);
    printf("finite amplitude eta(q,M) %.15Lf\n", finite_eta(w, q, M));
    printf("phi(q)=%d; J2(q)=%lld\n", totient(q), (long long)jordan_two(q));
    puts("residue  twice-age-row  twice-odd-row  endpoint-row");
    for (int n = 0; n < q; ++n)
        printf("%7d %14lld %14lld %13lld\n", n,
               (long long)row_twice(q, n, 0),
               (long long)row_twice(q, n, 1), (long long)ramanujan(q, n));
    puts("\nInteger rows are exact. eta(q,M) is a finite amplitude, not eta(q).");
    return 0;
}

typedef struct { int failures, exact, numerical, inequalities; long double max_error; } Check;
static void check_exact(Check *c, int64_t x, int64_t y)
{
    c->exact++;
    if (x != y) c->failures++;
}
static void check_near(Check *c, long double x, long double y)
{
    long double error = fabsl(x - y) / (1 + fabsl(y));
    c->numerical++;
    if (!isfinite(x) || !isfinite(y) || error > 2e-13L) c->failures++;
    if (error > c->max_error) c->max_error = error;
}
static void check_inequality(Check *c, int holds)
{
    c->inequalities++;
    if (!holds) c->failures++;
}

int weighted_remainder_state_verify(void)
{
    const char *names[] = {
        "primitive weights and reciprocal address budget",
        "gcd capacity, conserved deficit and reset increments",
        "centered ages, reflection and endpoint completion",
        "exact remainder covariance on complete CRT periods",
        "primitive conductor norms and odd-endpoint split",
        "finite variance and orthogonal conductor expansion",
        "block compensation and stationary energy bound",
        "conditional means on finite cylinders",
        "finite Mobius regrouping and endpoint extrema",
        "period-twelve perturbation and its exact variance"
    };
    Check c[10] = {{0}};
    long double w[MAX_PERIOD + 1] = {0};
    for (int k = 2; k <= MAX_PERIOD; ++k) w[k] = weighted_remainder_weight(k);
    for (int n = 2; n <= MAX_PERIOD; ++n) {
        long double budget = 0, inverse = 0;
        for (int d = 1; d <= n; ++d) if (n % d == 0) {
            budget += (long double)d * d * d * w[d];
            inverse += (long double)residue_mobius(n / d) * d * harmonic(d - 1);
        }
        check_near(&c[0], budget, n * harmonic(n - 1));
        check_near(&c[0], inverse / ((long double)n * n * n), w[n]);
        check_inequality(&c[0], w[n] > 0);
    }
    long double previous = 0;
    for (int n = 0; n <= 80; ++n) {
        long double J = 0, mass = 0, reset = 0, D = 0;
        for (int r = 1; r <= n; ++r) for (int s = 1; s <= n; ++s) {
            int g = residue_gcd(r, s);
            J += (long double)g * g / (3.0L * r * s);
        }
        for (int k = 2; k <= n; ++k) {
            mass += w[k]; D += (2.0L / 3) * w[k] * (n % k);
            if (n % k == 0) reset += k * w[k];
        }
        D += (2.0L / 3) * n * (1 - mass);
        check_near(&c[1], D, n - J);
        if (n) check_near(&c[1], D - previous, (2.0L / 3) * (1 - reset));
        previous = D;
    }
    for (int M = 2; M <= 12; ++M) {
        int L = 1;
        long double mean = 0;
        for (int k = 2; k <= M; ++k) {
            L = L / residue_gcd(L, k) * k;
            mean += w[k] * (k - 1) / 3;
        }
        check_near(&c[2], centered_age(w, M, 0), -mean);
        for (int n = 0; n < L; ++n) {
            long double y = centered_age(w, M, n), raw = 0;
            for (int k = 2; k <= M; ++k) raw += (2.0L / 3) * w[k] * (n % k);
            check_near(&c[2], y + mean, raw);
            check_near(&c[2], centered_age(w, M, L - 1 - n), -y);
        }
    }
    for (int k = 1; k <= 40; ++k) for (int l = 1; l <= 40; ++l) {
        int g = residue_gcd(k, l), L = k / g * l;
        int64_t sum = 0;
        for (int n = 0; n < L; ++n)
            sum += (int64_t)(2 * (n % k) - k + 1) * (2 * (n % l) - l + 1);
        check_exact(&c[3], 3 * sum, (int64_t)L * (g * g - 1));
    }
    for (int q = 2; q <= 120; ++q) {
        int64_t p2 = 0, r2 = 0;
        for (int n = 0; n < q; ++n) {
            int64_t p = row_twice(q, n, 0), r = row_twice(q, n, 1);
            check_exact(&c[4], p, r - ramanujan(q, n));
            p2 += p * p; r2 += r * r;
        }
        check_exact(&c[4], 3 * p2, (int64_t)q * jordan_two(q));
        check_exact(&c[4], 3 * r2, (int64_t)q * (jordan_two(q) - 3 * totient(q)));
    }
    for (int M = 2; M <= 8; ++M) {
        int L = 1;
        long double variance = 0, gram = 0, empirical = 0;
        for (int k = 2; k <= M; ++k) {
            L = L / residue_gcd(L, k) * k;
            long double eta = finite_eta(w, k, M);
            variance += jordan_two(k) * eta * eta / 27;
            for (int l = 2; l <= M; ++l)
                gram += (4.0L / 9) * w[k] * w[l] * weighted_remainder_covariance(k, l);
        }
        for (int n = 0; n < L; ++n) {
            long double y = centered_age(w, M, n), expansion = 0;
            empirical += y * y / L;
            for (int q = 2; q <= M; ++q)
                expansion += finite_eta(w, q, M) * row_twice(q, n, 0) / 3;
            check_near(&c[5], y, expansion);
        }
        check_near(&c[5], empirical, variance);
        check_near(&c[5], gram, variance);
        for (int H = 0; H <= 17; ++H) {
            long double energy = 0;
            for (int n = 0; n < L; ++n) {
                long double block = 0, ends = centered_age(w, M, n + H) - centered_age(w, M, n);
                for (int j = 1; j <= H; ++j) block += finite_increment(w, M, n + j);
                check_near(&c[6], block, ends);
                energy += ends * ends / L;
            }
            check_inequality(&c[6], energy <= 4 * variance + 1e-15L);
        }
    }
    for (int L = 2; L <= 12; ++L) {
        int period = L;
        for (int k = 2; k <= 6; ++k) period = period / residue_gcd(period, k) * k;
        for (int a = 0; a < L; ++a) {
            long double conditional = 0, predicted = 0;
            for (int n = a; n < period; n += L)
                conditional += centered_age(w, 6, n) / (period / L);
            for (int k = 2; k <= 6; ++k) {
                int d = residue_gcd(k, L);
                predicted += w[k] * (2 * (a % d) - d + 1) / 3;
            }
            check_near(&c[7], conditional, predicted);
        }
    }
    for (int Q = 2; Q <= 12; ++Q) {
        int L = 1;
        long double beta[13] = {0}, endpoint = 0;
        for (int d = 2; d <= Q; ++d) {
            L = L / residue_gcd(L, d) * d;
            for (int j = 1; j <= Q / d; ++j)
                beta[d] += residue_mobius(j) * finite_eta(w, d * j, MAX_PERIOD);
            check_inequality(&c[8], beta[d] > 0);
            endpoint += beta[d] * (d - 1) / 3;
        }
        for (int a = 0; a < L; ++a) {
            long double f = 0, positive = 0;
            for (int d = 2; d <= Q; ++d) {
                f += finite_eta(w, d, MAX_PERIOD) * row_twice(d, a, 0) / 3;
                positive += beta[d] * (2 * (a % d) - d + 1) / 3;
            }
            check_near(&c[8], f, positive);
            check_inequality(&c[8], fabsl(f) <= endpoint + 1e-15L);
            if (a > 0 && a < L - 1) check_inequality(&c[8], fabsl(f) < endpoint - 1e-15L);
        }
    }
    int64_t perturbation_square = 0, perturbation_mean = 0;
    for (int n = 0; n < 12; ++n) {
        int z3 = (2 * (n % 2) - 1) - 2 * (2 * (n % 3) - 2) + (2 * (n % 4) - 3);
        perturbation_mean += z3;
        perturbation_square += z3 * z3;
    }
    check_exact(&c[9], perturbation_mean, 0);
    check_exact(&c[9], 3 * perturbation_square, 12 * 56);
    int failures = 0, exact = 0, numerical = 0, inequalities = 0;
    long double maximum = 0;
    puts("Weighted remainder state verification\n");
    for (int g = 0; g < 10; ++g) {
        printf("  %s  %s\n", names[g], c[g].failures ? "FAIL" : "PASS");
        failures += c[g].failures; exact += c[g].exact; numerical += c[g].numerical;
        inequalities += c[g].inequalities;
        if (c[g].max_error > maximum) maximum = c[g].max_error;
    }
    printf("\nexact integer checks=%d; numerical checks=%d; floating inequality checks=%d\n",
           exact, numerical, inequalities);
    printf("maximum scaled error=%.3Le\n", maximum);
    printf("10/10 verification groups %s.\n", failures ? "did not pass" : "passed");
    puts("Finite cutoffs only. Conductor regrouping uses eta(q,240), not infinite eta(q).");
    puts("Haar limits, mixed L-value identities, asymptotic extrema and atomlessness");
    puts("require proofs; these computations do not certify them.");
    return failures == 0;
}

void weighted_remainder_state_help(void)
{
    puts("Weighted remainder state\n\n"
         "  nfield weighted-remainder-state inspect <resolution> <cutoff>\n"
         "  nfield weighted-remainder-state conductor <q> <cutoff>\n"
         "  nfield weighted-remainder-state boundary <resolution>\n"
         "  nfield weighted-remainder-state ramp <first> <second>\n"
         "  nfield weighted-remainder-state floor <prime> <address>\n"
         "  nfield weighted-remainder-state straighten <prime> <address>\n"
         "  nfield weighted-remainder-state clock <cutoff> <address>\n"
         "  nfield weighted-remainder-state clock-law <cutoff>\n"
         "  nfield weighted-remainder-state age-budget <cutoff>\n"
         "  nfield weighted-remainder-state finite-weights <address> [period:weight ...]\n"
         "  nfield weighted-remainder-state variance <cutoff>\n"
         "  nfield weighted-remainder-state rows <conductor> [address]\n"
         "  nfield weighted-remainder-state increment-covariance <cutoff> <shift>\n"
         "  nfield weighted-remainder-state increment-recurrence <cutoff>\n"
         "  nfield weighted-remainder-state fourier <conductor> <frequency> <cutoff> <finite|full>\n"
         "  nfield weighted-remainder-state amplitude-refinement <conductor> <period-cutoff> <zeta-cutoff> <mobius-cutoff>\n"
         "  nfield weighted-remainder-state expansion-constants <cutoff>\n"
         "  nfield weighted-remainder-state harmonic-expansion <conductor> <cutoff>\n"
         "  nfield weighted-remainder-state amplitude-expansion <conductor> <cutoff>\n"
         "  nfield weighted-remainder-state deficit-series <rational-exponent> <cutoff>\n"
         "  nfield weighted-remainder-state deficit-diagnostic <cutoff>\n"
         "  nfield weighted-remainder-state spectral-product <prime-cutoff>\n"
         "  nfield weighted-remainder-state spectral-mean <rational-x> <prime-cutoff>\n"
         "  nfield weighted-remainder-state spectral-energy <conductor> <period-cutoff>\n"
         "  nfield weighted-remainder-state spectral-tail <Q> <B> <M> <P> <N>\n"
         "  nfield weighted-remainder-state character-phase <denominator> <numerator>\n"
         "  nfield weighted-remainder-state character-table <modulus>\n"
         "  nfield weighted-remainder-state character-l <modulus> <odd-index> <series-cutoff>\n"
         "  nfield weighted-remainder-state mixed-moment <modulus> <series-cutoff> <zeta-cutoff> <period-cutoff>\n"
         "  nfield weighted-remainder-state cotangent-sums <modulus> <series-cutoff> <zeta-cutoff>\n"
         "  nfield weighted-remainder-state harmonic-polylog <real> <imaginary> <series-cutoff>\n"
         "  nfield weighted-remainder-state harmonic-root <denominator> <numerator> <series-cutoff> <zeta-cutoff>\n"
         "  nfield weighted-remainder-state harmonic-root-average <modulus> <series-cutoff>\n"
         "  nfield weighted-remainder-state sine-transform <modulus> <signed-frequency>\n"
         "  nfield weighted-remainder-state small-amplitudes <series-cutoff> <zeta-cutoff>\n"
         "  nfield weighted-remainder-state alignment <modulus> <M> <N> <P>\n"
         "  nfield weighted-remainder-state alignment-local <prime> <valuation>\n"
         "  nfield weighted-remainder-state harmonic-local <period> <constant-cutoff>\n"
         "  nfield weighted-remainder-state alignment-lcm <scale> <M> <N> <P>\n"
         "  nfield weighted-remainder-state alignment-growth <modulus> <scale> <M> <N> <P>\n"
         "  nfield weighted-remainder-state law-moment <M> <degree>\n"
         "  nfield weighted-remainder-state law-cdf <M> <threshold> <margin>\n"
         "  nfield weighted-remainder-state law-window <M> <lower> <upper> <margin>\n"
         "  nfield weighted-remainder-state law-concentration <M> <width> <margin>\n"
         "  nfield weighted-remainder-state law-characteristic <M> <frequency>\n"
         "  nfield weighted-remainder-state law-recurrence <M> <lower> <upper> <horizon>\n"
         "  nfield weighted-remainder-state law-activation <prime-cutoff> <block-length> <width>\n"
         "  nfield weighted-remainder-state law-tail-bound <M> <threshold> <modulus>\n"
         "  nfield weighted-remainder-state clock-difference <M> <address>\n"
         "  nfield weighted-remainder-state mass-inverse <cutoff> <period> [q:amplitude ...]\n"
         "  nfield weighted-remainder-state mass-recovery <period> <conductor-cutoff> <period-cutoff>\n"
         "  nfield weighted-remainder-state perturbation <cutoff> <address> <epsilon>\n"
         "  nfield weighted-remainder-state cycle <period> <residue> <address> <last>\n"
         "  nfield weighted-remainder-state cycle-tv <cutoff> <last>\n"
         "  nfield weighted-remainder-state covariance <first> <second>\n"
         "  nfield weighted-remainder-state amplitude <conductor> <cutoff>\n"
         "  nfield weighted-remainder-state tree <cutoff>\n"
         "  nfield weighted-remainder-state tree-node <first> <second>\n"
         "  nfield weighted-remainder-state weight <period>\n"
         "  nfield weighted-remainder-state budget <resolution>\n"
         "  nfield weighted-remainder-state mass <cutoff>\n"
         "  nfield weighted-remainder-state sawtooth <period> <slope> <residue>\n"
         "  nfield weighted-remainder-state dedekind <period> <slope>\n"
         "  nfield weighted-remainder-state gram <first-period> <first-slope> <second-period> <second-slope>\n"
         "  nfield weighted-remainder-state sawtooth-mean <period> <slope> <cylinder-period> <residue>\n"
         "  nfield weighted-remainder-state reset <resolution>\n"
         "  nfield weighted-remainder-state pairing <length> <period> <residue> <cutoff>\n"
         "  nfield weighted-remainder-state forcing <resolution>\n"
         "  nfield weighted-remainder-state block <start> <length>\n"
         "  nfield weighted-remainder-state crt [period:shift ...]\n"
         "  nfield weighted-remainder-state moment <length> <f|g> [shift:power ...]\n"
         "  nfield weighted-remainder-state haar-moment <cutoff> [shift ...]\n"
         "  nfield weighted-remainder-state cylinder <modulus> <address> <cutoff>\n"
         "  nfield weighted-remainder-state position <modulus> <address> <cutoff> <threshold>\n"
         "  nfield weighted-remainder-state position-weight <modulus> <address> <period> <cutoff>\n"
         "  nfield weighted-remainder-state conductor-full <Q> <address> <M>\n"
         "  nfield weighted-remainder-state conductor-beta <d> <Q> <M>\n"
         "  nfield weighted-remainder-state conductor-prime <Q> <prime>\n"
         "  nfield weighted-remainder-state conductor-extrema <Q> <M>\n"
         "  nfield weighted-remainder-state conductor-minimizers <Q> <M>\n"
         "  nfield weighted-remainder-state activation <n> <a> <u> <v> <probabilities> <values>\n"
         "  nfield weighted-remainder-state verify\n"
         "  nfield verify weighted-remainder-state\n\n"
         "Resolution is 0 through 1000000000; cutoff is 2 through 240.\n"
         "Conductor q is between 2 and the cutoff.\n"
         "Boundary resolution is 0 through 240; ramp periods are 1 through 240.\n"
         "Boundary atoms, capacity and direct ramp integrals use exact GMP rationals.\n"
         "Floor and straighten use primes 2..239 and signed 64-bit addresses, reduced modulo p squared.\n"
         "Straighten evaluates both original floor lists and midpoint response, including nonunits and jumps.\n"
         "Clock uses exact GMP signed addresses, finite cutoffs 2..240 and retained-mass increments.\n"
         "Clock-law enumerates every phase for cutoffs 2..12; equal values keep their multiplicities.\n"
         "Cycle reports orbit, stationary and Cesaro masses and the residue transition, for periods 2..240.\n"
         "Cycle and cycle-tv average observations 0..last, where last is any nonnegative GMP integer.\n"
         "Cycle-tv gives exact bounds using the omitted unit mass; covariance periods are 1..240.\n"
         "Age-budget evaluates the harmonic cross sum and Mobius first-moment formula for cutoffs 0..240.\n"
         "Finite-weights accepts exact signed rational weights at distinct periods 2..240, without normalization.\n"
         "It reports finite clocks, forcing, amplitudes, and both Gram and Jordan variances; probability flags are explicit.\n"
         "The completed unit-mass energy additionally requires nonnegative weights and a nonnegative address.\n"
         "Fourier returns rational coefficient and spectral-mass intervals at primitive signed frequencies.\n"
         "Its finite/full modes distinguish retained amplitudes from proved infinite-amplitude bounds.\n"
         "Perturbation uses cutoff 4..240 and rational 0<abs(epsilon)<1/24; the omitted collision tail is unchanged.\n"
         "Variance returns exact finite variance and proved rational full-variance/L2-error bounds for cutoffs 2..240.\n"
         "Amplitude returns exact rational bounds for the full amplitude; both inputs are 2..240.\n"
         "Tree cutoff, node coordinates and budget resolution are 1..240; weight and mass use 0..240.\n"
         "Tree reports exact coprime square mass, outgoing mass and its harmonic upper bound.\n"
         "Weight includes its finite Mobius inverse; budget returns the reciprocal-address divisor sum.\n"
         "Mass separates retained weights from the exact complement in the proved unit mass.\n"
         "It also reports the weighted first moment and the resulting finite deficit upper bound.\n"
         "Sawtooth, Dedekind and Gram values are exact rationals, with zero at integer arguments.\n"
         "Their periods are 1..240; signed 64-bit slopes must be units at their original periods.\n"
         "Residues accept signed 64-bit integers. Gram periods may have any common factor.\n"
         "Sawtooth-mean gives the actual cylinder mean; its cylinder period must divide the row period.\n"
         "Reset resolution, pairing length and period are 1..240; residue is 0..period-1.\n"
         "Pairing compares an exact residue-test average with a certified Haar interval.\n"
         "Forcing is full f at resolutions 1..240; block requires start+length<=240.\n"
         "Joint lists have at most 8 entries; CRT periods are 2..240 and shifts 0..240.\n"
         "Empirical moments use samples 1..length; length+each shift<=240, total degree<=16.\n"
         "Haar moments keep periods 2..cutoff, with (cutoff-1)^dimension<=65536.\n"
         "Empty products equal one. Joint values are exact rationals; omitted moment tails are not included.\n"
         "Cylinder uses modulus 1..240, cutoff 2..240, and any signed integer address.\n"
         "Position actions require 2<=modulus<=cutoff<=240; individual period is 0..240.\n"
         "Threshold is a rational number; exceedance is strict. Cylinder and position outputs\n"
         "enclose the full Haar quantities with exact rational endpoints and omitted mass bounds.\n"
         "Conductor-full and conductor-beta enclose full infinite-amplitude objects: 2<=Q,M<=240,\n"
         "2<=d<=Q, any signed integer address. Q limits conductors; M limits retained periods.\n"
         "Conductor-prime constructs the exact CRT candidate for a prime Q/2<p<=Q, Q>=3.\n"
         "Extrema and minimizers require Q>=3 and lcm(1..Q)<=50000; M is 2..240.\n"
         "They enclose the restricted gap. Minimizers lists every address not excluded by the bounds;\n"
         "overlapping intervals leave the exact minimizer unresolved. Complete endpoints are unique.\n"
         "Activation takes n=0..12, positive a and a closed interval [u,v] with v-u<a.\n"
         "Use comma-separated rational probabilities in [0,1/2] and exactly 2^n values,\n"
         "indexed by masks: bit i is coordinate i. For n=0 the probability list is '-'.\n"
         "Every upward edge must increase by at least a, including zero-probability patterns.\n"
         "Returns exact event and activation-mixture probabilities, active-count moments,\n"
         "the conditional Sperner bound and 400/(1+sum probabilities), a squared bound.\n"
         "Alignment encloses the full reset and alignment sums without enumerating the modulus.\n"
         "M=2..240 retains periods; N,P=1..240 control constants and absent-prime logarithms.\n"
         "Moduli are positive decimal integers, at most 4096 bits, with prime factors <=239 and valuations <=240.\n"
         "Alignment-local uses a prime and valuation 0..240; harmonic-local uses period 2..240.\n"
         "Alignment-lcm builds lcm(1..scale); alignment-growth compares an admitted modulus at scale 1..240.\n"
         "Growth reports exact prime products and bounded leading terms; availability flags govern normalization and losses.\n"
         "Finite growth values do not certify maximal-order limits.\n"
         "Law actions enumerate a complete finite quotient, retaining multiplicities, for M=2..12.\n"
         "Moments have degree 0..16; CDF and windows use rational endpoints and positive margins.\n"
         "Concentration maximizes closed-window mass at a nonnegative width. Recurrence uses horizon 1..240.\n"
         "Full-law probability bounds use the squared L2 budget; they may be the full interval [0,1].\n"
         "Characteristic uses rational frequency, directed MPFR rounding and an explicit cutoff error.\n"
         "Law-activation selects primes P/2<p<=P, P=4..240, and block length <=P/4.\n"
         "Its nonnegative width must be strictly below the smallest selected reset increment.\n"
         "Law-tail-bound permits M=2..240, positive threshold and cylinder modulus 1..240.\n"
         "Clock-difference compares signed addresses with 0 or -1 and completes D(n) when the reflected address <=M.\n"
         "Inspect conserved weights, finite centered ages and Haar variance.\n"
         "Integer covariance and conductor rows are exact finite arithmetic;\n"
         "weighted sums use long double. The infinite law is outside this computation.");
}
