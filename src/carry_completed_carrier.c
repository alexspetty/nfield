/* Carry-completed cyclic carriers, seam energies, and product-cycle Grams. */

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"

#define CCC_MAX_CLOCK 100000
#define CCC_MAX_PRIME 1009
#define CCC_MAX_STATES 5000000LL

static long long ccc_abs(long long value)
{
    return value < 0 ? -value : value;
}

static long long ccc_gcd(long long first, long long second)
{
    first = ccc_abs(first);
    second = ccc_abs(second);
    while (second != 0) {
        long long remainder = first % second;
        first = second;
        second = remainder;
    }
    return first == 0 ? 1 : first;
}

static int ccc_positive_mod(long long value, int modulus)
{
    long long answer = value % modulus;
    return (int)(answer < 0 ? answer + modulus : answer);
}

static int ccc_is_prime(int value)
{
    if (value < 2) return 0;
    if (value % 2 == 0) return value == 2;
    for (int divisor = 3; divisor <= value / divisor; divisor += 2)
        if (value % divisor == 0) return 0;
    return 1;
}

static int ccc_power_mod(int base, int exponent, int modulus)
{
    long long answer = 1;
    long long factor = ccc_positive_mod(base, modulus);
    while (exponent > 0) {
        if (exponent & 1) answer = answer * factor % modulus;
        factor = factor * factor % modulus;
        exponent >>= 1;
    }
    return (int)answer;
}

static int ccc_order(int value, int prime)
{
    if (value <= 0 || value >= prime) return 0;
    long long power = 1;
    for (int exponent = 1; exponent < prime; ++exponent) {
        power = power * value % prime;
        if (power == 1) return exponent;
    }
    return 0;
}

static void ccc_reduce(long long *numerator, long long *denominator)
{
    long long divisor = ccc_gcd(*numerator, *denominator);
    *numerator /= divisor;
    *denominator /= divisor;
    if (*denominator < 0) {
        *numerator = -*numerator;
        *denominator = -*denominator;
    }
}

static void ccc_print_fraction(long long numerator, long long denominator)
{
    ccc_reduce(&numerator, &denominator);
    if (denominator == 1) printf("%lld", numerator);
    else printf("%lld/%lld", numerator, denominator);
}

int carry_completed_carrier_compute(
        int clock_size, int source_prime, int source_step,
        CarryCompletedCarrierSummary *summary)
{
    int *log_generator = NULL;
    unsigned char *seen = NULL;
    int ok = 0;

    if (!summary || clock_size < 1 || clock_size > CCC_MAX_CLOCK ||
        source_prime < 3 || source_prime > CCC_MAX_PRIME ||
        !ccc_is_prime(source_prime))
        return 0;
    source_step = ccc_positive_mod(source_step, source_prime);
    if (source_step == 0) return 0;

    int source_order = ccc_order(source_step, source_prime);
    int half_order = (source_prime - 1) / 2;
    if (source_order != half_order || half_order % 2 == 0 ||
        source_prime != 2 * source_order + 1 ||
        clock_size % source_order != 0)
        return 0;

    int generator = ccc_positive_mod(-source_step, source_prime);
    if (ccc_order(generator, source_prime) != source_prime - 1 ||
        ccc_power_mod(generator, source_order, source_prime) !=
            source_prime - 1)
        return 0;
    if ((long long)clock_size >
            LLONG_MAX / (2LL * (source_prime - 1)))
        return 0;
    long long completed_size =
        2LL * clock_size * (source_prime - 1);
    if (completed_size > CCC_MAX_STATES) return 0;

    log_generator = malloc((size_t)source_prime * sizeof(*log_generator));
    seen = calloc((size_t)completed_size, sizeof(*seen));
    if (!log_generator || !seen) goto cleanup;
    for (int residue = 0; residue < source_prime; ++residue)
        log_generator[residue] = -1;
    int power = 1;
    for (int exponent = 0; exponent < source_prime - 1; ++exponent) {
        if (log_generator[power] != -1) goto cleanup;
        log_generator[power] = exponent;
        power = (int)((long long)power * generator % source_prime);
    }
    if (power != 1) goto cleanup;

    int inverse_step = ccc_power_mod(
        source_step, source_prime - 2, source_prime);
    int inverse_clock_power = 1;
    int transition_ok = 1;
    int half_turn_ok = 1;
    for (int clock = 0; clock < clock_size; ++clock) {
        for (int sheet = 0; sheet < 2; ++sheet) {
            for (int source = 1; source < source_prime; ++source) {
                int lane = (int)((long long)inverse_clock_power * source %
                                 source_prime);
                int exponent = log_generator[lane];
                if (exponent < 0) goto cleanup;
                long long coordinate = clock + (long long)clock_size * sheet
                    + 2LL * clock_size * exponent;
                if (coordinate < 0 || coordinate >= completed_size ||
                    seen[coordinate])
                    goto cleanup;
                seen[coordinate] = 1;

                int next_clock = clock + 1;
                int next_sheet = sheet;
                int next_source =
                    (int)((long long)source_step * source % source_prime);
                if (clock == clock_size - 1) {
                    next_clock = 0;
                    if (sheet == 0) next_sheet = 1;
                    else {
                        next_sheet = 0;
                        next_source = (int)((long long)next_source * generator
                                            % source_prime);
                    }
                }
                int next_inverse_power = next_clock == 0
                    ? 1
                    : (int)((long long)inverse_clock_power * inverse_step
                            % source_prime);
                int next_lane = (int)((long long)next_inverse_power *
                                      next_source % source_prime);
                int next_exponent = log_generator[next_lane];
                long long next_coordinate = next_clock
                    + (long long)clock_size * next_sheet
                    + 2LL * clock_size * next_exponent;
                if (next_coordinate != (coordinate + 1) % completed_size)
                    transition_ok = 0;

                int complement_lane = source_prime - lane;
                int complement_exponent = log_generator[complement_lane];
                long long complement_coordinate = clock
                    + (long long)clock_size * sheet
                    + 2LL * clock_size * complement_exponent;
                if (complement_exponent !=
                        (exponent + source_order) % (source_prime - 1) ||
                    complement_coordinate !=
                        (coordinate + completed_size / 2) % completed_size)
                    half_turn_ok = 0;
            }
        }
        inverse_clock_power =
            (int)((long long)inverse_clock_power * inverse_step % source_prime);
    }
    for (long long coordinate = 0; coordinate < completed_size; ++coordinate)
        if (!seen[coordinate]) goto cleanup;

    *summary = (CarryCompletedCarrierSummary){0};
    summary->clock_size = clock_size;
    summary->source_prime = source_prime;
    summary->source_step = source_step;
    summary->source_order = source_order;
    summary->complement_generator = generator;
    summary->completed_size = completed_size;
    summary->sheet_quotient_size = 2LL * clock_size;
    summary->clock_quotient_size = clock_size;
    summary->transition_conjugacy = transition_ok;
    summary->half_turn_complement = half_turn_ok;
    summary->factor_length = clock_size / source_order;
    summary->coprime_factorization =
        ccc_gcd(source_order, summary->factor_length) == 1;
    if (summary->coprime_factorization) {
        summary->degree_zero_cells =
            (long long)clock_size * (source_prime - 1);
        summary->degree_one_cells = 2LL * summary->degree_zero_cells;
        summary->degree_two_cells = summary->degree_zero_cells;
        long double first_gap = 2.0L - 2.0L * cosl(
            2.0L * acosl(-1.0L) / summary->factor_length);
        long double second_gap = 2.0L - 2.0L * cosl(
            2.0L * acosl(-1.0L) / source_order);
        summary->least_positive_hodge =
            first_gap < second_gap ? first_gap : second_gap;
    }
    ok = transition_ok && half_turn_ok;

cleanup:
    free(log_generator);
    free(seen);
    return ok;
}

int carry_completed_carrier_seam_values(
        int clock_size,
        long long *projected_numerator, long long *projected_denominator,
        long long *transverse_numerator, long long *transverse_denominator,
        long long *translated_numerator, long long *translated_denominator)
{
    if (!projected_numerator || !projected_denominator ||
        !transverse_numerator || !transverse_denominator ||
        !translated_numerator || !translated_denominator ||
        clock_size < 2 || clock_size > CCC_MAX_CLOCK)
        return 0;
    long long clock = clock_size;
    *projected_numerator = clock * clock - 2 * clock + 2;
    *projected_denominator = clock * clock;
    *transverse_numerator = 2 * (clock - 1);
    *transverse_denominator = clock * clock;
    *translated_numerator = 2 * (clock - 1);
    *translated_denominator = clock;
    ccc_reduce(projected_numerator, projected_denominator);
    ccc_reduce(transverse_numerator, transverse_denominator);
    ccc_reduce(translated_numerator, translated_denominator);
    return 1;
}

static long double ccc_cycle_gap(int frequency, int length)
{
    int reduced = ccc_positive_mod(frequency, length);
    long double angle = 2.0L * acosl(-1.0L) * reduced / length;
    return 2.0L - 2.0L * cosl(angle);
}

int carry_completed_carrier_product_gram(
        int first_length, int second_length,
        int first_step, int second_step,
        CarryCompletedCarrierGramSummary *summary)
{
    if (!summary || first_length < 2 || second_length < 2 ||
        first_length > CCC_MAX_CLOCK / second_length ||
        ccc_gcd(first_length, second_length) != 1 ||
        ccc_gcd(first_step, first_length) != 1 ||
        ccc_gcd(second_step, second_length) != 1)
        return 0;
    int clock_size = first_length * second_length;
    unsigned char *seen = calloc((size_t)clock_size, sizeof(*seen));
    if (!seen) return 0;

    long double trace = 0.0L;
    int golden_hits = 0;
    int bijective = 1;
    long double cubic_first = 0.0L;
    long double cubic_second = 0.0L;
    for (int first_frequency = 0;
         first_frequency < first_length; ++first_frequency) {
        for (int second_frequency = 0;
             second_frequency < second_length; ++second_frequency) {
            int clock_frequency = ccc_positive_mod(
                (long long)first_step * second_length * first_frequency +
                (long long)second_step * first_length * second_frequency,
                clock_size);
            if (seen[clock_frequency]) bijective = 0;
            seen[clock_frequency] = 1;
            long double response;
            if (first_frequency == 0 && second_frequency == 0) {
                response = (long double)first_step * first_step +
                           (long double)second_step * second_step;
            } else {
                long double denominator =
                    ccc_cycle_gap(first_frequency, first_length) +
                    ccc_cycle_gap(second_frequency, second_length);
                if (!(denominator > 0.0L)) {
                    free(seen);
                    return 0;
                }
                response = ccc_cycle_gap(clock_frequency, clock_size) /
                           denominator;
            }
            trace += response;
            long double residual = response * response -
                                   3.0L * response + 1.0L;
            if (fabsl(residual) < 1.0e-12L) golden_hits++;
            if (first_frequency == 0 && second_frequency == 1)
                cubic_first = response;
            if (first_frequency == 0 &&
                second_frequency == second_length - 1)
                cubic_second = response;
        }
    }
    for (int frequency = 0; frequency < clock_size; ++frequency)
        if (!seen[frequency]) bijective = 0;
    free(seen);

    *summary = (CarryCompletedCarrierGramSummary){0};
    summary->first_length = first_length;
    summary->second_length = second_length;
    summary->first_step = first_step;
    summary->second_step = second_step;
    summary->clock_size = clock_size;
    summary->frequency_bijection = bijective;
    summary->constant_response =
        (long double)first_step * first_step +
        (long double)second_step * second_step;
    summary->trace = trace;
    summary->golden_polynomial_hits = golden_hits;
    summary->first_centered_response = cubic_first;
    summary->second_centered_response = cubic_second;
    return bijective;
}

int carry_completed_carrier_inspect(
        int clock_size, int source_prime, int source_step)
{
    CarryCompletedCarrierSummary summary = {0};
    if (!carry_completed_carrier_compute(
            clock_size, source_prime, source_step, &summary)) {
        fprintf(stderr,
                "require N<=100000, an odd q=ord_p(s), p=2q+1 prime, q|N, and at most 5000000 completed states\n");
        return 1;
    }
    printf("Carry-completed cyclic carrier\n\n");
    printf("  clock N=%d; source prime p=%d; source step s=%d\n",
           summary.clock_size, summary.source_prime, summary.source_step);
    printf("  q=ord_p(s)=%d; complement generator g=-s=%d\n",
           summary.source_order, summary.complement_generator);
    printf("  ord_p(g)=p-1=%d and g^q=-1                 PASS\n",
           summary.source_prime - 1);
    printf("  completed cycle size M=2N(p-1)=%lld\n",
           summary.completed_size);
    printf("  quotient sizes M -> %lld -> %lld\n",
           summary.sheet_quotient_size, summary.clock_quotient_size);
    printf("  successor is addition by one in the exact coordinate  %s\n",
           summary.transition_conjugacy ? "PASS" : "FAIL");
    printf("  half-turn is source complement polarity               %s\n",
           summary.half_turn_complement ? "PASS" : "FAIL");
    if (summary.coprime_factorization) {
        printf("  product factors C_%d x C_%d\n",
               summary.factor_length, summary.source_order);
        printf("  cells over all lanes (C0,C1,C2)=(%lld,%lld,%lld)\n",
               summary.degree_zero_cells, summary.degree_one_cells,
               summary.degree_two_cells);
        printf("  least positive Hodge response=%.18Lf\n",
               summary.least_positive_hodge);
    } else {
        printf("  product-cycle factorization: unavailable because gcd(q,N/q)>1\n");
    }
    printf("\nResult  PASS\n");
    return 0;
}

int carry_completed_carrier_seam(int clock_size)
{
    long long projected_numerator = 0;
    long long projected_denominator = 0;
    long long transverse_numerator = 0;
    long long transverse_denominator = 0;
    long long translated_numerator = 0;
    long long translated_denominator = 0;
    if (!carry_completed_carrier_seam_values(
            clock_size, &projected_numerator, &projected_denominator,
            &transverse_numerator, &transverse_denominator,
            &translated_numerator, &translated_denominator)) {
        fprintf(stderr, "clock size must satisfy 2<=N<=100000\n");
        return 1;
    }
    printf("One-seam two-sheet compression\n\n");
    printf("  clock N=%d; seam weight c=1/%d\n", clock_size, clock_size);
    printf("  retained energy=");
    ccc_print_fraction(projected_numerator, projected_denominator);
    printf("\n  one-origin transverse energy=");
    ccc_print_fraction(transverse_numerator, transverse_denominator);
    printf("\n  retained + transverse=1                         PASS\n");
    printf("  sum over all translated origins=");
    ccc_print_fraction(translated_numerator, translated_denominator);
    printf("\n  translated energy=2(1-1/N)                     PASS\n");
    printf("\nResult  PASS\n");
    return 0;
}

int carry_completed_carrier_product(
        int first_length, int second_length,
        int first_step, int second_step)
{
    CarryCompletedCarrierGramSummary summary = {0};
    if (!carry_completed_carrier_product_gram(
            first_length, second_length, first_step, second_step, &summary)) {
        fprintf(stderr,
                "require coprime cycle lengths, each at least two, and steps primitive in their respective cycles\n");
        return 1;
    }
    printf("Coherent product-cycle carry Gram\n\n");
    printf("  product C_%d x C_%d; endpoint step=(%d,%d)\n",
           first_length, second_length, first_step, second_step);
    printf("  clock modes=%d; frequency map is bijective       %s\n",
           summary.clock_size,
           summary.frequency_bijection ? "PASS" : "FAIL");
    printf("  constant response=%.18Lf\n", summary.constant_response);
    printf("  numerical trace=%.18Lf\n", summary.trace);
    printf("  roots of x^2-3x+1 in the formed spectrum=%d\n",
           summary.golden_polynomial_hits);
    printf("  two centered second-factor responses=(%.18Lf, %.18Lf)\n",
           summary.first_centered_response,
           summary.second_centered_response);
    printf("  arithmetic status: finite Fourier evaluation in long double\n");
    printf("\nResult  PASS\n");
    return 0;
}

int carry_completed_carrier_verify(void)
{
    int topology_ok = 1;
    int topology_models = 0;
    const int clocks[] = {3, 6, 15, 22, 30};
    const int primes[] = {7, 7, 11, 23, 7};
    const int steps[] = {2, 2, 3, 2, 2};
    for (size_t index = 0; index < sizeof(clocks) / sizeof(clocks[0]); ++index) {
        CarryCompletedCarrierSummary summary = {0};
        topology_models++;
        if (!carry_completed_carrier_compute(
                clocks[index], primes[index], steps[index], &summary) ||
            !summary.transition_conjugacy || !summary.half_turn_complement)
            topology_ok = 0;
    }

    CarryCompletedCarrierSummary base_thirty = {0};
    int tower_ok = carry_completed_carrier_compute(
        30, 7, 2, &base_thirty) &&
        base_thirty.completed_size == 360 &&
        base_thirty.sheet_quotient_size == 60 &&
        base_thirty.clock_quotient_size == 30 &&
        base_thirty.degree_zero_cells == 180 &&
        base_thirty.degree_one_cells == 360 &&
        base_thirty.degree_two_cells == 180 &&
        fabsl(base_thirty.least_positive_hodge -
              (3.0L - sqrtl(5.0L)) / 2.0L) < 1.0e-17L;

    int seam_ok = 1;
    int seam_models = 0;
    for (int clock = 2; clock <= 1000; ++clock) {
        long long pn = 0, pd = 0, tn = 0, td = 0, an = 0, ad = 0;
        seam_models++;
        if (!carry_completed_carrier_seam_values(
                clock, &pn, &pd, &tn, &td, &an, &ad) ||
            pn * td + tn * pd != pd * td ||
            an * td != (long long)clock * tn * ad)
            seam_ok = 0;
    }
    long long pn = 0, pd = 0, tn = 0, td = 0, an = 0, ad = 0;
    int base_thirty_seam = carry_completed_carrier_seam_values(
        30, &pn, &pd, &tn, &td, &an, &ad) &&
        pn == 421 && pd == 450 && tn == 29 && td == 450 &&
        an == 29 && ad == 15;

    CarryCompletedCarrierGramSummary gram = {0};
    int gram_ok = carry_completed_carrier_product_gram(
        10, 3, -3, 1, &gram) &&
        gram.clock_size == 30 && gram.frequency_bijection &&
        fabsl(gram.constant_response - 10.0L) < 1.0e-18L &&
        fabsl(gram.trace - 30.0L * 2691.0L / 2030.0L) < 1.0e-12L &&
        gram.golden_polynomial_hits == 4 &&
        fabsl(gram.first_centered_response - 1.0L) < 1.0e-17L &&
        fabsl(gram.second_centered_response - 1.0L) < 1.0e-17L;

    int rejection_ok = 1;
    CarryCompletedCarrierSummary rejected = {0};
    CarryCompletedCarrierGramSummary rejected_gram = {0};
    rejection_ok =
        !carry_completed_carrier_compute(30, 7, 3, &rejected) &&
        !carry_completed_carrier_compute(31, 7, 2, &rejected) &&
        !carry_completed_carrier_compute(30, 9, 2, &rejected) &&
        !carry_completed_carrier_product_gram(
            10, 4, -3, 1, &rejected_gram);

    int passed = topology_ok + tower_ok + seam_ok + base_thirty_seam +
                 gram_ok + rejection_ok;
    printf("Carry-completed carrier verification\n\n");
    printf("  exact cyclic-coordinate models=%d                     %s\n",
           topology_models, topology_ok ? "PASS" : "FAIL");
    printf("  exact 360 -> 60 -> 30 tower and Hodge ledger          %s\n",
           tower_ok ? "PASS" : "FAIL");
    printf("  exact seam-energy models=%d                            %s\n",
           seam_models, seam_ok ? "PASS" : "FAIL");
    printf("  exact N=30 energies 421/450, 29/450, and 29/15        %s\n",
           base_thirty_seam ? "PASS" : "FAIL");
    printf("  thirty-mode Gram, trace, cubic pair, and golden roots %s\n",
           gram_ok ? "PASS" : "FAIL");
    printf("  unsupported parameter rejection                       %s\n",
           rejection_ok ? "PASS" : "FAIL");
    printf("\n%d/6 verification groups passed.\n", passed);
    printf("Computed  carrier topology and seam laws use exact integers and rationals.\n");
    printf("Computed  product-cycle Fourier responses use long double after the exact mode map.\n");
    printf("Open  the graded boundary-response operator and its scalar trace.\n");
    return passed == 6;
}

void carry_completed_carrier_help(void)
{
    printf(
        "Carry-completed cyclic carriers\n\n"
        "Commands\n"
        "  nfield carry-completed-carrier inspect <N> <p> <s>\n"
        "  nfield carry-completed-carrier seam <N>\n"
        "  nfield carry-completed-carrier product <L> <q> <a> <b>\n"
        "  nfield carry-completed-carrier verify\n"
        "  nfield verify carry-completed-carrier\n\n"
        "Objects\n"
        "  inspect   Let q=ord_p(s), require odd q, p=2q+1, and q|N.\n"
        "            Construct the 2N(p-1) coordinate, both quotient levels,\n"
        "            complement half-turn, and the coprime product cellulation.\n"
        "  seam      Compute retained, transverse, and all-origin seam energy\n"
        "            exactly for an N-position two-sheet clock.\n"
        "  product   Form the coherent Fourier response for endpoint step (a,b)\n"
        "            on C_L x C_q. The mode map is exact; responses are numerical.\n\n"
        "Scope\n"
        "  exact      cyclic conjugacy, quotient sizes, complement, cell counts,\n"
        "             seam energies, and the product frequency map.\n"
        "  numerical  cosine Hodge gaps and product-cycle response values.\n"
        "  external   exact rational face quotient and finite-field carrier blocks\n"
        "             are separate C certificates in the repository.\n"
        "  open       canonical assembly into a graded boundary response.\n"
    );
}
