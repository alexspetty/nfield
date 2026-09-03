/* Exact conductor ledger for signed boundaries of finite residue weights. */

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"

#define BCL_MAX_MODULUS 200000
#define BCL_MAX_ABS_WEIGHT 1000

int nfield_terminal_collision_conductor_ledger_run(int report);

static int bcl_gcd(int left, int right)
{
    while (right != 0) {
        int remainder = left % right;
        left = right;
        right = remainder;
    }
    return left < 0 ? -left : left;
}

static int bcl_totient(int value)
{
    int result = value;
    int remaining = value;
    for (int prime = 2; prime <= remaining / prime; prime++) {
        if (remaining % prime != 0) continue;
        result -= result / prime;
        while (remaining % prime == 0) remaining /= prime;
    }
    if (remaining > 1) result -= result / remaining;
    return result;
}

static int bcl_mobius(int value)
{
    int factors = 0;
    int remaining = value;
    for (int prime = 2; prime <= remaining / prime; prime++) {
        if (remaining % prime != 0) continue;
        remaining /= prime;
        factors++;
        if (remaining % prime == 0) return 0;
        while (remaining % prime == 0) remaining /= prime;
    }
    if (remaining > 1) factors++;
    return factors % 2 == 0 ? 1 : -1;
}

static int bcl_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0)
            return 0;
    return 1;
}

static int bcl_odd_prime_power(int modulus, int *prime, int *depth)
{
    if (!prime || !depth || modulus < 3 || modulus % 2 == 0) return 0;
    int factor = 0;
    for (int candidate = 3; candidate <= modulus / candidate; candidate += 2)
        if (modulus % candidate == 0) {
            factor = candidate;
            break;
        }
    if (factor == 0) factor = modulus;
    if (!bcl_is_prime(factor)) return 0;
    int remaining = modulus;
    int exponent = 0;
    while (remaining % factor == 0) {
        remaining /= factor;
        exponent++;
    }
    if (remaining != 1) return 0;
    *prime = factor;
    *depth = exponent;
    return 1;
}

static int bcl_power(int base, int exponent, int *value)
{
    if (!value || base < 2 || exponent < 1) return 0;
    int result = 1;
    for (int index = 0; index < exponent; index++) {
        if (result > BCL_MAX_MODULUS / base) return 0;
        result *= base;
    }
    *value = result;
    return 1;
}

static int bcl_store(__int128 value, long long *target)
{
    if (!target || value < LLONG_MIN || value > LLONG_MAX) return 0;
    *target = (long long)value;
    return 1;
}

static int bcl_pushdown_invariants(
        const long long *boundary, int modulus, int divisor,
        long long *diagonal, long long *antipodal, int *nonzero)
{
    long long *pushdown = calloc((size_t)divisor, sizeof(*pushdown));
    if (!pushdown || !diagonal || !antipodal || !nonzero) {
        free(pushdown);
        return 0;
    }
    for (int residue = 0; residue < modulus; residue++)
        if (bcl_gcd(residue, modulus) == 1)
            pushdown[residue % divisor] += boundary[residue];

    __int128 diagonal_sum = 0;
    __int128 antipodal_sum = 0;
    *nonzero = 0;
    for (int residue = 0; residue < divisor; residue++) {
        if (bcl_gcd(residue, divisor) != 1) continue;
        int opposite = (divisor - residue) % divisor;
        if (pushdown[residue] != 0) *nonzero = 1;
        diagonal_sum += (__int128)pushdown[residue] * pushdown[residue];
        antipodal_sum += (__int128)pushdown[residue] * pushdown[opposite];
    }
    int ok = bcl_store(diagonal_sum, diagonal) &&
             bcl_store(antipodal_sum, antipodal);
    free(pushdown);
    return ok;
}

static long long bcl_pushdown_value(
        const long long *boundary, int modulus, int divisor, int residue)
{
    long long value = 0;
    for (int index = 0; index < modulus; index++)
        if (bcl_gcd(index, modulus) == 1 && index % divisor == residue)
            value += boundary[index];
    return value;
}

static int bcl_primitive_odd_count(int modulus, int *count)
{
    __int128 twice_count = 0;
    if (!count) return 0;
    for (int divisor = 1; divisor <= modulus; divisor++) {
        if (modulus % divisor != 0) continue;
        int coefficient = bcl_mobius(modulus / divisor);
        int fixed_by_negation = 2 % divisor == 0;
        twice_count += (__int128)coefficient * bcl_totient(divisor) *
                       (1 - fixed_by_negation);
    }
    if (twice_count < 0 || twice_count % 2 != 0 ||
        twice_count / 2 > INT_MAX)
        return 0;
    *count = (int)(twice_count / 2);
    return 1;
}

static const BoundaryConductorLedgerRow *bcl_find_ledger_row(
        const BoundaryConductorLedgerSummary *summary, int divisor)
{
    for (int index = 0; index < summary->row_count; index++)
        if (summary->row[index].divisor == divisor)
            return &summary->row[index];
    return NULL;
}

int boundary_conductor_ledger_compute(
        int modulus, const int *weights, int weight_count,
        BoundaryConductorLedgerSummary *summary)
{
    long long *boundary = NULL;
    __int128 unit_norm = 0;
    __int128 twice_moment = 0;
    int binary = 1;
    int ok = 0;

    if (!summary || !weights || modulus < 3 || modulus > BCL_MAX_MODULUS ||
        weight_count != modulus)
        return 0;
    *summary = (BoundaryConductorLedgerSummary){
        .modulus = modulus,
        .conductor_balance = -1,
        .proper_pushdowns_vanish = 1,
        .top_concentrated = 1
    };
    boundary = calloc((size_t)modulus, sizeof(*boundary));
    if (!boundary) return 0;

    for (int cell = 0; cell < modulus; cell++) {
        if (weights[cell] < -BCL_MAX_ABS_WEIGHT ||
            weights[cell] > BCL_MAX_ABS_WEIGHT)
            goto cleanup;
        if (weights[cell] != 0 && weights[cell] != 1) binary = 0;
        int previous = cell == 0 ? modulus - 1 : cell - 1;
        boundary[cell] = (long long)weights[previous] - weights[cell];
        if (boundary[cell] != 0) summary->cyclic_boundary_points++;
    }
    if (binary) {
        int intervals = 0;
        for (int cell = 0; cell < modulus; cell++)
            if (weights[cell] == 1 &&
                (cell == 0 || weights[cell - 1] == 0))
                intervals++;
        summary->formal_boundary = 2 * intervals;
    } else {
        summary->formal_boundary = -1;
    }

    summary->antipodal_odd = 1;
    for (int residue = 0; residue < modulus; residue++) {
        if (bcl_gcd(residue, modulus) != 1) continue;
        int opposite = (modulus - residue) % modulus;
        unit_norm += (__int128)boundary[residue] * boundary[residue];
        if (boundary[opposite] != -boundary[residue])
            summary->antipodal_odd = 0;
    }
    if (!bcl_store(unit_norm, &summary->unit_norm)) goto cleanup;

    for (int divisor = 1; divisor <= modulus; divisor++) {
        if (modulus % divisor != 0) continue;
        int coefficient = bcl_mobius(modulus / divisor);
        if (summary->row_count >= NFIELD_BOUNDARY_LEDGER_MAX_ROWS)
            goto cleanup;
        BoundaryConductorLedgerRow *row =
            &summary->row[summary->row_count++];
        row->divisor = divisor;
        row->mobius = coefficient;
        row->totient = bcl_totient(divisor);
        if (!bcl_pushdown_invariants(
                boundary, modulus, divisor,
                &row->diagonal, &row->antipodal,
                &row->pushdown_nonzero))
            goto cleanup;
        row->difference = row->diagonal - row->antipodal;
        __int128 twice_contribution =
            (__int128)row->mobius * row->totient * row->difference;
        if (!bcl_store(twice_contribution, &row->twice_contribution))
            goto cleanup;
        twice_moment += twice_contribution;
        if (divisor < modulus && row->pushdown_nonzero)
            summary->proper_pushdowns_vanish = 0;
    }
    if (twice_moment % 2 != 0 ||
        !bcl_store(twice_moment / 2,
                   &summary->primitive_odd_moment) ||
        !bcl_primitive_odd_count(
            modulus, &summary->primitive_odd_characters))
        goto cleanup;

    for (int conductor = 1; conductor <= modulus; conductor++) {
        if (modulus % conductor != 0) continue;
        if (summary->energy_count >= NFIELD_BOUNDARY_LEDGER_MAX_ROWS)
            goto cleanup;
        BoundaryConductorEnergyRow *energy =
            &summary->energy[summary->energy_count++];
        energy->conductor = conductor;
        if (!bcl_primitive_odd_count(
                conductor, &energy->primitive_odd_characters))
            goto cleanup;

        __int128 twice_energy = 0;
        for (int divisor = 1; divisor <= conductor; divisor++) {
            if (conductor % divisor != 0) continue;
            const BoundaryConductorLedgerRow *row =
                bcl_find_ledger_row(summary, divisor);
            if (!row) goto cleanup;
            twice_energy +=
                (__int128)bcl_mobius(conductor / divisor) *
                row->totient * row->difference;
        }
        if (twice_energy < 0 || twice_energy % 2 != 0 ||
            !bcl_store(twice_energy / 2, &energy->energy))
            goto cleanup;

        __int128 full =
            (__int128)summary->full_odd_energy + energy->energy;
        if (!bcl_store(full, &summary->full_odd_energy))
            goto cleanup;
        if (conductor == modulus) {
            summary->top_conductor_energy = energy->energy;
        } else {
            __int128 proper =
                (__int128)summary->proper_conductor_energy + energy->energy;
            if (!bcl_store(proper, &summary->proper_conductor_energy))
                goto cleanup;
        }
    }

    {
        const BoundaryConductorLedgerRow *top =
            bcl_find_ledger_row(summary, modulus);
        long long direct_full = 0;
        if (!top ||
            !bcl_store((__int128)top->totient * top->difference / 2,
                       &direct_full) ||
            top->totient * (__int128)top->difference % 2 != 0 ||
            direct_full != summary->full_odd_energy ||
            summary->top_conductor_energy !=
                summary->primitive_odd_moment ||
            summary->full_odd_energy !=
                summary->proper_conductor_energy +
                summary->top_conductor_energy)
            goto cleanup;
    }
    summary->top_concentrated =
        summary->proper_conductor_energy == 0;

    if (summary->primitive_odd_characters > 0) {
        long long divisor = summary->primitive_odd_characters;
        long long common = bcl_gcd(
            (int)(summary->primitive_odd_moment % divisor), (int)divisor);
        if (common == 0) common = divisor;
        summary->mean_numerator = summary->primitive_odd_moment / common;
        summary->mean_denominator = divisor / common;
    }

    {
        int prime = 0;
        int depth = 0;
        if (bcl_odd_prime_power(modulus, &prime, &depth) && depth >= 2) {
            int lower = modulus / prime;
            summary->conductor_balance = 1;
            for (int residue = 0; residue < lower; residue++)
                if (bcl_gcd(residue, lower) == 1 &&
                    bcl_pushdown_value(
                        boundary, modulus, lower, residue) != 0) {
                    summary->conductor_balance = 0;
                    break;
                }
        }
    }
    ok = 1;

cleanup:
    free(boundary);
    return ok;
}

static int bcl_parse_support(
        const char *text, int modulus, int *weights, int *support_size)
{
    if (!text || !*text || !weights || !support_size) return 0;
    const char *cursor = text;
    int count = 0;
    while (*cursor != '\0') {
        char *end = NULL;
        long cell = strtol(cursor, &end, 10);
        if (end == cursor || cell < 0 || cell >= modulus ||
            weights[cell] != 0)
            return 0;
        weights[cell] = 1;
        count++;
        if (*end == '\0') break;
        if (*end != ',') return 0;
        cursor = end + 1;
        if (*cursor == '\0') return 0;
    }
    *support_size = count;
    return count > 0;
}

static void bcl_print_summary(
        const BoundaryConductorLedgerSummary *summary)
{
    printf("  top-conductor Mobius ledger\n");
    printf("  d       mu  phi       D       A     D-A  nonzero  twice term\n");
    for (int index = 0; index < summary->row_count; index++) {
        const BoundaryConductorLedgerRow *row = &summary->row[index];
        printf("  %-7d %3d %4d %7lld %7lld %7lld %8s %11lld\n",
               row->divisor, row->mobius, row->totient,
               row->diagonal, row->antipodal, row->difference,
               row->pushdown_nonzero ? "yes" : "no",
               row->twice_contribution);
    }
    printf("\n  exact-conductor spectrum\n");
    printf("  d       primitive odd characters       energy\n");
    for (int index = 0; index < summary->energy_count; index++) {
        const BoundaryConductorEnergyRow *energy = &summary->energy[index];
        printf("  %-7d %24d %12lld\n",
               energy->conductor, energy->primitive_odd_characters,
               energy->energy);
    }
    printf("\n  cyclic boundary points=%d; formal boundary=%d\n",
           summary->cyclic_boundary_points, summary->formal_boundary);
    printf("  unit-boundary squared norm=%lld\n", summary->unit_norm);
    printf("  antipodal oddness=%s; conductor balance=%s\n",
           summary->antipodal_odd ? "yes" : "no",
           summary->conductor_balance < 0 ? "not a depth-two prime power" :
           summary->conductor_balance ? "yes" : "no");
    printf("  all proper pushdowns vanish=%s\n",
           summary->proper_pushdowns_vanish ? "yes" : "no");
    printf("  top-conductor concentration=%s\n",
           summary->top_concentrated ? "yes" : "no");
    printf("  primitive odd moment=%lld; characters=%d; mean=%lld/%lld\n",
           summary->primitive_odd_moment,
           summary->primitive_odd_characters,
           summary->mean_numerator, summary->mean_denominator);
    printf("  exact energies: proper=%lld; top=%lld; full=%lld\n",
           summary->proper_conductor_energy,
           summary->top_conductor_energy,
           summary->full_odd_energy);
}

int boundary_conductor_ledger_inspect(int modulus, const char *support)
{
    if (modulus < 3 || modulus > BCL_MAX_MODULUS) {
        fprintf(stderr, "require 3<=modulus<=200000\n");
        return 1;
    }
    int *weights = calloc((size_t)modulus, sizeof(*weights));
    if (!weights) return 1;
    int support_size = 0;
    if (!bcl_parse_support(
            support, modulus, weights, &support_size)) {
        fprintf(stderr,
                "support must be a comma-separated list of distinct cells in [0,modulus)\n");
        free(weights);
        return 1;
    }
    BoundaryConductorLedgerSummary summary = {0};
    int ok = boundary_conductor_ledger_compute(
        modulus, weights, modulus, &summary);
    printf("Boundary conductor ledger\n\n");
    printf("  modulus=%d; support=%s; marked cells=%d\n\n",
           modulus, support, support_size);
    if (ok) bcl_print_summary(&summary);
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    free(weights);
    return ok ? 0 : 1;
}

static int bcl_terminal_weights(
        int base, int depth, int *modulus, int **weights)
{
    if (!modulus || !weights || depth < 2 ||
        !bcl_power(base, depth, modulus))
        return 0;
    *weights = calloc((size_t)*modulus, sizeof(**weights));
    if (!*weights) return 0;
    int leading = 1;
    int middle_count = 1;
    for (int index = 1; index < depth; index++) leading *= base;
    for (int index = 2; index < depth; index++) middle_count *= base;
    for (int digit = 0; digit < base; digit++)
        for (int middle = 0; middle < middle_count; middle++)
            (*weights)[digit * leading + base * middle + digit] = 1;
    return 1;
}

int boundary_conductor_ledger_terminal(int base, int depth)
{
    int modulus = 0;
    int *weights = NULL;
    if (!bcl_terminal_weights(base, depth, &modulus, &weights)) {
        fprintf(stderr,
                "require base>=2, depth>=2, and base^depth<=20000\n");
        return 1;
    }
    BoundaryConductorLedgerSummary summary = {0};
    int ok = boundary_conductor_ledger_compute(
        modulus, weights, modulus, &summary);
    printf("Terminal collision boundary conductor ledger\n\n");
    printf("  base=%d depth=%d modulus=%d\n\n", base, depth, modulus);
    if (ok) bcl_print_summary(&summary);
    printf("\nResult  %s\n", ok ? "PASS" : "FAIL");
    free(weights);
    return ok ? 0 : 1;
}

static const BoundaryConductorEnergyRow *bcl_find_energy_row(
        const BoundaryConductorLedgerSummary *summary, int conductor)
{
    for (int index = 0; index < summary->energy_count; index++)
        if (summary->energy[index].conductor == conductor)
            return &summary->energy[index];
    return NULL;
}

int boundary_conductor_ledger_verify(void)
{
    int base_nine_ok = 1;
    int prime_power_ok = 1;
    int base_fifteen_ok = 1;
    int sufficient_not_necessary_ok = 1;
    int embedded_ok = nfield_terminal_collision_conductor_ledger_run(0) == 0;
    int domain_ok = 1;
    int prime_power_models = 0;

    {
        int weights[9] = {1, 0, 0, 0, 1, 0, 0, 0, 1};
        BoundaryConductorLedgerSummary summary = {0};
        base_nine_ok = boundary_conductor_ledger_compute(
            9, weights, 9, &summary) &&
            summary.formal_boundary == 6 && summary.unit_norm == 4 &&
            summary.primitive_odd_moment == 24 &&
            summary.primitive_odd_characters == 2 &&
            summary.mean_numerator == 12 && summary.mean_denominator == 1 &&
            summary.antipodal_odd && summary.conductor_balance &&
            summary.proper_pushdowns_vanish && summary.top_concentrated &&
            summary.proper_conductor_energy == 0 &&
            summary.top_conductor_energy == 24 &&
            summary.full_odd_energy == 24;
    }

    static const int primes[] = {3, 5, 7, 11};
    for (size_t index = 0;
         index < sizeof(primes) / sizeof(primes[0]); index++) {
        for (int depth = 2; depth <= 3; depth++) {
            int modulus = 0;
            int *weights = NULL;
            BoundaryConductorLedgerSummary summary = {0};
            if (!bcl_terminal_weights(
                    primes[index], depth, &modulus, &weights) ||
                !boundary_conductor_ledger_compute(
                    modulus, weights, modulus, &summary) ||
                summary.formal_boundary != 2 * modulus / primes[index] ||
                summary.primitive_odd_moment !=
                    (long long)bcl_totient(modulus) * summary.unit_norm ||
                summary.mean_numerator != 2LL * summary.formal_boundary ||
                summary.mean_denominator != 1 ||
                !summary.antipodal_odd || !summary.conductor_balance ||
                !summary.proper_pushdowns_vanish ||
                !summary.top_concentrated ||
                summary.proper_conductor_energy != 0 ||
                summary.top_conductor_energy !=
                    summary.primitive_odd_moment)
                prime_power_ok = 0;
            else
                prime_power_models++;
            free(weights);
        }
    }

    {
        int modulus = 0;
        int *weights = NULL;
        BoundaryConductorLedgerSummary summary = {0};
        if (!bcl_terminal_weights(15, 2, &modulus, &weights) ||
            !boundary_conductor_ledger_compute(
                modulus, weights, modulus, &summary)) {
            base_fifteen_ok = 0;
        } else {
            const BoundaryConductorLedgerRow *row15 =
                bcl_find_ledger_row(&summary, 15);
            const BoundaryConductorLedgerRow *row45 =
                bcl_find_ledger_row(&summary, 45);
            const BoundaryConductorLedgerRow *row75 =
                bcl_find_ledger_row(&summary, 75);
            const BoundaryConductorLedgerRow *row225 =
                bcl_find_ledger_row(&summary, 225);
            static const int conductors[] = {1, 3, 5, 9, 15, 25, 45, 75, 225};
            static const long long energies[] = {0, 0, 0, 24, 0, 240, 360, 400, 896};
            base_fifteen_ok = row15 && row45 && row75 && row225 &&
                row15->difference == 0 && row45->difference == 32 &&
                row75->difference == 32 && row225->difference == 32 &&
                summary.formal_boundary == 30 &&
                summary.primitive_odd_moment == 896 &&
                summary.primitive_odd_characters == 32 &&
                summary.mean_numerator == 28 && summary.mean_denominator == 1 &&
                !summary.proper_pushdowns_vanish &&
                !summary.top_concentrated &&
                summary.proper_conductor_energy == 1024 &&
                summary.top_conductor_energy == 896 &&
                summary.full_odd_energy == 1920;
            for (size_t index = 0;
                 index < sizeof(conductors) / sizeof(conductors[0]); index++) {
                const BoundaryConductorEnergyRow *energy =
                    bcl_find_energy_row(&summary, conductors[index]);
                if (!energy || energy->energy != energies[index])
                    base_fifteen_ok = 0;
            }
        }
        free(weights);
    }

    {
        int weights[25] = {0};
        BoundaryConductorLedgerSummary summary = {0};
        for (int first = 0; first < 5; first++)
            for (int second = first + 1; second < 5; second++)
                weights[5 * first + second] = 1;
        if (!boundary_conductor_ledger_compute(
                25, weights, 25, &summary)) {
            sufficient_not_necessary_ok = 0;
        } else {
            const BoundaryConductorLedgerRow *pushdown =
                bcl_find_ledger_row(&summary, 5);
            const BoundaryConductorEnergyRow *energy =
                bcl_find_energy_row(&summary, 5);
            sufficient_not_necessary_ok =
                pushdown && energy && pushdown->pushdown_nonzero &&
                energy->energy == 0 &&
                !summary.proper_pushdowns_vanish &&
                summary.top_concentrated &&
                summary.proper_conductor_energy == 0;
        }
    }

    {
        int weights[9] = {0};
        BoundaryConductorLedgerSummary summary = {0};
        domain_ok = !boundary_conductor_ledger_compute(2, weights, 9, &summary) &&
                    !boundary_conductor_ledger_compute(9, weights, 8, &summary) &&
                    !boundary_conductor_ledger_compute(
                        BCL_MAX_MODULUS + 1, weights, 9, &summary);
    }

    int passed = base_nine_ok + prime_power_ok + base_fifteen_ok +
                 sufficient_not_necessary_ok + embedded_ok + domain_ok;
    printf("Boundary conductor ledger verification\n\n");
    printf("  modulus-nine boundary moment and mean twelve       %s\n",
           base_nine_ok ? "PASS" : "FAIL");
    printf("  terminal odd-prime-power models=%d                 %s\n",
           prime_power_models, prime_power_ok ? "PASS" : "FAIL");
    printf("  base-fifteen exact spectrum 1024+896=1920          %s\n",
           base_fifteen_ok ? "PASS" : "FAIL");
    printf("  nonzero pushdown with zero proper odd energy       %s\n",
           sufficient_not_necessary_ok ? "PASS" : "FAIL");
    printf("  independent terminal-ledger audit agreement        %s\n",
           embedded_ok ? "PASS" : "FAIL");
    printf("  modulus, weight-count, and capacity rejection      %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("\n%d/6 verification groups passed.\n", passed);
    printf("Exact boundary  every endpoint, pushdown, Mobius coefficient,\n");
    printf("exact-conductor energy, primitive moment, and reduced mean uses\n");
    printf("signed integer arithmetic. Each exact energy is checked nonnegative.\n");
    printf("Scope  arbitrary bounded integer weights on finite residue spaces;\n");
    printf("terminal diagonals are generated examples, not a separate theory.\n");
    return passed == 6;
}

void boundary_conductor_ledger_help(void)
{
    printf(
        "Boundary conductor ledger\n\n"
        "Commands\n"
        "  nfield boundary-conductor-ledger inspect <modulus>\n"
        "      --support <cell,cell,...>\n"
        "      Build every divisor pushdown and the exact-conductor spectrum.\n"
        "  nfield boundary-conductor-ledger terminal <base> <depth>\n"
        "      Generate the first-digit/last-digit collision boundary.\n"
        "  nfield boundary-conductor-ledger verify\n"
        "  nfield verify boundary-conductor-ledger\n\n"
        "Examples\n"
        "  nfield boundary-conductor-ledger inspect 9 --support 0,4,8\n"
        "  nfield boundary-conductor-ledger terminal 15 2\n\n"
        "Scope\n"
        "  exact        signed boundary, unit pushdowns, diagonal and antipodal\n"
        "               terms, Mobius coefficients, primitive odd moments,\n"
        "               nonnegative exact-conductor energies, totals, and mean.\n"
        "  criterion    reports antipodal oddness, prime-power conductor balance,\n"
        "               exact top-conductor concentration, and the stronger\n"
        "               sufficient condition that all proper pushdowns vanish.\n"
        "  boundary     3<=modulus<=200000 with bounded integer weights; the CLI\n"
        "               accepts indicator supports and the library accepts\n"
        "               arbitrary bounded integer weights.\n"
    );
}

int terminal_collision_conductor_ledger_audit(void)
{
    printf("Terminal collision conductor ledger\n");
    printf("Exact finite integer audit\n\n");

    if (nfield_terminal_collision_conductor_ledger_run(1) != 0) {
        printf("\nResult  FAIL\n");
        return 1;
    }

    printf("\nCoverage  eight odd-prime-power cases and one base-15 ledger.\n");
    printf("Classification  exact finite confirmation of the displayed cases.\n");
    printf("Result  PASS\n");
    return 0;
}

int terminal_collision_conductor_ledger_verify(void)
{
    int ok = nfield_terminal_collision_conductor_ledger_run(0) == 0;

    printf("Terminal collision conductor ledger verification\n\n");
    printf("  eight declared prime-power cases               %s\n",
           ok ? "PASS" : "FAIL");
    printf("  base-15 active-conductor ledger and mean 28     %s\n",
           ok ? "PASS" : "FAIL");
    printf("  exact integer endpoint and conductor arithmetic %s\n",
           ok ? "PASS" : "FAIL");
    printf("\n3/3 verification groups %s.\n",
           ok ? "passed" : "did not pass");
    printf("Compatibility  fixed audit retained beside the parameterized ledger.\n");
    return ok;
}

void terminal_collision_conductor_ledger_help(void)
{
    printf(
        "Terminal collision conductor ledger\n\n"
        "Commands\n"
        "  nfield terminal-collision-conductor-ledger audit\n"
        "      Reproduce the eight prime-power rows and the base-15 ledger.\n"
        "  nfield terminal-collision-conductor-ledger verify\n"
        "  nfield verify terminal-collision-conductor-ledger\n\n"
        "Scope\n"
        "  exact finite     p in {3,5,7,11}, depth N in {2,3}.\n"
        "  composite case  base 15, modulus 225, active conductors 45 and 75,\n"
        "                  moment 896, 32 primitive odd characters, mean 28.\n"
        "  arithmetic      signed endpoint counts and the primitive odd\n"
        "                  conductor kernel, all evaluated with integers.\n"
        "  compatibility   this fixed audit is retained for regression; use\n"
        "                  boundary-conductor-ledger for parameterized inputs.\n"
    );
}
