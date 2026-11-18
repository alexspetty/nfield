/* Installed C99 research-profile consumer with independent finite examples. */
#include <nfield/research.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned checks;
#define CHECK(condition) do { ++checks; if (!(condition)) { \
    fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #condition); exit(1); \
} } while (0)

static int near(long double a, long double b)
{
    return fabsl(a - b) <= 2e-11L * (1 + fabsl(a) + fabsl(b));
}

static void expansions(void)
{
    static const int digits[] = {1,4,2,8,5,7};
    Repetend r = repetend_compute(1,7,10);
    CHECK(r.len == 6 && r.cycle_start == 0 && r.cycle_len == 6);
    for (int i=0; i<18; ++i) CHECK(repetend_digit_at(&r,i) == digits[i%6]);
    repetend_free(&r);
    r = repetend_compute(1,8,10);
    CHECK(r.len == 3 && r.cycle_len == 0);
    CHECK(r.digits[0] == 1 && r.digits[1] == 2 && r.digits[2] == 5);
    repetend_free(&r);

    Field f = field_build(7,10);
    CHECK(f.n == 7 && f.base == 10 && f.num_rows == 6);
    for (int i=0; i<6; ++i) {
        CHECK(f.rows[i].k == i+1 && f.rows[i].rep.cycle_len == 6);
        int remainder = i+1;
        for (int j=0; j<6; ++j) {
            CHECK(f.rows[i].rep.digits[j] == (10*remainder)/7);
            remainder = (10*remainder)%7;
        }
    }
    field_free(&f);
    CHECK(mult_order(10,7) == 6);
    CHECK(mult_order(10,11) == 2);
    CHECK(is_b_smooth(360,30) && !is_b_smooth(77,30));
}

static int direct_collisions(int p, int base, int multiplier)
{
    int count=0;
    for (int r=1; r<p; ++r)
        count += base*r/p == base*((r*multiplier)%p)/p;
    return count;
}

static void collision_and_spectrum(void)
{
    static const int primes[] = {3,5,7,11,13,17};
    for (unsigned pi=0; pi<sizeof(primes)/sizeof(primes[0]); ++pi) {
        int p=primes[pi];
        for (int base=2; base<=10; ++base) {
            int direct,table,unit;
            CHECK(all_prime_collision_label_value(p,base,1,&direct,&table,&unit));
            CHECK(direct == direct_collisions(p,base,base%p)-(p-1)/base);
            CHECK(unit == (base%p != 0));
            CHECK(table == (unit ? direct : 0));
            if (!unit) continue;
            int sizes[10],count=0;
            CHECK(spectral_power_bin_sizes(p,base,sizes,10,&count));
            CHECK(count == base);
            for (int digit=0; digit<base; ++digit) {
                int expected=0;
                for (int r=1; r<p; ++r) expected += base*r/p == digit;
                CHECK(sizes[digit] == expected);
            }
            for (int multiplier=1; multiplier<p; ++multiplier) {
                int a,b;
                CHECK(autocorrelation_collision_count(p,base,multiplier,&a));
                CHECK(a == direct_collisions(p,base,multiplier));
                if (base < p) {
                    CHECK(bin_derangements_collision_count(p,base,multiplier,&b));
                    CHECK(b == a);
                } else {
                    CHECK(!bin_derangements_collision_count(p,base,multiplier,&b));
                }
            }
            double power[17];
            CHECK(spectral_power_values(p,base,power,17,&count));
            CHECK(count == p);
            /* Pair expansion of the squared transform, independent of the
             * implementation's per-bin real/imaginary accumulation. */
            for (int k=0; k<p; ++k) {
                long double expected=0;
                for (int r=1; r<p; ++r) for (int t=1; t<p; ++t)
                    if (base*r/p == base*t/p)
                        expected += cosl(2*acosl(-1.0L)*k*(r-t)/p);
                CHECK(near(power[k],expected));
            }
        }
    }
    int values[10],count;
    CHECK(!spectral_power_bin_sizes(9,10,values,10,&count));
    CHECK(!spectral_power_bin_sizes(7,10,values,9,&count));
    CHECK(!all_prime_collision_label_value(9,10,1,values,values+1,values+2));
}

static void cylinders_and_boundaries(void)
{
    const int weights[] = {1,-2,3,0};
    long long intrinsic,boundary,bulk,left,right;
    CHECK(finite_prefix_slice_identity(5,2,2,weights,4,
        &intrinsic,&boundary,&bulk,&left,&right));
    CHECK(intrinsic == 2 && boundary == 0 && bulk == 2 && left == -2 && right == -2);
    CHECK(finite_prefix_slice_identity_all_denominators(6,2,2,weights,4,
        &intrinsic,&boundary,&bulk,&left,&right));
    CHECK(intrinsic == 5 && boundary == 4 && bulk == 2 && left == 12 && right == 12);
    CHECK(!finite_prefix_slice_identity(6,2,2,weights,4,
        &intrinsic,&boundary,&bulk,&left,&right));
    int transient,persistent,depth,kernel,image;
    CHECK(positional_transport_collapse(12,10,&transient,&persistent,&depth,&kernel,&image));
    CHECK(transient == 4 && persistent == 3 && depth == 2 && kernel == 4 && image == 3);

    const int indicator[] = {0,1,0};
    BoundaryConductorLedgerSummary ledger;
    CHECK(boundary_conductor_ledger_compute(3,indicator,3,&ledger));
    /* Boundary is (0,-1,1); its unique odd unit character reads -2. */
    CHECK(ledger.unit_norm == 2 && ledger.primitive_odd_characters == 1);
    CHECK(ledger.primitive_odd_moment == 4 && ledger.full_odd_energy == 4);
    CHECK(ledger.mean_numerator == 4 && ledger.mean_denominator == 1);
    CHECK(ledger.antipodal_odd && ledger.top_concentrated);
    CHECK(!boundary_conductor_ledger_compute(3,indicator,2,&ledger));

    const int transition[] = {0,0};
    FiniteStateOrbitBoundarySummary cycle;
    CHECK(finite_state_orbit_boundary_compute(2,3,1,1,0,
        transition,2,indicator,3,&cycle));
    CHECK(cycle.transient_length == 0 && cycle.cycle_length == 2);
    CHECK(cycle.cycle_remainder[0] == 1 && cycle.cycle_remainder[1] == 2);
    CHECK(cycle.cycle_digit[0] == 0 && cycle.cycle_digit[1] == 1);
    CHECK(cycle.cycle_weight[0] == 1 && cycle.cycle_weight[1] == 0);
    CHECK(cycle.dynamical_boundary[0] == -1 && cycle.dynamical_boundary[1] == 1);
    CHECK(cycle.boundary_sum == 0 && cycle.boundary_squared_norm == 2);
    CHECK(!finite_state_orbit_boundary_compute(2,3,1,1,0,
        transition,1,indicator,3,&cycle));
}

static long double age(int n)
{
    return (2*(n%2)-1)/12.0L + (2*(n%3)-2)/18.0L +
           (2*(n%4)-3)/36.0L;
}

static void weighted_clocks(void)
{
    long double variance=0;
    for (int n=0; n<12; ++n) variance += age(n)*age(n)/12;
    for (int n=0; n<36; ++n) {
        WeightedRemainderState s;
        CHECK(weighted_remainder_state_compute(n,4,&s));
        CHECK(near(s.mass,1.0L/2));
        CHECK(near(s.stationary_age,5.0L/18));
        CHECK(near(s.centered_age,age(n)));
        CHECK(near(s.finite_increment,age(n)-age((n+11)%12)));
        CHECK(near(s.variance,variance));
    }
    WeightedRemainderState invalid;
    CHECK(!weighted_remainder_state_compute(-1,4,&invalid));
    CHECK(!weighted_remainder_state_compute(0,241,&invalid));
    CHECK(isnan(weighted_remainder_weight(241)));
    CHECK(near(weighted_remainder_covariance(4,6),1.0L/4));
}

static void finite_energy(void)
{
    PrimeBaseCollisionEnergy energy;
    CHECK(prime_base_collision_energy_values(3,&energy));
    /* Unit multipliers 1,2,4,5,7,8 give centered numerators
     * 2,4,2,-2,-4,-2; their squared sum is 48. */
    CHECK(energy.modulus == 9 && energy.unit_count == 6);
    CHECK(energy.energy_numerator == 48 && energy.energy_denominator == 9);
    CHECK(energy.raw_variance == 7 && energy.half_centered_square == 22);
    CHECK(energy.dedekind_scaled_numerator == 576);
    CHECK(!prime_base_collision_energy_values(4,&energy));
}

int main(void)
{
    expansions(); collision_and_spectrum();
    cylinders_and_boundaries(); weighted_clocks(); finite_energy();
    printf("research library: %u independent finite assertions passed\n",checks);
    return 0;
}
