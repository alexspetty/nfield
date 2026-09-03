/* Shared exact arithmetic for additive boundaries of multiplicative orbits. */

#include <stdlib.h>

#include "orbit_boundary_core.h"

int orbit_boundary_is_prime(int value)
{
    if (value < 2) return 0;
    if (value < 4) return 1;
    if (value % 2 == 0 || value % 3 == 0) return 0;
    for (int divisor = 5; divisor <= value / divisor; divisor += 6)
        if (value % divisor == 0 || value % (divisor + 2) == 0) return 0;
    return 1;
}

int orbit_boundary_gcd(int left, int right)
{
    while (right != 0) {
        int remainder = left % right;
        left = right;
        right = remainder;
    }
    return left < 0 ? -left : left;
}

int orbit_boundary_prime_power(int prime, int depth, int cap, int *modulus)
{
    if (!modulus || !orbit_boundary_is_prime(prime) || depth < 1 || cap < 2)
        return 0;
    int result = 1;
    for (int index = 0; index < depth; index++) {
        if (result > cap / prime) return 0;
        result *= prime;
    }
    *modulus = result;
    return 1;
}

int orbit_boundary_modular_power(int base, int exponent, int modulus)
{
    if (modulus < 2 || exponent < 0) return 0;
    long long result = 1 % modulus;
    long long power = base % modulus;
    if (power < 0) power += modulus;
    while (exponent > 0) {
        if (exponent & 1) result = result * power % modulus;
        power = power * power % modulus;
        exponent >>= 1;
    }
    return (int)result;
}

int orbit_boundary_multiplicative_order(int base, int modulus)
{
    if (modulus < 2 || orbit_boundary_gcd(base, modulus) != 1) return 0;
    int residue = 1;
    for (int order = 1; order <= modulus; order++) {
        residue = (int)((long long)residue * base % modulus);
        if (residue < 0) residue += modulus;
        if (residue == 1) return order;
    }
    return 0;
}

int orbit_boundary_phi_prime_power(int prime, int depth, int *phi)
{
    int modulus = 0;
    if (!phi || !orbit_boundary_prime_power(
            prime, depth, 2000000000, &modulus))
        return 0;
    *phi = modulus / prime * (prime - 1);
    return 1;
}

void orbit_boundary_free(OrbitBoundary *orbit)
{
    if (!orbit) return;
    free(orbit->support);
    free(orbit->boundary);
    *orbit = (OrbitBoundary){0};
}

static int orbit_boundary_allocate(int modulus, OrbitBoundary *orbit)
{
    if (!orbit || modulus < 2) return 0;
    *orbit = (OrbitBoundary){.modulus = modulus};
    orbit->support = calloc((size_t)modulus, sizeof(*orbit->support));
    orbit->boundary = calloc((size_t)modulus, sizeof(*orbit->boundary));
    if (!orbit->support || !orbit->boundary) {
        orbit_boundary_free(orbit);
        return 0;
    }
    return 1;
}

static void orbit_boundary_difference(OrbitBoundary *orbit)
{
    for (int residue = 0; residue < orbit->modulus; residue++) {
        int previous = residue == 0 ? orbit->modulus - 1 : residue - 1;
        orbit->boundary[residue] =
            (int)orbit->support[previous] - (int)orbit->support[residue];
    }
}

int orbit_boundary_build_subgroup(int base, int modulus,
                                  OrbitBoundary *orbit)
{
    if (orbit_boundary_gcd(base, modulus) != 1 ||
        !orbit_boundary_allocate(modulus, orbit))
        return 0;
    int residue = 1;
    do {
        if (orbit->support[residue]) {
            orbit_boundary_free(orbit);
            return 0;
        }
        orbit->support[residue] = 1;
        orbit->support_size++;
        residue = (int)((long long)residue * base % modulus);
        if (residue < 0) residue += modulus;
    } while (residue != 1);
    orbit_boundary_difference(orbit);
    return 1;
}

int orbit_boundary_build_units(int modulus, OrbitBoundary *orbit)
{
    if (!orbit_boundary_allocate(modulus, orbit)) return 0;
    for (int residue = 0; residue < modulus; residue++) {
        if (orbit_boundary_gcd(residue, modulus) == 1) {
            orbit->support[residue] = 1;
            orbit->support_size++;
        }
    }
    orbit_boundary_difference(orbit);
    return 1;
}

int orbit_boundary_odd_energy(const OrbitBoundary *orbit, int phi,
                              long long *diagonal,
                              long long *antipodal,
                              long long *energy)
{
    if (!orbit || !orbit->boundary || !diagonal || !antipodal || !energy ||
        phi < 1 || phi % 2 != 0)
        return 0;
    long long diagonal_sum = 0;
    long long antipodal_sum = 0;
    for (int residue = 0; residue < orbit->modulus; residue++) {
        if (orbit_boundary_gcd(residue, orbit->modulus) != 1) continue;
        int opposite = residue == 0 ? 0 : orbit->modulus - residue;
        diagonal_sum +=
            (long long)orbit->boundary[residue] * orbit->boundary[residue];
        antipodal_sum +=
            (long long)orbit->boundary[residue] * orbit->boundary[opposite];
    }
    long long difference = diagonal_sum - antipodal_sum;
    if (difference < 0 || (long long)phi * difference % 2 != 0) return 0;
    *diagonal = diagonal_sum;
    *antipodal = antipodal_sum;
    *energy = (long long)phi * difference / 2;
    return 1;
}

int orbit_boundary_legendre(int value, int prime)
{
    value %= prime;
    if (value < 0) value += prime;
    if (value == 0) return 0;
    int result = orbit_boundary_modular_power(
        value, (prime - 1) / 2, prime);
    return result == 1 ? 1 : -1;
}
