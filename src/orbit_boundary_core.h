#ifndef NFIELD_ORBIT_BOUNDARY_CORE_H
#define NFIELD_ORBIT_BOUNDARY_CORE_H

typedef struct {
    int modulus;
    int support_size;
    unsigned char *support;
    int *boundary;
} OrbitBoundary;

int orbit_boundary_is_prime(int value);
int orbit_boundary_gcd(int left, int right);
int orbit_boundary_prime_power(int prime, int depth, int cap, int *modulus);
int orbit_boundary_modular_power(int base, int exponent, int modulus);
int orbit_boundary_multiplicative_order(int base, int modulus);
int orbit_boundary_phi_prime_power(int prime, int depth, int *phi);
int orbit_boundary_build_subgroup(int base, int modulus,
                                  OrbitBoundary *orbit);
int orbit_boundary_build_units(int modulus, OrbitBoundary *orbit);
int orbit_boundary_odd_energy(const OrbitBoundary *orbit, int phi,
                              long long *diagonal,
                              long long *antipodal,
                              long long *energy);
int orbit_boundary_legendre(int value, int prime);
void orbit_boundary_free(OrbitBoundary *orbit);

#endif
