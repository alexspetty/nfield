#ifndef NFIELD_COLLISION_MAGNITUDE_MOMENTS_H
#define NFIELD_COLLISION_MAGNITUDE_MOMENTS_H

#include <stdint.h>

typedef struct {
    int base, count, failures;
    int64_t energy_numerator;
    long double mean_x, mean_y, mean_xy, mean_x2, mean_y2;
    long double mean_x2y2, mean_x_three_halves, mean_y3, mean_y4;
    long double mean_chi2_real, mean_chi2_imag;
    long double mean_y2_chi2_real, mean_y2_chi2_imag, variance_y_margin;
    long double correlation, enrichment, max_identity_error;
} CollisionMagnitudeMoments;

/* All primitive odd characters at an odd prime base from 5 through 127. */
CollisionMagnitudeMoments collision_magnitude_moments(int base);

#endif
