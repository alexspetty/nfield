/* Reuse one result for a divisor forest and an identity collapse. */
#include <stdio.h>
#include <stdlib.h>
#include <nfield/nfield.h>

#define TRY(call) do { \
    nfield_status status_ = (call); \
    if (status_ != NFIELD_OK) { \
        fprintf(stderr, "%s: %s\n", #call, nfield_status_string(status_)); \
        goto cleanup; \
    } \
} while (0)

int main(void)
{
    nfield_source *source = NULL;
    nfield_source_info info;
    mpq_t weights[4], coefficient, energy;
    mpz_t divisor, modulus;
    int result = EXIT_FAILURE;

    for (unsigned i = 0; i < 4; ++i) {
        mpq_init(weights[i]);
        mpq_set_ui(weights[i], 1, 1);
    }
    mpq_inits(coefficient, energy, NULL);
    mpz_init_set_ui(divisor, 1);
    mpz_init(modulus);

    TRY(nfield_source_create(&source));
    TRY(nfield_source_divisor(source, 4, (const mpq_t *)weights, divisor, 0));
    TRY(nfield_source_get_info(source, &info));
    TRY(nfield_source_modulus(source, modulus));
    gmp_printf("N=%u D=%Zd modulus=N^N*D=%Zd has_work=%d\n",
               info.cutoff, divisor, modulus, info.has_work);
    puts("harmonic destination selected_coefficient_at_harmonic");
    for (unsigned k = 1; k <= info.cutoff; ++k) {
        unsigned destination;
        TRY(nfield_source_destination(source, k, &destination));
        TRY(nfield_source_coefficient(source, NFIELD_SELECTED, k, coefficient));
        gmp_printf("%u %u %Qd\n", k, destination, coefficient);
    }

    /* The next successful call replaces this handle's previous computation. */
    mpz_set_ui(modulus, 0);
    TRY(nfield_source_collapse(source, 4, (const mpq_t *)weights, modulus, 25));
    TRY(nfield_source_get_info(source, &info));
    TRY(nfield_source_energy(source, NFIELD_CONTINUOUS, NFIELD_SELECTED, energy));
    gmp_printf("identity collapse M=0 Q=%u selected_continuous_energy=%Qd\n",
               info.grid, energy);
    puts("harmonic destination selected_coefficient_at_harmonic");
    for (unsigned k = 1; k <= info.cutoff; ++k) {
        unsigned destination;
        TRY(nfield_source_destination(source, k, &destination));
        TRY(nfield_source_coefficient(source, NFIELD_SELECTED, k, coefficient));
        gmp_printf("%u %u %Qd\n", k, destination, coefficient);
    }
    result = EXIT_SUCCESS;

cleanup:
    nfield_source_destroy(source);
    mpz_clears(divisor, modulus, NULL);
    mpq_clears(coefficient, energy, NULL);
    for (unsigned i = 0; i < 4; ++i) mpq_clear(weights[i]);
    return result;
}
