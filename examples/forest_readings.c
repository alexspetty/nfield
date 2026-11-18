/* Exact prime-square forest readings through the installed C API. */
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

int main(int argc, char **argv)
{
    static const struct {
        nfield_forest_quantity quantity;
        const char *name;
    } readings[] = {
        {NFIELD_FOREST_CONTINUOUS_ENERGY, "continuous_energy"},
        {NFIELD_FOREST_SAMPLED_ENERGY, "sampled_energy"},
        {NFIELD_FOREST_DEFECT, "defect"},
        {NFIELD_FOREST_ORIGIN_CONTACT, "origin_contact"},
        {NFIELD_FOREST_CORRECTED_DEFECT, "corrected_defect"},
        {NFIELD_FOREST_SIGNED_WORK, "forest_signed_work"},
        {NFIELD_FOREST_COMPLEMENT_WORK, "complement_signed_work"},
        {NFIELD_FOREST_ABSOLUTE_WORK, "forest_absolute_work"},
        {NFIELD_FOREST_RESTORATION_WORK, "restoration_work"},
        {NFIELD_FOREST_COMPLEMENT_CLOCK_WORK, "complement_clock_work"},
        {NFIELD_FOREST_CURVATURE, "curvature"},
        {NFIELD_FOREST_SIGNED_WORK_BOUND, "signed_work_bound"}
    };
    nfield_forest *forest = NULL;
    nfield_forest_info info;
    mpz_t divisor;
    mpq_t value, signed_work, clock_work;
    int result = EXIT_FAILURE;

    mpz_init_set_ui(divisor, 1);
    mpq_inits(value, signed_work, clock_work, NULL);
    if (argc > 2 || (argc == 2 && mpz_set_str(divisor, argv[1], 10) != 0)) {
        fprintf(stderr, "Usage: %s [positive-divisor]\n", argv[0]);
        goto cleanup;
    }
    TRY(nfield_forest_create(&forest));
    TRY(nfield_forest_compute(forest, 5, divisor));
    TRY(nfield_forest_get_info(forest, &info));
    printf("libnfield %s, API %u\n", nfield_version(), nfield_api_version());
    gmp_printf("p=%u N=%u Q=%u D=%Zd selected_clocks=%u\n",
               info.prime, info.cutoff, info.grid, divisor, info.selected_count);

    for (size_t i = 0; i < sizeof(readings) / sizeof(readings[0]); ++i) {
        TRY(nfield_forest_value(forest, readings[i].quantity, value));
        gmp_printf("%s=%Qd\n", readings[i].name, value);
    }

    puts("k rough selected destination population A_k W_k");
    for (unsigned k = 1; k <= info.cutoff; ++k) {
        nfield_forest_clock_info clock;
        TRY(nfield_forest_get_clock_info(forest, k, &clock));
        TRY(nfield_forest_clock_work(forest, NFIELD_CLOCK_SIGNED_WORK,
                                    k, signed_work));
        TRY(nfield_forest_clock_work(forest, NFIELD_CLOCK_ORDERED_WORK,
                                    k, clock_work));
        gmp_printf("%u %u %u %u %u %Qd %Qd\n", k, clock.rough,
                   clock.selected, clock.destination, clock.population,
                   signed_work, clock_work);
    }
    result = EXIT_SUCCESS;

cleanup:
    nfield_forest_destroy(forest);
    mpq_clears(value, signed_work, clock_work, NULL);
    mpz_clear(divisor);
    return result;
}
