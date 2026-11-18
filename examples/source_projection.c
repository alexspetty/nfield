/* Select reset masses and retain the signed mixed-energy contribution. */
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
    const unsigned cutoff = 4, grid = 25;
    const long numerators[] = {1, -2, 3, 1};
    const unsigned long denominators[] = {1, 1, 2, 1};
    const unsigned char mask[] = {0, 1, 1, 0};
    const char *component_names[] = {"original", "selected", "complement"};
    const char *form_names[] = {"continuous", "sampled"};
    nfield_source *source = NULL;
    mpq_t weights[4], value[5];
    int result = EXIT_FAILURE;

    for (unsigned i = 0; i < cutoff; ++i) {
        mpq_init(weights[i]);
        mpq_set_si(weights[i], numerators[i], denominators[i]);
        mpq_canonicalize(weights[i]);
    }
    for (unsigned i = 0; i < 5; ++i) mpq_init(value[i]);

    TRY(nfield_source_create(&source));
    TRY(nfield_source_project(source, cutoff, (const mpq_t *)weights, mask, grid));
    puts("N=4 Q=25 weights=[1,-2,3/2,1] selected_resets={2,3}");
    puts("k mask original_c selected_c complement_c selected_mass");
    for (unsigned k = 1; k <= cutoff; ++k) {
        unsigned selected;
        TRY(nfield_source_mask(source, k, &selected));
        for (unsigned c = 0; c < 3; ++c)
            TRY(nfield_source_coefficient(source, (nfield_component)c, k, value[c]));
        TRY(nfield_source_mass(source, NFIELD_SELECTED, k, value[3]));
        gmp_printf("%u %u %Qd %Qd %Qd %Qd\n", k, selected,
                   value[0], value[1], value[2], value[3]);
    }

    for (unsigned f = 0; f < 2; ++f) {
        for (unsigned c = 0; c < 3; ++c)
            TRY(nfield_source_energy(source, (nfield_form)f,
                                     (nfield_component)c, value[c]));
        TRY(nfield_source_mixed(source, (nfield_form)f, value[3]));
        mpq_add(value[4], value[1], value[2]);
        mpq_add(value[4], value[4], value[3]);
        gmp_printf("%s original=%Qd selected=%Qd complement=%Qd "
                   "twice_mixed=%Qd reconstructed=%Qd\n", form_names[f],
                   value[0], value[1], value[2], value[3], value[4]);
    }

    puts("Ordered readings use the complete original field as receiver.");
    for (unsigned c = 0; c < 3; ++c) {
        TRY(nfield_source_reset_work(source, (nfield_component)c, value[0]));
        TRY(nfield_source_ordered_work(source, (nfield_component)c, value[1]));
        gmp_printf("%s reset_work=%Qd ordered_work=%Qd\n",
                   component_names[c], value[0], value[1]);
    }
    result = EXIT_SUCCESS;

cleanup:
    nfield_source_destroy(source);
    for (unsigned i = 0; i < 5; ++i) mpq_clear(value[i]);
    for (unsigned i = 0; i < cutoff; ++i) mpq_clear(weights[i]);
    return result;
}
