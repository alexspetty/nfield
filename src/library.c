#include <nfield/nfield.h>
#include "reset_source.h"
#include "reset_forest.h"
#include <stdlib.h>

#if NFIELD_SOURCE_MAX_CUTOFF != RESET_SOURCE_MAX_CUTOFF || \
    NFIELD_SOURCE_MAX_GRID != RESET_SOURCE_MAX_GRID || \
    NFIELD_FOREST_MAX_PRIME != RESET_FOREST_MAX_PRIME
#error Public resource limits must match the calculation kernels
#endif

struct nfield_source { ResetSource value; int ready; };
struct nfield_forest { ResetForest value; int ready; };

const char *nfield_version(void) { return NFIELD_VERSION; }
unsigned nfield_api_version(void) { return NFIELD_API_VERSION; }
const char *nfield_status_string(nfield_status status)
{
    switch (status) {
    case NFIELD_OK: return "success";
    case NFIELD_EINVAL: return "invalid argument";
    case NFIELD_ERANGE: return "dimension or index outside supported range";
    case NFIELD_ESTATE: return "result has not been computed";
    case NFIELD_ENODATA: return "requested quantity was not computed";
    case NFIELD_ENOMEM: return "result allocation failed";
    default: return "unknown status";
    }
}

static nfield_status source_ready(const nfield_source *source, const void *out)
{
    if (!source || !out) return NFIELD_EINVAL;
    return source->ready ? NFIELD_OK : NFIELD_ESTATE;
}

static nfield_status source_component(const nfield_source *source,
    nfield_component component, const void *out)
{
    nfield_status status = source_ready(source, out);
    if (status != NFIELD_OK) return status;
    return (unsigned)component < RS_COMPONENT_COUNT ? NFIELD_OK : NFIELD_EINVAL;
}

static nfield_status source_index(const nfield_source *source,
    unsigned k, const void *out)
{
    nfield_status status = source_ready(source, out);
    if (status != NFIELD_OK) return status;
    return k && k <= source->value.cutoff ? NFIELD_OK : NFIELD_ERANGE;
}

nfield_status nfield_source_create(nfield_source **out)
{
    if (!out || *out) return NFIELD_EINVAL;
    nfield_source *source = malloc(sizeof(*source));
    if (!source) return NFIELD_ENOMEM;
    reset_source_init(&source->value);
    source->ready = 0;
    *out = source;
    return NFIELD_OK;
}

void nfield_source_destroy(nfield_source *source)
{
    if (!source) return;
    reset_source_clear(&source->value);
    free(source);
}

static nfield_status source_inputs(const nfield_source *source,
    unsigned cutoff, const mpq_t *weights, unsigned grid)
{
    if (!source) return NFIELD_EINVAL;
    if (cutoff > NFIELD_SOURCE_MAX_CUTOFF || grid > NFIELD_SOURCE_MAX_GRID)
        return NFIELD_ERANGE;
    if (cutoff && !weights) return NFIELD_EINVAL;
    for (unsigned i = 0; i < cutoff; ++i)
        if (!mpz_sgn(mpq_denref(weights[i]))) return NFIELD_EINVAL;
    return NFIELD_OK;
}

/* Convert the public zero-based input to the kernels' mathematical indexing.
 * Canonicalize copies only. Borrowed inputs never become result storage. */
static void source_weights(mpq_t *input, unsigned cutoff, const mpq_t *weights)
{
    for (unsigned j = 0; j <= cutoff; ++j) {
        mpq_init(input[j]);
        if (j) {
            /* mpq_set expects a positive denominator. Copy the integers
             * separately so an initialized raw rational can be normalized. */
            mpz_set(mpq_numref(input[j]), mpq_numref(weights[j - 1]));
            mpz_set(mpq_denref(input[j]), mpq_denref(weights[j - 1]));
            mpq_canonicalize(input[j]);
        }
    }
}

static void source_weights_clear(mpq_t *input, unsigned cutoff)
{
    for (unsigned j = 0; j <= cutoff; ++j) mpq_clear(input[j]);
}

nfield_status nfield_source_project(nfield_source *source, unsigned cutoff,
    const mpq_t *weights, const unsigned char *mask, unsigned grid)
{
    nfield_status status = source_inputs(source, cutoff, weights, grid);
    if (status != NFIELD_OK) return status;
    if (cutoff && !mask) return NFIELD_EINVAL;
    for (unsigned i = 0; i < cutoff; ++i)
        if (mask[i] > 1) return NFIELD_EINVAL;
    mpq_t input[NFIELD_SOURCE_MAX_CUTOFF + 1];
    unsigned char selection[NFIELD_SOURCE_MAX_CUTOFF + 1] = {0};
    source_weights(input, cutoff, weights);
    for (unsigned j = 1; j <= cutoff; ++j) selection[j] = mask[j - 1];
    int ok = reset_source_project(&source->value, cutoff, input, selection, grid);
    source_weights_clear(input, cutoff);
    if (!ok) return NFIELD_EINVAL;
    source->ready = 1;
    return NFIELD_OK;
}

nfield_status nfield_source_collapse(nfield_source *source, unsigned cutoff,
    const mpq_t *weights, const mpz_t modulus, unsigned grid)
{
    nfield_status status = source_inputs(source, cutoff, weights, grid);
    if (status != NFIELD_OK) return status;
    if (!modulus || mpz_sgn(modulus) < 0) return NFIELD_EINVAL;
    mpq_t input[NFIELD_SOURCE_MAX_CUTOFF + 1];
    source_weights(input, cutoff, weights);
    int ok = reset_source_collapse(&source->value, cutoff, input, modulus, grid);
    source_weights_clear(input, cutoff);
    if (!ok) return NFIELD_EINVAL;
    source->ready = 1;
    return NFIELD_OK;
}

nfield_status nfield_source_divisor(nfield_source *source, unsigned cutoff,
    const mpq_t *weights, const mpz_t divisor, unsigned grid)
{
    nfield_status status = source_inputs(source, cutoff, weights, grid);
    if (status != NFIELD_OK) return status;
    if (!divisor || mpz_sgn(divisor) <= 0) return NFIELD_EINVAL;
    mpz_t modulus;
    mpz_init(modulus);
    mpz_ui_pow_ui(modulus, cutoff, cutoff);
    mpz_mul(modulus, modulus, divisor);
    status = nfield_source_collapse(source, cutoff, weights, modulus, grid);
    mpz_clear(modulus);
    return status;
}

nfield_status nfield_source_get_info(const nfield_source *source,
    nfield_source_info *out)
{
    nfield_status status = source_ready(source, out);
    if (status != NFIELD_OK) return status;
    const ResetSource *r = &source->value;
    *out = (nfield_source_info){r->cutoff, r->grid, r->has_work, r->saturated};
    return NFIELD_OK;
}

nfield_status nfield_source_coefficient(const nfield_source *source,
    nfield_component component, unsigned k, mpq_t out)
{
    nfield_status status = source_component(source, component, out);
    if (status != NFIELD_OK) return status;
    status = source_index(source, k, out);
    if (status != NFIELD_OK) return status;
    mpq_set(out, source->value.coefficient[component][k]);
    return NFIELD_OK;
}

nfield_status nfield_source_mass(const nfield_source *source,
    nfield_component component, unsigned k, mpq_t out)
{
    nfield_status status = source_component(source, component, out);
    if (status != NFIELD_OK) return status;
    status = source_index(source, k, out);
    if (status != NFIELD_OK) return status;
    mpq_set(out, source->value.mass[component][k]);
    return NFIELD_OK;
}

nfield_status nfield_source_total(const nfield_source *source,
    nfield_component component, mpq_t out)
{
    nfield_status status = source_component(source, component, out);
    if (status != NFIELD_OK) return status;
    mpq_set(out, source->value.total[component]);
    return NFIELD_OK;
}

nfield_status nfield_source_energy(const nfield_source *source,
    nfield_form form, nfield_component component, mpq_t out)
{
    nfield_status status = source_component(source, component, out);
    if (status != NFIELD_OK) return status;
    if ((unsigned)form >= RS_FORM_COUNT) return NFIELD_EINVAL;
    if (!source->value.has_work) return NFIELD_ENODATA;
    mpq_set(out, source->value.energy[form][component]);
    return NFIELD_OK;
}

nfield_status nfield_source_mixed(const nfield_source *source,
    nfield_form form, mpq_t out)
{
    nfield_status status = source_ready(source, out);
    if (status != NFIELD_OK) return status;
    if ((unsigned)form >= RS_FORM_COUNT) return NFIELD_EINVAL;
    if (!source->value.has_work) return NFIELD_ENODATA;
    mpq_set(out, source->value.mixed[form]);
    return NFIELD_OK;
}

nfield_status nfield_source_ordered_work(const nfield_source *source,
    nfield_component component, mpq_t out)
{
    nfield_status status = source_component(source, component, out);
    if (status != NFIELD_OK) return status;
    if (!source->value.has_work) return NFIELD_ENODATA;
    mpq_set(out, source->value.ordered_work[component]);
    return NFIELD_OK;
}

nfield_status nfield_source_reset_work(const nfield_source *source,
    nfield_component component, mpq_t out)
{
    nfield_status status = source_component(source, component, out);
    if (status != NFIELD_OK) return status;
    if (!source->value.has_work) return NFIELD_ENODATA;
    mpq_set(out, source->value.reset_work[component]);
    return NFIELD_OK;
}

nfield_status nfield_source_clock_work(const nfield_source *source,
    unsigned k, mpq_t out)
{
    nfield_status status = source_index(source, k, out);
    if (status != NFIELD_OK) return status;
    if (!source->value.has_work) return NFIELD_ENODATA;
    mpq_set(out, source->value.clock_work[k]);
    return NFIELD_OK;
}

nfield_status nfield_source_primitive_work(const nfield_source *source,
    unsigned k, mpq_t out)
{
    nfield_status status = source_index(source, k, out);
    if (status != NFIELD_OK) return status;
    if (!source->value.has_work) return NFIELD_ENODATA;
    mpq_set(out, source->value.primitive_work[k]);
    return NFIELD_OK;
}

nfield_status nfield_source_mask(const nfield_source *source,
    unsigned k, unsigned *out)
{
    nfield_status status = source_index(source, k, out);
    if (status != NFIELD_OK) return status;
    *out = source->value.mask[k];
    return NFIELD_OK;
}

nfield_status nfield_source_modulus(const nfield_source *source, mpz_t out)
{
    nfield_status status = source_ready(source, out);
    if (status != NFIELD_OK) return status;
    if (!source->value.saturated) return NFIELD_ENODATA;
    mpz_set(out, source->value.modulus);
    return NFIELD_OK;
}

nfield_status nfield_source_destination(const nfield_source *source,
    unsigned k, unsigned *out)
{
    nfield_status status = source_index(source, k, out);
    if (status != NFIELD_OK) return status;
    if (!source->value.saturated) return NFIELD_ENODATA;
    *out = source->value.destination[k];
    return NFIELD_OK;
}

static nfield_status forest_prime(unsigned prime)
{
    if (prime < 3 || prime > NFIELD_FOREST_MAX_PRIME) return NFIELD_ERANGE;
    if (!(prime & 1)) return NFIELD_EINVAL;
    for (unsigned d = 3; d <= prime / d; d += 2)
        if (prime % d == 0) return NFIELD_EINVAL;
    return NFIELD_OK;
}

static nfield_status forest_ready(const nfield_forest *forest, const void *out)
{
    if (!forest || !out) return NFIELD_EINVAL;
    return forest->ready ? NFIELD_OK : NFIELD_ESTATE;
}

nfield_status nfield_forest_create(nfield_forest **out)
{
    if (!out || *out) return NFIELD_EINVAL;
    nfield_forest *forest = malloc(sizeof(*forest));
    if (!forest) return NFIELD_ENOMEM;
    reset_forest_init(&forest->value);
    forest->ready = 0;
    *out = forest;
    return NFIELD_OK;
}

void nfield_forest_destroy(nfield_forest *forest)
{
    if (!forest) return;
    reset_forest_clear(&forest->value);
    free(forest);
}

nfield_status nfield_forest_compute(nfield_forest *forest, unsigned prime,
    const mpz_t divisor)
{
    if (!forest || !divisor || mpz_sgn(divisor) <= 0) return NFIELD_EINVAL;
    nfield_status status = forest_prime(prime);
    if (status != NFIELD_OK) return status;
    if (!reset_forest_compute(&forest->value, prime, divisor)) return NFIELD_EINVAL;
    forest->ready = 1;
    return NFIELD_OK;
}

nfield_status nfield_forest_return_divisor(mpz_t out, unsigned prime,
    unsigned window)
{
    if (!out) return NFIELD_EINVAL;
    nfield_status status = forest_prime(prime);
    if (status != NFIELD_OK) return status;
    if (window < NFIELD_FOREST_MIN_RETURN || window > NFIELD_FOREST_MAX_RETURN)
        return NFIELD_ERANGE;
    return reset_forest_return_divisor(out, prime, window) ? NFIELD_OK : NFIELD_EINVAL;
}

nfield_status nfield_forest_get_info(const nfield_forest *forest,
    nfield_forest_info *out)
{
    nfield_status status = forest_ready(forest, out);
    if (status != NFIELD_OK) return status;
    const ResetForest *r = &forest->value;
    *out = (nfield_forest_info){r->prime, r->cutoff, r->grid, r->count};
    return NFIELD_OK;
}

nfield_status nfield_forest_divisor(const nfield_forest *forest, mpz_t out)
{
    nfield_status status = forest_ready(forest, out);
    if (status != NFIELD_OK) return status;
    mpz_set(out, forest->value.divisor);
    return NFIELD_OK;
}

nfield_status nfield_forest_value(const nfield_forest *forest,
    nfield_forest_quantity quantity, mpq_t out)
{
    static const unsigned map[] = {
        RF_CONTINUOUS, RF_SAMPLED, RF_DEFECT, RF_CONTACT, RF_CORRECTED,
        RF_FOREST, RF_OTHER, RF_ABSOLUTE, RF_RESTORATION, RF_OTHER_CLOCKS,
        RF_CURVATURE, RF_SIGNED_BOUND
    };
    nfield_status status = forest_ready(forest, out);
    if (status != NFIELD_OK) return status;
    if ((unsigned)quantity >= sizeof(map) / sizeof(map[0])) return NFIELD_EINVAL;
    mpq_set(out, forest->value.value[map[quantity]]);
    return NFIELD_OK;
}

nfield_status nfield_forest_get_clock_info(const nfield_forest *forest,
    unsigned k, nfield_forest_clock_info *out)
{
    nfield_status status = forest_ready(forest, out);
    if (status != NFIELD_OK) return status;
    if (!k || k > forest->value.cutoff) return NFIELD_ERANGE;
    const ResetForest *r = &forest->value;
    *out = (nfield_forest_clock_info){r->rough[k], r->selected[k],
        r->projection[k], r->population[k]};
    return NFIELD_OK;
}

nfield_status nfield_forest_clock_work(const nfield_forest *forest,
    nfield_clock_quantity quantity, unsigned k, mpq_t out)
{
    nfield_status status = forest_ready(forest, out);
    if (status != NFIELD_OK) return status;
    if (!k || k > forest->value.cutoff) return NFIELD_ERANGE;
    switch (quantity) {
    case NFIELD_CLOCK_SIGNED_WORK: mpq_set(out, forest->value.signed_work[k]); break;
    case NFIELD_CLOCK_ABSOLUTE_WORK: mpq_set(out, forest->value.absolute_work[k]); break;
    case NFIELD_CLOCK_ORDERED_WORK: mpq_set(out, forest->value.clock_work[k]); break;
    default: return NFIELD_EINVAL;
    }
    return NFIELD_OK;
}
