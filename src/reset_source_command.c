#include "reset_source.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

static int rs_uint(const char *s, unsigned max, unsigned *out)
{
    if (!s || !*s) return 0;
    for (const char *p = s; *p; ++p) if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end;
    unsigned long n = strtoul(s, &end, 10);
    if (errno || *end || n > max) return 0;
    *out = (unsigned)n;
    return 1;
}

static int rs_integer(const char *s, int signed_value, size_t max_digits)
{
    if (signed_value && *s == '-') ++s;
    size_t digits = strlen(s);
    if (!digits || digits > max_digits) return 0;
    for (; *s; ++s) if (*s < '0' || *s > '9') return 0;
    return 1;
}

static int rs_rational(mpq_t out, char *s)
{
    char *slash = strchr(s, '/');
    if (slash) {
        *slash = '\0';
        int valid = rs_integer(s, 1, 256) && rs_integer(slash + 1, 0, 256);
        *slash = '/';
        if (!valid) return 0;
    } else if (!rs_integer(s, 1, 256)) return 0;
    if (mpq_set_str(out, s, 10) || mpz_sgn(mpq_denref(out)) <= 0) return 0;
    mpq_canonicalize(out);
    return 1;
}

static int rs_list(const char *text, mpq_t *coefficient, unsigned char *mask,
                   unsigned n, int weights)
{
    if (!strcmp(text, "none")) return !weights || n == 0;
    if (!weights && !strcmp(text, "all")) {
        for (unsigned k = 1; k <= n; ++k) mask[k] = 1;
        return 1;
    }
    size_t length = strlen(text);
    if (!length || length > 33000) return 0;
    char *copy = malloc(length + 1);
    if (!copy) return 0;
    memcpy(copy, text, length + 1);
    unsigned count = 0;
    int valid = 1;
    char *part = copy;
    for (;;) {
        char *comma = strchr(part, ',');
        if (comma) *comma = '\0';
        if (weights) {
            if (++count > n || !rs_rational(coefficient[count], part)) { valid = 0; break; }
        } else {
            unsigned k;
            if (!rs_uint(part, n, &k) || !k || mask[k]) { valid = 0; break; }
            mask[k] = 1;
        }
        if (!comma) break;
        part = comma + 1;
    }
    if (weights && count != n) valid = 0;
    free(copy);
    return valid;
}

void reset_source_help(void)
{
    puts("Project your own source onto selected resets\n\n"
         "  nfield reset-forest project N [--weights c1,...,cN]\n"
         "      [--modulus M | --divisor D | --mask k1,...,km]\n"
         "      [--grid Q] [--json | --csv]\n\n"
         "Choose N coefficients for B_c(x)=2 sum c_j psi(jx), with midpoint\n"
         "psi(integer)=0. Weights are exact signed integers or fractions.\n"
         "Default weights are all one. A selection keeps specified reset\n"
         "masses and uses divisor inversion to recover its source coefficients.\n"
         "These coefficients can be negative; they are not a frequency mask.\n\n"
         "--modulus M selects k dividing M and sends harmonic j to gcd(j,M).\n"
         "M=0 selects every reset. --divisor D uses M=N^N D, selecting k whose\n"
         "N-rough part divides D. Default D=1. --mask accepts a reset list,\n"
         "all or none, including selections that are not divisor forests.\n\n"
         "The result retains original, selected and complementary sources,\n"
         "their reset masses and both ordered boundary readings. Continuous\n"
         "and sampled energies retain twice the mixed pairing. Q defaults to\n"
         "(N+1)^2; --grid 0 requests coordinates without work calculations.\n"
         "Arbitrary grids are allowed, including those meeting nonorigin resets.\n\n"
         "  nfield reset-forest project 4 --modulus 6 --weights 1,-2,3/2,1 --json\n"
         "  nfield reset-forest project 6 --mask 2,3 --grid 49 --csv\n\n"
         "Vary the selection while keeping weights and grid fixed to measure\n"
         "its mixed work. JSON includes energies and all rows; CSV exposes the\n"
         "source, reset masses and clock readings for reuse in other programs.\n"
         "Limits: N=0..64; Q=0..65536; 256 digits per rational numerator or\n"
         "denominator; 4096 digits for M or D. These are exact finite results.");
}

static void rs_json(const ResetSource *r, const char *kind)
{
    printf("{\"schema\":\"nfield.reset-source.v1\",\"cutoff\":%u,\"grid\":", r->cutoff);
    if (r->has_work) printf("%u", r->grid); else fputs("null", stdout);
    printf(",\"selection\":{\"kind\":\"%s\",\"modulus\":", kind);
    if (r->saturated) gmp_printf("\"%Zd\"", r->modulus); else fputs("null", stdout);
    fputs("},\"normalization\":\"B_c=2*sum(c_j*psi(j*x)); psi(integer)=0\",\"totals\":{", stdout);
    const char *component[] = {"original", "selected", "complement"};
    for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c)
        gmp_printf("%s\"%s\":\"%Qd\"", c ? "," : "", component[c], r->total[c]);
    fputs("},\"energies\":", stdout);
    if (!r->has_work) fputs("null", stdout);
    else {
        mpq_t defect;
        mpq_init(defect);
        putchar('{');
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) {
            mpq_sub(defect, r->energy[RS_CONTINUOUS][c], r->energy[RS_SAMPLED][c]);
            gmp_printf("%s\"%s\":{\"continuous\":\"%Qd\",\"sampled\":\"%Qd\",\"defect\":\"%Qd\"}",
                       c ? "," : "", component[c], r->energy[RS_CONTINUOUS][c], r->energy[RS_SAMPLED][c], defect);
        }
        mpq_sub(defect, r->mixed[RS_CONTINUOUS], r->mixed[RS_SAMPLED]);
        gmp_printf(",\"twice_mixed\":{\"continuous\":\"%Qd\",\"sampled\":\"%Qd\",\"defect\":\"%Qd\"}}",
                   r->mixed[RS_CONTINUOUS], r->mixed[RS_SAMPLED], defect);
        mpq_clear(defect);
    }
    fputs(",\"boundary_work\":", stdout);
    if (!r->has_work) fputs("null", stdout);
    else {
        putchar('{');
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c)
            gmp_printf("%s\"%s\":{\"primitive_reset\":\"%Qd\",\"ordered_clock\":\"%Qd\"}",
                       c ? "," : "", component[c], r->reset_work[c], r->ordered_work[c]);
        putchar('}');
    }
    fputs(",\"rows\":[", stdout);
    for (unsigned j = 1; j <= r->cutoff; ++j) {
        printf("%s{\"index\":%u,\"reset_selected\":%s,\"destination\":", j > 1 ? "," : "", j, r->mask[j] ? "true" : "false");
        if (r->saturated) printf("%u", r->destination[j]); else fputs("null", stdout);
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c)
            gmp_printf(",\"%s_coefficient\":\"%Qd\",\"%s_reset_mass\":\"%Qd\"",
                       component[c], r->coefficient[c][j], component[c], r->mass[c][j]);
        if (r->has_work)
            gmp_printf(",\"primitive_reading\":\"%Qd\",\"complete_clock_work\":\"%Qd\"", r->primitive_work[j], r->clock_work[j]);
        else fputs(",\"primitive_reading\":null,\"complete_clock_work\":null", stdout);
        putchar('}');
    }
    puts("]}");
}

static void rs_csv(const ResetSource *r)
{
    puts("index,reset_selected,destination,original_coefficient,selected_coefficient,complement_coefficient,original_reset_mass,selected_reset_mass,complement_reset_mass,primitive_reading,complete_clock_work");
    for (unsigned j = 1; j <= r->cutoff; ++j) {
        printf("%u,%u,", j, r->mask[j]);
        if (r->saturated) printf("%u", r->destination[j]);
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) gmp_printf(",%Qd", r->coefficient[c][j]);
        for (unsigned c = 0; c < RS_COMPONENT_COUNT; ++c) gmp_printf(",%Qd", r->mass[c][j]);
        if (r->has_work) gmp_printf(",%Qd,%Qd\n", r->primitive_work[j], r->clock_work[j]);
        else puts(",,");
    }
}

static void rs_text(const ResetSource *r)
{
    printf("Source selection at cutoff %u\n", r->cutoff);
    if (r->saturated) gmp_printf("modulus=%Zd\n", r->modulus);
    fputs("Selected resets:", stdout);
    int any = 0;
    for (unsigned j = 1; j <= r->cutoff; ++j) if (r->mask[j]) { printf(" %u", j); any = 1; }
    puts(any ? "" : " none");
    puts("\n index  original  selected  complement  original reset mass  selected reset mass");
    for (unsigned j = 1; j <= r->cutoff; ++j)
        gmp_printf(" %5u  %Qd  %Qd  %Qd  %Qd  %Qd\n", j, r->coefficient[0][j], r->coefficient[1][j], r->coefficient[2][j], r->mass[0][j], r->mass[1][j]);
    if (!r->has_work) { puts("\nCoordinates only. Choose --grid Q to measure energy and boundary work."); return; }
    printf("\nGrid %u; exact midpoint readings\n", r->grid);
    const char *forms[] = {"continuous", "sampled"};
    for (unsigned f = 0; f < RS_FORM_COUNT; ++f)
        gmp_printf("%s: original=%Qd selected=%Qd complement=%Qd twice_mixed=%Qd\n", forms[f],
                   r->energy[f][0], r->energy[f][1], r->energy[f][2], r->mixed[f]);
    puts("original energy = selected energy + complement energy + twice_mixed");
    gmp_printf("ordered boundary work: original=%Qd selected=%Qd complement=%Qd\n",
               r->ordered_work[0], r->ordered_work[1], r->ordered_work[2]);
    puts("Each selected reset still reads the complete original source.");
}

int reset_source_command(int argc, char **argv)
{
    unsigned n, grid;
    if (!argc || (argc == 1 && (!strcmp(argv[0], "help") || !strcmp(argv[0], "--help")))) {
        reset_source_help(); return 0;
    }
    if (!rs_uint(argv[0], RESET_SOURCE_MAX_CUTOFF, &n)) goto bad;
    grid = (n + 1) * (n + 1);
    const char *weights = NULL, *selection = "1", *kind = "divisor";
    int format = 0, selected = 0, grid_set = 0;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--weights")) {
            if (weights || ++i >= argc) goto bad;
            weights = argv[i];
        } else if (!strcmp(argv[i], "--modulus") || !strcmp(argv[i], "--divisor") || !strcmp(argv[i], "--mask")) {
            if (selected || i + 1 >= argc) goto bad;
            selected = 1;
            kind = argv[i] + 2;
            selection = argv[++i];
        } else if (!strcmp(argv[i], "--grid")) {
            if (grid_set || ++i >= argc || !rs_uint(argv[i], RESET_SOURCE_MAX_GRID, &grid)) goto bad;
            grid_set = 1;
        } else if (!strcmp(argv[i], "--json") || !strcmp(argv[i], "--csv")) {
            if (format) goto bad;
            format = !strcmp(argv[i], "--json") ? 1 : 2;
        } else goto bad;
    }
    mpq_t coefficient[RESET_SOURCE_MAX_CUTOFF + 1];
    unsigned char mask[RESET_SOURCE_MAX_CUTOFF + 1] = {0};
    for (unsigned j = 0; j <= n; ++j) { mpq_init(coefficient[j]); if (j) mpq_set_ui(coefficient[j], 1, 1); }
    mpz_t modulus, factor;
    mpz_inits(modulus, factor, NULL);
    ResetSource result;
    reset_source_init(&result);
    int valid = !weights || rs_list(weights, coefficient, mask, n, 1);
    if (valid && !strcmp(kind, "mask")) {
        valid = rs_list(selection, coefficient, mask, n, 0) &&
                reset_source_project(&result, n, coefficient, mask, grid);
    } else if (valid) {
        valid = rs_integer(selection, 0, 4096) && mpz_set_str(modulus, selection, 10) == 0;
        if (valid && !strcmp(kind, "divisor")) {
            valid = mpz_sgn(modulus) > 0;
            mpz_ui_pow_ui(factor, n, n);
            mpz_mul(modulus, modulus, factor);
        }
        if (valid) valid = reset_source_collapse(&result, n, coefficient, modulus, grid);
    }
    if (valid) {
        if (format == 1) rs_json(&result, kind);
        else if (format == 2) rs_csv(&result);
        else rs_text(&result);
    }
    reset_source_clear(&result);
    mpz_clears(modulus, factor, NULL);
    for (unsigned j = 0; j <= n; ++j) mpq_clear(coefficient[j]);
    if (valid) return 0;
bad:
    fputs("Invalid source selection. Use nfield reset-forest project --help for inputs and limits.\n", stderr);
    return 2;
}
