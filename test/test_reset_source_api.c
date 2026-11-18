#include "../src/reset_source.h"
#include <stdio.h>

static unsigned checks;
#define REQUIRE(condition) do { ++checks; if (!(condition)) { \
    fprintf(stderr, "Source API contract failed at line %d\n", __LINE__); return 1; } } while (0)

int main(void)
{
    ResetSource source;
    reset_source_init(&source);
    mpq_t c[4], mass;
    for (unsigned j = 0; j < 4; ++j) mpq_init(c[j]);
    mpq_init(mass);
    mpq_set_ui(c[1], 2, 1);
    mpq_set_si(c[2], -1, 2);
    mpq_set_ui(c[3], 3, 1);
    mpz_t modulus;
    mpz_init_set_ui(modulus, 2);
    REQUIRE(reset_source_collapse(&source, 3, c, modulus, 16));
    REQUIRE(mpq_cmp_ui(source.coefficient[RS_SELECTED][1], 5, 1) == 0);
    REQUIRE(mpq_cmp_si(source.total[RS_SELECTED], 9, 2) == 0);
    REQUIRE(source.has_work);
    unsigned char invalid[4] = {0, 1, 2, 1};
    REQUIRE(!reset_source_project(&source, 3, c, invalid, 0));
    REQUIRE(source.has_work && source.grid == 16);
    REQUIRE(mpq_cmp_ui(source.coefficient[RS_SELECTED][1], 5, 1) == 0);
    REQUIRE(!reset_source_project(&source, 65, NULL, NULL, 0));
    REQUIRE(!reset_source_project(&source, 3, NULL, invalid, 0));
    REQUIRE(!reset_source_project(NULL, 3, c, invalid, 0));
    mpz_set_si(modulus, -1);
    REQUIRE(!reset_source_collapse(&source, 3, c, modulus, 0));
    REQUIRE(mpq_cmp_si(source.total[RS_SELECTED], 9, 2) == 0);
    mpz_set_ui(modulus, 1);
    REQUIRE(!reset_source_collapse(&source, 3, c, modulus, RESET_SOURCE_MAX_GRID + 1));
    REQUIRE(source.grid == 16);

    /* Inputs may alias the returned source and carrier. */
    REQUIRE(reset_source_collapse(&source, 3, source.coefficient[RS_SELECTED], source.modulus, 0));
    REQUIRE(mpq_cmp_ui(source.coefficient[RS_SELECTED][1], 5, 1) == 0);
    REQUIRE(mpq_cmp_si(source.coefficient[RS_SELECTED][2], -1, 2) == 0);
    REQUIRE(!source.has_work && source.grid == 0);
    REQUIRE(mpq_sgn(source.energy[RS_CONTINUOUS][RS_ORIGINAL]) == 0);
    REQUIRE(reset_source_collapse(&source, 3, source.coefficient[RS_SELECTED], modulus, 0));
    REQUIRE(mpq_cmp_si(source.coefficient[RS_SELECTED][1], 9, 2) == 0);
    REQUIRE(mpq_sgn(source.coefficient[RS_SELECTED][2]) == 0);
    reset_source_mass(mass, c, 3, 0);
    REQUIRE(mpq_sgn(mass) == 0);
    reset_source_mass(mass, c, 3, 4);
    REQUIRE(mpq_sgn(mass) == 0);
    reset_source_mass(c[1], c, 3, 1);
    REQUIRE(mpq_cmp_si(c[1], 9, 2) == 0);
    REQUIRE(reset_source_project(&source, 0, NULL, NULL, 1));
    REQUIRE(source.cutoff == 0 && source.has_work);
    REQUIRE(mpq_sgn(source.total[RS_ORIGINAL]) == 0);
    REQUIRE(mpq_sgn(source.energy[RS_SAMPLED][RS_ORIGINAL]) == 0);
    for (unsigned j = 0; j < 4; ++j) mpq_clear(c[j]);
    mpq_clear(mass);
    mpz_clear(modulus);
    reset_source_clear(&source);
    printf("Source API contracts: %u checks passed.\n", checks);
    return 0;
}
