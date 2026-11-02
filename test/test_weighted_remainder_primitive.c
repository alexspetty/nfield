#include "../src/weighted_remainder_primitive.h"
#include "../src/weighted_remainder_state.h"
#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>

static unsigned edge_checks;
#define CHECK(condition) do { assert(condition); ++edge_checks; } while (0)

static void sentinels(mpq_t q[4])
{
    for (unsigned i = 0; i < 4; ++i) mpq_set_ui(q[i], 11 + i, 17);
}

static void unchanged(mpq_t q[4])
{
    for (unsigned i = 0; i < 4; ++i) CHECK(mpq_cmp_ui(q[i], 11 + i, 17) == 0);
}

int main(void)
{
    mpq_t q[4];
    for (unsigned i = 0; i < 4; ++i) mpq_init(q[i]);
    const unsigned bad[] = {0, 241, UINT_MAX};
    for (unsigned i = 0; i < sizeof bad / sizeof *bad; ++i) {
        sentinels(q);
        CHECK(!weighted_remainder_tree_node_q(q[0], q[1], q[2], q[3], bad[i], 1));
        unchanged(q);
        CHECK(!weighted_remainder_tree_node_q(q[0], q[1], q[2], q[3], 1, bad[i]));
        unchanged(q);
        CHECK(!weighted_remainder_tree_address_q(q[0], bad[i], 1));
        unchanged(q);
        CHECK(!weighted_remainder_tree_address_q(q[0], 1, bad[i]));
        unchanged(q);
        unsigned nodes = 999;
        CHECK(!weighted_remainder_tree_box_q(q[0], q[1], q[2], bad[i], &nodes));
        CHECK(nodes == 999);
        unchanged(q);
        CHECK(!weighted_remainder_budget_q(q[0], bad[i]));
        unchanged(q);
    }
    for (unsigned i = 1; i < sizeof bad / sizeof *bad; ++i) {
        sentinels(q);
        CHECK(!weighted_remainder_weight_inverse_q(q[0], bad[i]));
        unchanged(q);
        CHECK(!weighted_remainder_mass_q(q[0], q[1], bad[i]));
        unchanged(q);
        CHECK(!weighted_remainder_mass_budget_q(q[0], q[1], q[2], q[3], bad[i]));
        unchanged(q);
    }
    for (unsigned i = 0; i < 4; ++i) for (unsigned j = i + 1; j < 4; ++j) {
        sentinels(q);
        mpq_ptr out[4] = {q[0], q[1], q[2], q[3]};
        out[j] = out[i];
        CHECK(!weighted_remainder_tree_node_q(out[0], out[1], out[2], out[3], 6, 7));
        unchanged(q);
        CHECK(!weighted_remainder_mass_budget_q(out[0], out[1], out[2], out[3], 6));
        unchanged(q);
    }
    for (unsigned i = 0; i < 3; ++i) for (unsigned j = i + 1; j < 3; ++j) {
        sentinels(q);
        mpq_ptr out[3] = {q[0], q[1], q[2]};
        out[j] = out[i];
        unsigned nodes = 999;
        CHECK(!weighted_remainder_tree_box_q(out[0], out[1], out[2], 6, &nodes));
        CHECK(nodes == 999);
        unchanged(q);
    }
    sentinels(q);
    CHECK(!weighted_remainder_mass_q(q[0], q[0], 6));
    unchanged(q);
    CHECK(weighted_remainder_tree_box_q(q[0], q[1], q[2], 1, NULL));
    CHECK(mpq_cmp_ui(q[0], 1, 2) == 0);
    CHECK(isnan(weighted_remainder_weight(-1)));
    CHECK(isnan(weighted_remainder_weight(241)));
    printf("edge_checks %u\n", edge_checks);

    for (unsigned a = 1; a <= 40; ++a) for (unsigned b = 1; b <= 40; ++b) {
        assert(weighted_remainder_tree_node_q(q[0], q[1], q[2], q[3], a, b));
        gmp_printf("node %u %u %Qd %Qd %Qd %Qd\n", a, b, q[0], q[1], q[2], q[3]);
        assert(weighted_remainder_tree_address_q(q[0], a, b));
        gmp_printf("address %u %u %Qd\n", a, b, q[0]);
    }
    const unsigned large[] = {1, 119, 120, 238, 239, 240};
    for (unsigned i = 0; i < sizeof large / sizeof *large; ++i)
        for (unsigned j = 0; j < sizeof large / sizeof *large; ++j) {
            unsigned a = large[i], b = large[j];
            assert(weighted_remainder_tree_node_q(q[0], q[1], q[2], q[3], a, b));
            gmp_printf("node %u %u %Qd %Qd %Qd %Qd\n", a, b, q[0], q[1], q[2], q[3]);
            assert(weighted_remainder_tree_address_q(q[0], a, b));
            gmp_printf("address %u %u %Qd\n", a, b, q[0]);
        }
    for (unsigned m = 1; m <= 240; ++m) if (m <= 80 || m == 120 || m == 180 || m >= 239) {
        unsigned nodes;
        assert(weighted_remainder_tree_box_q(q[0], q[1], q[2], m, &nodes));
        gmp_printf("tree %u %u %Qd %Qd %Qd\n", m, nodes, q[0], q[1], q[2]);
    }
    for (unsigned n = 0; n <= 240; ++n) {
        assert(weighted_remainder_weight_q(q[0], n));
        assert(weighted_remainder_weight_inverse_q(q[1], n));
        gmp_printf("weight %u %Qd %Qd ", n, q[0], q[1]);
        printf("%.24Lg\n", weighted_remainder_weight((int)n));
        assert(weighted_remainder_mass_q(q[0], q[1], n));
        gmp_printf("mass %u %Qd %Qd\n", n, q[0], q[1]);
        assert(weighted_remainder_mass_budget_q(q[0], q[1], q[2], q[3], n));
        gmp_printf("mass_budget %u %Qd %Qd %Qd %Qd\n", n, q[0], q[1], q[2], q[3]);
        if (n) {
            assert(weighted_remainder_budget_q(q[0], n));
            gmp_printf("budget %u %Qd\n", n, q[0]);
        }
    }
    for (unsigned i = 0; i < 4; ++i) mpq_clear(q[i]);
    return 0;
}
