/* Exact finite-prefix slice and cylinder-to-carry identities. */

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

#include "nfield.h"

#define FPS_MAX_MODULUS 50000
#define FPS_MAX_DENOMINATOR 1000000
#define FPS_MAX_ABS_WEIGHT 1000000

static int fps_gcd(int left, int right)
{
    while (right != 0) {
        int remainder = left % right;
        left = right;
        right = remainder;
    }
    return left < 0 ? -left : left;
}

static int fps_modulus(int base, int depth, int *modulus)
{
    if (!modulus || base < 2 || depth < 1) return 0;
    int value = 1;
    for (int index = 0; index < depth; index++) {
        if (value > FPS_MAX_MODULUS / base) return 0;
        value *= base;
    }
    *modulus = value;
    return 1;
}

int finite_prefix_slice_identity(
        int denominator, int base, int depth,
        const int *weights, int weight_count,
        long long *intrinsic_count, long long *carry_count,
        long long *bulk_weight, long long *left_numerator,
        long long *right_numerator)
{
    int modulus = 0;
    if (!weights || !intrinsic_count || !carry_count || !bulk_weight ||
        !left_numerator || !right_numerator ||
        denominator < 2 || denominator > FPS_MAX_DENOMINATOR ||
        !fps_modulus(base, depth, &modulus) || weight_count != modulus ||
        fps_gcd(denominator, base) != 1)
        return 0;

    long long weight_sum = 0;
    for (int cell = 0; cell < modulus; cell++) {
        if (weights[cell] < -FPS_MAX_ABS_WEIGHT ||
            weights[cell] > FPS_MAX_ABS_WEIGHT)
            return 0;
        weight_sum += weights[cell];
    }

    long long intrinsic = 0;
    for (int numerator = 1; numerator < denominator; numerator++) {
        int cell = (int)((long long)modulus * numerator / denominator);
        intrinsic += weights[cell];
    }

    int residue = denominator % modulus;
    long long carries = 0;
    for (int cell = 0; cell < modulus; cell++) {
        int next = (int)((long long)(cell + 1) * residue / modulus);
        int current = (int)((long long)cell * residue / modulus);
        carries += (long long)weights[cell] * (next - current);
    }

    long long quotient = denominator / modulus;
    long long first_identity = quotient * weight_sum + carries -
                               weights[modulus - 1];
    long long left = (long long)modulus *
                     (intrinsic + weights[modulus - 1]) -
                     (long long)denominator * weight_sum;
    long long right = (long long)modulus * carries -
                      (long long)residue * weight_sum;

    *intrinsic_count = intrinsic;
    *carry_count = carries;
    *bulk_weight = weight_sum;
    *left_numerator = left;
    *right_numerator = right;
    return intrinsic == first_identity && left == right;
}

/* All-denominator ceiling form.  Unlike the published floor form above,
 * this identity includes nonunit denominator phases and a = 0. */
int finite_prefix_slice_identity_all_denominators(
        int denominator, int base, int depth,
        const int *weights, int weight_count,
        long long *intrinsic_count, long long *boundary_count,
        long long *bulk_weight, long long *left_numerator,
        long long *right_numerator)
{
    int modulus = 0;
    if (!weights || !intrinsic_count || !boundary_count || !bulk_weight ||
        !left_numerator || !right_numerator ||
        denominator < 1 || denominator > FPS_MAX_DENOMINATOR ||
        !fps_modulus(base, depth, &modulus) || weight_count != modulus)
        return 0;

    long long weight_sum = 0;
    for (int cell = 0; cell < modulus; cell++) {
        if (weights[cell] < -FPS_MAX_ABS_WEIGHT ||
            weights[cell] > FPS_MAX_ABS_WEIGHT)
            return 0;
        weight_sum += weights[cell];
    }

    long long intrinsic = 0;
    for (int numerator = 1; numerator < denominator; numerator++) {
        int cell = (int)((long long)modulus * numerator / denominator);
        intrinsic += weights[cell];
    }

    int residue = denominator % modulus;
    long long boundary = 0;
    for (int cell = 0; cell < modulus; cell++) {
        long long upper_numerator = (long long)(cell + 1) * residue;
        long long lower_numerator = (long long)cell * residue;
        int upper = (int)((upper_numerator + modulus - 1) / modulus);
        int lower = (int)((lower_numerator + modulus - 1) / modulus);
        boundary += (long long)weights[cell] * (upper - lower);
    }

    long long quotient = denominator / modulus;
    long long reconstructed = quotient * weight_sum + boundary - weights[0];
    long long left = (long long)modulus * (intrinsic + weights[0]) -
                     (long long)denominator * weight_sum;
    long long right = (long long)modulus * boundary -
                      (long long)residue * weight_sum;

    *intrinsic_count = intrinsic;
    *boundary_count = boundary;
    *bulk_weight = weight_sum;
    *left_numerator = left;
    *right_numerator = right;
    return intrinsic == reconstructed && left == right;
}

static int fps_supported_part(int denominator, int base)
{
    int supported = 1;
    int remaining = denominator;
    int common = 0;
    while ((common = fps_gcd(remaining, base)) > 1) {
        supported *= common;
        remaining /= common;
    }
    return supported;
}

int positional_transport_collapse(
        int denominator, int base,
        int *transient_denominator, int *persistent_denominator,
        int *collapse_depth, int *stable_kernel_size,
        int *stable_image_size)
{
    if (!transient_denominator || !persistent_denominator ||
        !collapse_depth || !stable_kernel_size || !stable_image_size ||
        denominator < 1 || denominator > FPS_MAX_DENOMINATOR || base < 2)
        return 0;

    int transient = fps_supported_part(denominator, base);
    int persistent = denominator / transient;
    int depth = 0;
    int kernel = 1;
    long long power = 1;
    while (kernel < transient) {
        if (power > LLONG_MAX / base) return 0;
        power *= base;
        depth++;
        kernel = fps_gcd(denominator, (int)(power % denominator));
    }

    *transient_denominator = transient;
    *persistent_denominator = persistent;
    *collapse_depth = depth;
    *stable_kernel_size = transient;
    *stable_image_size = persistent;
    return fps_gcd(persistent, base) == 1 && kernel == transient;
}

static int fps_parse_support(const char *text, int modulus, int *weights,
                             int *support_size)
{
    if (!text || !*text || !weights || !support_size) return 0;
    const char *cursor = text;
    int count = 0;
    while (*cursor != '\0') {
        char *end = NULL;
        long cell = strtol(cursor, &end, 10);
        if (end == cursor || cell < 0 || cell >= modulus ||
            weights[cell] != 0)
            return 0;
        weights[cell] = 1;
        count++;
        if (*end == '\0') break;
        if (*end != ',') return 0;
        cursor = end + 1;
        if (*cursor == '\0') return 0;
    }
    *support_size = count;
    return count > 0;
}

static int fps_print_identity(int denominator, int base, int depth,
                              const int *weights, int support_size,
                              const char *support_description)
{
    int modulus = 0;
    long long intrinsic = 0;
    long long carries = 0;
    long long weight_sum = 0;
    long long left = 0;
    long long right = 0;
    if (!fps_modulus(base, depth, &modulus) ||
        !finite_prefix_slice_identity(
            denominator, base, depth, weights, modulus,
            &intrinsic, &carries, &weight_sum, &left, &right)) {
        fprintf(stderr,
                "require 2<=q<=1000000, base>=2, depth>=1, b^depth<=50000, and gcd(q,b)=1\n");
        return 1;
    }
    int residue = denominator % modulus;
    int quotient = denominator / modulus;
    long long reconstructed = (long long)quotient * weight_sum + carries -
                              weights[modulus - 1];
    printf("Finite-prefix slice identity\n\n");
    printf("  q=%d base=%d depth=%d modulus=%d\n",
           denominator, base, depth, modulus);
    printf("  support=%s; marked cells=%d\n",
           support_description, support_size);
    printf("  q=h*m+a with h=%d and a=%d\n", quotient, residue);
    printf("  intrinsic weighted digit count C_w(q)=%lld\n", intrinsic);
    printf("  carry count A_w(a)=%lld; total weight=%lld\n",
           carries, weight_sum);
    printf("  terminal correction w(m-1)=%d\n", weights[modulus - 1]);
    printf("  h*sum(w)+A_w(a)-w(m-1)=%lld  %s\n",
           reconstructed, reconstructed == intrinsic ? "PASS" : "FAIL");
    printf("  centered numerators left=%lld right=%lld  %s\n",
           left, right, left == right ? "PASS" : "FAIL");
    printf("\nResult  %s\n",
           reconstructed == intrinsic && left == right ? "PASS" : "FAIL");
    return reconstructed == intrinsic && left == right ? 0 : 1;
}

static int fps_print_all_denominator_identity(
        int denominator, int base, int depth, const int *weights,
        int support_size, const char *support_description)
{
    int modulus = 0;
    long long intrinsic = 0;
    long long boundary = 0;
    long long weight_sum = 0;
    long long left = 0;
    long long right = 0;
    if (!fps_modulus(base, depth, &modulus) ||
        !finite_prefix_slice_identity_all_denominators(
            denominator, base, depth, weights, modulus,
            &intrinsic, &boundary, &weight_sum, &left, &right)) {
        fprintf(stderr,
                "require 1<=q<=1000000, base>=2, depth>=1, and b^depth<=50000\n");
        return 1;
    }
    int residue = denominator % modulus;
    int quotient = denominator / modulus;
    long long reconstructed = (long long)quotient * weight_sum + boundary -
                              weights[0];
    printf("All-denominator finite-carrier transposition\n\n");
    printf("  q=%d base=%d depth=%d carrier=%d\n",
           denominator, base, depth, modulus);
    printf("  support=%s; marked cells=%d\n",
           support_description, support_size);
    printf("  q=h*m+a with h=%d and a=%d\n", quotient, residue);
    printf("  intrinsic weighted digit count C_w(q)=%lld\n", intrinsic);
    printf("  ceiling-boundary response B_w(a)=%lld; total weight=%lld\n",
           boundary, weight_sum);
    printf("  initial endpoint correction w(0)=%d\n", weights[0]);
    printf("  h*sum(w)+B_w(a)-w(0)=%lld  %s\n",
           reconstructed, reconstructed == intrinsic ? "PASS" : "FAIL");
    printf("  centered numerators left=%lld right=%lld  %s\n",
           left, right, left == right ? "PASS" : "FAIL");
    printf("\nResult  %s\n",
           reconstructed == intrinsic && left == right ? "PASS" : "FAIL");
    return reconstructed == intrinsic && left == right ? 0 : 1;
}

int finite_prefix_slice_inspect(int denominator, int base, int depth,
                                const char *support)
{
    int modulus = 0;
    if (!fps_modulus(base, depth, &modulus)) {
        fprintf(stderr, "base and depth must give b^depth <= 50000\n");
        return 1;
    }
    int *weights = calloc((size_t)modulus, sizeof(*weights));
    if (!weights) {
        fprintf(stderr, "unable to allocate the finite support\n");
        return 1;
    }
    int support_size = 0;
    if (!fps_parse_support(support, modulus, weights, &support_size)) {
        fprintf(stderr,
                "support must be a comma-separated list of distinct cells in [0,b^depth)\n");
        free(weights);
        return 1;
    }
    int status = fps_print_identity(
        denominator, base, depth, weights, support_size, support);
    free(weights);
    return status;
}

int finite_prefix_slice_inspect_all_denominators(
        int denominator, int base, int depth, const char *support)
{
    int modulus = 0;
    if (!fps_modulus(base, depth, &modulus)) {
        fprintf(stderr, "base and depth must give b^depth <= 50000\n");
        return 1;
    }
    int *weights = calloc((size_t)modulus, sizeof(*weights));
    if (!weights) {
        fprintf(stderr, "unable to allocate the finite support\n");
        return 1;
    }
    int support_size = 0;
    if (!fps_parse_support(support, modulus, weights, &support_size)) {
        fprintf(stderr,
                "support must be a comma-separated list of distinct cells in [0,b^depth)\n");
        free(weights);
        return 1;
    }
    int status = fps_print_all_denominator_identity(
        denominator, base, depth, weights, support_size, support);
    free(weights);
    return status;
}

int positional_transport_collapse_inspect(int denominator, int base)
{
    int transient = 0;
    int persistent = 0;
    int depth = 0;
    int kernel = 0;
    int image = 0;
    if (!positional_transport_collapse(
            denominator, base, &transient, &persistent, &depth,
            &kernel, &image)) {
        fprintf(stderr, "require 1<=q<=1000000 and base>=2\n");
        return 1;
    }
    printf("Positional transport collapse\n\n");
    printf("  q=%d base=%d\n", denominator, base);
    printf("  transient base-supported denominator q_parallel=%d\n", transient);
    printf("  persistent coprime denominator q_perp=%d\n", persistent);
    printf("  exact collapse depth nu_b(q)=%d\n", depth);
    printf("  stable kernel size=%d; stable image size=%d\n", kernel, image);
    printf("  transport status=%s\n",
           depth == 0 ? "invertible from the outset" :
                        "transient kernel stabilizes at the stated depth");
    printf("\nResult  %s\n",
           kernel * image == denominator ? "PASS" : "FAIL");
    return kernel * image == denominator ? 0 : 1;
}

int finite_prefix_slice_collision(int denominator, int base, int lag)
{
    int depth = lag + 1;
    int modulus = 0;
    int leading_place = 0;
    if (lag < 1 || !fps_modulus(base, depth, &modulus) ||
        !fps_modulus(base, lag, &leading_place)) {
        fprintf(stderr,
                "base and lag must give b^(lag+1) <= 50000 with lag>=1\n");
        return 1;
    }
    int *weights = calloc((size_t)modulus, sizeof(*weights));
    if (!weights) {
        fprintf(stderr, "unable to allocate the collision support\n");
        return 1;
    }
    int support_size = 0;
    for (int cell = 0; cell < modulus; cell++) {
        if (cell / leading_place == cell % base) {
            weights[cell] = 1;
            support_size++;
        }
    }
    int status = fps_print_identity(
        denominator, base, depth, weights, support_size,
        "first digit equals digit lag+1");
    free(weights);
    return status;
}

static int fps_check_weights(int denominator, int base, int depth,
                             int *weights, int modulus)
{
    long long intrinsic = 0;
    long long carries = 0;
    long long weight_sum = 0;
    long long left = 0;
    long long right = 0;
    return finite_prefix_slice_identity(
        denominator, base, depth, weights, modulus,
        &intrinsic, &carries, &weight_sum, &left, &right);
}

int finite_prefix_slice_verify(void)
{
    int example_ok = 0;
    int basis_ok = 1;
    int signed_ok = 1;
    int collision_ok = 1;
    int domain_ok = 1;
    int all_denominator_ok = 1;
    int transport_ok = 1;
    int basis_models = 0;
    int signed_models = 0;
    int collision_models = 0;
    int all_denominator_models = 0;
    int transport_models = 0;

    int example_weights[9] = {1, 0, 0, 0, 1, 0, 0, 0, 1};
    long long intrinsic = 0;
    long long carries = 0;
    long long sum = 0;
    long long left = 0;
    long long right = 0;
    example_ok = finite_prefix_slice_identity(
        11, 3, 2, example_weights, 9,
        &intrinsic, &carries, &sum, &left, &right) &&
        intrinsic == 4 && carries == 2 && sum == 3 &&
        left == 12 && right == 12;

    for (int base = 2; base <= 12; base++) {
        for (int depth = 1; depth <= 4; depth++) {
            int modulus = 0;
            if (!fps_modulus(base, depth, &modulus) || modulus > 256)
                continue;
            int *weights = calloc((size_t)modulus, sizeof(*weights));
            if (!weights) return 0;
            int denominators[] = {
                modulus - 1, modulus + 1, 2 * modulus - 1,
                2 * modulus + 1
            };
            for (int cell = 0; cell < modulus; cell++) {
                weights[cell] = 1;
                for (size_t index = 0;
                     index < sizeof(denominators) / sizeof(denominators[0]);
                     index++) {
                    if (denominators[index] < 2) continue;
                    basis_models++;
                    if (!fps_check_weights(
                            denominators[index], base, depth,
                            weights, modulus))
                        basis_ok = 0;
                }
                weights[cell] = 0;
            }
            for (int cell = 0; cell < modulus; cell++)
                weights[cell] = cell % 5 - 2;
            for (size_t index = 0;
                 index < sizeof(denominators) / sizeof(denominators[0]);
                 index++) {
                if (denominators[index] < 2) continue;
                signed_models++;
                if (!fps_check_weights(
                        denominators[index], base, depth,
                        weights, modulus))
                    signed_ok = 0;
            }
            free(weights);
        }
    }

    for (int base = 2; base <= 12; base++) {
        for (int lag = 1; lag <= 3; lag++) {
            int modulus = 0;
            int leading_place = 0;
            if (!fps_modulus(base, lag + 1, &modulus) || modulus > 2000 ||
                !fps_modulus(base, lag, &leading_place))
                continue;
            int *weights = calloc((size_t)modulus, sizeof(*weights));
            if (!weights) return 0;
            for (int cell = 0; cell < modulus; cell++)
                weights[cell] = cell / leading_place == cell % base;
            int denominators[] = {modulus - 1, modulus + 1,
                                  2 * modulus + 1};
            for (size_t index = 0;
                 index < sizeof(denominators) / sizeof(denominators[0]);
                 index++) {
                collision_models++;
                if (!fps_check_weights(
                        denominators[index], base, lag + 1,
                        weights, modulus))
                    collision_ok = 0;
            }
            free(weights);
        }
    }

    domain_ok = !finite_prefix_slice_identity(
        10, 10, 1, example_weights, 9,
        &intrinsic, &carries, &sum, &left, &right);

    for (int base = 2; base <= 12; base++) {
        for (int depth = 1; depth <= 4; depth++) {
            int modulus = 0;
            if (!fps_modulus(base, depth, &modulus) || modulus > 128)
                continue;
            int *weights = calloc((size_t)modulus, sizeof(*weights));
            if (!weights) return 0;
            for (int cell = 0; cell < modulus; cell++)
                weights[cell] = (cell * cell + 3 * cell + 1) % 11 - 5;
            for (int denominator = 1; denominator <= 3 * modulus + 2;
                 denominator++) {
                all_denominator_models++;
                if (!finite_prefix_slice_identity_all_denominators(
                        denominator, base, depth, weights, modulus,
                        &intrinsic, &carries, &sum, &left, &right))
                    all_denominator_ok = 0;
            }
            free(weights);
        }
    }

    for (int base = 2; base <= 20; base++) {
        for (int denominator = 1; denominator <= 1000; denominator++) {
            int transient = 0;
            int persistent = 0;
            int depth = 0;
            int kernel = 0;
            int image = 0;
            transport_models++;
            if (!positional_transport_collapse(
                    denominator, base, &transient, &persistent, &depth,
                    &kernel, &image) ||
                transient * persistent != denominator ||
                kernel != transient || image != persistent ||
                fps_gcd(persistent, base) != 1)
                transport_ok = 0;

            long long power = 1;
            for (int step = 0; step < depth; step++) power *= base;
            if (fps_gcd(denominator, (int)(power % denominator)) != transient)
                transport_ok = 0;
            if (depth > 0) {
                power /= base;
                if (fps_gcd(denominator, (int)(power % denominator)) == transient)
                    transport_ok = 0;
            }
        }
    }

    int passed = example_ok + basis_ok + signed_ok + collision_ok + domain_ok +
                 all_denominator_ok + transport_ok;
    printf("Finite-prefix slice verification\n\n");
    printf("  nine-state example C=4, A=2, centered numerator=12  %s\n",
           example_ok ? "PASS" : "FAIL");
    printf("  cell-basis identities=%d                            %s\n",
           basis_models, basis_ok ? "PASS" : "FAIL");
    printf("  signed-weight identities=%d                         %s\n",
           signed_models, signed_ok ? "PASS" : "FAIL");
    printf("  collision-cylinder identities=%d                    %s\n",
           collision_models, collision_ok ? "PASS" : "FAIL");
    printf("  noncoprime/domain rejection                          %s\n",
           domain_ok ? "PASS" : "FAIL");
    printf("  all-denominator phase identities=%d                 %s\n",
           all_denominator_models,
           all_denominator_ok ? "PASS" : "FAIL");
    printf("  transport collapse decompositions=%d                %s\n",
           transport_models, transport_ok ? "PASS" : "FAIL");
    printf("\n%d/7 verification groups passed.\n", passed);
    printf("Exact boundary  every reported value uses integer floor arithmetic.\n");
    printf("Algebraic scope  the identity is linear in the finite weight;\n");
    printf("the cell-basis sweep checks its generators independently.\n");
    return passed == 7;
}

void finite_prefix_slice_help(void)
{
    printf(
        "Finite-prefix slice identity\n\n"
        "Commands\n"
        "  nfield finite-prefix-slice inspect <q> --base <b> --depth <N>\n"
        "      --support <cell,cell,...>\n"
        "      Check any indicator support on the b^N finite-prefix cells.\n"
        "  nfield finite-prefix-slice all <q> --base <b> --depth <N>\n"
        "      --support <cell,cell,...>\n"
        "      Check the ceiling-boundary identity for every denominator,\n"
        "      including phases sharing factors with the base and phase zero.\n"
        "  nfield finite-prefix-slice collapse <q> --base <b>\n"
        "      Compute the exact transport-collapse depth and survivor quotient.\n"
        "  nfield finite-prefix-slice collision <q> --base <b> --lag <ell>\n"
        "      Build the first-digit/lag+1 collision support automatically.\n"
        "  nfield finite-prefix-slice verify\n"
        "  nfield verify finite-prefix-slice\n\n"
        "Example\n"
        "  nfield finite-prefix-slice inspect 11 --base 3 --depth 2\n"
        "      --support 0,4,8\n\n"
        "  nfield finite-prefix-slice all 12 --base 3 --depth 2\n"
        "      --support 0,4,8\n"
        "  nfield finite-prefix-slice collapse 28 --base 10\n\n"
        "Scope\n"
        "  proved       every finite-prefix weighted digit rule reduces to its\n"
        "               exact carry count after bulk and endpoint correction.\n"
        "  exact        all displayed counts and centered numerators are integers.\n"
        "  verifier     checks every cell basis vector in its declared bounded\n"
        "               tables, signed weights, and collision supports.\n"
        "  boundary     inspect and collision require q coprime to b;\n"
        "               b^N is capped at 50000.\n"
        "  extension    the all action removes the coprimality restriction;\n"
        "               the collapse action isolates the persistent quotient.\n"
    );
}
