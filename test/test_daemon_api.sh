#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

BIN="${BIN:-./nfield}"
PORT="${NFIELD_TEST_PORT:-$((19090 + ($$ % 1000)))}"
log_file="$(mktemp)"
daemon_pid=""

cleanup() {
    if [ -n "$daemon_pid" ] && kill -0 "$daemon_pid" 2>/dev/null; then
        kill "$daemon_pid" 2>/dev/null || true
        wait "$daemon_pid" 2>/dev/null || true
    fi
    rm -f "$log_file"
}
trap cleanup EXIT

"$BIN" daemon --port "$PORT" --threads 1 >"$log_file" 2>&1 &
daemon_pid=$!

api_request() {
    local command="$1"
    local response=""
    for _ in $(seq 1 50); do
        if exec 3<>"/dev/tcp/127.0.0.1/$PORT" 2>/dev/null; then
            printf '{"cmd":"%s"}\n' "$command" >&3
            IFS= read -r response <&3
            exec 3<&-
            exec 3>&-
            printf '%s' "$response"
            return 0
        fi
        sleep 0.1
    done
    printf 'daemon did not accept requests\n' >&2
    return 1
}

printf 'nfield daemon API regression tests\n'
printf '==================================================\n\n'

native_refinement="$(api_request 'native-refinement trace 4 8')"
grep -Fq 'full infinite norm; period=840' <<<"$native_refinement"
grep -Fq 'uniform lower bound OPEN' <<<"$native_refinement"
printf '  native refinement through JSON/TCP: PASS\n'

native_refinement_json="$(api_request 'native-refinement trace 4 6 --json')"
python3 -c 'import json,sys; response=json.loads(sys.stdin.read()); data=json.loads(response["output"]); assert data["status"]=="PASS" and data["first"]==4 and data["last"]==6 and data["uniform_lower_bound_proved"] is False' <<<"$native_refinement_json"
printf '  native refinement interval JSON through JSON/TCP: PASS\n'

native_collision4_json="$(api_request 'native-refinement collision4 --json')"
python3 -c 'import json,sys; response=json.loads(sys.stdin.read()); data=json.loads(response["output"]); assert data["status"]=="PASS" and data["first"]==4 and data["last"]==8 and float(data["capture_fraction"]["hi"])<.001 and float(data["signed_response"]["hi"])<0' <<<"$native_collision4_json"
printf '  native collision4 calibration through JSON/TCP: PASS\n'

native_collision_families_json="$(api_request 'native-refinement collision-families --json')"
python3 -c 'import json,sys; response=json.loads(sys.stdin.read()); data=json.loads(response["output"]); families={row["modulus"]:row for row in data["families"]}; assert data["status"]=="PASS" and families[9]["finite_orbit_rank"]==2 and families[9]["projected_shell_rank"]==2 and families[25]["finite_orbit_rank"]==8 and families[25]["projected_shell_rank"]==4 and data["combined"]["projected_shell_rank"]==4' <<<"$native_collision_families_json"
printf '  native translated collision families through JSON/TCP: PASS\n'

native_collision_families_16_json="$(api_request 'native-refinement collision-families 8 16 --json')"
python3 -c 'import json,sys; response=json.loads(sys.stdin.read()); data=json.loads(response["output"]); families={row["modulus"]:row for row in data["families"]}; assert data["status"]=="PASS" and data["first"]==8 and data["last"]==16 and data["complete_period_audit"] is False and families[25]["finite_orbit_rank"]==8 and families[25]["projected_shell_rank"]==8 and families[25]["projected_rank_exact"] is True' <<<"$native_collision_families_16_json"
printf '  native q25 rank-budget exhaustion through JSON/TCP: PASS\n'

native_collision_tower_49_json="$(api_request 'native-refinement collision-families 4 16 --json')"
python3 -c 'import json,sys; response=json.loads(sys.stdin.read()); data=json.loads(response["output"]); families={row["modulus"]:row for row in data["families"]}; assert data["status"]=="PASS" and data["combined"]["finite_tower_rank"]==11 and data["combined"]["projected_shell_rank"]==11 and data["combined"]["blind_codimension"]==1 and families[49]["finite_orbit_rank"]==18 and families[49]["projected_shell_rank"]==12 and data["extension_49"]["rank_increment"]==1 and float(data["extension_49"]["prior_blind_detection_fraction"]["lo"])>.999999' <<<"$native_collision_tower_49_json"
printf '  native CRT rank exhaustion and q49 recovery through JSON/TCP: PASS\n'

reciprocal_selection="$(api_request 'reciprocal-square-selection inspect 3 4 --base 10')"
grep -Fq 'exact alignment alpha_b(pm)=7/11' <<<"$reciprocal_selection"
grep -Fq 'threshold certificate A^2+A*B-B^2=5' <<<"$reciprocal_selection"
grep -Fq 'Result  PASS' <<<"$reciprocal_selection"
printf '  reciprocal-square selection through JSON/TCP: PASS\n'

reciprocal_cubic="$(api_request 'reciprocal-square-selection cubic 3')"
grep -Fq 'factorization: (x-2)(x^2+x-1)' <<<"$reciprocal_cubic"
grep -Fq 'remainder: (0)*x' <<<"$reciprocal_cubic"
grep -Fq 'Result  PASS' <<<"$reciprocal_cubic"
printf '  reciprocal-square cubic through JSON/TCP: PASS\n'

reciprocal_verification="$(api_request 'verify reciprocal-square-selection')"
grep -Fq '12/12 verification groups passed.' <<<"$reciprocal_verification"
grep -Fq '1/1 verifications passed.' <<<"$reciprocal_verification"
printf '  reciprocal-square verifier through JSON/TCP: PASS\n'

weighted_profile="$(api_request 'weighted-reference-profile inspect 3 4 1 1 --base 10')"
grep -Fq 'terminating block=3  reference block=4  other blocks=4' <<<"$weighted_profile"
grep -Fq 'exact score C_q,lambda(m)=7/11' <<<"$weighted_profile"
grep -Fq 'Result  PASS' <<<"$weighted_profile"
printf '  weighted reference profile through JSON/TCP: PASS\n'

weighted_branch="$(api_request 'weighted-reference-profile branch 3 3')"
grep -Fq 'lambda_q,r=(0 + 3*tau)/2' <<<"$weighted_branch"
grep -Fq 'rational coordinate no' <<<"$weighted_branch"
grep -Fq 'Result  PASS' <<<"$weighted_branch"
printf '  reciprocal-golden branch through JSON/TCP: PASS\n'

weighted_torsion="$(api_request 'weighted-reference-profile torsion')"
grep -Fq 'order two: every q>=2 at lambda=0' <<<"$weighted_torsion"
grep -Fq 'order six: no rational unit-interval weight' <<<"$weighted_torsion"
grep -Fq 'Result  PASS' <<<"$weighted_torsion"
printf '  rational profile torsion through JSON/TCP: PASS\n'

weighted_reflection_product="$(api_request 'weighted-reference-profile reflection-product 4')"
grep -Fq 'R_q*S=[[2,-1],[5,-3]]' <<<"$weighted_reflection_product"
grep -Fq 'projectively Fibonacci after primitive sign normalization: yes' <<<"$weighted_reflection_product"
grep -Fq 'profile intersection above one: none' <<<"$weighted_reflection_product"
printf '  reflection-product family through JSON/TCP: PASS\n'

weighted_oriented_words="$(api_request 'weighted-reference-profile oriented-words 4')"
grep -Fq 'positive output action -P*(S*R_q)*P=[[1,1],[1,0]]' \
    <<<"$weighted_oriented_words"
grep -Fq 'S*R_4=-R_2*S, the same projective action  PASS' \
    <<<"$weighted_oriented_words"
printf '  oriented profile words through JSON/TCP: PASS\n'

weighted_transport="$(api_request 'weighted-reference-profile transport')"
grep -Fq 'S^3=-I, projective order three  PASS' <<<"$weighted_transport"
grep -Fq 'unique x>1 is phi^2=2+tau; common value is tau  PASS' <<<"$weighted_transport"
grep -Fq "A'=S*R=[[0,1],[1,1]]" <<<"$weighted_transport"
grep -Fq "J*A'*J=[[1,1],[1,0]], the Fibonacci operator  PASS" <<<"$weighted_transport"
grep -Fq 'R*S fixes phi^2; S*R fixes tau  PASS' <<<"$weighted_transport"
grep -Fq 'strictly totally positive powers  PASS' <<<"$weighted_transport"
grep -Fq 'Result  PASS' <<<"$weighted_transport"
printf '  binary-ternary golden transport through JSON/TCP: PASS\n'

weighted_verification="$(api_request 'verify weighted-reference-profile')"
grep -Fq '16/16 verification groups passed.' <<<"$weighted_verification"
grep -Fq '1/1 verifications passed.' <<<"$weighted_verification"
printf '  weighted reference verifier through JSON/TCP: PASS\n'

digit_partition_table="$(api_request 'digit-partition table')"
grep -Fq 'p=3: 2/3=0.667' <<<"$digit_partition_table"
grep -Fq 'p=17: 2/17=0.118' <<<"$digit_partition_table"
grep -Fq 'Result  PASS' <<<"$digit_partition_table"
printf '  digit-partition table through JSON/TCP: PASS\n'

digit_partition_verification="$(api_request 'verify digit-partition')"
grep -Fq '9/9 equation groups passed.' <<<"$digit_partition_verification"
grep -Fq '1/1 verifications passed.' <<<"$digit_partition_verification"
printf '  digit-partition verifier through JSON/TCP: PASS\n'

alignment_limit_cosets="$(api_request 'alignment-limit cosets 53 --base 10')"
grep -Fq '4 multiplicative cosets' <<<"$alignment_limit_cosets"
grep -Fq '80/689' <<<"$alignment_limit_cosets"
grep -Fq '82/689' <<<"$alignment_limit_cosets"
grep -Fq 'all cosets equidistributed: no' <<<"$alignment_limit_cosets"
printf '  alignment-limit cosets through JSON/TCP: PASS\n'

alignment_limit_verification="$(api_request 'verify alignment-limit')"
grep -Fq '7/7 finite checks passed.' <<<"$alignment_limit_verification"
grep -Fq 'named p=53 values and period-four cycle' <<<"$alignment_limit_verification"
grep -Fq '1/1 verifications passed.' <<<"$alignment_limit_verification"
printf '  alignment-limit verifier through JSON/TCP: PASS\n'

three_tier_inspection="$(api_request 'three-tier inspect 21 --base 10')"
grep -Fq 'canonical decomposition n = t*m = 21*1' <<<"$three_tier_inspection"
grep -Fq 'direct-clock comparison = PASS' <<<"$three_tier_inspection"
grep -Fq 'tier = III' <<<"$three_tier_inspection"
printf '  three-tier composite rough part through JSON/TCP: PASS\n'

three_tier_verification="$(api_request 'verify three-tier')"
grep -Fq '8/8 finite checks passed.' <<<"$three_tier_verification"
grep -Fq 'odd-base middle digit, fixed point, and exact two-core family' <<<"$three_tier_verification"
grep -Fq '1/1 verifications passed.' <<<"$three_tier_verification"
printf '  three-tier verifier through JSON/TCP: PASS\n'

coherence_prime_core="$(api_request 'coherence-decomposition prime-core 3 4 --base 10')"
grep -Fq 'C(s-1,2) + (p-1)C(s,2) = 15' <<<"$coherence_prime_core"
grep -Fq 'sigma_10(12) = 3/11' <<<"$coherence_prime_core"
grep -Fq 'alpha=F+sigma with different sample-space averages: PASS' <<<"$coherence_prime_core"
printf '  coherence prime-core decomposition through JSON/TCP: PASS\n'

coherence_verification="$(api_request 'verify coherence-decomposition')"
grep -Fq 'finite deficits, limit coefficients, and gap width' <<<"$coherence_verification"
grep -Fq '8/8 finite checks passed.' <<<"$coherence_verification"
grep -Fq '1/1 verifications passed.' <<<"$coherence_verification"
printf '  coherence verifier through JSON/TCP: PASS\n'

cross_matrix="$(api_request 'cross-alignment matrix 12 --base 10')"
grep -Fq 'exact one-hot Gram reconstruction G=L*A: PASS' <<<"$cross_matrix"
grep -Fq 'reference alignment alpha = 7/11' <<<"$cross_matrix"
grep -Fq 'pairwise off-diagonal mean sigma = 3/11' <<<"$cross_matrix"
grep -Fq 'Result: PASS' <<<"$cross_matrix"
printf '  synchronized matrix through JSON/TCP: PASS\n'

cross_fourier="$(api_request 'cross-alignment fourier 17 --base 10')"
grep -Fq 'exact LxL circulant block check: PASS' <<<"$cross_fourier"
grep -Fq 'numerical DFT/full-spectrum agreement: PASS' <<<"$cross_fourier"
printf '  orbit Fourier reduction through JSON/TCP: PASS\n'

cross_verification="$(api_request 'verify cross-alignment')"
grep -Fq '7/7 finite checks passed.' <<<"$cross_verification"
grep -Fq '1/1 verifications passed.' <<<"$cross_verification"
printf '  synchronized matrix verifier through JSON/TCP: PASS\n'

cross_help="$(api_request 'help cross-alignment')"
grep -Fq 'Synchronized matrix and orbit-spectrum tools' <<<"$cross_help"
if grep -Fq 'The Cross-Alignment Matrix' <<<"$cross_help" ||
   grep -Fq '10.5281/zenodo' <<<"$cross_help"; then
    printf 'cross-alignment help is tied to a work title or DOI\n' >&2
    exit 1
fi
printf '  object-first synchronized matrix help through JSON/TCP: PASS\n'

spectral_inspection="$(api_request 'spectral-structure inspect 7 --base 2')"
grep -Fq 'exact rank bound = 4; numerical rank <= bound: PASS' <<<"$spectral_inspection"
grep -Fq 'exact off-diagonal square sum' <<<"$spectral_inspection"
grep -Fq 'tolerance 1e-8' <<<"$spectral_inspection"
grep -Fq 'Result: PASS' <<<"$spectral_inspection"
printf '  orbit-frequency inspection through JSON/TCP: PASS\n'

spectral_two_coset="$(api_request 'spectral-structure two-coset 13 --base 10')"
grep -Fq 'Q = 2*delta_3' <<<"$spectral_two_coset"
grep -Fq 'exact levels: 2/3 and 4/3, each with multiplicity 6' <<<"$spectral_two_coset"
grep -Fq 'numerical global spectrum (tolerance 1e-8): 2 levels' <<<"$spectral_two_coset"
printf '  orbit-frequency two-coset branch through JSON/TCP: PASS\n'

spectral_character="$(api_request 'spectral-structure character 17 --base 10')"
grep -Fq 'distinct from Dirichlet L-values' <<<"$spectral_character"
grep -Fq 'Numerical Fourier evaluation uses tolerance 1e-8' <<<"$spectral_character"
if grep -Fq 'No analytic continuation' <<<"$spectral_character"; then
    printf 'spectral character output contains defensive analytic language\n' >&2
    exit 1
fi
printf '  orbit-frequency character energy through JSON/TCP: PASS\n'

spectral_help="$(api_request 'help spectral-structure')"
grep -Fq 'Multiplicative orbit-frequency structure' <<<"$spectral_help"
grep -Fq 'distinct from the additive digit-bin spectrum' <<<"$spectral_help"
if grep -Fq 'The Spectral Structure of Fractional Fields' <<<"$spectral_help" ||
   grep -Fq '10.5281/zenodo' <<<"$spectral_help"; then
    printf 'spectral-structure help is tied to a work title or DOI\n' >&2
    exit 1
fi
printf '  object-first orbit-frequency help through JSON/TCP: PASS\n'

examples="$(api_request 'spectral-structure examples')"
grep -Fq 'Orbit-frequency exact examples and numerical spectral contrasts' <<<"$examples"
grep -Fq 'two cosets alone do not force two levels: PASS' <<<"$examples"
printf '  spectral-structure examples through JSON/TCP: PASS\n'

verification="$(api_request 'verify spectral-structure')"
grep -Fq '7/7 finite checks passed.' <<<"$verification"
grep -Fq '1/1 verifications passed.' <<<"$verification"
printf '  spectral-structure verifier through JSON/TCP: PASS\n'

power_examples="$(api_request 'spectral-power examples')"
grep -Fq 'Spectral-power exact examples and numerical Fourier checks' <<<"$power_examples"
grep -Fq 'same additive power with different multiplicative orders  PASS' <<<"$power_examples"
printf '  spectral-power examples through JSON/TCP: PASS\n'

power_verification="$(api_request 'verify spectral-power')"
grep -Fq '8/8 finite checks passed.' <<<"$power_verification"
grep -Fq '1/1 verifications passed.' <<<"$power_verification"
printf '  spectral-power verifier through JSON/TCP: PASS\n'

autocorrelation_inspect="$(api_request 'autocorrelation inspect 41 --base 10')"
grep -Fq 'The Fourier slice is aggregate; the reference word is one orbit.' <<<"$autocorrelation_inspect"
grep -Fq 'Result  PASS' <<<"$autocorrelation_inspect"
printf '  autocorrelation multi-orbit inspection through JSON/TCP: PASS\n'

autocorrelation_verification="$(api_request 'verify autocorrelation')"
grep -Fq '8/8 verification groups passed.' <<<"$autocorrelation_verification"
grep -Fq '1/1 verifications passed.' <<<"$autocorrelation_verification"
printf '  autocorrelation verifier through JSON/TCP: PASS\n'

phase_gate_inspect="$(api_request 'phase-gate inspect 7 3 --base 10')"
grep -Fq 'weighted sum / p^2' <<<"$phase_gate_inspect"
grep -Fq 'Gamma=0 iff C=0  PASS' <<<"$phase_gate_inspect"
grep -Fq 'Result  PASS' <<<"$phase_gate_inspect"
printf '  phase-gate spectral inspection through JSON/TCP: PASS\n'

phase_gate_bin_word="$(api_request 'phase-gate bin-word 43 --base 10')"
grep -Fq 'CF(10/3) = [3,3]' <<<"$phase_gate_bin_word"
grep -Fq 'G(0,0) = 178' <<<"$phase_gate_bin_word"
printf '  phase-gate Euclidean bin word through JSON/TCP: PASS\n'

phase_gate_prime_sum="$(api_request 'phase-gate prime-sum 2 --base 10 --max-prime 997')"
grep -Fq 'leading coefficient = 0.100000000000' <<<"$phase_gate_prime_sum"
grep -Fq 'The ratio is finite evidence' <<<"$phase_gate_prime_sum"
printf '  phase-gate prime-sum boundary through JSON/TCP: PASS\n'

phase_gate_verification="$(api_request 'verify phase-gate')"
grep -Fq '11/11 verification groups passed.' <<<"$phase_gate_verification"
grep -Fq '1/1 verifications passed.' <<<"$phase_gate_verification"
printf '  phase-gate verifier through JSON/TCP: PASS\n'

bin_derangements_inspect="$(api_request 'bin-derangements inspect 13 --base 10')"
grep -Fq 'explicit family is exactly the zero set' <<<"$bin_derangements_inspect"
grep -Fq 'within-bin ratio-set size is p-b = 3' <<<"$bin_derangements_inspect"
grep -Fq 'Result  PASS' <<<"$bin_derangements_inspect"
printf '  bin-derangements exact inspection through JSON/TCP: PASS\n'

bin_derangements_verification="$(api_request 'verify bin-derangements')"
grep -Fq '12/12 verification groups passed.' <<<"$bin_derangements_verification"
grep -Fq '1/1 verifications passed.' <<<"$bin_derangements_verification"
printf '  bin-derangements verifier through JSON/TCP: PASS\n'

global_help="$(api_request '--help')"
grep -Fq 'Command-line tools' <<<"$global_help"
grep -Fq 'Common commands' <<<"$global_help"
grep -Fq 'Find more' <<<"$global_help"
grep -Fq 'nfield commands' <<<"$global_help"
grep -Fq 'nfield completion' <<<"$global_help"
printf '  global help through JSON/TCP: PASS\n'

rejected_shell_syntax="$(api_request '--help;printf INJECTED')"
grep -Fq 'Invalid command syntax: use plain arguments without shell operators' \
    <<<"$rejected_shell_syntax"
if grep -Fq 'Command-line tools' <<<"$rejected_shell_syntax"; then
    printf 'daemon executed rejected shell syntax\n' >&2
    exit 1
fi
printf '  shell-free daemon dispatch rejection: PASS\n'

verify_help="$(api_request 'verify')"
grep -Fq 'List verifiers without running them' <<<"$verify_help"
grep -Fq 'Tool verifiers' <<<"$verify_help"
grep -Fq 'does not establish a universal or analytic theorem' <<<"$verify_help"
if grep -Fq 'Synchronized digit-partition verification' <<<"$verify_help"; then
    printf 'bare verify unexpectedly ran the full suite\n' >&2
    exit 1
fi
printf '  safe verifier index through JSON/TCP: PASS\n'

verification_map="$(api_request 'help reading-map')"
grep -Fq 'Repetend Rigidity at the Golden Scale' <<<"$verification_map"
grep -Fq 'weighted-reference-profile' <<<"$verification_map"
grep -Fq 'Digit-Partitioning Primes and the Alignment Formula' <<<"$verification_map"
grep -Fq 'The Coherence Decomposition' <<<"$verification_map"
grep -Fq 'The Cross-Alignment Matrix' <<<"$verification_map"
grep -Fq 'The Spectral Power of the Digit Function' <<<"$verification_map"
grep -Fq 'The General Neutrality Theorem' <<<"$verification_map"
grep -Fq 'The Structure That Survives' <<<"$verification_map"
grep -Fq 'Commands stay parameterized and independent of the title' <<<"$verification_map"
printf '  work-to-object reading map through JSON/TCP: PASS\n'

collision_characters_inspect="$(api_request 'collision-characters inspect 100 --base 10 --lag 1 --sigma 1 --tau 0.25')"
grep -Fq 'U_b has phi(b)=4 classes and 4 characters' <<<"$collision_characters_inspect"
grep -Fq 'conjugate-character pairing' <<<"$collision_characters_inspect"
grep -Fq 'Result  PASS' <<<"$collision_characters_inspect"
printf '  collision-character decomposition through JSON/TCP: PASS\n'

collision_characters_snapshot="$(api_request 'collision-characters snapshot')"
grep -Fq '10000   1224' <<<"$collision_characters_snapshot"
grep -Fq '4/4 reference rows reproduced.' <<<"$collision_characters_snapshot"
printf '  collision-character snapshot through JSON/TCP: PASS\n'

collision_characters_verification="$(api_request 'verify collision-characters')"
grep -Fq '13/13 verification groups passed.' <<<"$collision_characters_verification"
grep -Fq '1/1 verifications passed.' <<<"$collision_characters_verification"
printf '  collision-character verifier through JSON/TCP: PASS\n'

silent_recipe="$(api_request 'silent-primes recipe --base 10 --lag 1')"
grep -Fq 'prime divisors p>b = {11,13,19,23,37,41,73}' <<<"$silent_recipe"
grep -Fq 'Result  PASS' <<<"$silent_recipe"
printf '  silent-prime finite recipe through JSON/TCP: PASS\n'

silent_prime="$(api_request 'silent-primes prime 13 --base 8 --lag 1')"
grep -Fq 'repetend-silent but not a globally silent prime' <<<"$silent_prime"
grep -Fq 'Result  PASS' <<<"$silent_prime"
printf '  silent-prime orbit distinction through JSON/TCP: PASS\n'

silent_variance="$(api_request 'silent-primes variance 97 --base 10')"
grep -Fq 'variance from direct population and interval ledger = 11096/1849' <<<"$silent_variance"
grep -Fq 'full variance asymptotic is open' <<<"$silent_variance"
printf '  silent-prime exact variance through JSON/TCP: PASS\n'

silent_snapshot="$(api_request 'silent-primes snapshot')"
grep -Fq '7/7 base-ten rows reproduced from exact rational values' <<<"$silent_snapshot"
grep -Fq '5/5 cross-base rows reproduced' <<<"$silent_snapshot"
printf '  silent-prime variance snapshot through JSON/TCP: PASS\n'

silent_verification="$(api_request 'verify silent-primes')"
grep -Fq '14/14 verification groups passed.' <<<"$silent_verification"
grep -Fq '1/1 verifications passed.' <<<"$silent_verification"
printf '  silent-prime verifier through JSON/TCP: PASS\n'

fluctuation_prime="$(api_request 'collision-fluctuation prime 191 --base 10')"
grep -Fq 'Delta_b(p) = -9/1' <<<"$fluctuation_prime"
grep -Fq 'F_10(91) = -9  PASS' <<<"$fluctuation_prime"
printf '  collision-fluctuation exact prime through JSON/TCP: PASS\n'

fluctuation_classes="$(api_request 'collision-fluctuation classes --base 10')"
grep -Fq 'all-family mean = -9/10' <<<"$fluctuation_classes"
grep -Fq 'Result  PASS' <<<"$fluctuation_classes"
printf '  collision-fluctuation classes through JSON/TCP: PASS\n'

fluctuation_verification="$(api_request 'verify collision-fluctuation')"
grep -Fq '9/9 verification groups passed.' <<<"$fluctuation_verification"
grep -Fq '1/1 verifications passed.' <<<"$fluctuation_verification"
printf '  collision-fluctuation verifier through JSON/TCP: PASS\n'

centered_inspect="$(api_request 'collision-centering inspect 1009 --base 10 --lag 2')"
grep -Fq 'T_b,ell(n mod q) = +8  PASS' <<<"$centered_inspect"
grep -Fq 'T^circ = 173/25' <<<"$centered_inspect"
printf '  collision-centering exact inspection through JSON/TCP: PASS\n'

centered_gate="$(api_request 'collision-centering gate --base 10 --lag 2')"
grep -Fq 'centered table is odd under a -> -a' <<<"$centered_gate"
grep -Fq 'Result  PASS' <<<"$centered_gate"
printf '  collision-centering spectral gate through JSON/TCP: PASS\n'

centered_verification="$(api_request 'verify collision-centering')"
grep -Fq '10/10 verification groups passed.' <<<"$centered_verification"
grep -Fq '1/1 verifications passed.' <<<"$centered_verification"
printf '  collision-centering verifier through JSON/TCP: PASS\n'

centered_help="$(api_request 'help collision-centering')"
grep -Fq 'All-lag collision centering' <<<"$centered_help"
grep -Fq 'external analytic inputs' <<<"$centered_help"
if grep -Fq 'The Centered Collision Sum' <<<"$centered_help" ||
   grep -Fq '10.5281/zenodo' <<<"$centered_help"; then
    printf 'collision-centering help is tied to a work title or DOI\n' >&2
    exit 1
fi
printf '  object-first collision-centering help through JSON/TCP: PASS\n'

periodic_inspect="$(api_request 'collision-table inspect 9 --base 10')"
grep -Fq 'fingerprint class n mod b^2 = 9' <<<"$periodic_inspect"
grep -Fq 'table fingerprint T_b(9) = +8  PASS' <<<"$periodic_inspect"
printf '  collision periodic-table inspection through JSON/TCP: PASS\n'

periodic_summary="$(api_request 'collision-table summary --base 10')"
grep -Fq 'positive/zero/negative = 8/12/20' <<<"$periodic_summary"
grep -Fq 'exactly half the cells are negative  PASS' <<<"$periodic_summary"
printf '  collision periodic-table summary through JSON/TCP: PASS\n'

periodic_verification="$(api_request 'verify collision-table')"
grep -Fq '9/9 verification groups passed.' <<<"$periodic_verification"
grep -Fq '1/1 verifications passed.' <<<"$periodic_verification"
printf '  collision periodic-table verifier through JSON/TCP: PASS\n'

periodic_help="$(api_request 'help collision-table')"
grep -Fq 'Lag-one collision table' <<<"$periodic_help"
if grep -Fq 'The Collision Periodic Table' <<<"$periodic_help" ||
   grep -Fq '10.5281/zenodo' <<<"$periodic_help"; then
    printf 'collision-table help is tied to a work title or DOI\n' >&2
    exit 1
fi
printf '  object-first collision-table help through JSON/TCP: PASS\n'

transform_gate="$(api_request 'collision-transform gate --base 10 --lag 2')"
grep -Fq 'centered signal satisfies f(-a)=-f(a)' <<<"$transform_gate"
grep -Fq 'Result  PASS' <<<"$transform_gate"
printf '  collision-transform finite gate through JSON/TCP: PASS\n'

transform_spectrum="$(api_request 'collision-transform spectrum --base 10 --lag 1')"
grep -Fq 'character factors C2 C20' <<<"$transform_spectrum"
grep -Fq 'resolved active coefficients = 17' <<<"$transform_spectrum"
grep -Fq 'inverse reconstruction error' <<<"$transform_spectrum"
grep -Fq 'Result  PASS' <<<"$transform_spectrum"
printf '  collision-transform spectrum through JSON/TCP: PASS\n'

transform_verification="$(api_request 'verify collision-transform')"
grep -Fq '13/13 verification groups passed.' <<<"$transform_verification"
grep -Fq '1/1 verifications passed.' <<<"$transform_verification"
printf '  collision-transform verifier through JSON/TCP: PASS\n'

transform_help="$(api_request 'help collision-transform')"
grep -Fq 'Centered collision transform and prime windows' <<<"$transform_help"
if grep -Fq 'The Collision Transform and the Critical Strip' <<<"$transform_help" \
    || grep -Fq '10.5281/zenodo' <<<"$transform_help"; then
    printf 'collision-transform help is tied to a work title or DOI\n' >&2
    exit 1
fi
printf '  object-first collision-transform help through JSON/TCP: PASS\n'

neutrality_channels="$(api_request 'residue-three-neutrality channels --base 10')"
grep -Fq 'true class one centered sum is zero' <<<"$neutrality_channels"
grep -Fq 'true class two centered sum is zero' <<<"$neutrality_channels"
grep -Fq 'Result  PASS' <<<"$neutrality_channels"
printf '  neutrality true channels through JSON/TCP: PASS\n'

neutrality_verification="$(api_request 'verify residue-three-neutrality')"
grep -Fq '8/8 verification groups passed.' <<<"$neutrality_verification"
grep -Fq '1/1 verifications passed.' <<<"$neutrality_verification"
printf '  neutrality verifier through JSON/TCP: PASS\n'

neutrality_help="$(api_request 'help residue-three-neutrality')"
grep -Fq 'Residue-three neutrality' <<<"$neutrality_help"
if grep -Fq 'The Neutrality Theorem' <<<"$neutrality_help" ||
   grep -Fq '10.5281/zenodo' <<<"$neutrality_help"; then
    printf 'residue-three-neutrality help is tied to a work title or DOI\n' >&2
    exit 1
fi
printf '  object-first residue-three-neutrality help through JSON/TCP: PASS\n'

general_coordinate="$(api_request 'compatible-residue-channels inspect 101 7 --base 10')"
grep -Fq 'internal representative class a mod q = 1' <<<"$general_coordinate"
grep -Fq 'true integer class n mod q = 3' <<<"$general_coordinate"
grep -Fq 'a + m*t mod q = 3  PASS' <<<"$general_coordinate"
printf '  compatible residue coordinate through JSON/TCP: PASS\n'

general_channels="$(api_request 'compatible-residue-channels channels 7 --base 10')"
grep -Fq 'Each channel is one complete table copy with raw mean -1/2' <<<"$general_channels"
grep -Fq 'Result  PASS' <<<"$general_channels"
printf '  compatible residue channels through JSON/TCP: PASS\n'

general_snapshot="$(api_request 'compatible-residue-channels snapshot')"
grep -Fq 'All three reference finite tables reproduced to displayed precision.' <<<"$general_snapshot"
grep -Fq 'Result  PASS' <<<"$general_snapshot"
printf '  compatible residue reference snapshot through JSON/TCP: PASS\n'

general_verification="$(api_request 'verify compatible-residue-channels')"
grep -Fq '6/6 verification groups passed.' <<<"$general_verification"
grep -Fq '1/1 verifications passed.' <<<"$general_verification"
printf '  compatible residue verifier through JSON/TCP: PASS\n'

general_help="$(api_request 'help compatible-residue-channels')"
grep -Fq 'Compatible residue channels' <<<"$general_help"
if grep -Fq 'The General Neutrality Theorem' <<<"$general_help" ||
   grep -Fq '10.5281/zenodo' <<<"$general_help" ||
   grep -Fq 'general-neutrality' <<<"$general_help"; then
    printf 'compatible-residue-channels help is tied to a work title, DOI, or alias\n' >&2
    exit 1
fi
printf '  object-first compatible residue help through JSON/TCP: PASS\n'

centered_table="$(api_request 'centered-collision-table inspect 3 1 5')"
grep -Fq 'centered table f_b,ell(a) = -2/3' <<<"$centered_table"
grep -Fq 'Result  PASS' <<<"$centered_table"
printf '  centered collision table through JSON/TCP: PASS\n'

centered_verification="$(api_request 'verify centered-collision-table')"
grep -Fq '2/2 verification groups passed.' <<<"$centered_verification"
grep -Fq '1/1 verifications passed.' <<<"$centered_verification"
printf '  centered collision table verifier through JSON/TCP: PASS\n'

pairing="$(api_request 'finite-character-pairing one 3 2 --cutoff 10000')"
grep -Fq 'character decomposition = +1.164682321142' <<<"$pairing"
grep -Fq 'finite numerical evidence' <<<"$pairing"
printf '  finite character pairing through JSON/TCP: PASS\n'

pairing_verification="$(api_request 'verify finite-character-pairing')"
grep -Fq '4/4 verification groups passed.' <<<"$pairing_verification"
grep -Fq '1/1 verifications passed.' <<<"$pairing_verification"
printf '  finite character pairing verifier through JSON/TCP: PASS\n'

orthogonality="$(api_request 'coprime-base-orthogonality audit')"
grep -Fq '45 pairwise normalized inner products' <<<"$orthogonality"
grep -Fq 'nonzero cross terms = 0' <<<"$orthogonality"
grep -Fq 'exact weighted Pythagorean identity  PASS' <<<"$orthogonality"
printf '  coprime-base orthogonality through JSON/TCP: PASS\n'

orthogonality_pair="$(api_request 'coprime-base-orthogonality pair 3 2 5 3')"
grep -Fq 'normalized cross-term numerator = 0  EXACT ZERO' <<<"$orthogonality_pair"
grep -Fq 'Result  PASS' <<<"$orthogonality_pair"
printf '  parameterized coprime pair through JSON/TCP: PASS\n'

common_quotient="$(api_request 'coprime-base-orthogonality common-quotient 6 1 15 1')"
grep -Fq 'complete-lcm cross numerator = 5040' <<<"$common_quotient"
grep -Fq 'conditional-mean cross numerator = 5040' <<<"$common_quotient"
grep -Fq 'common-quotient inner product  PASS' <<<"$common_quotient"
printf '  common-quotient cross term through JSON/TCP: PASS\n'

orthogonality_verification="$(api_request 'verify coprime-base-orthogonality')"
grep -Fq '5/5 verification groups passed.' <<<"$orthogonality_verification"
grep -Fq '1/1 verifications passed.' <<<"$orthogonality_verification"
printf '  coprime-base orthogonality verifier through JSON/TCP: PASS\n'

prime_window="$(api_request 'natural-prime-sum-window common-tail --lower 997 --cutoff 2000000')"
grep -Fq 'positive bases=3; negative bases=7' <<<"$prime_window"
grep -Fq 'Result  PASS' <<<"$prime_window"
printf '  natural prime-sum window through JSON/TCP: PASS\n'

prime_window_verification="$(api_request 'verify natural-prime-sum-window')"
grep -Fq '3/3 verification groups passed.' <<<"$prime_window_verification"
grep -Fq '1/1 verifications passed.' <<<"$prime_window_verification"
printf '  natural prime-sum window verifier through JSON/TCP: PASS\n'

primitive_sector="$(api_request 'primitive-odd-sector inspect 13 --cutoff 2000000')"
grep -Fq 'primitive odd characters=72; induced odd characters=6' <<<"$primitive_sector"
grep -Fq 'sector-factorization error' <<<"$primitive_sector"
printf '  primitive odd sector through JSON/TCP: PASS\n'

primitive_sector_verification="$(api_request 'verify primitive-odd-sector')"
grep -Fq '5/5 verification groups passed.' <<<"$primitive_sector_verification"
grep -Fq '1/1 verifications passed.' <<<"$primitive_sector_verification"
printf '  primitive odd sector verifier through JSON/TCP: PASS\n'

relabeling="$(api_request 'conjugate-pair-relabeling exact-law')"
grep -Fq 'exact second-moment numerator identity  PASS' <<<"$relabeling"
grep -Fq 'Result  PASS' <<<"$relabeling"
printf '  conjugate-pair relabeling through JSON/TCP: PASS\n'

relabeling_verification="$(api_request 'verify conjugate-pair-relabeling')"
grep -Fq '3/3 verification groups passed.' <<<"$relabeling_verification"
grep -Fq '1/1 verifications passed.' <<<"$relabeling_verification"
printf '  conjugate-pair relabeling verifier through JSON/TCP: PASS\n'

reflection_well="$(api_request 'additive-reflection-well inspect 10')"
grep -Fq 'K(0) numerator = -26600' <<<"$reflection_well"
grep -Fq 'Fourier square identity and nonpositivity    PASS' <<<"$reflection_well"
printf '  additive reflection well through JSON/TCP: PASS\n'

reflection_well_verification="$(api_request 'verify additive-reflection-well')"
grep -Fq '4/4 verification groups passed.' <<<"$reflection_well_verification"
grep -Fq '1/1 verifications passed.' <<<"$reflection_well_verification"
printf '  additive reflection well verifier through JSON/TCP: PASS\n'

reflected_pairs="$(api_request 'reflected-prime-pair-sign sweep 10 --max-even 100000')"
grep -Fq 'ordered prime pairs=1268016' <<<"$reflected_pairs"
grep -Fq 'positive weighted terms=0  PASS' <<<"$reflected_pairs"
printf '  reflected prime-pair sign through JSON/TCP: PASS\n'

reflected_pair_verification="$(api_request 'verify reflected-prime-pair-sign')"
grep -Fq '4/4 verification groups passed.' <<<"$reflected_pair_verification"
grep -Fq '1/1 verifications passed.' <<<"$reflected_pair_verification"
printf '  reflected prime-pair sign verifier through JSON/TCP: PASS\n'

factorization="$(api_request 'collision-spectrum-factorization inspect 5 1')"
grep -Fq 'primitive fiber-sum magnitude' <<<"$factorization"
grep -Fq 'diagonal reduction error' <<<"$factorization"
grep -Fq 'factorization error' <<<"$factorization"
printf '  collision-spectrum factorization through JSON/TCP: PASS\n'

bernoulli_transform="$(api_request 'collision-spectrum-factorization transform 73 1 74')"
grep -Fq 'fractional-part transform error' <<<"$bernoulli_transform"
grep -Fq 'floor transform error' <<<"$bernoulli_transform"
grep -Fq 'Result  PASS' <<<"$bernoulli_transform"
printf '  Bernoulli floor transform through JSON/TCP: PASS\n'

factorization_verification="$(api_request 'verify collision-spectrum-factorization')"
grep -Fq '6/6 verification groups passed.' <<<"$factorization_verification"
grep -Fq '1/1 verifications passed.' <<<"$factorization_verification"
printf '  collision-spectrum factorization verifier through JSON/TCP: PASS\n'

special_moment="$(api_request 'special-value-moment ledger')"
grep -Fq 'Every weighted L(1) moment equals the collision-energy side  PASS' <<<"$special_moment"
grep -Fq 'Result  PASS' <<<"$special_moment"
printf '  special-value moment through JSON/TCP: PASS\n'

special_moment_verification="$(api_request 'verify special-value-moment')"
grep -Fq '4/4 verification groups passed.' <<<"$special_moment_verification"
grep -Fq '1/1 verifications passed.' <<<"$special_moment_verification"
printf '  special-value moment verifier through JSON/TCP: PASS\n'

cyclotomic="$(api_request 'base-five-cyclotomic-identity audit')"
grep -Fq '0 mismatches  PASS' <<<"$cyclotomic"
grep -Fq 'sum |S_G|^4 = 4800  PASS' <<<"$cyclotomic"
printf '  base-five cyclotomic identity through JSON/TCP: PASS\n'

cyclotomic_verification="$(api_request 'verify base-five-cyclotomic-identity')"
grep -Fq '6/6 verification groups passed.' <<<"$cyclotomic_verification"
grep -Fq '1/1 verifications passed.' <<<"$cyclotomic_verification"
printf '  base-five cyclotomic identity verifier through JSON/TCP: PASS\n'

short_sum_correlation="$(api_request 'short-sum-bernoulli-correlation ledger')"
grep -Fq 'All 18 declared finite correlations  PASS' <<<"$short_sum_correlation"
grep -Fq 'Checked characters=14372' <<<"$short_sum_correlation"
printf '  short-sum Bernoulli correlation through JSON/TCP: PASS\n'

short_sum_correlation_verification="$(api_request 'verify short-sum-bernoulli-correlation')"
grep -Fq '3/3 verification groups passed.' <<<"$short_sum_correlation_verification"
grep -Fq '1/1 verifications passed.' <<<"$short_sum_correlation_verification"
printf '  short-sum Bernoulli correlation verifier through JSON/TCP: PASS\n'

remainder_state="$(api_request 'weighted-remainder-state inspect 6 6')"
grep -Fq 'completed deficit      1.700000000000000' <<<"$remainder_state"
grep -Fq 'continuous capacity    4.300000000000000' <<<"$remainder_state"
printf '  weighted remainder state through JSON/TCP: PASS\n'

remainder_boundary="$(api_request 'weighted-remainder-state boundary 6')"
grep -Fq 'capacity 43/10' <<<"$remainder_boundary"
grep -Fq 'deficit 17/10' <<<"$remainder_boundary"
grep -Fq '0/1 6' <<<"$remainder_boundary"
remainder_ramp="$(api_request 'weighted-remainder-state ramp 6 4')"
grep -Fq 'integral 1/72' <<<"$remainder_ramp"

remainder_floor="$(api_request 'weighted-remainder-state floor 5 1')"
grep -Fq 'floor_response 4/5' <<<"$remainder_floor"
remainder_straighten="$(api_request 'weighted-remainder-state straighten 5 -1')"
grep -Fq 'floor_response 16/5' <<<"$remainder_straighten"
grep -Fq 'midpoint_response 16/5' <<<"$remainder_straighten"
grep -Fq 'difference 0' <<<"$remainder_straighten"
printf '  exact floor lists and signed midpoint straightening through JSON/TCP: PASS\n'
remainder_clock="$(api_request 'weighted-remainder-state clock 2 -1')"
grep -Fq 'centered_age 1/12' <<<"$remainder_clock"
grep -Fq 'omitted_mass 3/4' <<<"$remainder_clock"
remainder_cycle="$(api_request 'weighted-remainder-state cycle 3 2 -1 6')"
grep -Fq 'next_residue 0' <<<"$remainder_cycle"
grep -Fq 'cesaro_mass 1/21' <<<"$remainder_cycle"
remainder_tv="$(api_request 'weighted-remainder-state cycle-tv 2 0')"
grep -Fq 'tv_lower 1/8' <<<"$remainder_tv"
grep -Fq 'tv_upper 7/8' <<<"$remainder_tv"
remainder_covariance="$(api_request 'weighted-remainder-state covariance 6 4')"
grep -Fq 'covariance 1/4' <<<"$remainder_covariance"
remainder_age_budget="$(api_request 'weighted-remainder-state age-budget 3')"
grep -Fq 'harmonic_cross_sum 1' <<<"$remainder_age_budget"
grep -Fq 'first_moment_mobius 1' <<<"$remainder_age_budget"
printf '  exact clocks, cycle probabilities, total variation and covariance through JSON/TCP: PASS\n'
remainder_weights="$(api_request 'weighted-remainder-state finite-weights 6 2:1/2 3:1/2')"
grep -Fq 'admissible_probability_mass 1' <<<"$remainder_weights"
grep -Fq 'unit_energy 6' <<<"$remainder_weights"
grep -Fq 'gram_variance 11/108' <<<"$remainder_weights"
remainder_perturbation="$(api_request 'weighted-remainder-state perturbation 4 6 1/48')"
grep -Fq 'centered_age_change 1/36' <<<"$remainder_perturbation"
grep -Fq 'stationary_age_change 0' <<<"$remainder_perturbation"
grep -Fq 'perturbation_norm_sq 56/27' <<<"$remainder_perturbation"
printf '  exact finite weights and period-twelve perturbations through JSON/TCP: PASS\n'
remainder_variance="$(api_request 'weighted-remainder-state variance 2')"
grep -Fq 'finite_variance 1/144' <<<"$remainder_variance"
grep -Fq 'potential_error_squared_upper 1152' <<<"$remainder_variance"
grep -Fq 'cross_upper 3' <<<"$remainder_variance"
grep -Fq 'full_variance_upper 166753/144' <<<"$remainder_variance"
printf '  proved rational variance enclosure through JSON/TCP: PASS\n'
remainder_rows="$(api_request 'weighted-remainder-state rows 6 -1')"
grep -Fq 'primitive_norm_squared=2' <<<"$remainder_rows"
grep -Fq 'row 5 1 3/2 1 1' <<<"$remainder_rows"
remainder_inverse="$(api_request 'weighted-remainder-state mass-inverse 6 2 2:3/4 3:1/4 6:1/4')"
grep -Fq 'recovered_mass=1/2' <<<"$remainder_inverse"
remainder_recovery="$(api_request 'weighted-remainder-state mass-recovery 2 2 2')"
grep -Fq 'beta_lower=1/4' <<<"$remainder_recovery"
grep -Fq 'inverse_tail_error=7' <<<"$remainder_recovery"
grep -Fq 'mass_upper=8' <<<"$remainder_recovery"
printf '  exact primitive rows and finite/full mass recovery through JSON/TCP: PASS\n'
remainder_increment="$(api_request 'weighted-remainder-state increment-covariance 2 1')"
grep -Fq 'finite_arithmetic=-1/36' <<<"$remainder_increment"
grep -Fq 'finite_ramanujan=-1/36' <<<"$remainder_increment"
grep -Fq 'cross_upper=23/2' <<<"$remainder_increment"
grep -Fq 'covariance_error=4631' <<<"$remainder_increment"
remainder_recurrence="$(api_request 'weighted-remainder-state increment-recurrence 12')"
grep -Fq 'cutoff_period=27720' <<<"$remainder_recurrence"
grep -Fq 'finite_return_equals_zero=1' <<<"$remainder_recurrence"
printf '  exact increment covariance and proved recurrence enclosure through JSON/TCP: PASS\n'
remainder_fourier="$(api_request 'weighted-remainder-state fourier 2 -1 2 finite')"
grep -Fq 'mode=finite' <<<"$remainder_fourier"
grep -Fq 'residue=1' <<<"$remainder_fourier"
grep -Fq 'g_lower=-1/6' <<<"$remainder_fourier"
grep -Fq 'y_real_lower=-1/12' <<<"$remainder_fourier"
grep -Fq 'y_imag_lower=0' <<<"$remainder_fourier"
grep -Fq 'y_mass_lower=1/144' <<<"$remainder_fourier"
remainder_full_fourier="$(api_request 'weighted-remainder-state fourier 2 1 2 full')"
grep -Fq 'mode=full' <<<"$remainder_full_fourier"
grep -Fq 'amplitude_upper=1' <<<"$remainder_full_fourier"
grep -Fq 'g_lower=-2/3' <<<"$remainder_full_fourier"
printf '  rational finite/full primitive Fourier intervals through JSON/TCP: PASS\n'
printf '  exact boundary and ramp through JSON/TCP: PASS\n'

remainder_amplitude="$(api_request 'weighted-remainder-state amplitude 2 2')"
grep -Fq 'lower 1/4' <<<"$remainder_amplitude"
grep -Fq 'upper 1' <<<"$remainder_amplitude"
grep -Fq 'width 3/4' <<<"$remainder_amplitude"
printf '  exact amplitude enclosure through JSON/TCP: PASS\n'

remainder_refinement="$(api_request 'weighted-remainder-state amplitude-refinement 2 2 1 1')"
grep -Fq 'delta=7/8' <<<"$remainder_refinement"
grep -Fq 'jordan_three=7' <<<"$remainder_refinement"
grep -Fq 'seed_prefix=1/4' <<<"$remainder_refinement"
grep -Fq 'refinement_lower=5/42' <<<"$remainder_refinement"
grep -Fq 'refinement_upper=11/7' <<<"$remainder_refinement"
grep -Fq 'mobius_lower=-13/32' <<<"$remainder_refinement"
remainder_unit_refinement="$(api_request 'weighted-remainder-state amplitude-refinement 1 2 1 1')"
grep -Fq 'retained_amplitude=1/4' <<<"$remainder_unit_refinement"
grep -Fq 'amplitude_lower=1' <<<"$remainder_unit_refinement"
grep -Fq 'amplitude_upper=1' <<<"$remainder_unit_refinement"
printf '  exact harmonic seed and full amplitude refinement through JSON/TCP: PASS\n'

remainder_constants="$(api_request 'weighted-remainder-state expansion-constants 1')"
grep -Fq 'gamma_lower=1/2' <<<"$remainder_constants"
grep -Fq 'gamma_upper=7/12' <<<"$remainder_constants"
remainder_harmonic_expansion="$(api_request 'weighted-remainder-state harmonic-expansion 1 1')"
grep -Fq 'amplitude_expansion_available=0' <<<"$remainder_harmonic_expansion"
grep -Fq 'harmonic_prefix=0' <<<"$remainder_harmonic_expansion"
remainder_uniform_expansion="$(api_request 'weighted-remainder-state amplitude-expansion 8 12')"
grep -Fq 'prime_base=2' <<<"$remainder_uniform_expansion"
grep -Fq 'prime_exponent=3' <<<"$remainder_uniform_expansion"
grep -Fq 'rho=4/7' <<<"$remainder_uniform_expansion"
remainder_dirichlet="$(api_request 'weighted-remainder-state deficit-series 2 6')"
grep -Fq 'prefix_lower=1/36' <<<"$remainder_dirichlet"
grep -Fq 'prefix_upper=1/36' <<<"$remainder_dirichlet"
remainder_deficit_diagnostic="$(api_request 'weighted-remainder-state deficit-diagnostic 1')"
grep -Fq 'literal_loss_bound=3979/8000' <<<"$remainder_deficit_diagnostic"
grep -Fq 'literal_margin=4021/8000' <<<"$remainder_deficit_diagnostic"
printf '  rational expansion constants, prime powers and Dirichlet diagnostics through JSON/TCP: PASS\n'

remainder_spectral_product="$(api_request 'weighted-remainder-state spectral-product 2')"
grep -Fq 'product_upper=61/98' <<<"$remainder_spectral_product"
remainder_spectral_mean="$(api_request 'weighted-remainder-state spectral-mean 5/2 2')"
grep -Fq 'h_sum=61/49' <<<"$remainder_spectral_mean"
grep -Fq 'correction_floor_mean=122/245' <<<"$remainder_spectral_mean"
remainder_spectral_energy="$(api_request 'weighted-remainder-state spectral-energy 2 2')"
grep -Fq 'energy_lower=1/144' <<<"$remainder_spectral_energy"
remainder_spectral_tail="$(api_request 'weighted-remainder-state spectral-tail 4 4 2 1 1')"
grep -Fq 'energy_band_upper=0' <<<"$remainder_spectral_tail"
grep -Fq 'projection_tail_lower=0' <<<"$remainder_spectral_tail"
printf '  spectral product, signed mean, energy and full tail through JSON/TCP: PASS\n'

remainder_character_phase="$(api_request 'weighted-remainder-state character-phase 2 1')"
grep -Fq 'phase_real_lower=-1' <<<"$remainder_character_phase"
grep -Fq 'phase_imag_upper=0' <<<"$remainder_character_phase"
remainder_character_table="$(api_request 'weighted-remainder-state character-table 8')"
grep -Fq 'character_count=4' <<<"$remainder_character_table"
remainder_character_l="$(api_request 'weighted-remainder-state character-l 6 1 1')"
grep -Fq 'character_conductor=3' <<<"$remainder_character_l"
grep -Fq 'l_two_prefix_real_lower=1' <<<"$remainder_character_l"
remainder_mixed_moment="$(api_request 'weighted-remainder-state mixed-moment 2 1 1 2')"
grep -Fq 'odd_count=0' <<<"$remainder_mixed_moment"
grep -Fq 'eta_lower=1/2' <<<"$remainder_mixed_moment"
remainder_cotangent="$(api_request 'weighted-remainder-state cotangent-sums 1 1 1')"
grep -Fq 'unit_lower=0' <<<"$remainder_cotangent"
grep -Fq 'eta_lower=1' <<<"$remainder_cotangent"
remainder_polylog="$(api_request 'weighted-remainder-state harmonic-polylog 3/5 4/5 2')"
grep -Fq 'prefix_real_lower=-7/100' <<<"$remainder_polylog"
grep -Fq 'prefix_imag_upper=6/25' <<<"$remainder_polylog"
remainder_harmonic_root="$(api_request 'weighted-remainder-state harmonic-root 2 1 2 2')"
grep -Fq 'harmonic_prefix_real_lower=1/4' <<<"$remainder_harmonic_root"
grep -Fq 'cubic_prefix_lower=-7/8' <<<"$remainder_harmonic_root"
remainder_root_average="$(api_request 'weighted-remainder-state harmonic-root-average 2 2')"
grep -Fq 'selected_prefix=1/4' <<<"$remainder_root_average"
remainder_sine_transform="$(api_request 'weighted-remainder-state sine-transform 3 -6')"
grep -Fq 'frequency=-6' <<<"$remainder_sine_transform"
grep -Fq 'cotangent_rhs_upper=0' <<<"$remainder_sine_transform"
remainder_small_amplitudes="$(api_request 'weighted-remainder-state small-amplitudes 1 1')"
grep -Fq 'induced_factor=5/4' <<<"$remainder_small_amplitudes"
grep -Fq 'induced_prefix_rhs=1' <<<"$remainder_small_amplitudes"
printf '  character, mixed-moment, cotangent, harmonic-root and small-conductor readouts through JSON/TCP: PASS\n'

primitive_tree="$(api_request 'weighted-remainder-state tree 1')"
grep -Fq 'primitive_pair_mass 1/2' <<<"$primitive_tree"
grep -Fq 'outgoing_mass 3/2' <<<"$primitive_tree"
grep -Fq 'harmonic_upper_bound 4' <<<"$primitive_tree"
grep -Fq 'primitive_address_mass 1/4' <<<"$primitive_tree"
primitive_node="$(api_request 'weighted-remainder-state tree-node 2 3')"
grep -Fq 'potential 5/36' <<<"$primitive_node"
grep -Fq 'loss 1/30' <<<"$primitive_node"
grep -Fq 'address_mass 1/50' <<<"$primitive_node"
primitive_weight="$(api_request 'weighted-remainder-state weight 2')"
grep -Fq 'weight 1/4' <<<"$primitive_weight"
grep -Fq 'budget_inverse 1/4' <<<"$primitive_weight"
primitive_budget="$(api_request 'weighted-remainder-state budget 2')"
grep -Fq 'budget 2' <<<"$primitive_budget"
primitive_mass="$(api_request 'weighted-remainder-state mass 2')"
grep -Fq 'retained_mass 1/4' <<<"$primitive_mass"
grep -Fq 'omitted_mass 3/4' <<<"$primitive_mass"
grep -Fq 'weighted_mass 1/2' <<<"$primitive_mass"
grep -Fq 'deficit_upper_bound 4/3' <<<"$primitive_mass"
printf '  exact primitive tree, weights, budget and mass through JSON/TCP: PASS\n'

sawtooth_row="$(api_request 'weighted-remainder-state sawtooth 5 2 1')"
grep -Fq 'value -1/10' <<<"$sawtooth_row"
sawtooth_dedekind="$(api_request 'weighted-remainder-state dedekind 5 1')"
grep -Fq 'dedekind_sum 1/5' <<<"$sawtooth_dedekind"
sawtooth_gram="$(api_request 'weighted-remainder-state gram 6 1 9 1')"
grep -Fq 'haar_pairing 1/324' <<<"$sawtooth_gram"
sawtooth_mean="$(api_request 'weighted-remainder-state sawtooth-mean 6 1 3 1')"
grep -Fq 'conditional_mean -1/12' <<<"$sawtooth_mean"
printf '  exact sawtooth, Dedekind, Haar pairing and conditional mean through JSON/TCP: PASS\n'

remainder_pairing="$(api_request 'weighted-remainder-state pairing 6 2 0 2')"
grep -Fq 'finite average 7/135' <<<"$remainder_pairing"
grep -Fq 'Haar lower -1/3' <<<"$remainder_pairing"
grep -Fq 'Haar upper 2/3' <<<"$remainder_pairing"
printf '  exact boundary pairing through JSON/TCP: PASS\n'

remainder_crt="$(api_request 'weighted-remainder-state crt 4:0 6:2')"
grep -Fq 'haar_probability=1/12' <<<"$remainder_crt"
grep -Fq 'residue=4' <<<"$remainder_crt"
remainder_moment="$(api_request 'weighted-remainder-state moment 6 g 0:1 1:2')"
grep -Fq 'finite_moment=41519/2187000' <<<"$remainder_moment"
remainder_haar_moment="$(api_request 'weighted-remainder-state haar-moment 4 0 1')"
grep -Fq 'finite_haar_reset_moment=1/9' <<<"$remainder_haar_moment"
remainder_block="$(api_request 'weighted-remainder-state block 6 4')"
grep -Fq 'deficit_difference=1979/3780' <<<"$remainder_block"
remainder_forcing="$(api_request 'weighted-remainder-state forcing 6')"
grep -Fq 'full_reset_forcing=6/5' <<<"$remainder_forcing"
printf '  exact joint CRT, moments and blocks through JSON/TCP: PASS\n'

remainder_cylinder="$(api_request 'weighted-remainder-state cylinder 2 -1 2')"
grep -Fq 'finite_mean=1/12' <<<"$remainder_cylinder"
grep -Fq 'mean_radius=1/4' <<<"$remainder_cylinder"
remainder_position="$(api_request 'weighted-remainder-state position 2 1 2 1/2')"
grep -Fq 'exceedance_lower=1/4' <<<"$remainder_position"
remainder_weight="$(api_request 'weighted-remainder-state position-weight 2 1 2 2')"
grep -Fq 'probability_upper=1' <<<"$remainder_weight"
printf '  exact cylinder and position intervals through JSON/TCP: PASS\n'

remainder_verification="$(api_request 'verify weighted-remainder-state')"
grep -Fq '10/10 verification groups passed.' <<<"$remainder_verification"
grep -Fq '1/1 verifications passed.' <<<"$remainder_verification"
printf '  weighted remainder verifier through JSON/TCP: PASS\n'

fiber_cancellation="$(api_request 'primitive-character-cancellation inspect 5 1 1')"
grep -Fq 'conductor witnesses and exact fiber sizes  PASS' <<<"$fiber_cancellation"
grep -Fq 'Result  PASS' <<<"$fiber_cancellation"
printf '  primitive-character cancellation through JSON/TCP: PASS\n'

fiber_cancellation_verification="$(api_request 'verify primitive-character-cancellation')"
grep -Fq '3/3 verification groups passed.' <<<"$fiber_cancellation_verification"
grep -Fq '1/1 verifications passed.' <<<"$fiber_cancellation_verification"
printf '  primitive-character cancellation verifier through JSON/TCP: PASS\n'

zeta_factorization="$(api_request 'periodic-zeta-factorization inspect 5 1 1 --sigma 0.5 --tau 0.2')"
grep -Fq 'transform relative error' <<<"$zeta_factorization"
grep -Fq 'Result  PASS' <<<"$zeta_factorization"
printf '  periodic-zeta factorization through JSON/TCP: PASS\n'

zeta_factorization_verification="$(api_request 'verify periodic-zeta-factorization')"
grep -Fq '5/5 verification groups passed.' <<<"$zeta_factorization_verification"
grep -Fq '1/1 verifications passed.' <<<"$zeta_factorization_verification"
printf '  periodic-zeta factorization verifier through JSON/TCP: PASS\n'

boundary_recovery="$(api_request 'collision-boundary-recovery inspect 5 1 1')"
grep -Fq 'exact-recovery numerical error' <<<"$boundary_recovery"
grep -Fq 'Result  PASS' <<<"$boundary_recovery"
printf '  collision-boundary recovery through JSON/TCP: PASS\n'

boundary_recovery_verification="$(api_request 'verify collision-boundary-recovery')"
grep -Fq '4/4 verification groups passed.' <<<"$boundary_recovery_verification"
grep -Fq '1/1 verifications passed.' <<<"$boundary_recovery_verification"
printf '  collision-boundary recovery verifier through JSON/TCP: PASS\n'

active_channel="$(api_request 'active-collision-channel inspect 5 1 1')"
grep -Fq 'classification = active' <<<"$active_channel"
grep -Fq 'not search for, certify, or locate' <<<"$active_channel"
printf '  active collision channel through JSON/TCP: PASS\n'

active_channel_verification="$(api_request 'verify active-collision-channel')"
grep -Fq '4/4 verification groups passed.' <<<"$active_channel_verification"
grep -Fq '1/1 verifications passed.' <<<"$active_channel_verification"
printf '  active collision channel verifier through JSON/TCP: PASS\n'

collision_conjugation="$(api_request 'collision-coordinate conjugation 21 8 --base 10')"
grep -Fq 'collision equivalence holds point by point' <<<"$collision_conjugation"
grep -Fq 'Result  PASS' <<<"$collision_conjugation"
printf '  composite-modulus base conjugation through JSON/TCP: PASS\n'

collision_coordinate="$(api_request 'collision-coordinate inspect 13 6 --base 10')"
grep -Fq 'coordinate formula 2*#wraps=2  PASS' <<<"$collision_coordinate"
grep -Fq 'Result  PASS' <<<"$collision_coordinate"
printf '  collision coordinate through JSON/TCP: PASS\n'

collision_coordinate_verification="$(api_request 'verify collision-coordinate')"
grep -Fq '6/6 verification groups passed.' <<<"$collision_coordinate_verification"
grep -Fq '1/1 verifications passed.' <<<"$collision_coordinate_verification"
printf '  collision-coordinate verifier through JSON/TCP: PASS\n'

finite_determination="$(api_request 'finite-determination inspect 191 --base 10 --lag 1')"
grep -Fq 'exact finite-table value S_l([N]_m)=-9  PASS' <<<"$finite_determination"
grep -Fq 'Result  PASS' <<<"$finite_determination"
printf '  finite determination through JSON/TCP: PASS\n'

finite_determination_verification="$(api_request 'verify finite-determination')"
grep -Fq '8/8 verification groups passed.' <<<"$finite_determination_verification"
grep -Fq '1/1 verifications passed.' <<<"$finite_determination_verification"
printf '  finite-determination verifier through JSON/TCP: PASS\n'

reflection_identity="$(api_request 'reflection-identity inspect 9 --base 10 --lag 1')"
grep -Fq 'reflected pair sum=-1; expected -1  PASS' <<<"$reflection_identity"
grep -Fq 'Result  PASS' <<<"$reflection_identity"
printf '  reflection identity through JSON/TCP: PASS\n'

reflection_identity_verification="$(api_request 'verify reflection-identity')"
grep -Fq '4/4 verification groups passed.' <<<"$reflection_identity_verification"
grep -Fq '1/1 verifications passed.' <<<"$reflection_identity_verification"
printf '  reflection-identity verifier through JSON/TCP: PASS\n'

half_group="$(api_request 'half-group inspect 10 3')"
grep -Fq '|W_n|=2; phi(m)/2=2' <<<"$half_group"
grep -Fq 'Result  PASS' <<<"$half_group"
printf '  half-group theorem through JSON/TCP: PASS\n'

half_group_verification="$(api_request 'verify half-group')"
grep -Fq '4/4 verification groups passed.' <<<"$half_group_verification"
grep -Fq '1/1 verifications passed.' <<<"$half_group_verification"
printf '  half-group verifier through JSON/TCP: PASS\n'

all_prime_label="$(api_request 'all-prime-collision-label inspect 13 --base 10 --lag 1')"
grep -Fq 'finite-table residue=13 label=-1  PASS' <<<"$all_prime_label"
grep -Fq 'Result  PASS' <<<"$all_prime_label"
printf '  all-prime collision label through JSON/TCP: PASS\n'

all_prime_label_verification="$(api_request 'verify all-prime-collision-label')"
grep -Fq '3/3 verification groups passed.' <<<"$all_prime_label_verification"
grep -Fq '1/1 verifications passed.' <<<"$all_prime_label_verification"
printf '  all-prime collision-label verifier through JSON/TCP: PASS\n'

spectral_quotient="$(api_request 'finite-spectral-quotient inspect 10 --lag 1 --prime-count 40 --tau 1')"
grep -Fq 'observed label states q=11; exact bulk multiplicity N-q=29' <<<"$spectral_quotient"
grep -Fq 'Result  PASS' <<<"$spectral_quotient"
printf '  finite spectral quotient through JSON/TCP: PASS\n'

spectral_quotient_verification="$(api_request 'verify finite-spectral-quotient')"
grep -Fq '8/8 verification groups passed.' <<<"$spectral_quotient_verification"
grep -Fq '1/1 verifications passed.' <<<"$spectral_quotient_verification"
printf '  finite spectral-quotient verifier through JSON/TCP: PASS\n'

finite_prefix_slice="$(api_request 'finite-prefix-slice inspect 11 --base 3 --depth 2 --support 0,4,8')"
grep -Fq 'centered numerators left=12 right=12  PASS' <<<"$finite_prefix_slice"
grep -Fq 'Result  PASS' <<<"$finite_prefix_slice"
printf '  finite-prefix slice through JSON/TCP: PASS\n'

finite_prefix_slice_verification="$(api_request 'verify finite-prefix-slice')"
grep -Fq '7/7 verification groups passed.' <<<"$finite_prefix_slice_verification"
grep -Fq '1/1 verifications passed.' <<<"$finite_prefix_slice_verification"
printf '  finite-prefix slice verifier through JSON/TCP: PASS\n'

boundary_bernoulli="$(api_request 'boundary-bernoulli-factorization inspect 3 2 1 --support 0,4,8')"
grep -Fq 'visible boundary endpoints=4; squared norm=4' <<<"$boundary_bernoulli"
grep -Fq 'Result  PASS' <<<"$boundary_bernoulli"
printf '  boundary-Bernoulli factorization through JSON/TCP: PASS\n'

boundary_bernoulli_verification="$(api_request 'verify boundary-bernoulli-factorization')"
grep -Fq '10/10 verification groups passed.' <<<"$boundary_bernoulli_verification"
grep -Fq '1/1 verifications passed.' <<<"$boundary_bernoulli_verification"
printf '  boundary-Bernoulli verifier through JSON/TCP: PASS\n'

boundary_spectrum="$(api_request 'boundary-bernoulli-factorization spectrum 3 2 --support 0,4,8')"
grep -Fq 'odd channels=3; expected=3  PASS' <<<"$boundary_spectrum"
grep -Fq 'Result  PASS' <<<"$boundary_spectrum"
printf '  conductor-depth boundary spectrum through JSON/TCP: PASS\n'

boundary_correlation="$(api_request 'boundary-bernoulli-factorization correlation 3 2 1 2')"
grep -Fq 'Mobius-Dedekind combination=0.203703703703704' <<<"$boundary_correlation"
grep -Fq 'Result  PASS' <<<"$boundary_correlation"
printf '  unit sawtooth correlation through JSON/TCP: PASS\n'

boundary_ledger="$(api_request 'boundary-conductor-ledger inspect 9 --support 0,4,8')"
grep -Fq 'primitive odd moment=24; characters=2; mean=12/1' <<<"$boundary_ledger"
grep -Fq 'exact energies: proper=0; top=24; full=24' <<<"$boundary_ledger"
grep -Fq 'Result  PASS' <<<"$boundary_ledger"
printf '  boundary conductor ledger through JSON/TCP: PASS\n'

boundary_ledger_verification="$(api_request 'verify boundary-conductor-ledger')"
grep -Fq '6/6 verification groups passed.' <<<"$boundary_ledger_verification"
grep -Fq '1/1 verifications passed.' <<<"$boundary_ledger_verification"
printf '  boundary conductor-ledger verifier through JSON/TCP: PASS\n'

finite_state_boundary="$(api_request 'finite-state-orbit-boundary parity 2 7 1')"
grep -Fq 'eventual cycle length=6' <<<"$finite_state_boundary"
grep -Fq 'nonzero dynamical-boundary cells=2; squared norm=2' <<<"$finite_state_boundary"
grep -Fq 'Result  PASS' <<<"$finite_state_boundary"
printf '  finite-state orbit boundary through JSON/TCP: PASS\n'

finite_state_boundary_verification="$(api_request 'verify finite-state-orbit-boundary')"
grep -Fq '5/5 verification groups passed.' <<<"$finite_state_boundary_verification"
grep -Fq '1/1 verifications passed.' <<<"$finite_state_boundary_verification"
printf '  finite-state orbit-boundary verifier through JSON/TCP: PASS\n'

full_orbit_energy="$(api_request 'full-orbit-energy inspect 2 3 2')"
grep -Fq 'exact odd-kernel boundary energy=9' <<<"$full_orbit_energy"
grep -Fq 'exact conductor p=3 energy=9' <<<"$full_orbit_energy"
grep -Fq 'Result  PASS' <<<"$full_orbit_energy"
printf '  full-orbit energy through JSON/TCP: PASS\n'

full_orbit_energy_verification="$(api_request 'verify full-orbit-energy')"
grep -Fq '6/6 verification groups passed.' <<<"$full_orbit_energy_verification"
grep -Fq '1/1 verifications passed.' <<<"$full_orbit_energy_verification"
printf '  full-orbit energy verifier through JSON/TCP: PASS\n'

quadratic_orbit_energy="$(api_request 'quadratic-orbit-energy inspect 7')"
grep -Fq 'exact off-resonance energy=2' <<<"$quadratic_orbit_energy"
grep -Fq 'Result  PASS' <<<"$quadratic_orbit_energy"
printf '  quadratic-orbit energy through JSON/TCP: PASS\n'

quadratic_orbit_energy_verification="$(api_request 'verify quadratic-orbit-energy')"
grep -Fq '4/4 verification groups passed.' <<<"$quadratic_orbit_energy_verification"
grep -Fq '1/1 verifications passed.' <<<"$quadratic_orbit_energy_verification"
printf '  quadratic-orbit energy verifier through JSON/TCP: PASS\n'

subgroup_jacobi="$(api_request 'subgroup-jacobi-expansion inspect 7 2 1')"
grep -Fq 'subgroup order=3; index=2' <<<"$subgroup_jacobi"
grep -Fq 'Result  PASS' <<<"$subgroup_jacobi"
printf '  subgroup Jacobi expansion through JSON/TCP: PASS\n'

subgroup_jacobi_verification="$(api_request 'verify subgroup-jacobi-expansion')"
grep -Fq '5/5 verification groups passed.' <<<"$subgroup_jacobi_verification"
grep -Fq '1/1 verifications passed.' <<<"$subgroup_jacobi_verification"
printf '  subgroup Jacobi-expansion verifier through JSON/TCP: PASS\n'

prime_base_energy="$(api_request 'prime-base-collision-energy inspect 5')"
grep -Fq 'exact centered energy E_b=48' <<<"$prime_base_energy"
grep -Fq '12*b^2*E_b from ratio/Dedekind sum=14400  PASS' <<<"$prime_base_energy"
grep -Fq 'Result  PASS' <<<"$prime_base_energy"
printf '  prime-base collision energy through JSON/TCP: PASS\n'

prime_base_energy_verification="$(api_request 'verify prime-base-collision-energy')"
grep -Fq '7/7 verification groups passed.' <<<"$prime_base_energy_verification"
grep -Fq '1/1 verifications passed.' <<<"$prime_base_energy_verification"
printf '  prime-base collision-energy verifier through JSON/TCP: PASS\n'

boundary_defect="$(api_request 'arithmetic-boundary-defect inspect 5')"
grep -Fq 'proved secondary coefficient -1/pi^2' <<<"$boundary_defect"
grep -Fq 'PASS (exact finite extraction)' <<<"$boundary_defect"
printf '  arithmetic boundary defect through JSON/TCP: PASS\n'

boundary_defect_verification="$(api_request 'verify arithmetic-boundary-defect')"
grep -Fq '4/4 verification groups passed.' <<<"$boundary_defect_verification"
grep -Fq '1/1 verifications passed.' <<<"$boundary_defect_verification"
printf '  arithmetic boundary-defect verifier through JSON/TCP: PASS\n'

completed_carrier="$(api_request 'carry-completed-carrier inspect 30 7 2')"
grep -Fq 'completed cycle size M=2N(p-1)=360' <<<"$completed_carrier"
grep -Fq 'quotient sizes M -> 60 -> 30' <<<"$completed_carrier"
grep -Fq 'Result  PASS' <<<"$completed_carrier"
printf '  carry-completed carrier through JSON/TCP: PASS\n'

carrier_seam="$(api_request 'carry-completed-carrier seam 30')"
grep -Fq 'retained energy=421/450' <<<"$carrier_seam"
grep -Fq 'one-origin transverse energy=29/450' <<<"$carrier_seam"
grep -Fq 'Result  PASS' <<<"$carrier_seam"
printf '  carry seam energy through JSON/TCP: PASS\n'

carrier_product="$(api_request 'carry-completed-carrier product 10 3 -3 1')"
grep -Fq 'roots of x^2-3x+1 in the formed spectrum=4' <<<"$carrier_product"
grep -Fq 'frequency map is bijective       PASS' <<<"$carrier_product"
grep -Fq 'Result  PASS' <<<"$carrier_product"
printf '  coherent carrier product Gram through JSON/TCP: PASS\n'

completed_carrier_verification="$(api_request 'verify carry-completed-carrier')"
grep -Fq '6/6 verification groups passed.' <<<"$completed_carrier_verification"
grep -Fq '1/1 verifications passed.' <<<"$completed_carrier_verification"
printf '  carry-completed carrier verifier through JSON/TCP: PASS\n'

terminal_ledger="$(api_request 'terminal-collision-conductor-ledger audit')"
grep -Fq 'PASS p=3 N=2 m=9' <<<"$terminal_ledger"
grep -Fq 'conductors=(15,45,75,225) differences=(0,32,32,32) moment=896 characters=32 mean=28' <<<"$terminal_ledger"
printf '  terminal collision conductor ledger through JSON/TCP: PASS\n'

terminal_ledger_verification="$(api_request 'verify terminal-collision-conductor-ledger')"
grep -Fq '3/3 verification groups passed.' <<<"$terminal_ledger_verification"
grep -Fq '1/1 verifications passed.' <<<"$terminal_ledger_verification"
printf '  terminal collision conductor ledger verifier through JSON/TCP: PASS\n'

oriented_comparison="$(api_request 'oriented-digit-comparison inspect 10 20')"
grep -Fq 'direct ceiling response=8' <<<"$oriented_comparison"
grep -Fq 'proper nonunit: active' <<<"$oriented_comparison"
grep -Fq 'Result  PASS' <<<"$oriented_comparison"
printf '  oriented two-digit comparison through JSON/TCP: PASS\n'

oriented_comparison_verification="$(api_request 'verify oriented-digit-comparison')"
grep -Fq '7/7 verification groups passed.' <<<"$oriented_comparison_verification"
grep -Fq '1/1 verifications passed.' <<<"$oriented_comparison_verification"
printf '  oriented two-digit comparison verifier through JSON/TCP: PASS\n'

oriented_trichotomy="$(api_request 'oriented-digit-comparison trichotomy 5 2')"
grep -Fq 'direct ascents=2 equalities=1 descents=6' <<<"$oriented_trichotomy"
grep -Fq 'analysis mass=9 collision=1 orientation=4' <<<"$oriented_trichotomy"
grep -Fq 'Result  PASS' <<<"$oriented_trichotomy"
printf '  oriented comparison trichotomy through JSON/TCP: PASS\n'

printf '\nAll API regression checks passed.\n'
