/-
Author: Alexander S. Petty
-/

import NField.Alignment.SilentPrimesClosure
import NField.Alignment.BinDerangementsClosure
import NField.Papers.BinDerangements

/-!
# Silent Primes and the Variance of the Collision Count

Reader-facing theorem map for the Lean companion to
`papers/silent_primes.tex`.

## Checked here

* The positive silent integer is exactly the manuscript's displayed
  subtraction formula.
* A prime is globally silent at a fixed lag exactly when it divides one of
  the `b-1` silent integers.
* Repetend silence is represented over the full Fermat window, which repeats
  the multiplicative orbit without changing its zero predicate.
* Every repetend-silent prime satisfies the exact bound
  `p <= b^(ell+1)`.
* At base ten and lag one, the nine silent integers and the complete seven
  globally silent and repetend-silent primes are certified exactly.
* The collision coordinate and its displayed inverse are proved mutually
  inverse on their manuscript domains.
* The intrinsic collision count is exactly twice the positive-comparison
  count and has the displayed signed sawtooth form.
* The pointwise collision profile is exactly `2Q - 2 sum Y_m`.
* Floor crossings are exactly the ceiling-interval events.  The interval
  families are disjoint, have the displayed cardinalities, and their
  intersections equal the complete double-sum overlap ledger.
* The exact constructive mean algebra is inherited from the checked
  gate-width companion, and its two displayed rational forms are proved
  equal.
* Population variance is translation invariant and quadratic under scaling,
  which gives the exact overlap-ledger formula.
* The diagonal expression differs from `2Q/3` by at most ten in every
  admissible finite instance, which proves the stated fixed-base bounded
  remainder.

## Proof boundary

The silent-prime recipe, repetend bound, seven-prime classification,
coordinate formula, interval ledger, exact variance algebra, and diagonal
bounded remainder are checked against intrinsic long-division digits and the
proved zero gate.  The finite table values are executable certificates in
nfield.  The conjectured full variance limit remains a conjecture.  No theorem
below represents that limit as proved.
-/

namespace NField.Papers.SilentPrimes

open scoped BigOperators
open NField.CollisionDefinition
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.SpectralPower
open NField.Alignment.AutocorrelationFormula
open NField.Alignment.BinDerangements
open NField.Alignment.BinDerangementsClosure
open NField.Alignment.SilentPrimes
open NField.Alignment.SilentPrimesClosure

/-- Exact conjugation of interval digit bins to residue classes. -/
theorem digit_bin_conjugation {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (r s : ZMod p) :
    NField.CollisionDefinition.digitBin b p r.val =
        NField.CollisionDefinition.digitBin b p s.val ↔
      ((b : ZMod p) * r).val % b = ((b : ZMod p) * s).val % b :=
  digit_eq_iff_transformed_mod hb hp hbp r s

/-- Exact collision-congruence count after the base permutation. -/
theorem collision_congruence {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) (hg0 : g ≠ 0) :
    collisionCount (primeDigitWord b p hb hp.pos) g =
      transformedCollisionCount b p g :=
  collisionCount_eq_transformedCollisionCount hb hp hbp g hg0

/-- Range, excluded value, and defining identity of the collision coordinate. -/
theorem collision_coordinate_certificate {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    0 < gateParameter b p g ∧ gateParameter b p g < p ∧
      gateParameter b p g ≠ b ∧
      (gateParameter b p g : ZMod p) * (1 - g) = (b : ZMod p) :=
  ⟨gateParameter_pos hb hp hbp hg1, gateParameter_lt g,
    gateParameter_ne_base hb hp hbp hg0 hg1,
    gateParameter_mul_one_sub hp hg1⟩

/-- Exact zero gate. -/
theorem zero_gate {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    collisionCount (primeDigitWord b p hb hp.pos) g = 0 ↔
      gateParameter b p g < b :=
  collisionCount_eq_zero_iff_parameter_lt hb hp hbp hg0 hg1

/-- Exact displayed zero family and its cardinality. -/
theorem zero_family_and_width {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    (∀ g : ZMod p,
      g ∈ derangingFamily b p ↔
        g ≠ 0 ∧ collisionCount
          (primeDigitWord b p (by omega) hp.pos) g = 0) ∧
      (derangingFamily b p).card = b - 1 :=
  ⟨fun g => mem_derangingFamily_iff hb2 hp hbp g,
    derangingFamily_card (by omega) hp hbp⟩

/-- A complete-field derangement is silent on every selected orbit. -/
theorem global_derangement_restricts_to_every_orbit
    {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) (orbit : Finset (ZMod N))
    (g : ZMod N) (hzero : collisionCount word g = 0) :
    restrictedCollisionCount word orbit g = 0 :=
  restrictedCollisionCount_eq_zero_of_collisionCount_eq_zero
    word orbit g hzero

/-- A full nonzero-residue orbit reads the intrinsic collision count exactly. -/
theorem full_orbit_collision_equality
    {G : Type*} [Fintype G] [AddCommGroup G]
    {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) (orbit : G ≃ NonzeroResidue N)
    (lag : G) (a : ZMod N) (hzero : word 0 = none)
    (hmotion : ∀ t, (orbit (t + lag)).val = a * (orbit t).val) :
    fullOrbitAutocorrelation word orbit lag = (collisionCount word a : ℂ) := by
  rw [fullOrbitAutocorrelation_eq_collision word orbit lag a hzero hmotion]
  exact multiplicativeCollision_eq_collisionCount word a

/-- Exact base-eight shorter-orbit boundary. -/
theorem base_eight_short_orbit_boundary :
    let word := primeDigitWord 8 13 (by norm_num) (by norm_num)
    let orbit : Finset (ZMod 13) := {1, 5, 8, 12}
    restrictedCollisionCount word orbit 8 = 0 ∧
      collisionCount word 8 = 2 :=
  baseEight_thirteen_short_orbit_counterexample

/-- Exact factor recipe for globally silent primes. -/
theorem global_silent_prime_recipe {b p ell : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    GloballySilentAt b p ell (by omega) hp ↔
      ∃ u ∈ Finset.Ico 1 b, p ∣ silentInteger b ell u :=
  globallySilentAt_iff_exists_dvd_silentInteger hb2 hp hbp

/-- Exact upper bound for repetend-silent primes. -/
theorem repetend_silent_prime_bound {b p ell : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    (hsilent : RepetendSilentAt b p ell) :
    p ≤ b ^ (ell + 1) :=
  repetendSilentAt_bound hb2 hp hbp hsilent

/-- Explicit global-silence bound, which also gives fixed-lag finiteness. -/
theorem global_silent_prime_bound {b p ell : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hsilent : GloballySilentAt b p ell (by omega) hp) :
    p ≤ b ^ (ell + 1) :=
  globallySilentAt_bound hb2 hp hbp hsilent

/-- First term and constant backward step of the silent-integer progression. -/
theorem silent_integer_progression {b ell u : ℕ}
    (hb : 1 ≤ b) (hu : u + 1 ≤ b) :
    silentInteger b ell 1 = b ^ ell * (b - 1) + 1 ∧
      silentInteger b ell u =
        silentInteger b ell (u + 1) + (b ^ ell - 1) :=
  ⟨silentInteger_first_term b ell, silentInteger_step hb hu⟩

/-- The nine exact base-ten lag-one silent integers. -/
theorem decimal_silent_integer_certificate :
    (Finset.Ico 1 10).image (silentInteger 10 1) =
      ({19, 28, 37, 46, 55, 64, 73, 82, 91} : Finset ℕ) :=
  decimal_lag_one_silent_integers

/-- Complete global-silence classification in base ten at lag one. -/
theorem seven_global_silent_primes {p : ℕ}
    (hp : Nat.Prime p) (hbp : 10 < p) [NeZero p] :
    GloballySilentAt 10 p 1 (by omega) hp ↔
      p ∈ ({11, 13, 19, 23, 37, 41, 73} : Finset ℕ) :=
  decimal_lag_one_globally_silent_iff hp hbp

/-- Complete repetend-silence classification in base ten at lag one. -/
theorem seven_repetend_silent_primes {p : ℕ}
    (hp : Nat.Prime p) (hbp : 10 < p) :
    RepetendSilentAt 10 p 1 ↔
      p ∈ ({11, 13, 19, 23, 37, 41, 73} : Finset ℕ) :=
  decimal_lag_one_repetend_silent_iff hp hbp

/-- The displayed coordinate inverse recovers the coordinate. -/
theorem collision_coordinate_inverse_left {b p c : ℕ}
    (hp : Nat.Prime p) [NeZero p] (hb : 0 < b) (hbp : b < p)
    (hc : 0 < c) (hcp : c < p) :
    gateParameter b p (coordinateMultiplier b p c) = c :=
  gateParameter_coordinateMultiplier hp hb hbp hc hcp

/-- Recovering a nonidentity multiplier from its coordinate gives the
original multiplier. -/
theorem collision_coordinate_inverse_right {b p : ℕ}
    (hp : Nat.Prime p) [NeZero p] (hb : 0 < b) (hbp : b < p)
    {g : ZMod p} (hg1 : g ≠ 1) :
    coordinateMultiplier b p (gateParameter b p g) = g :=
  coordinateMultiplier_gateParameter hp hb hbp hg1

/-- Exact intrinsic positive-comparison formula. -/
theorem collision_coordinate_formula
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    collisionCount (primeDigitWord b p (by omega) hp.pos) g =
      2 * (positiveComparisonSet b p ((p - 1) / b)
        (gateParameter b p g)).card :=
  collision_coordinate_positive_comparisons hb2 hp hbp hg0 hg1

/-- Every nonidentity collision count is even. -/
theorem collision_count_even
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    Even (collisionCount (primeDigitWord b p (by omega) hp.pos) g) := by
  refine ⟨(positiveComparisonSet b p ((p - 1) / b)
    (gateParameter b p g)).card, ?_⟩
  rw [collision_coordinate_formula hb2 hp hbp hg0 hg1]
  omega

/-- Exact signed sawtooth form of the collision count. -/
theorem signed_sawtooth_collision_formula
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    let Q := (p - 1) / b
    let c := gateParameter b p g
    ((collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℤ) =
      (Q : ℤ) + ∑ m ∈ Finset.Icc 1 Q,
        sawtoothSign p (m * c) (m * b) :=
  collision_coordinate_signed_sawtooth hb2 hp hbp hg0 hg1

/-- No signed sawtooth term vanishes in the constructive range. -/
theorem signed_sawtooth_term_nonzero
    {p b c m : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hm0 : 0 < m) (hmp : m < p)
    (hbp : b < p) (hcp : c < p) (hmb : m * b < p) (hcb : c ≠ b) :
    rationalSawtooth p (m * c) - rationalSawtooth p (m * b) ≠ 0 :=
  constructive_sawtooth_difference_ne_zero
    hp hm0 hmp hbp hcp hmb hcb

/-- Exact pointwise bridge to the failure-indicator profile used by the
variance ledger. -/
theorem collision_failure_profile
    {b p c : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] (hbc : b < c) (hcp : c < p) :
    collisionCount (primeDigitWord b p (by omega) hp.pos)
        (coordinateMultiplier b p c) =
      2 * ((p - 1) / b) -
        2 * (failureComparisonSet b p ((p - 1) / b) c).card :=
  coordinateMultiplier_collision_failure_profile hb2 hp hbp hbc hcp

/-- Exact equality of the two displayed constructive-mean forms. -/
theorem exact_mean_second_form {b Q R : ℕ}
    (hN : 0 < b * (Q - 1) + R) :
    ((Q * (b * (Q - 1) + 2 * R) : ℕ) : ℚ) /
        (b * (Q - 1) + R : ℕ) =
      (Q : ℚ) + (Q * R : ℕ) / (b * (Q - 1) + R : ℕ) :=
  constructive_mean_second_form hN

/-- Exact mean over the literal constructive multiplier set. -/
theorem constructive_population_mean {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    ((∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℚ) /
        ((constructiveMultiplierSet b p (by omega) hp).card : ℚ) =
      constructiveMeanValue b Q R :=
  NField.Papers.BinDerangements.actual_constructive_mean
    hb2 hp hbp1 hdivision hR

/-- Exact first- and second-moment overlap ledger. -/
theorem finite_overlap_moments
    {α μ : Type*} [Fintype α] [Fintype μ] [DecidableEq α]
    (events : μ → Finset α) :
    (∑ x : α, failureTotal events x =
        ∑ m : μ, ((events m).card : ℚ)) ∧
      (∑ x : α, failureTotal events x ^ 2 =
        ∑ m : μ, ∑ n : μ, ((events m ∩ events n).card : ℚ)) :=
  ⟨sum_failureTotal events, sum_failureTotal_sq events⟩

/-- Exact variance formula for the collision profile represented by its
failure intervals. -/
theorem exact_interval_overlap_variance
    {α μ : Type*} [Fintype α] [Nonempty α] [Fintype μ]
    [DecidableEq α] (events : μ → Finset α) (Q : ℕ) :
    populationVariance
        (fun x => (2 * Q : ℚ) - 2 * failureTotal events x) =
      4 * ((Fintype.card α : ℚ)⁻¹ *
          (∑ m : μ, ∑ n : μ, ((events m ∩ events n).card : ℚ)) -
        ((Fintype.card α : ℚ)⁻¹ *
          ∑ m : μ, ((events m).card : ℚ)) ^ 2) :=
  collisionProfile_variance_eq_overlap_ledger events Q

/-- The floor crossing is one exactly on the displayed ceiling-interval
union. -/
theorem floor_crossing_interval_event
    {p b m c : ℕ} (hp : 0 < p) (hb : 0 < b) (hm : 0 < m)
    (hbc : b < c) (hcp : c < p) (hmb : m * b < p) :
    floorCrossing p b m c = 1 ↔
      c ∈ ceilingIntervalUnion p b m :=
  floorCrossing_eq_one_iff_mem_ceilingIntervalUnion
    hp hb hm hbc hcp hmb

/-- The failure comparison for a constructive coordinate is exactly the
ceiling-interval event. -/
theorem failure_comparison_interval_event
    {b p c m : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] (hbc : b < c) (hcp : c < p)
    (hm : m ∈ Finset.Icc 1 ((p - 1) / b)) :
    m ∈ failureComparisonSet b p ((p - 1) / b) c ↔
      c ∈ ceilingIntervalUnion p b m :=
  failure_comparison_iff_ceiling_interval hb2 hp hbp hbc hcp hm

/-- Each ceiling-interval family has the displayed size. -/
theorem ceiling_interval_family_size {p b m : ℕ}
    (hb : 0 < b) (hm : 0 < m) (hbm : b * m < p) :
    (ceilingIntervalUnion p b m).card = b * (m - 1) :=
  ceilingIntervalUnion_card hb hm hbm

/-- Every ceiling interval lies in the constructive coordinate range. -/
theorem ceiling_interval_constructive_range {p b m : ℕ}
    (hm : 0 < m) (hbm : b * m < p) :
    ceilingIntervalUnion p b m ⊆ Finset.Icc (b + 1) (p - 1) :=
  ceilingIntervalUnion_subset_constructiveCoordinates hm hbm

/-- Exact closed double-sum formula for every pairwise overlap. -/
theorem ceiling_interval_overlap_ledger {p b m n : ℕ}
    (hb : 0 < b) (hm : 0 < m) (hn : 0 < n)
    (hbm : b * m < p) (hbn : b * n < p) :
    ((ceilingIntervalUnion p b m) ∩
      (ceilingIntervalUnion p b n)).card =
      ∑ k ∈ Finset.Ico 1 m, ∑ l ∈ Finset.Ico 1 n,
        (b - Nat.dist (ceilingStart p m k) (ceilingStart p n l)) :=
  ceilingIntervalUnion_inter_card hb hm hn hbm hbn

/-- Uniform finite remainder bound proving the manuscript's diagonal
`2Q/3 + O_b(1)` statement. -/
theorem diagonal_variance_bounded_remainder {b Q R : ℕ}
    (hb : 0 < b) (hQ : 1 ≤ Q) (hR : R < b)
    (hN : 0 < b * (Q - 1) + R) :
    |diagonalVariance b Q R - (2 * (Q : ℚ) / 3)| ≤ 10 :=
  diagonalVariance_remainder_abs_le_ten hb hQ hR hN

#check digit_bin_conjugation
#check collision_congruence
#check collision_coordinate_certificate
#check zero_gate
#check zero_family_and_width
#check global_derangement_restricts_to_every_orbit
#check full_orbit_collision_equality
#check base_eight_short_orbit_boundary
#check silentInteger_eq_displayed
#check global_silent_prime_recipe
#check repetend_silent_prime_bound
#check global_silent_prime_bound
#check silent_integer_progression
#check decimal_silent_integer_certificate
#check seven_global_silent_primes
#check seven_repetend_silent_primes
#check collision_coordinate_inverse_left
#check collision_coordinate_inverse_right
#check collision_coordinate_formula
#check collision_count_even
#check signed_sawtooth_collision_formula
#check signed_sawtooth_term_nonzero
#check collision_failure_profile
#check NField.Alignment.BinDerangements.constructive_collision_mean
#check exact_mean_second_form
#check constructive_population_mean
#check finite_overlap_moments
#check populationVariance_affine
#check exact_interval_overlap_variance
#check floor_crossing_interval_event
#check failure_comparison_interval_event
#check ceiling_interval_family_size
#check ceiling_interval_constructive_range
#check ceiling_interval_overlap_ledger
#check diagonal_variance_bounded_remainder

end NField.Papers.SilentPrimes
