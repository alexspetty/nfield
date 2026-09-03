/-
Author: Alexander S. Petty
-/

import NField.Alignment.BinDerangementsClosure

/-!
# Bin Derangements and the Gate Width Theorem

Reader-facing theorem map for the Lean companion to
`papers/bin_derangements.tex`.

## Checked here

* Euclidean division by `p` is written exactly in terms of the transformed
  residue `[b r]_p`.
* Multiplication by `b` sends equality of intrinsic digit bins to equality of
  ordinary residue classes modulo `b`, in both directions.
* The intrinsic collision count is exactly the transformed congruence count.
* The parameter `c=[b(1-g)⁻¹]_p` is positive, lies below `p`, cannot equal
  `b`, and satisfies `c(1-g)=b` for every nonzero nonidentity multiplier.
* The lower side `c<b` has no collision.  Both quotient orders in the
  manuscript's contradiction are proved.  The upper side `b<c` has the
  manuscript's explicit collision at `x=p-c`.
* Collision freedom is therefore equivalent to `c<b`.
* The collision-free multipliers are exactly `-u/(b-u)` for `1≤u<b`.
  The parametrization is injective, has cardinality `b-1`, and pairs `u`
  with `b-u` under inversion.
* The collision-mass sum rule is proved by an exact finite double count and
  specialized to the intrinsic prime digit word.
* The constructive-total and rational-mean algebra is checked from the
  Euclidean two-length mass.  The first constructive range has mean two.
* A full nonzero-residue orbit reads the same zero gate as cyclic
  autocorrelation.  The primitive-root content is isolated in the explicit
  orbit and motion hypotheses.
* Kernel-reduced certificates reproduce the complete decimal prime-thirteen
  bin sizes, zero set, and both positive collision counts.

## Proof boundary

The central gate-width theorem is proved against the intrinsic long-division
digit word, without an assumed gate classification and without a
primitive-root hypothesis.

The publication closure now proves the displayed floor-difference formula,
the complete `Q`/`Q+1` distribution with exactly `R` long bins, the literal
within-bin ratio characterization and its cardinality, the constructive set's
exact count and collision mass, both special ranges, the uniform asymptotic
bound and ratio limit, and the shorter-orbit counterexample.  No manuscript
claim remains outside the checked finite and asymptotic theorem map.
-/

namespace NField.Papers.BinDerangements

open scoped BigOperators
open ZMod
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.Alignment.AutocorrelationFormula
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.BinDerangements
open NField.Alignment.BinDerangementsClosure

/-- Exact displayed floor-difference formula, including the last-bin endpoint
correction. -/
theorem exact_bin_cardinality {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (d : Fin b) :
    (binSet (primeDigitWord b p (by omega) hp.pos) d).card =
      ((d.val + 1) * p) / b - (d.val * p) / b -
        (if d.val = b - 1 then 1 else 0) := by
  rw [primeDigitWord_bin_card (by omega) hp.pos]
  exact digitBinPopulation_floor_formula hb2 hp hbp d.isLt

/-- Exact quotient/remainder distribution and its square mass. -/
theorem exact_bin_distribution {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hdivision : p - 1 = b * Q + R) (hR : R < b) :
    (∀ d : Fin b,
      (binSet (primeDigitWord b p (by omega) hp.pos) d).card = Q ∨
      (binSet (primeDigitWord b p (by omega) hp.pos) d).card = Q + 1) ∧
    ((Finset.univ.filter fun d : Fin b =>
      (binSet (primeDigitWord b p (by omega) hp.pos) d).card = Q).card =
        b - R) ∧
    ((Finset.univ.filter fun d : Fin b =>
      (binSet (primeDigitWord b p (by omega) hp.pos) d).card = Q + 1).card =
        R) ∧
    digitBinSquareSum b p = b * Q ^ 2 + R * (2 * Q + 1) := by
  have hb : 0 < b := by omega
  have hqr : (p - 1) / b = Q ∧ (p - 1) % b = R :=
    (Nat.div_mod_unique hb).2 ⟨by omega, hR⟩
  have hmodel := primeDigitWord_twoLengthIntervalModel hb hp.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    simpa [hqr.1] using hmodel.length_cases d
  · simpa [hqr.1, hqr.2] using hmodel.small_count
  · simpa [hqr.1, hqr.2] using hmodel.large_count
  · simpa [hqr.1, hqr.2] using
      (digitBinSquareSum_eq_quotient_remainder hb hp.pos)

/-- Exact Euclidean decomposition behind the digit-bin conjugation. -/
theorem euclidean_digit_decomposition {b p : ℕ}
    (hbp : b < p) [NeZero p] (r : ZMod p) :
    b * r.val =
      p * NField.CollisionDefinition.digitBin b p r.val +
        ((b : ZMod p) * r).val :=
  digit_decomposition hbp r

/-- Exact interval-to-congruence conjugation for the intrinsic digit map. -/
theorem bin_conjugation {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (r s : ZMod p) :
    NField.CollisionDefinition.digitBin b p r.val =
        NField.CollisionDefinition.digitBin b p s.val ↔
      ((b : ZMod p) * r).val % b =
        ((b : ZMod p) * s).val % b :=
  digit_eq_iff_transformed_mod hb hp hbp r s

/-- Exact collision-congruence identity for the intrinsic prime word. -/
theorem collision_congruence {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) (hg0 : g ≠ 0) :
    collisionCount (primeDigitWord b p hb hp.pos) g =
      transformedCollisionCount b p g :=
  collisionCount_eq_transformedCollisionCount hb hp hbp g hg0

/-- The gate parameter has the exact range, excluded value, and defining
congruence used in the manuscript. -/
theorem gate_parameter_certificate {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    0 < gateParameter b p g ∧
      gateParameter b p g < p ∧
      gateParameter b p g ≠ b ∧
      (gateParameter b p g : ZMod p) * (1 - g) = (b : ZMod p) := by
  exact ⟨gateParameter_pos hb hp hbp hg1,
    gateParameter_lt g,
    gateParameter_ne_base hb hp hbp hg0 hg1,
    gateParameter_mul_one_sub hp hg1⟩

/-- The complete zero-side/positive-side gate criterion. -/
theorem zero_gate_criterion {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    collisionCount (primeDigitWord b p hb hp.pos) g = 0 ↔
      gateParameter b p g < b :=
  collisionCount_eq_zero_iff_parameter_lt hb hp hbp hg0 hg1

/-- Exact displayed classification of every collision-free multiplier. -/
theorem exact_deranging_family {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (g : ZMod p) :
    g ∈ derangingFamily b p ↔
      g ≠ 0 ∧ collisionCount
        (primeDigitWord b p (by omega) hp.pos) g = 0 :=
  mem_derangingFamily_iff hb2 hp hbp g

/-- The exact gate width is fixed by the base. -/
theorem gate_width {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    (derangingFamily b p).card = b - 1 :=
  derangingFamily_card hb hp hbp

/-- Complementary parameters give inverse deranging multipliers. -/
theorem inverse_pairing {b p u : ℕ}
    (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hu0 : 0 < u) (hub : u < b) :
    derangingMultiplier b p (b - u) =
      (derangingMultiplier b p u)⁻¹ :=
  derangingMultiplier_complement hp hbp hu0 hub

/-- For an even base, the middle parameter is exactly the multiplier `-1`. -/
theorem even_base_midpoint {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (heven : Even b) :
    derangingMultiplier b p (b / 2) = -1 :=
  derangingMultiplier_half_eq_neg_one hb2 hp hbp heven

/-- Literal within-bin ratio representation and the exact ratio-set
cardinality. -/
theorem ratio_set_certificate {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    (∀ g : ZMod p,
      g ∈ intrinsicWithinBinRatioSet b p (by omega) hp ↔
        ∃ d : Fin b, ∃ a r : ZMod p,
          a ∈ binSet (primeDigitWord b p (by omega) hp.pos) d ∧
          r ∈ binSet (primeDigitWord b p (by omega) hp.pos) d ∧
          g = a * r⁻¹) ∧
      (intrinsicWithinBinRatioSet b p (by omega) hp).card = p - b := by
  constructor
  · intro g
    exact mem_withinBinRatioSet_iff hp
      (primeDigitWord b p (by omega) hp.pos)
      (primeDigitWord_zero b p (by omega) hp.pos) g
  · exact intrinsicWithinBinRatioSet_card hb2 hp hbp

/-- Exact collision-mass double count. -/
theorem collision_mass_sum_rule {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p] :
    ∑ g : ZMod p,
        collisionCount (primeDigitWord b p hb hp.pos) g =
      NField.Alignment.digitBinSquareSum b p :=
  prime_collisionCount_sum_rule hb hp

/-- Closed quotient/remainder form of the collision mass. -/
theorem collision_mass_closed_form {b p Q R : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p)
    (hdivision : p - 1 = b * Q + R) (hR : R < b) :
    digitBinSquareSum b p = b * Q ^ 2 + R * (2 * Q + 1) := by
  have hqr : (p - 1) / b = Q ∧ (p - 1) % b = R :=
    (Nat.div_mod_unique hb).2 ⟨by omega, hR⟩
  simpa [hqr.1, hqr.2] using
    (digitBinSquareSum_eq_quotient_remainder hb hp.pos)

/-- The actual constructive set has the displayed count and total collision
mass. -/
theorem constructive_set_certificate {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    (constructiveMultiplierSet b p (by omega) hp).card =
        b * (Q - 1) + R ∧
      (∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g) =
          Q * (b * (Q - 1) + 2 * R) := by
  have hcount := constructiveMultiplierSet_card hb2 hp hbp1
  have hsum := constructiveMultiplierSet_collision_sum hb2 hp hbp1
  have hb : 0 < b := by omega
  have hqr : (p - 1) / b = Q ∧ (p - 1) % b = R :=
    (Nat.div_mod_unique hb).2 ⟨by omega, hR⟩
  simp only [hqr.1, hqr.2] at hsum
  have hQ : 1 ≤ Q := by
    by_contra hnot
    have hQzero : Q = 0 := by omega
    subst Q
    simp at hdivision
    omega
  have htotal := constructive_collision_total hQ hdivision
  have hQsplit : Q = (Q - 1) + 1 := by omega
  have hdivision' : p - 1 = b * (Q - 1) + b + R := by
    calc
      p - 1 = b * Q + R := hdivision
      _ = b * ((Q - 1) + 1) + R := by rw [← hQsplit]
      _ = b * (Q - 1) + b + R := by
        simp [Nat.mul_add, Nat.add_assoc]
  constructor
  · calc
      (constructiveMultiplierSet b p (by omega) hp).card = p - b - 1 := hcount
      _ = b * (Q - 1) + R := by omega
  · exact hsum.trans htotal

/-- Exact constructive-total algebra from Euclidean two-length mass. -/
theorem constructive_total {b p Q R : ℕ}
    (hQ : 1 ≤ Q) (hdivision : p - 1 = b * Q + R) :
    (b * Q ^ 2 + R * (2 * Q + 1)) - (p - 1) =
      Q * (b * (Q - 1) + 2 * R) :=
  constructive_collision_total hQ hdivision

/-- Exact rational constructive mean. -/
theorem constructive_mean {b p Q R : ℕ}
    (hQ : 1 ≤ Q) (hdivision : p - 1 = b * Q + R)
    (hpositive : 0 < b * (Q - 1) + R) :
    ((b * Q ^ 2 + R * (2 * Q + 1) - (p - 1) : ℕ) : ℚ) /
        ((b * (Q - 1) + R : ℕ) : ℚ) =
      (Q * (b * (Q - 1) + 2 * R) : ℕ) /
        ((b * (Q - 1) + R : ℕ) : ℚ) :=
  constructive_collision_mean hQ hdivision hpositive

/-- The average over the actual constructive multiplier set is the displayed
rational formula. -/
theorem actual_constructive_mean {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    ((∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℚ) /
        ((constructiveMultiplierSet b p (by omega) hp).card : ℚ) =
      constructiveMeanValue b Q R := by
  obtain ⟨hcount, hsum⟩ :=
    constructive_set_certificate hb2 hp hbp1 hdivision hR
  rw [hcount, hsum]
  rfl

/-- The remainder-zero case, the complete mean-two range, and the uniform
bounded correction. -/
theorem exact_special_ranges {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (_hp : Nat.Prime p)
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    (R = 0 → constructiveMeanValue b Q R = Q) ∧
      (constructiveMeanValue b Q R = 2 ↔ p ≤ 2 * b + 1) ∧
      (0 ≤ constructiveMeanValue b Q R - Q ∧
        constructiveMeanValue b Q R - Q ≤ 1) := by
  have hb : 0 < b := by omega
  have hQ : 1 ≤ Q := by
    by_contra hnot
    have hQzero : Q = 0 := by omega
    subst Q
    simp at hdivision
    omega
  have hden : 0 < b * (Q - 1) + R := by
    by_cases hQone : Q = 1
    · subst Q
      simp
      omega
    · have hQminus : 0 < Q - 1 := Nat.sub_pos_of_lt (by omega)
      have hmul := Nat.mul_pos hb hQminus
      omega
  refine ⟨?_, constructiveMeanValue_eq_two_iff hb hdivision hR hbp1,
    constructiveMeanValue_correction_bounds hb hQ hR hden⟩
  intro hRzero
  subst R
  have hQtwo : 1 < Q := by
    by_contra hnot
    have hQone : Q = 1 := by omega
    subst Q
    simp at hdivision
    omega
  exact constructiveMeanValue_eq_quotient_of_remainder_zero hb hQtwo

/-- With the base fixed and the admissible remainder allowed to vary, the
mean-to-quotient ratio tends to one. -/
theorem constructive_mean_ratio_limit
    {b : ℕ} (hb : 0 < b) (R : ℕ → ℕ) (hR : ∀ Q, R Q < b) :
    Filter.Tendsto
      (fun Q : ℕ => constructiveMeanValue b Q (R Q) / Q)
      Filter.atTop (nhds 1) :=
  constructiveMeanValue_ratio_tendsto_one hb R hR

/-- Full-orbit zero-lag readout. -/
theorem zero_lag_readout
    {G : Type*} [Fintype G] [AddCommGroup G]
    {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (orbit : G ≃ NonzeroResidue p) (lag : G) (g : ZMod p)
    (hmotion : ∀ t, (orbit (t + lag)).val = g * (orbit t).val)
    (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    fullOrbitAutocorrelation (primeDigitWord b p hb hp.pos) orbit lag = 0 ↔
      gateParameter b p g < b :=
  fullOrbitAutocorrelation_eq_zero_iff_parameter_lt
    hb hp hbp orbit lag g hmotion hg0 hg1

/-- A primitive-root exponent clock has exactly `b-1` nonzero zero lags. -/
theorem zero_lag_count {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    (hpb : ¬p ∣ b) [NeZero p]
    (hprimitive : IsPrimitiveRoot (primeBaseUnit b p hp hpb) (p - 1)) :
    letI : NeZero (primeBasePeriod b p hp hpb) :=
      ⟨(primeBasePeriod_pos hp hpb).ne'⟩
    let hfull := primeBasePeriod_eq_full_of_isPrimitiveRoot hp hpb hprimitive
    (zeroLagSet (primeDigitWord b p (by omega) hp.pos)
      (canonicalPrimeOrbitEquiv hp hpb hfull)).card = b - 1 := by
  letI : NeZero (primeBasePeriod b p hp hpb) :=
    ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  dsimp only
  apply zeroLagSet_card hb2 hp hbp
  rw [canonicalPrimeOrbitEquiv_apply]
  simp

/-- Full-group silence descends to every restricted orbit. -/
theorem restricted_orbit_inheritance {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) (orbit : Finset (ZMod N))
    (g : ZMod N) (hzero : collisionCount word g = 0) :
    restrictedCollisionCount word orbit g = 0 :=
  restrictedCollisionCount_eq_zero_of_collisionCount_eq_zero
    word orbit g hzero

/-- The converse fails exactly: base eight at prime thirteen is silent on its
four-element orbit at lag one but has full-group collision count two. -/
theorem shorter_orbit_converse_failure :
    let word := primeDigitWord 8 13 (by norm_num) (by norm_num)
    let orbit : Finset (ZMod 13) := {1, 5, 8, 12}
    restrictedCollisionCount word orbit 8 = 0 ∧
      collisionCount word 8 = 2 :=
  baseEight_thirteen_short_orbit_counterexample

/-- Complete decimal prime-thirteen fixture: bin populations, deranging
family, and both constructive collision counts. -/
theorem decimal_thirteen_fixture :
    decimalThirteenBinSizes = [1, 1, 1, 2, 1, 1, 2, 1, 1, 1] ∧
      derangingFamily 10 13 =
        ({2, 3, 4, 5, 7, 8, 9, 10, 12} : Finset (ZMod 13)) ∧
      collisionCount decimalThirteenDigitWord 6 = 2 ∧
      collisionCount decimalThirteenDigitWord 11 = 2 := by
  exact ⟨decimalThirteenBinSizes_certificate,
    decimal_thirteen_deranging_family,
    decimal_thirteen_collision_six,
    decimal_thirteen_collision_eleven⟩

#check digit_decomposition
#check digit_eq_iff_transformed_mod
#check collisionCount_eq_transformedCollisionCount
#check gateParameter_mul_one_sub
#check gateParameter_ne_base
#check transformedCollisionCount_eq_zero_of_parameter_lt
#check transformedCollisionCount_pos_of_base_lt_parameter
#check collisionCount_eq_zero_iff_parameter_lt
#check derangingMultiplier_parameter_identity
#check mem_derangingFamily_iff
#check derangingFamily_card
#check derangingMultiplier_complement
#check collisionCount_sum_rule
#check prime_collisionCount_sum_rule
#check constructive_collision_total
#check constructive_collision_mean
#check fullOrbitAutocorrelation_eq_zero_iff_parameter_lt
#check decimal_thirteen_deranging_family
#check decimal_thirteen_collision_six
#check decimal_thirteen_collision_eleven

end NField.Papers.BinDerangements
