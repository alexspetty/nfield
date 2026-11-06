/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CenteredSourceDetails
import NField.Alignment.PrimeLogarithmicIntegral
import NField.Alignment.CollisionCharacterPrimeLimit
import NField.Alignment.AllLagPrimeDrift
import NField.Alignment.CenteredCollisionClosure
import NField.Papers.CollisionFluctuationSum

/-!
# The Centered Collision Sum

## Coverage

The all-lag collision table, fiber centering and character gates are
formalized. Fixed-progression prime and Mertens results give the centered
little-o estimate, harmonic limit, gated character formula and unconditional
all-lag drift.

## Scope and assumptions

The all-lag table is defined modulo `b^(ell+1)` and uses the actual coarse
reduction fibers. The prime and Mertens results apply at fixed modulus and
give limits for the original real cutoffs. They do not supply a
growing-modulus uniform estimate. The constructive mean uses unit multipliers
other than one with positive collision count. The four decimal rows remain
finite computations.
-/

namespace NField.Papers.CenteredCollisionSum

open scoped BigOperators ComplexConjugate Topology
open Filter
open NField.CollisionDefinition
open NField.Alignment.BinDerangementsClosure
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.SpectralPower
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionFluctuationClosure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionTransform
open NField.Alignment.NeutralityTheorem

/-! ## Direct finite determination -/

/-- Exact cardinality of the first/last-digit diagonal. -/
theorem all_lag_diagonal_cardinality {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell :=
  allLagDiagonal_card hb2 hell

/-- The intrinsic digit collision count is the endpoint-corrected diagonal
slice score at every positive lag. -/
theorem direct_collision_is_diagonal_slice_score
    {b ell p t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : p = allLagModulus b ell * t + a)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    (directAllLagCollisionCount b ell p : ℤ) =
      allLagSliceScore b ell p :=
  directAllLagCollisionCount_eq_allLagSliceScore
    hb2 hell hp ha halt hcop

/-- The direct collision deviation is the exact finite table throughout the
full coprime progression. -/
theorem direct_finite_table_determination
    {b ell t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcop

/-- The universal finite table gives one explicit uniform bound throughout
every coprime progression. -/
theorem direct_table_uniform_bound {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ B : ℕ, ∀ t a : ℕ, 1 ≤ a → a < allLagModulus b ell →
      a.Coprime (allLagModulus b ell) →
      Int.natAbs (directAllLagDeviation b ell
        (allLagModulus b ell * t + a)) ≤ B := by
  let B := ∑ a ∈ Finset.range (allLagModulus b ell),
    Int.natAbs (allLagTable b ell a)
  refine ⟨B, ?_⟩
  intro t a ha halt hcop
  rw [directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcop]
  have hle := Finset.single_le_sum
    (s := Finset.range (allLagModulus b ell))
    (f := fun r => Int.natAbs (allLagTable b ell r))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr halt)
  simpa [B] using hle

/-- Exact periodicity of the endpoint-corrected table. -/
theorem all_lag_table_periodicity {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 0 < a)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  allLagSliceDeviation_eq_table hb2 hell ha hcop

/-! ## Reflection, fibers, and the spectral gate -/

/-- Concrete reflection on every unit coordinate. -/
theorem exact_all_lag_reflection {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagTable b ell a +
      allLagTable b ell (allLagModulus b ell - a) = -1 :=
  allLagTable_reflection hb2 hell ha halt hcop

/-- Reflection fixes the grand mean of the literal unit table at `-1/2`. -/
theorem exact_grand_mean
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (Fintype.card (UnitClass (allLagModulus b ell)) : ℂ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b ell), allLagUnitTable b ell a =
      -1 / 2 :=
  allLagUnitTable_grand_mean hb2 hell

/-- Every natural representative fiber has exactly `b^ell` entries. -/
theorem exact_reduction_fiber_cardinality {b ell u : ℕ}
    (hb2 : 2 ≤ b) (hu : u ∈ reducedResidues b) :
    (tableFiber b ell u).card = b ^ ell :=
  tableFiber_card hb2 hu

/-- Every natural coarse fiber has exact centered sum zero. -/
theorem exact_natural_fiber_centering
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
        centeredCollisionTransform b ell a = 0 :=
  natural_centering_fiber_sum_zero u

/-- The naturally centered table has total mass zero. -/
theorem exact_centered_total_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a : UnitClass (allLagModulus b ell),
      centeredCollisionTransform b ell a = 0 :=
  centeredCollisionTransform_sum_zero

/-- Reflected coarse fibers have exact means summing to `-1`. -/
theorem exact_natural_fiber_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  natural_fiber_mean_reflection hb2 hell u

/-- Natural centering turns the concrete reflection law into oddness. -/
theorem exact_centered_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTransform b ell (-a) =
      -centeredCollisionTransform b ell a :=
  natural_centered_reflection hb2 hell a

/-- Every even character coefficient vanishes. -/
theorem exact_even_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (heven : χ.Even) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  natural_even_character_gate hb2 hell χ heven

/-- Every character descending to the base unit group vanishes. -/
theorem exact_base_factored_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (χ : Character (allLagModulus b ell)) (hfactor : BaseFactored χ) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  natural_base_factored_character_gate χ hfactor

/-- At prime base and lag one, every active channel is primitive and odd. -/
theorem exact_prime_base_support
    {b : ℕ} (hb : Nat.Prime b)
    [NeZero b] [NeZero (allLagModulus b 1)]
    {χ : Character (allLagModulus b 1)}
    (hactive : χ ∈ transformActiveCharacters b 1) :
    χ.IsPrimitive ∧ χ.Odd :=
  primeBase_active_primitive_and_odd hb hactive

/-- Exact finite character decomposition of every centered weighted packet. -/
theorem exact_finite_character_packet_decomposition
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass (allLagModulus b ell))
    (weight : ι → ℂ) :
    ∑ i, centeredCollisionTransform b ell (residue i) * weight i =
      ∑ χ : Character (allLagModulus b ell),
        collisionCoefficient (centeredCollisionTransform b ell) χ *
          ∑ i, χ (residue i).val * weight i :=
  transform_finite_packet_decomposition residue weight

/-! ## Constructive mean and drift -/

/-- The literal constructive population contains unit multipliers other than
one with positive collision count, and its exact mean is the displayed
rational object. -/
theorem exact_constructive_population_mean {b p Q R : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    ((∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℚ) /
        ((constructiveMultiplierSet b p (by omega) hp).card : ℚ) =
      constructiveMeanValue b Q R :=
  NField.Papers.CollisionFluctuationSum.exact_constructive_population_mean
    hb2 hp hbp1 hdivision hR

/-- The literal constructive population has exactly `p-b-1` members. -/
theorem exact_constructive_population_cardinality {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) [NeZero p]
    (hbp1 : b + 1 < p) :
    (constructiveMultiplierSet b p (by omega) hp).card = p - b - 1 :=
  constructiveMultiplierSet_card hb2 hp hbp1

/-- At every positive lag above `b^(ell+1)`, the power multiplier belongs to
the literal constructive population. -/
theorem exact_all_lag_multiplier_constructive
    {b p ell : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : Nat.Prime p) [NeZero p]
    (hlarge : b ^ (ell + 1) < p) :
    powerMultiplier b p ell ∈
      constructiveMultiplierSet b p (by omega) hp :=
  powerMultiplier_mem_constructiveMultiplierSet hb2 hell hp hlarge

/-- The denominator in the constructive mean is exactly `p-b-1`. -/
theorem constructive_population_denominator {b p Q R : ℕ}
    (hbp1 : b + 1 < p) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) :
    p - b - 1 = b * (Q - 1) + R := by
  have hQ : 1 ≤ Q := by
    by_contra hnot
    have hQzero : Q = 0 := by omega
    subst Q
    simp at hdivision
    omega
  have hmul : b * Q = b * (Q - 1) + b := by
    calc
      b * Q = b * ((Q - 1) + 1) := by
        rw [Nat.sub_add_cancel hQ]
      _ = b * (Q - 1) + b := by simp [Nat.mul_add]
  rw [hmul] at hdivision
  omega

/-- The constructive mean is `Q` plus its exact rational correction. -/
theorem exact_constructive_mean_second_form {b Q R : ℕ}
    (hden : 0 < b * (Q - 1) + R) :
    constructiveMeanValue b Q R =
      (Q : ℚ) + (Q * R : ℕ) / (b * (Q - 1) + R : ℕ) :=
  constructiveMeanValue_eq_quotient_plus_correction hden

/-- Subtracting the constructive mean gives the exact integer and rational
decomposition used at every lag. -/
theorem exact_all_lag_fluctuation_decomposition
    (C Q R N : ℕ) :
    (C : ℚ) - ((Q : ℚ) + (Q * R : ℕ) / (N : ℕ)) =
      (C : ℚ) - Q - (Q * R : ℕ) / (N : ℕ) :=
  NField.Papers.CollisionFluctuationSum.exact_fluctuation_decomposition
    C Q R N

/-- Exact expansion of the constructive-mean correction. -/
theorem exact_correction_expansion {b Q R N : ℕ}
    (hb : 0 < b) (hN : 0 < N) (hR : R < b)
    (hrelation : N + b = b * Q + R) :
    ((Q * R : ℕ) : ℚ) / N =
      (R : ℚ) / b + ((R * (b - R) : ℕ) : ℚ) / (b * N) :=
  correction_expansion hb hN hR hrelation

/-- The actual reduced-residue mean of the remainder term is
`1/2-1/b`. -/
theorem exact_remainder_class_mean {b : ℕ} (hb2 : 2 ≤ b) :
    (Fintype.card (BaseUnit b) : ℚ)⁻¹ *
        ∑ u : BaseUnit b, ((u : ℚ) - 1) / b =
      1 / 2 - 1 / b :=
  baseUnit_remainder_mean hb2

/-- The two exact finite means combine to `-(b-1)/b`. -/
theorem exact_drift_coefficient (b : ℚ) (hb : b ≠ 0) :
    (-1 / 2) - (1 / 2 - 1 / b) = -(b - 1) / b :=
  drift_coefficient b hb

/-- Once the two classwise analytic residual limits are supplied, their
subtraction has the exact all-lag drift coefficient. -/
theorem exact_all_lag_drift_from_component_limits
    {α : Type*} {l integerPart correction : α → ℝ}
    {κS κR : ℝ} {lfilter : Filter α} (b : ℕ) (hb2 : 2 ≤ b)
    (hS : Tendsto
      (fun x => integerPart x - (-1 / 2) * l x) lfilter (𝓝 κS))
    (hR : Tendsto
      (fun x => correction x - (1 / 2 - 1 / (b : ℝ)) * l x)
      lfilter (𝓝 κR)) :
    Tendsto
      (fun x => (integerPart x - correction x) -
        (-(b - 1 : ℝ) / b) * l x) lfilter (𝓝 (κS - κR)) :=
  collision_drift_limit_from_component_limits b hb2 hS hR

/-! ## Prime-base columns -/

/-- The exact unit-multiplier floor sum used in the prime-base column proof. -/
theorem exact_prime_base_floor_sum_unit
    {b c s : ℕ} (hb : Nat.Prime b)
    (hspos : 1 ≤ s) (hslt : s < b) (hc : ¬b ∣ c) :
    columnFloorSum b c s =
      (c - 1) * (b - 1) / 2 + c * s / b :=
  columnFloorSum_unit_prime hb hspos hslt hc

/-- The exact base-multiple floor sum used at the column endpoint. -/
theorem exact_prime_base_floor_sum_multiple
    {b h s : ℕ} (hb : 0 < b) :
    columnFloorSum b (b * h) s =
      h * b * (b - 1) / 2 + b * (h * s / b) :=
  columnFloorSum_base_multiple hb

/-- Every prime-base lag-one column has sum `s-p`. -/
theorem exact_prime_base_column_sum
    {p s : ℕ} (hp : p.Prime) (hspos : 0 < s) (hslt : s < p) :
    tableFiberSum p 1 s = (s : ℤ) - p :=
  primeBase_tableFiberSum hp hspos hslt

/-- Every prime-base lag-one column has mean `s/p-1`. -/
theorem exact_prime_base_column_mean
    {p s : ℕ} (hp : p.Prime) (hspos : 0 < s) (hslt : s < p) :
    (p : ℚ)⁻¹ * (tableFiberSum p 1 s : ℚ) =
      (s : ℚ) / p - 1 :=
  primeBase_tableFiberMean hp hspos hslt

/-- The two exact base-three column totals. -/
theorem exact_base_three_column_totals :
    (tableFiber 3 1 1).card = 3 ∧ tableFiberSum 3 1 1 = -2 ∧
    (tableFiber 3 1 2).card = 3 ∧ tableFiberSum 3 1 2 = -1 :=
  base_three_column_totals

/-- The four exact base-ten lag-one column totals. -/
theorem exact_decimal_column_totals :
    (tableFiber 10 1 1).card = 10 ∧ tableFiberSum 10 1 1 = -17 ∧
    (tableFiber 10 1 3).card = 10 ∧ tableFiberSum 10 1 3 = -9 ∧
    (tableFiber 10 1 7).card = 10 ∧ tableFiberSum 10 1 7 = -1 ∧
    (tableFiber 10 1 9).card = 10 ∧ tableFiberSum 10 1 9 = 7 :=
  decimal_lag_one_column_totals

/-- The two lag-two decimal values distinguish classes that agree modulo one
hundred. -/
theorem decimal_lag_two_table_check :
    directAllLagDeviation 10 2 1009 = 8 ∧
    directAllLagDeviation 10 2 1109 = -10 ∧
    allLagTable 10 2 (1009 % 1000) = 8 ∧
    allLagTable 10 2 (1109 % 1000) = -10 :=
  decimal_lag_two_distinguishing_values

/-! ## Conditional prime limits -/

/-- Common class density plus exact centering gives the unweighted limit
zero. -/
theorem exact_centered_common_class_limit
    {α ι : Type*} [Fintype α] {lfilter : Filter ι}
    (f : α → ℝ) (A : ι → α → ℝ) (c : ℝ)
    (hzero : ∑ a, f a = 0)
    (hclass : ∀ a, Tendsto (fun x => A x a) lfilter (𝓝 c)) :
    Tendsto (fun x => ∑ a, f a * A x a) lfilter (𝓝 0) :=
  centered_progression_common_limit f A c hzero hclass

/-- Common class growth cancels, leaving the weighted class constants in the
reciprocal-prime limit. -/
theorem exact_centered_residual_class_limit
    {α ι : Type*} [Fintype α] {lfilter : Filter ι}
    (f : α → ℝ) (A : ι → α → ℝ) (common : ι → ℝ)
    (K : α → ℝ) (hzero : ∑ a, f a = 0)
    (hclass : ∀ a,
      Tendsto (fun x => A x a - common x) lfilter (𝓝 (K a))) :
    Tendsto (fun x => ∑ a, f a * A x a) lfilter
      (𝓝 (∑ a, f a * K a)) :=
  centered_progression_residual_limit f A common K hzero hclass

#check all_lag_diagonal_cardinality
#check direct_collision_is_diagonal_slice_score
#check direct_finite_table_determination
#check direct_table_uniform_bound
#check all_lag_table_periodicity
#check exact_all_lag_reflection
#check exact_grand_mean
#check exact_reduction_fiber_cardinality
#check exact_natural_fiber_centering
#check exact_centered_total_zero
#check exact_natural_fiber_mean_reflection
#check exact_centered_reflection
#check exact_even_character_gate
#check exact_base_factored_character_gate
#check exact_prime_base_support
#check exact_finite_character_packet_decomposition
#check exact_constructive_population_mean
#check exact_constructive_population_cardinality
#check exact_all_lag_multiplier_constructive
#check constructive_population_denominator
#check exact_constructive_mean_second_form
#check exact_all_lag_fluctuation_decomposition
#check exact_correction_expansion
#check exact_remainder_class_mean
#check exact_drift_coefficient
#check exact_all_lag_drift_from_component_limits
#check exact_prime_base_floor_sum_unit
#check exact_prime_base_floor_sum_multiple
#check exact_prime_base_column_sum
#check exact_prime_base_column_mean
#check exact_base_three_column_totals
#check exact_decimal_column_totals
#check decimal_lag_two_table_check
#check exact_centered_common_class_limit
#check exact_centered_residual_class_limit

end NField.Papers.CenteredCollisionSum

/-! Analytic conclusions selected from their defining source modules. -/

#check NField.Alignment.PrimePeriodicLimits.prime_progression_logarithmic_integral_limit
#check NField.Alignment.ProgressionMertens.real_cutoff_mertens_progression
#check NField.Alignment.CollisionPrimeLimits.real_centered_collision_prime_littleO
#check NField.Alignment.CollisionPrimeLimits.real_centered_collision_harmonic_limit
#check NField.Alignment.CollisionPrimeLimits.centered_harmonic_character_formula
#check NField.Alignment.CollisionPrimeLimits.all_lag_constructive_prime_drift
#check NField.Alignment.CenteredSourceDetails.nonidentity_collision_sum
#check NField.Alignment.CenteredSourceDetails.raw_table_principal_coefficient
#check NField.Alignment.CenteredSourceDetails.raw_table_nonprincipal_even_zero
