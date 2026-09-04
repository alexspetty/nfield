/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SilentPrimes

/-!
# The collision fluctuation sum

Exact finite-table, reflection, mean, and correction arithmetic for the Lean
companion to "The Collision Fluctuation Sum".
-/

namespace NField.Alignment.CollisionFluctuationSum

open scoped BigOperators
open NField.CollisionDefinition

/-! ## The finite lag-one table -/

/-- The two-digit diagonal indices `(b + 1) d`, for `0 <= d < b`. -/
def diagonalSlices (b : ℕ) : Finset ℕ :=
  (Finset.range b).image fun d => (b + 1) * d

/-- There are exactly `b` diagonal slices. -/
theorem diagonalSlices_card (b : ℕ) : (diagonalSlices b).card = b := by
  unfold diagonalSlices
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro d _ e _ hde
    exact Nat.mul_left_cancel (Nat.succ_pos b) hde

/-- One floor jump in the manuscript's finite table, kept in `ℤ` so that
later deviations may be negative. -/
def floorJump (M a n : ℕ) : ℤ :=
  (((n + 1) * a / M : ℕ) : ℤ) - (((n * a) / M : ℕ) : ℤ)

/-- The exact finite table `F_b(a)` from the manuscript. -/
def fluctuationTable (b a : ℕ) : ℤ :=
  -1 - ((a / b : ℕ) : ℤ) +
    ∑ n ∈ diagonalSlices b, floorJump (b ^ 2) a n

/-- The endpoint-corrected sum of diagonal slice populations. -/
def sliceCollisionScore (b p : ℕ) : ℤ :=
  -1 + ∑ n ∈ diagonalSlices b, floorJump (b ^ 2) p n

/-- The integer deviation obtained from the exact slice score. -/
def sliceDeviation (b p : ℕ) : ℤ :=
  sliceCollisionScore b p - (((p - 1) / b : ℕ) : ℤ)

/-- Adding a complete modulus block adds the same integer `t` to every floor
jump. -/
theorem floorJump_add_modulus_mul {M t a n : ℕ} (hM : 0 < M) :
    floorJump M (M * t + a) n = (t : ℤ) + floorJump M a n := by
  have hfirst :
      (n + 1) * (M * t + a) / M =
        (n + 1) * t + ((n + 1) * a) / M := by
    rw [show (n + 1) * (M * t + a) =
        M * ((n + 1) * t) + (n + 1) * a by ring]
    exact Nat.mul_add_div hM _ _
  have hsecond :
      n * (M * t + a) / M = n * t + (n * a) / M := by
    rw [show n * (M * t + a) = M * (n * t) + n * a by ring]
    exact Nat.mul_add_div hM _ _
  unfold floorJump
  rw [hfirst, hsecond]
  push_cast
  ring

/-- A complete `b^2` block adds `b t` to the diagonal slice score. -/
theorem sliceCollisionScore_add_square_mul {b t a : ℕ} (hb : 0 < b) :
    sliceCollisionScore b (b ^ 2 * t + a) =
      (b * t : ℕ) + sliceCollisionScore b a := by
  unfold sliceCollisionScore
  simp_rw [floorJump_add_modulus_mul (pow_pos hb 2)]
  rw [Finset.sum_add_distrib]
  simp [diagonalSlices_card]
  ring

/-- Removing one does not change the quotient when the dividend has a
nonzero remainder. -/
theorem pred_div_eq_div {a b : ℕ} (hb : 0 < b) (ha : 0 < a)
    (hmod : a % b ≠ 0) : (a - 1) / b = a / b := by
  have hmodpos : 0 < a % b := Nat.pos_of_ne_zero hmod
  have hdivision := Nat.mod_add_div a b
  have hlower : (a / b) * b ≤ a - 1 := by
    rw [Nat.mul_comm]
    omega
  have hupper : a - 1 < (a / b + 1) * b := by
    have ha_upper : a < (a / b + 1) * b :=
      (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self (a / b))
    omega
  apply Nat.div_eq_of_lt_le
  · exact hlower
  · exact hupper

/-- Coprimality to `b^2` forces a nonzero remainder modulo `b`. -/
theorem mod_base_ne_zero_of_coprime_square {a b : ℕ} (hb2 : 2 ≤ b)
    (hcop : Nat.Coprime a (b ^ 2)) : a % b ≠ 0 := by
  intro hmod
  have hba : b ∣ a := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hcopb : Nat.Coprime a b :=
    Nat.Coprime.of_dvd_right (by exact dvd_pow_self b (by omega)) hcop
  have hb1 : b = 1 := Nat.eq_one_of_dvd_coprimes hcopb hba dvd_rfl
  omega

/-- The finite table is periodic after the exact slice formula has been
reached.  This is the algebraic content of substituting `p=b^2 t+a` into the
slice count and subtracting `Q`. -/
theorem sliceDeviation_eq_fluctuationTable {b t a : ℕ}
    (hb2 : 2 ≤ b) (ha : 0 < a) (hcop : Nat.Coprime a (b ^ 2)) :
    sliceDeviation b (b ^ 2 * t + a) = fluctuationTable b a := by
  have hb : 0 < b := by omega
  have hpred :
      (b ^ 2 * t + a - 1) / b = b * t + a / b := by
    have hsub : b ^ 2 * t + a - 1 = b * (b * t) + (a - 1) := by
      rw [Nat.add_sub_assoc (by omega : 1 ≤ a)]
      congr 1
      ring
    rw [hsub, Nat.mul_add_div hb]
    rw [pred_div_eq_div hb ha
      (mod_base_ne_zero_of_coprime_square hb2 hcop)]
  unfold sliceDeviation fluctuationTable
  rw [sliceCollisionScore_add_square_mul hb, hpred]
  unfold sliceCollisionScore
  push_cast
  ring

/-! ## A directly executable collision check -/

/-- Direct lag-one collision count in the manuscript's positive residue
coordinates. -/
def directLagOneCollisionCount (b p : ℕ) : ℕ :=
  ∑ r ∈ Finset.Ico 1 p,
    if digitBin b p r = digitBin b p ((b * r) % p) then 1 else 0

/-- Direct integer deviation `C_{p,b}(b)-Q`. -/
def directIntegerDeviation (b p : ℕ) : ℤ :=
  (directLagOneCollisionCount b p : ℤ) - (((p - 1) / b : ℕ) : ℤ)

/-- Primes used by the bounded direct regression certificate. -/
def decimalRegressionPrimes : Finset ℕ :=
  (Finset.Icc 101 1000).filter Nat.Prime

/-! ## Reflection and exact means -/

/-- The reduced representatives in `[1,m)`. -/
def reducedResidues (m : ℕ) : Finset ℕ :=
  (Finset.Ico 1 m).filter fun a => Nat.Coprime a m

/-- A permutation whose paired values have constant sum forces the exact
finite mean to be half that constant. -/
theorem finite_mean_of_pair_sum {α : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (F : α → ℚ) (c : ℚ)
    (hpair : ∀ a, F a + F (e a) = c) :
    (Fintype.card α : ℚ)⁻¹ * ∑ a, F a = c / 2 := by
  have hcard : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hreindex : (∑ a, F (e a)) = ∑ a, F a := e.sum_comp F
  have hdouble : 2 * ∑ a, F a = (Fintype.card α : ℚ) * c := by
    calc
      2 * ∑ a, F a = (∑ a, F a) + ∑ a, F a := by ring
      _ = (∑ a, F a) + ∑ a, F (e a) := by rw [hreindex]
      _ = ∑ a, (F a + F (e a)) := by rw [Finset.sum_add_distrib]
      _ = (Fintype.card α : ℚ) * c := by simp [hpair]
  field_simp [hcard]
  linear_combination hdouble

/-- The reflection law with pair sum `-1` gives grand mean `-1/2`. -/
theorem grand_mean_of_reflection {α : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (F : α → ℚ)
    (hreflect : ∀ a, F a + F (e a) = -1) :
    (Fintype.card α : ℚ)⁻¹ * ∑ a, F a = -1 / 2 := by
  simpa using finite_mean_of_pair_sum e F (-1) hreflect

/-- Complement pairing with representative sum `b` gives the manuscript's
remainder mean after subtracting one and dividing by `b`. -/
theorem remainder_mean_of_complement {α : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (u : α → ℚ) (b : ℚ) (hb : b ≠ 0)
    (hpair : ∀ a, u a + u (e a) = b) :
    (Fintype.card α : ℚ)⁻¹ * ∑ a, (u a - 1) / b =
      1 / 2 - 1 / b := by
  have hpair' : ∀ a, (u a - 1) / b + (u (e a) - 1) / b =
      1 - 2 / b := by
    intro a
    field_simp [hb]
    linear_combination hpair a
  rw [finite_mean_of_pair_sum e (fun a => (u a - 1) / b)
    (1 - 2 / b) hpair']
  field_simp

/-! ## Base-ten exact certificates -/

/-- The finite table obeys reflection at every unit modulo one hundred. -/
theorem decimal_table_reflection :
    ∀ a ∈ reducedResidues 100,
      fluctuationTable 10 a + fluctuationTable 10 (100 - a) = -1 := by
  decide

/-- The forty unit representatives modulo one hundred. -/
theorem decimal_reduced_residue_count : (reducedResidues 100).card = 40 := by
  decide

/-- The base-ten table sum is `-20`, hence its exact grand mean is `-1/2`. -/
theorem decimal_table_sum :
    ∑ a ∈ reducedResidues 100, fluctuationTable 10 a = -20 := by
  decide

/-- Restrict the unit table to one final digit. -/
def decimalResidueClass (r : ℕ) : Finset ℕ :=
  (reducedResidues 100).filter fun a => a % 10 = r

/-- Each possible final digit has exactly ten lifts modulo one hundred. -/
theorem decimal_class_cardinalities :
    (decimalResidueClass 1).card = 10 ∧
    (decimalResidueClass 3).card = 10 ∧
    (decimalResidueClass 7).card = 10 ∧
    (decimalResidueClass 9).card = 10 := by
  decide

/-- Exact numerators of the four displayed base-ten class means. -/
theorem decimal_class_table_sums :
    (∑ a ∈ decimalResidueClass 1, fluctuationTable 10 a) = -17 ∧
    (∑ a ∈ decimalResidueClass 3, fluctuationTable 10 a) = -9 ∧
    (∑ a ∈ decimalResidueClass 7, fluctuationTable 10 a) = -1 ∧
    (∑ a ∈ decimalResidueClass 9, fluctuationTable 10 a) = 7 := by
  decide

/-- Exact rational class means from the base-ten table. -/
theorem decimal_class_table_means :
    ((10 : ℚ)⁻¹ * (-17 : ℚ) = -17 / 10) ∧
    ((10 : ℚ)⁻¹ * (-9 : ℚ) = -9 / 10) ∧
    ((10 : ℚ)⁻¹ * (-1 : ℚ) = -1 / 10) ∧
    ((10 : ℚ)⁻¹ * (7 : ℚ) = 7 / 10) := by
  norm_num

/-! ## Correction and drift arithmetic -/

/-- Exact expansion of the constructive-mean correction. -/
theorem correction_expansion {b Q R N : ℕ}
    (hb : 0 < b) (hN : 0 < N) (hR : R < b)
    (hrelation : N + b = b * Q + R) :
    ((Q * R : ℕ) : ℚ) / N =
      (R : ℚ) / b + ((R * (b - R) : ℕ) : ℚ) / (b * N) := by
  have hrelationQ : (N : ℚ) + b = b * Q + R := by
    exact_mod_cast hrelation
  have hbne : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hNne : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp [hbne, hNne]
  rw [Nat.cast_sub (Nat.le_of_lt hR)]
  have hmul := congrArg (fun x : ℚ => (R : ℚ) * x) hrelationQ
  nlinarith [hmul]

/-- The two exact mean contributions combine to the claimed drift
coefficient. -/
theorem drift_coefficient (b : ℚ) (hb : b ≠ 0) :
    (-1 / 2) - (1 / 2 - 1 / b) = -(b - 1) / b := by
  field_simp
  ring

/-- The base-ten drift coefficient is exactly `-9/10`. -/
theorem decimal_drift_coefficient :
    (-1 / 2 : ℚ) - (1 / 2 - 1 / 10) = -9 / 10 := by
  norm_num

/-- For a proper natural remainder, `R/b` is integral exactly in the
zero-remainder case. -/
theorem remainder_term_integral_iff_zero {b R : ℕ}
    (hb : 0 < b) (hR : R < b) :
    (∃ z : ℤ, (z : ℚ) = (R : ℚ) / b) ↔ R = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hRq : (R : ℚ) < (b : ℚ) := by exact_mod_cast hR
    have hz_nonneg_q : (0 : ℚ) ≤ (z : ℚ) := by
      rw [hz]
      positivity
    have hz_lt_one_q : (z : ℚ) < 1 := by
      rw [hz]
      exact (div_lt_one hbq).2 hRq
    have hz_nonneg : (0 : ℤ) ≤ z := by exact_mod_cast hz_nonneg_q
    have hz_lt_one : z < (1 : ℤ) := by exact_mod_cast hz_lt_one_q
    have hz_zero : z = 0 := by omega
    subst z
    field_simp [hbq.ne'] at hz
    norm_num at hz
    exact_mod_cast hz.symm
  · rintro rfl
    exact ⟨0, by norm_num⟩

/-- The correction term `R/b` can be rational without being integral. -/
theorem decimal_remainder_term_is_not_integral :
    (2 : ℚ) / 10 = 1 / 5 ∧
      ¬ ∃ z : ℤ, (z : ℚ) = (2 : ℚ) / 10 := by
  constructor
  · norm_num
  · rintro ⟨z, hz⟩
    have hzbounds : (0 : ℚ) < (z : ℚ) ∧ (z : ℚ) < 1 := by
      rw [hz]
      norm_num
    have hz0 : (0 : ℤ) < z := by exact_mod_cast hzbounds.1
    have hz1 : z < (1 : ℤ) := by exact_mod_cast hzbounds.2
    omega

end NField.Alignment.CollisionFluctuationSum
