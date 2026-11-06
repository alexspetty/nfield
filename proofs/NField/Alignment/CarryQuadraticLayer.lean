/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindInverseResidueTransform
import NField.Alignment.SawtoothLValue

/-! # The unit correlation in the quadratic carry layer

The unit condition is removed by the existing finite Möbius indicator. Each
multiple-of-a-divisor row is then the classical Dedekind sum at the quotient
modulus, with the midpoint value at zero preserved.
-/

noncomputable section
namespace NField.Alignment.CarryQuadraticLayer
open scoped BigOperators ZMod
open CollisionCharacterStructure CarryBoundarySpectra DedekindReciprocity
  DedekindInverseResidueTransform SawtoothLValue

/-- The rational sawtooth is the same midpoint function at every natural residue. -/
theorem rationalSawtooth_cast {m : ℕ} [NeZero m] (a : ℕ) :
    (rationalSawtooth a m : ℂ) = centeredSawtooth (a : ZMod m) := by
  rw [← rationalSawtooth_val_eq_centeredSawtooth]
  simp only [rationalSawtooth, ZMod.val_natCast, Nat.mod_mod]

/-- Exact reindexing from the unit group to its coprime least residues. -/
theorem unit_sum_eq_coprime_range {m : ℕ} [NeZero m] (f : ℕ → ℂ) :
    (∑ a : UnitClass m, f a.val.val) =
      ∑ a ∈ (Finset.range m).filter (fun a => a.Coprime m), f a := by
  classical
  apply Finset.sum_bij (fun u _ => u.val.val)
  · intro u _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr u.val.val_lt,
      ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ h
    exact Units.ext (ZMod.val_injective m h)
  · intro a ha
    have halt : a < m := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hcop : a.Coprime m := (Finset.mem_filter.mp ha).2
    refine ⟨ZMod.unitOfCoprime a hcop, Finset.mem_univ _, ?_⟩
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt halt]
  · intro a _
    rfl

/-- Title: `Möbius formula for the unit sawtooth correlation`. -/
theorem coprime_sawtooth_moebius {m h : ℕ} (hm : 0 < m) :
    (∑ a ∈ (Finset.range m).filter (fun a => a.Coprime m),
      (rationalSawtooth a m : ℂ) * rationalSawtooth (h * a) m) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (arithmeticDedekindSum h (m / d) : ℂ) := by
  classical
  let f : ℕ → ℂ := fun a =>
    (rationalSawtooth a m : ℂ) * rationalSawtooth (h * a) m
  change (∑ a ∈ (Finset.range m).filter (fun a => a.Coprime m), f a) = _
  rw [Finset.sum_filter]
  calc
    (∑ a ∈ Finset.range m, if a.Coprime m then f a else 0) =
        ∑ a ∈ Finset.range m, f a * (if a.Coprime m then (1 : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
    _ = ∑ a ∈ Finset.range m, f a *
        ∑ d ∈ m.divisors, if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0 := by
          simp_rw [complex_coprime_indicator_moebius hm]
    _ = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ a ∈ Finset.range m, if d ∣ a then f a else 0 := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d _
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp [mul_comm]
    _ = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (arithmeticDedekindSum h (m / d) : ℂ) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdpos := Nat.pos_of_mem_divisors hd
          have hdm : d ∣ m := (Nat.mem_divisors.mp hd).1
          have hqpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hdm) hdpos
          rw [sum_range_divisible_reindex hdpos hdm]
          congr 1
          simp only [arithmeticDedekindSum, Rat.cast_sum, Rat.cast_mul]
          apply Finset.sum_congr rfl
          intro a _
          dsimp [f]
          have hmfactor : m = d * (m / d) := (Nat.mul_div_cancel' hdm).symm
          conv_lhs => rw [hmfactor]
          rw [rationalSawtooth_scale hdpos hqpos,
            show h * (d * a) = d * (h * a) by ring,
            rationalSawtooth_scale hdpos hqpos]

/-- Title: `Actual unit group correlation as Dedekind sums`. -/
theorem unit_sawtooth_correlation_moebius {m : ℕ} [NeZero m]
    (x y : UnitClass m) :
    (∑ a : UnitClass m, centeredSawtooth (x.val * a.val) *
      centeredSawtooth (y.val * a.val)) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (arithmeticDedekindSum (y * x⁻¹).val.val (m / d) : ℂ) := by
  classical
  let h : UnitClass m := y * x⁻¹
  have hr := Equiv.sum_comp (Equiv.mulLeft x⁻¹)
    (fun a : UnitClass m => centeredSawtooth (x.val * a.val) *
      centeredSawtooth (y.val * a.val))
  have hpoint (a : UnitClass m) :
      centeredSawtooth (x.val * (x⁻¹ * a).val) *
        centeredSawtooth (y.val * (x⁻¹ * a).val) =
      centeredSawtooth a.val * centeredSawtooth (h.val * a.val) := by
    simp only [Units.val_mul, ← mul_assoc]
    rw [← Units.val_mul x x⁻¹]
    simp [h, Units.val_mul]
  rw [← hr]
  change (∑ a : UnitClass m, centeredSawtooth (x.val * (x⁻¹ * a).val) *
    centeredSawtooth (y.val * (x⁻¹ * a).val)) = _
  simp_rw [hpoint]
  have ht (a : UnitClass m) :
      centeredSawtooth a.val * centeredSawtooth (h.val * a.val) =
      (rationalSawtooth a.val.val m : ℂ) * rationalSawtooth (h.val.val * a.val.val) m := by
    rw [rationalSawtooth_cast, rationalSawtooth_cast]
    simp
  simp_rw [ht]
  rw [unit_sum_eq_coprime_range (fun a =>
    (rationalSawtooth a m : ℂ) * rationalSawtooth (h.val.val * a) m)]
  exact coprime_sawtooth_moebius (NeZero.pos m)

/-- Title: `Primitive Bernoulli magnitude and the Dirichlet L value`. -/
theorem primitive_bernoulli_l_value_norm {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (χ : Character m) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖bernoulliOne χ⁻¹‖ = Real.sqrt m / Real.pi *
      ‖DirichletCharacter.LFunction χ 1‖ := by
  have hi : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have h := bernoulliOne_normSq_eq_LFunction hm (inverse_isPrimitive hprim) hi
  simp only [inv_inv, Complex.normSq_eq_norm_sq] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  exact h

end NField.Alignment.CarryQuadraticLayer
