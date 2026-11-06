/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetConductor

/-! # Oddness, complete-period cancellation and kernel mass -/

noncomputable section

namespace NField.Alignment.CommonResetKernel

open scoped BigOperators
open CommonResetFourier CommonResetConductor DedekindFourierMoment
open BernoulliCurvature PrimitiveAdditiveConvolution

theorem cotangentResidue_odd {m : ℕ} [NeZero m] (hm : 2 ≤ m) (x : ZMod m) :
    cotangentResidue (-x) = -cotangentResidue x := by
  apply Complex.ofReal_injective
  push_cast
  apply mul_left_cancel₀ (show Complex.I/2 ≠ 0 by norm_num)
  rw [← dft_cotangent, mul_neg, ← dft_cotangent]
  exact dft_sawtooth_odd hm x

theorem cotangentResidue_sum_zero {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    (∑ x : ZMod m, cotangentResidue x) = 0 := by
  have h := Equiv.sum_comp (Equiv.neg (ZMod m)) cotangentResidue
  simp only [Equiv.neg_apply, cotangentResidue_odd hm, Finset.sum_neg_distrib] at h
  linarith

theorem sum_primitive_eq_units {m : ℕ} [NeZero m] (hm : 2 ≤ m) (f : ZMod m → ℝ) :
    (∑ a ∈ (Finset.range m).filter (fun a => a.Coprime m), f (a : ZMod m)) =
      ∑ u : (ZMod m)ˣ, f u.val := by
  letI : Fact (1 < m) := ⟨by omega⟩
  have h := (primitiveNatEquiv m hm).sum_comp (fun u : (ZMod m)ˣ => f u.val)
  rw [← h, reducedResidues_eq_Ico hm,
    Finset.sum_subtype ((Finset.Ico 1 m).filter (fun a => a.Coprime m)) (by intro; rfl)]
  apply Finset.sum_congr rfl
  intro a _
  simp [primitiveNatEquiv, ZMod.coe_unitOfCoprime]

def unitKernel {m : ℕ} [NeZero m] (h : ZMod m) : ℝ :=
  (1/4 : ℝ)*∑ u : (ZMod m)ˣ, cotangentResidue u.val*cotangentResidue (h*u.val)

/-- Title: `The exact-order kernel is the intrinsic unit cotangent sum`. -/
theorem conductorKernel_eq_units {m : ℕ} [NeZero m] (hm : 2 ≤ m) (h : ℕ) :
    conductorKernel m h = unitKernel (h : ZMod m) := by
  unfold conductorKernel unitKernel
  congr 1
  rw [← sum_primitive_eq_units hm (fun x : ZMod m =>
    cotangentResidue x*cotangentResidue ((h : ZMod m)*x))]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Nat.cast_mul, cotangentResidue_nat, cotangentResidue_nat]

/-- Title: `The exact-order kernel is odd in its numerator`. -/
theorem unitKernel_odd {m : ℕ} [NeZero m] (hm : 2 ≤ m) (h : ZMod m) :
    unitKernel (-h) = -unitKernel h := by
  unfold unitKernel
  simp only [neg_mul, cotangentResidue_odd hm, mul_neg, Finset.sum_neg_distrib]

/-- Title: `Every full period of the exact-order kernel cancels`. -/
theorem unitKernel_sum_zero {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    (∑ h : ZMod m, unitKernel h) = 0 := by
  unfold unitKernel
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hzero (u : (ZMod m)ˣ) : (∑ h : ZMod m, cotangentResidue (h*u.val)) = 0 := by
    have he := Equiv.sum_comp u.mulLeft cotangentResidue
    simp only [Units.mulLeft_apply] at he
    simpa only [mul_comm, cotangentResidue_sum_zero hm] using he
  simp only [← Finset.mul_sum, hzero, mul_zero, Finset.sum_const_zero]

theorem conductorKernel_sum_zero {m : ℕ} (hm : 0 < m) :
    (∑ h ∈ Finset.range m, conductorKernel m h) = 0 := by
  by_cases hm1 : m = 1
  · subst m
    simp [conductorKernel_one]
  · letI : NeZero m := ⟨hm.ne'⟩
    rw [← CommonResetGrid.sum_residue_values]
    simp only [conductorKernel_eq_units (by omega : 2 ≤ m), ZMod.natCast_zmod_val]
    exact unitKernel_sum_zero (by omega)

/-- Title: `The cotangent mass has the printed harmonic bound`. -/
theorem cotangent_mass_bound {m : ℕ} [NeZero m] :
    (∑ x : ZMod m, |cotangentResidue x|) ≤ (m : ℝ)*(harmonic m : ℝ) := by
  have he (x : ZMod m) :
      ‖ZMod.dft (CarryBoundarySpectra.centeredSawtooth : ZMod m → ℂ) x‖ =
        |cotangentResidue x|/2 := by
    rw [dft_cotangent, norm_mul, norm_div]
    simp [Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
  have hb := sawtoothFourierNormMass_le (NeZero.pos m)
  rw [← dft_centeredSawtooth_normMass_eq] at hb
  simp only [he, ← Finset.sum_div] at hb
  linarith

theorem unit_cotangent_mass_le_all {m : ℕ} [NeZero m] :
    (∑ u : (ZMod m)ˣ, |cotangentResidue u.val|) ≤ ∑ x : ZMod m, |cotangentResidue x| := by
  classical
  have hu : Function.Injective (fun u : (ZMod m)ˣ => u.val) := Units.val_injective
  have he : (∑ u : (ZMod m)ˣ, |cotangentResidue u.val|) =
      ∑ x ∈ Finset.univ.image (fun u : (ZMod m)ˣ => u.val), |cotangentResidue x| := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => hu h
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => abs_nonneg _)

/-- Title: `The exact-order kernel has bounded complete absolute mass`. -/
theorem unitKernel_mass_bound {m : ℕ} [NeZero m] :
    (∑ h : ZMod m, |unitKernel h|) ≤ (m : ℝ)^2*(harmonic m : ℝ)^2/4 := by
  have hrow (h : ZMod m) : |unitKernel h| ≤
      (1/4 : ℝ)*∑ u : (ZMod m)ˣ, |cotangentResidue u.val| * |cotangentResidue (h*u.val)| := by
    unfold unitKernel
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)]
    gcongr
    simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
      (fun u : (ZMod m)ˣ => cotangentResidue u.val*cotangentResidue (h*u.val)) Finset.univ
  have hperm (u : (ZMod m)ˣ) :
      (∑ h : ZMod m, |cotangentResidue (h*u.val)|) =
        ∑ h : ZMod m, |cotangentResidue h| := by
    have he := Equiv.sum_comp u.mulLeft (fun h => |cotangentResidue h|)
    simpa only [Units.mulLeft_apply, mul_comm] using he
  calc
    _ ≤ ∑ h : ZMod m, (1/4 : ℝ)*∑ u : (ZMod m)ˣ,
        |cotangentResidue u.val| * |cotangentResidue (h*u.val)| :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = (1/4 : ℝ)*(∑ u : (ZMod m)ˣ, |cotangentResidue u.val|)*
        (∑ h : ZMod m, |cotangentResidue h|) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [← Finset.mul_sum, hperm]
      rw [← Finset.sum_mul]
      ring
    _ ≤ (1/4 : ℝ)*((m : ℝ)*(harmonic m : ℝ))*((m : ℝ)*(harmonic m : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          ((unit_cotangent_mass_le_all (m := m)).trans (cotangent_mass_bound (m := m)))
          (by norm_num)
      · exact cotangent_mass_bound (m := m)
      · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      · exact mul_nonneg (by norm_num) (le_trans
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (cotangent_mass_bound (m := m)))
    _ = _ := by ring

end NField.Alignment.CommonResetKernel
