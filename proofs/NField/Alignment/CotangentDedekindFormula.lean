/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CotangentGrid

/-! # The classical Dedekind formula with literal real cotangents -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CotangentDedekindFormula
open scoped BigOperators
open CotangentGrid DedekindFourierMoment DedekindCollisionKernel
  DedekindReciprocity CarryBoundarySpectra

theorem complex_cotangent_product (a b : ℝ) :
    (Complex.I/2*(a : ℂ))*(Complex.I/2*(-b : ℂ))=
      (1/4 : ℂ)*((a*b : ℝ) : ℂ) := by
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

theorem dedekind_cotangent_unit {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) :
    dedekindSum u=
      ((1/(4*(m : ℝ))*(∑ x : ZMod m,cotGrid m x.val*cotGrid m (u.val*x).val) : ℝ) : ℂ) := by
  have h := dedekindSum_eq_additiveFourier u⁻¹
  simp only [inv_inv,dedekindSum_inv] at h
  simp_rw [dft_real_cot,cot_grid_neg,Complex.ofReal_neg] at h
  simp_rw [complex_cotangent_product] at h
  rw [← Finset.mul_sum] at h
  rw [h]
  push_cast
  ring

theorem cotangent_unit_multiple {m n : ℕ} [NeZero m] (hn : n.Coprime m)
    (x : ZMod m) :
    cotGrid m ((ZMod.unitOfCoprime n hn).val*x).val=cotGrid m (n*x.val) := by
  rw [ZMod.coe_unitOfCoprime,ZMod.val_mul,ZMod.val_natCast,Nat.mod_mul_mod]
  exact cot_grid_mod (Nat.pos_of_ne_zero (NeZero.ne m)) _

/-- Title: `The real cotangent formula for a Dedekind sum`. -/
theorem arithmetic_dedekind_cotangent {m n : ℕ} (hm : 0 < m) (hn : n.Coprime m) :
    (arithmeticDedekindSum n m : ℝ)=
      1/(4*(m : ℝ))*∑ j ∈ Finset.Ico 1 m,
        Real.cot (Real.pi*(j : ℝ)/(m : ℝ))*
          Real.cot (Real.pi*(n*j : ℕ)/(m : ℝ)) := by
  letI : NeZero m := ⟨hm.ne'⟩
  have h := dedekind_cotangent_unit (ZMod.unitOfCoprime n hn)
  rw [dedekindSum_unitOfCoprime_eq_arithmeticDedekindSum hn] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ratCast_re,Complex.ofReal_re] at hr
  simp_rw [cotangent_unit_multiple hn] at hr
  rw [sum_zmod_real (fun j => cotGrid m j*cotGrid m (n*j))] at hr
  have hset : Finset.range m=insert 0 (Finset.Ico 1 m) := by
    ext j
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Ico]
    omega
  rw [hset,Finset.sum_insert (by simp),cot_grid_zero,zero_mul,zero_add] at hr
  exact hr

end NField.Alignment.CotangentDedekindFormula
