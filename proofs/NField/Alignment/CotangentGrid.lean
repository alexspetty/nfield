/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.DedekindInverseResidueTransform

/-! # Literal real cotangents on a residue grid -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CotangentGrid
open scoped BigOperators
open DedekindFourierMoment DedekindInverseResidueTransform
  CarryBoundarySpectra

def cotGrid (m n : ℕ) : ℝ := Real.cot (Real.pi*(n : ℝ)/(m : ℝ))

theorem cot_grid_zero (m : ℕ) : cotGrid m 0=0 := by
  simp [cotGrid,Real.cot_eq_cos_div_sin]

theorem cot_grid_mod {m : ℕ} (hm : 0 < m) (n : ℕ) : cotGrid m (n%m)=cotGrid m n := by
  have hmR : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  have he : Real.pi*((n%m : ℕ) : ℝ)/(m : ℝ)=
      Real.pi*(n : ℝ)/(m : ℝ)-((n/m : ℕ) : ℝ)*Real.pi := by
    have h := Nat.mod_add_div n m
    have hR : ((n%m : ℕ) : ℝ)+(m : ℝ)*((n/m : ℕ) : ℝ)=(n : ℝ) := by
      exact_mod_cast h
    field_simp
    nlinarith [congrArg (fun x : ℝ => Real.pi*x) hR]
  unfold cotGrid
  rw [he,← Real.tan_inv_eq_cot,Real.tan_sub_nat_mul_pi,Real.tan_inv_eq_cot]

theorem cot_grid_mul_scale {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (r : ℕ) :
    cotGrid (d*q) (d*r)=cotGrid q r := by
  unfold cotGrid
  congr 1
  push_cast
  field_simp

theorem cot_grid_neg {m : ℕ} [NeZero m] (x : ZMod m) :
    cotGrid m (-x).val= -cotGrid m x.val := by
  by_cases hx : x=0
  · subst x
    simp [cot_grid_zero]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  rw [ZMod.neg_val,if_neg hx]
  have he : Real.pi*((m-x.val : ℕ) : ℝ)/(m : ℝ)=
      Real.pi-Real.pi*(x.val : ℝ)/(m : ℝ) := by
    rw [Nat.cast_sub x.val_lt.le]
    field_simp
  unfold cotGrid
  rw [he,← Real.tan_inv_eq_cot,← Real.tan_inv_eq_cot,Real.tan_pi_sub,inv_neg]

theorem sawtooth_fourier_real_cot {m n : ℕ} (hm : 0 < m) (hn : n < m) :
    sawtoothFourier m n=Complex.I/2*(cotGrid m n : ℂ) := by
  by_cases hz : n=0
  · subst n
    rw [sawtoothFourier_zero hm,cot_grid_zero]
    simp
  rw [sawtoothFourier_eq_cotangent hm (Nat.pos_of_ne_zero hz) hn]
  congr 1
  rw [cotGrid,Complex.ofReal_cot]
  congr 1
  push_cast
  ring

theorem dft_real_cot {m : ℕ} [NeZero m] (x : ZMod m) :
    ZMod.dft (centeredSawtooth : ZMod m → ℂ) x=
      Complex.I/2*(cotGrid m x.val : ℂ) := by
  have h := sawtooth_fourier_real_cot (Nat.pos_of_ne_zero (NeZero.ne m)) x.val_lt
  rw [sawtoothFourier_eq_dft,ZMod.natCast_zmod_val] at h
  exact h

theorem norm_sawtooth_fourier_real_cot {m n : ℕ} (hm : 0 < m) (hn : n < m) :
    ‖sawtoothFourier m n‖=|cotGrid m n|/2 := by
  rw [sawtooth_fourier_real_cot hm hn,norm_mul,norm_div,Complex.norm_I]
  norm_num [Complex.norm_real,Real.norm_eq_abs]
  ring

/-- Title: `The literal cotangent frequency has the circular-distance bound`. -/
theorem cotangent_circular_bound {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    |cotGrid m n| ≤ (m : ℝ)/(2*(min n (m-n) : ℕ)) := by
  have h := norm_sawtoothFourier_le hm hn hnm
  rw [norm_sawtooth_fourier_real_cot hm hnm] at h
  have he : (m : ℝ)/(2*(min n (m-n) : ℕ))=
      2*((m : ℝ)/(4*(circularDistance m n : ℝ))) := by
    unfold circularDistance
    ring
  rw [he]
  linarith

theorem sum_zmod_real {m : ℕ} [NeZero m] (f : ℕ → ℝ) :
    (∑ x : ZMod m,f x.val)=∑ n ∈ Finset.range m,f n := by
  have he := (ZMod.finEquiv m).toEquiv.sum_comp (fun x : ZMod m => f x.val)
  have hv (x : Fin m) : ((ZMod.finEquiv m).toEquiv x).val=x.val := by
    rw [show ((ZMod.finEquiv m).toEquiv x : ZMod m)=(x.val : ZMod m) by
      exact ConductorDepthSawtooth.finEquiv_eq_natCast x]
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt x.isLt]
  simp_rw [hv] at he
  exact he.symm.trans (Fin.sum_univ_eq_sum_range f m)

end NField.Alignment.CotangentGrid
