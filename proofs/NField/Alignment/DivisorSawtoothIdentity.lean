/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.DivisorHyperbolaIdentity
import NField.Alignment.DivisorHarmonicMain
import NField.Alignment.ReciprocalFloorSmoothing

/-! # The real-cutoff divisor error as an exact floor-sawtooth sum -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorSawtoothIdentity
open scoped BigOperators Classical
open DivisorHyperbolaIdentity DivisorHarmonicMain ReciprocalFloorSmoothing

theorem sum_Icc_eq_range {A : Type*} [AddCommMonoid A] (f : ℕ → A) (M : ℕ) :
    (∑ a ∈ Finset.Icc 1 M,f a)=∑ i ∈ Finset.range M,f (i+1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_range_succ,ih]

theorem floor_saw_decomposition (x : ℝ) (hx : 0≤x) (a : ℕ) :
    ((⌊x⌋₊/a : ℕ) : ℝ)=x/(a : ℝ)-1/2-floorSaw (x/(a : ℝ)) := by
  rw [← Nat.floor_div_natCast,natCast_floor_eq_intCast_floor (by positivity)]
  unfold floorSaw Int.fract
  ring

theorem harmonic_saw_sum (x : ℝ) (hx : 0≤x) (M : ℕ) :
    (∑ a ∈ Finset.Icc 1 M,((⌊x⌋₊/a : ℕ) : ℝ))=
      x*(harmonic M : ℝ)-(M : ℝ)/2-floorSawPrefix 0 M x := by
  simp_rw [floor_saw_decomposition x hx]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  have hmain : (∑ a ∈ Finset.Icc 1 M,x/(a : ℝ))=x*(harmonic M : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
      Finset.mul_sum,div_eq_mul_inv]
  have hsaw : (∑ a ∈ Finset.Icc 1 M,floorSaw (x/(a : ℝ)))=floorSawPrefix 0 M x := by
    rw [sum_Icc_eq_range]
    simp only [floorSawPrefix,zero_add]
  rw [hmain,hsaw]
  simp [div_eq_mul_inv]

theorem real_divisor_sawtooth_identity {M : ℕ} {x : ℝ} (hM : 1≤M)
    (hlo : (M : ℝ)^2≤x) (hhi : x<((M : ℝ)+1)^2) :
    divisorCount ⌊x⌋₊=2*x*(harmonic M : ℝ)-(M : ℝ)-(M : ℝ)^2-
      2*floorSawPrefix 0 M x := by
  have hm : (0 : ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hx : 0<x := (sq_pos_of_pos hm).trans_le hlo
  have hlow : M^2≤⌊x⌋₊ := (Nat.le_floor_iff hx.le).mpr (by exact_mod_cast hlo)
  have hhigh : ⌊x⌋₊<(M+1)^2 := by
    have hh := (Nat.floor_le hx.le).trans_lt hhi
    exact_mod_cast hh
  have hMN : M≤⌊x⌋₊ := by nlinarith
  rw [divisor_hyperbola ⌊x⌋₊ M hMN hlow hhigh,harmonic_saw_sum x hx.le]
  ring

theorem real_divisor_error_bound {M : ℕ} {x : ℝ} (hM : 1≤M)
    (hlo : (M : ℝ)^2≤x) (hhi : x<((M : ℝ)+1)^2) :
    |divisorCount ⌊x⌋₊-(x*Real.log x+(2*Real.eulerMascheroniConstant-1)*x)|≤
      14+2*|floorSawPrefix 0 M x| := by
  rw [real_divisor_sawtooth_identity hM hlo hhi]
  have he : 2*x*(harmonic M : ℝ)-(M : ℝ)-(M : ℝ)^2-2*floorSawPrefix 0 M x-
      (x*Real.log x+(2*Real.eulerMascheroniConstant-1)*x)=
      (2*x*(harmonic M : ℝ)-(M : ℝ)-(M : ℝ)^2-
        (x*Real.log x+(2*Real.eulerMascheroniConstant-1)*x))+(-2*floorSawPrefix 0 M x) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  norm_num
  exact bounded_hyperbola_main hM hlo hhi

end NField.Alignment.DivisorSawtoothIdentity
