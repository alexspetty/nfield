/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealSawtoothDistribution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Periodic integral symmetries for real sawtooth products -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealSawtoothIntegralSymmetry
open scoped BigOperators Topology Classical
open MeasureTheory Set CollisionDedekindPairing RealSawtoothDistribution

theorem periodic_integral_shift {f : ℝ→ℝ} (hf : Function.Periodic f 1) (d : ℝ) :
    (∫ x in (0:ℝ)..1, f (x+d))=∫ x in (0:ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_comm (1:ℝ) d] using hf.intervalIntegral_add_eq d 0

theorem periodic_integral_mul {f : ℝ→ℝ} (hf : Function.Periodic f 1)
    (hi : ∀ a b, IntervalIntegrable f volume a b) {n : ℕ} (hn : 0<n) :
    (∫ x in (0:ℝ)..1, f ((n:ℝ)*x))=∫ x in (0:ℝ)..1, f x := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have h := hf.intervalIntegral_add_zsmul_eq (n:ℤ) 0 hi
  simp only [zero_add,zsmul_eq_mul,Int.cast_natCast,mul_one] at h
  rw [intervalIntegral.integral_comp_mul_left _ hnR,mul_zero,mul_one,h,smul_eq_mul]
  field_simp

theorem sawtooth_pair_periodic (r s : ℕ) :
    Function.Periodic (fun x => periodicSawtooth ((r:ℝ)*x)*periodicSawtooth ((s:ℝ)*x)) 1 := by
  intro x
  simp only [mul_add,mul_one,sawtooth_add_nat]

theorem sawtooth_mod_shift (x : ℝ) {r : ℕ} (hr : 0<r) (a : ℕ) :
    periodicSawtooth (x+(a:ℝ)/r)=periodicSawtooth (x+((a%r:ℕ):ℝ)/r) := by
  have hrR : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  have hsplit : (a:ℝ)=(r:ℝ)*(a/r:ℕ)+(a%r:ℕ) := by exact_mod_cast (Nat.div_add_mod a r).symm
  have he : x+(a:ℝ)/r=(x+((a%r:ℕ):ℝ)/r)+(a/r:ℕ) := by
    field_simp
    nlinarith [hsplit]
  rw [he,sawtooth_add_nat]

theorem sawtooth_twisted_distribution {r s : ℕ} (hr : 0<r) (hcop : s.Coprime r) (x : ℝ) :
    (∑ j ∈ Finset.range r, periodicSawtooth (x+(s:ℝ)*j/r))=periodicSawtooth ((r:ℝ)*x) := by
  letI : NeZero r := ⟨hr.ne'⟩
  let u := ZMod.unitOfCoprime s hcop
  have hu (j : ZMod r) : (u.val*j).val=(s*j.val)%r := by
    have he : u.val*j=((s*j.val:ℕ):ZMod r) := by simp [u]
    rw [he,ZMod.val_natCast]
  calc
    _ = ∑ j ∈ Finset.range r, periodicSawtooth (x+((s*j%r:ℕ):ℝ)/r) := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [Nat.cast_mul] using sawtooth_mod_shift x hr (s*j)
    _ = ∑ j : ZMod r, periodicSawtooth (x+((s*j.val%r:ℕ):ℝ)/r) :=
      (ProfiniteRemainderMeasure.sum_zmod_val r _).symm
    _ = ∑ j : ZMod r, periodicSawtooth (x+((u.val*j).val:ℝ)/r) := by simp only [hu]
    _ = ∑ j : ZMod r, periodicSawtooth (x+(j.val:ℝ)/r) :=
      Equiv.sum_comp u.mulLeft (fun j : ZMod r => periodicSawtooth (x+(j.val:ℝ)/r))
    _ = ∑ j ∈ Finset.range r, periodicSawtooth (x+(j:ℝ)/r) :=
      ProfiniteRemainderMeasure.sum_zmod_val r (fun j : ℕ => periodicSawtooth (x+(j:ℝ)/r))
    _ = _ := sawtooth_distribution hr x

end NField.Alignment.RealSawtoothIntegralSymmetry
