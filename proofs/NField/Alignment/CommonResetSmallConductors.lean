/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetEndpoint

/-! # The complete small-conductor contribution -/

noncomputable section

namespace NField.Alignment.CommonResetSmallConductors

open scoped BigOperators
open CommonResetFourier CommonResetConductor CommonResetKernel CommonResetLift
open CommonResetEndpoint DedekindInverseResidueTransform

theorem harmonic_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  positivity

theorem harmonic_monotone : Monotone (fun n : ℕ => (harmonic n : ℝ)) := by
  intro m n hmn
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => by positivity)

theorem abs_sum_le_half_mass {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (hf : ∑ a, f a = 0) (s : Finset α) :
    |∑ a ∈ s, f a| ≤ (∑ a, |f a|)/2 := by
  have hsplit := s.sum_add_sum_compl f
  have habs := s.sum_add_sum_compl (fun a => |f a|)
  rw [hf] at hsplit
  have hneg : (∑ a ∈ sᶜ, f a) = -(∑ a ∈ s, f a) := by linarith
  have hfirst := Finset.abs_sum_le_sum_abs f s
  have hsecond := Finset.abs_sum_le_sum_abs f sᶜ
  rw [hneg, abs_neg] at hsecond
  linarith

/-- Title: `Every permuted terminal prefix uses at most half the kernel mass`. -/
theorem kernel_prefix_bound {t q : ℕ} (ht : 2 ≤ t) (hq : q.Coprime t)
    (r : ℕ) (hr : r < t) :
    |∑ a ∈ Finset.Icc 1 r, conductorKernel t (inverseResidue q t*a)| ≤
      (t : ℝ)^2*(harmonic t : ℝ)^2/8 := by
  classical
  letI : NeZero t := ⟨by omega⟩
  let u : (ZMod t)ˣ := (ZMod.unitOfCoprime q hq)⁻¹
  let f : ZMod t → ℝ := fun a => unitKernel (u.val*a)
  have he (a : ℕ) : conductorKernel t (inverseResidue q t*a) = f (a : ZMod t) := by
    rw [conductorKernel_eq_units ht, Nat.cast_mul]
    dsimp [f, u]
    congr 2
    unfold inverseResidue
    rw [dif_neg (by omega : t ≠ 0), dif_pos hq, ZMod.natCast_zmod_val]
  have hf : (∑ a : ZMod t, f a) = 0 := by
    have h := Equiv.sum_comp u.mulLeft unitKernel
    simpa only [Units.mulLeft_apply, unitKernel_sum_zero ht] using h
  have hmass : (∑ a : ZMod t, |f a|) ≤ (t : ℝ)^2*(harmonic t : ℝ)^2/4 := by
    have h := Equiv.sum_comp u.mulLeft (fun a : ZMod t => |unitKernel a|)
    simp only [Units.mulLeft_apply] at h
    rw [show (∑ a : ZMod t, |f a|) = ∑ a : ZMod t, |unitKernel a| from h]
    exact unitKernel_mass_bound
  simp only [he]
  rw [← prefixIndicator_sum r hr f]
  simp only [prefixIndicator, ite_mul, Finset.sum_ite, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero]
  have hb := abs_sum_le_half_mass f hf
    (Finset.univ.filter (fun a : ZMod t => a.val ∈ Finset.Icc 1 r))
  linarith

def smallConductorSource (N q K : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 2 K, |(2*(harmonic (N/t) : ℝ)/(t : ℝ))*
    ∑ a ∈ Finset.Icc 1 (N%t), conductorKernel t (inverseResidue q t*a)|

theorem sum_natCast_Icc (K : ℕ) :
    (∑ t ∈ Finset.Icc 1 K, (t : ℝ)) = (K : ℝ)*((K : ℝ)+1)/2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K+1), ih]
    push_cast
    ring

/-- Title: `All frequencies at the small conductors satisfy the printed finite bound`. -/
theorem small_conductor_bound (N q K : ℕ)
    (hq : ∀ t ∈ Finset.Icc 2 K, q.Coprime t) :
    smallConductorSource N q K ≤
      (harmonic N : ℝ)*(K : ℝ)*((K : ℝ)+1)*(harmonic K : ℝ)^2/8 := by
  have hterm (t : ℕ) (ht : t ∈ Finset.Icc 2 K) :
      |(2*(harmonic (N/t) : ℝ)/(t : ℝ))*
        ∑ a ∈ Finset.Icc 1 (N%t), conductorKernel t (inverseResidue q t*a)| ≤
        ((harmonic N : ℝ)*(harmonic K : ℝ)^2/4)*(t : ℝ) := by
    have ht2 := (Finset.mem_Icc.mp ht).1
    have htpos : 0 < t := by omega
    have htR : (0 : ℝ) < t := by exact_mod_cast htpos
    have hpre := kernel_prefix_bound ht2 (hq t ht) (N%t) (Nat.mod_lt N htpos)
    rw [abs_mul, abs_of_nonneg (div_nonneg
      (mul_nonneg (by norm_num) (harmonic_nonneg _)) htR.le)]
    calc
      _ ≤ (2*(harmonic (N/t) : ℝ)/(t : ℝ))*
          ((t : ℝ)^2*(harmonic t : ℝ)^2/8) :=
        mul_le_mul_of_nonneg_left hpre (div_nonneg
          (mul_nonneg (by norm_num) (harmonic_nonneg _)) htR.le)
      _ = (harmonic (N/t) : ℝ)*(t : ℝ)*(harmonic t : ℝ)^2/4 := by
        field_simp
        ring
      _ ≤ (harmonic N : ℝ)*(t : ℝ)*(harmonic K : ℝ)^2/4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (harmonic_monotone (Nat.div_le_self N t)) htR.le
        · simpa only [pow_two] using mul_self_le_mul_self (harmonic_nonneg t)
            (harmonic_monotone (Finset.mem_Icc.mp ht).2)
        · exact sq_nonneg _
        · exact mul_nonneg (harmonic_nonneg N) htR.le
      _ = _ := by ring
  calc
    _ ≤ ∑ t ∈ Finset.Icc 2 K, ((harmonic N : ℝ)*(harmonic K : ℝ)^2/4)*(t : ℝ) :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ t ∈ Finset.Icc 1 K, ((harmonic N : ℝ)*(harmonic K : ℝ)^2/4)*(t : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        have h := Finset.mem_Icc.mp ht
        exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
      · intro t _ _
        exact mul_nonneg (div_nonneg (mul_nonneg (harmonic_nonneg _) (sq_nonneg _))
          (by norm_num)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum, sum_natCast_Icc]
      ring

end NField.Alignment.CommonResetSmallConductors
