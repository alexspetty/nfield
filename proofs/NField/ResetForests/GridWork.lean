/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.GridFourier
import NField.ResetForests.Targets
import NField.ResetForests.Words
/-! # The literal reset-grid estimate and coherent cutoff

The intrinsic residue estimate is transported to the manuscript's natural
harmonic indices. Midpoint resets and nonunit sample addresses are retained.
-/

noncomputable section

namespace NField.ResetForests.ResetGrid

open scoped BigOperators
open NField.Alignment
open CollisionRampEnergy CommonResetGrid DedekindReciprocity

theorem sum_nonzero_residues {R : Type*} [AddCommMonoid R] {k : ℕ} [NeZero k]
    (f : ℕ → R) (hf : f 0=0) :
    (∑ h : ZMod k, f h.val) = ∑ h ∈ Finset.Icc 1 (k-1), f h := by
  rw [CommonResetBernoulliLifts.sum_residue_values,
    sum_range_eq_sum_Ico_one f (NeZero.pos k) hf]
  congr 1

def liftedCoefficients {k : ℕ} (c : ℕ → ℂ) (h : ZMod k) : ℂ :=
  if h.val=0 then 0 else c h.val

theorem lifted_coefficients_energy {k : ℕ} [NeZero k] (c : ℕ → ℂ) :
    (∑ h : ZMod k, ‖liftedCoefficients c h‖^2) =
      ∑ h ∈ Finset.Icc 1 (k-1), ‖c h‖^2 := by
  change (∑ h : ZMod k, ‖if h.val=0 then 0 else c h.val‖^2)=_
  rw [sum_nonzero_residues (fun n => ‖if n=0 then 0 else c n‖^2) (by simp)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [if_neg (by have := (Finset.mem_Icc.mp hh).1; omega)]

theorem complete_grid_lift {k : ℕ} [NeZero k] (c : ℕ → ℂ) (a : ℕ) :
    completeGridField (liftedCoefficients c) (a : ZMod k) = Core.resetGridField k c a := by
  unfold completeGridField Core.resetGridField
  congr 1
  have he (h : ZMod k) :
      liftedCoefficients c h*CarryBoundarySpectra.centeredSawtooth (h*(a : ZMod k)) =
        c h.val*(midpointRow h.val ((a : ℝ)/(k : ℝ)) : ℂ) := by
    rw [midpointRow_grid]
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
    by_cases hz : h.val=0
    · have hz' : h=0 := by
        apply ZMod.val_injective
        simpa using hz
      subst h
      simp [liftedCoefficients, CarryBoundarySpectra.centeredSawtooth]
    · simp only [liftedCoefficients, if_neg hz]
  simp_rw [he]
  exact sum_nonzero_residues
    (fun h => c h*(midpointRow h ((a : ℝ)/(k : ℝ)) : ℂ)) (by simp [midpointRow])

/-- The complete residue proof implies the exact printed estimate of Lemma7.1. -/
theorem reset_grid_estimate : Core.ResetGridEstimate := by
  intro k hk c
  letI : NeZero k := ⟨by omega⟩
  have hs := complete_grid_energy_bound (liftedCoefficients (k := k) c)
  have hfields : (∑ x : ZMod k, ‖completeGridField (liftedCoefficients c) x‖^2) =
      ∑ a ∈ Finset.range k, ‖Core.resetGridField k c a‖^2 := by
    have he (x : ZMod k) :
        completeGridField (liftedCoefficients c) x = Core.resetGridField k c x.val := by
      simpa only [ZMod.natCast_zmod_val] using complete_grid_lift (k := k) c x.val
    simp_rw [he]
    exact CommonResetBernoulliLifts.sum_residue_values (m := k)
      (fun a => ‖Core.resetGridField k c a‖^2)
  rw [hfields, lifted_coefficients_energy] at hs
  have ht : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne k)⟩
  have hτ : (k.divisors.card : ℝ) ≤ (k.divisors.card : ℝ)^2 := by nlinarith
  exact hs.trans (by gcongr)

theorem cutoff_grid_field (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (a : ℕ) :
    Core.resetGridField k (fun h => if h ≤ N%k then 1 else 0) a =
      (boundaryResponse N ((a : ℝ)/(k : ℝ)) : ℂ) := by
  have hrem := Core.cutoff_word_remainder hk N a
  have hb : boundaryResponse N ((a : ℝ)/(k : ℝ)) =
      boundaryResponse (N%k) ((a : ℝ)/(k : ℝ)) := by
    simp_rw [CommonResetSampling.boundaryResponse_rational (by omega : 0 < k)]
    rw [hrem]
  rw [hb, boundaryResponse]
  unfold Core.resetGridField
  push_cast
  congr 1
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  have he : (Finset.Icc 1 (k-1)).filter (fun h => h ≤ N%k) = Finset.Icc 1 (N%k) := by
    ext h
    have hr := Nat.mod_lt N (by omega : 0 < k)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [he]

theorem cutoff_coefficients_energy (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    (∑ h ∈ Finset.Icc 1 (k-1), ‖(if h ≤ N%k then 1 else 0 : ℂ)‖^2) = (N%k : ℕ) := by
  have hr := Nat.mod_lt N (by omega : 0 < k)
  have ht (h : ℕ) : ‖(if h ≤ N%k then 1 else 0 : ℂ)‖^2 =
      if h ≤ N%k then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  simp_rw [ht]
  rw [← Finset.sum_filter]
  have he : (Finset.Icc 1 (k-1)).filter (fun h => h ≤ N%k) = Finset.Icc 1 (N%k) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  simp [he]

theorem coherent_cutoff_grid_bound (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    (∑ a ∈ Finset.range k, |boundaryResponse N ((a : ℝ)/(k : ℝ))|^2) ≤
      (k : ℝ)*(N%k : ℕ)*(k.divisors.card : ℝ)^2*(harmonic k : ℝ)^2 := by
  have hs := reset_grid_estimate k hk (fun h => if h ≤ N%k then 1 else 0)
  simp_rw [cutoff_grid_field N hk, Complex.norm_real, Real.norm_eq_abs] at hs
  rw [cutoff_coefficients_energy N hk] at hs
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs' := (mul_le_mul_of_nonneg_left hs (le_of_lt hkR))
  field_simp at hs'
  nlinarith

theorem reset_absolute_work_bound (N : ℕ) {k : ℕ} (hk : 2 ≤ k)
    (g : ℕ → ℝ) (hg : ∀ a, |g a| ≤ 1/2) :
    ((N/k : ℕ) : ℝ)*
      (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        |boundaryResponse N ((a : ℝ)/(k : ℝ))*g a|) ≤
      (N : ℝ)/2*Real.sqrt k*(k.divisors.card : ℝ)*(harmonic k : ℝ) := by
  classical
  let s := (Finset.Ico 1 k).filter (fun a => a.Coprime k)
  let B := fun a : ℕ => boundaryResponse N ((a : ℝ)/(k : ℝ))
  have hsub : s ⊆ Finset.range k := by
    intro a ha
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
  have hcard : (s.card : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range k)
  have hB : (∑ a ∈ s, |B a|^2) ≤
      (k : ℝ)*(N%k : ℕ)*(k.divisors.card : ℝ)^2*(harmonic k : ℝ)^2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ => sq_nonneg _)).trans (coherent_cutoff_grid_bound N hk)
  have hg2 : (∑ a ∈ s, |g a|^2) ≤ (k : ℝ)/4 := by
    calc
      _ ≤ ∑ _a ∈ s, (1/4 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        nlinarith [hg a, abs_nonneg (g a)]
      _ = (s.card : ℝ)/4 := by simp; ring
      _ ≤ _ := by gcongr
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => |B a|) (fun a => |g a|)
  have hwork : (∑ a ∈ s, |B a*g a|)^2 ≤
      ((k : ℝ)*(N%k : ℕ)*(k.divisors.card : ℝ)^2*(harmonic k : ℝ)^2)*((k : ℝ)/4) := by
    simp_rw [abs_mul]
    exact hcs.trans (mul_le_mul hB hg2 (by positivity) (by positivity))
  have hm : ((N/k : ℕ) : ℝ)*(k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N k
  have hr : ((N%k : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.mod_lt N (by omega : 0 < k)).le
  have hH : (0 : ℝ) ≤ (harmonic k : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : k ≠ 0)).le
  have hsq :
      (((N/k : ℕ) : ℝ)*(∑ a ∈ s, |B a*g a|))^2 ≤
        ((N : ℝ)/2*Real.sqrt k*(k.divisors.card : ℝ)*(harmonic k : ℝ))^2 := by
    calc
      _ = ((N/k : ℕ) : ℝ)^2*(∑ a ∈ s, |B a*g a|)^2 := mul_pow _ _ _
      _ ≤ ((N/k : ℕ) : ℝ)^2*
          (((k : ℝ)*(N%k : ℕ)*(k.divisors.card : ℝ)^2*(harmonic k : ℝ)^2)*((k : ℝ)/4)) := by
        exact mul_le_mul_of_nonneg_left hwork (sq_nonneg _)
      _ = (((N/k : ℕ) : ℝ)*(k : ℝ))^2*(N%k : ℕ)*
          (k.divisors.card : ℝ)^2*(harmonic k : ℝ)^2/4 := by ring
      _ ≤ (N : ℝ)^2*(k : ℝ)*(k.divisors.card : ℝ)^2*(harmonic k : ℝ)^2/4 := by
        gcongr
      _ = _ := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        ring
  change ((N/k : ℕ) : ℝ)*(∑ a ∈ s, |B a*g a|) ≤ _
  have hright : 0 ≤ (N : ℝ)/2*Real.sqrt k*(k.divisors.card : ℝ)*(harmonic k : ℝ) := by positivity
  nlinarith

theorem midpointRow_abs_bound (Q : ℕ) (x : ℝ) : |midpointRow Q x| ≤ 1/2 := by
  unfold midpointRow affineRow
  split_ifs
  · norm_num
  · rw [abs_le]
    constructor <;> linarith [Int.fract_nonneg ((Q : ℝ)*x), Int.fract_lt_one ((Q : ℝ)*x)]

theorem coherent_reset_absolute_bound (N Q : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    ((N/k : ℕ) : ℝ)*
      (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        |boundaryResponse N ((a : ℝ)/(k : ℝ))*midpointRow Q ((a : ℝ)/(k : ℝ))|) ≤
      (N : ℝ)/2*Real.sqrt k*(k.divisors.card : ℝ)*(harmonic k : ℝ) :=
  reset_absolute_work_bound N hk _ (fun _ => midpointRow_abs_bound _ _)

theorem midpoint_phase_abs_bound (x : ℝ) :
    |midpointRow 1 x| ≤ 1/2 := midpointRow_abs_bound 1 x

/-- The printed absolute-work assertion holds for every integer sampling phase. -/
theorem integer_reset_absolute_bound (N : ℕ) (Q : ℤ) {k : ℕ} (hk : 2 ≤ k) :
    ((N/k : ℕ) : ℝ)*
      (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        |boundaryResponse N ((a : ℝ)/(k : ℝ))*
          midpointRow 1 ((Q : ℝ)*(a : ℝ)/(k : ℝ))|) ≤
      (N : ℝ)/2*Real.sqrt k*(k.divisors.card : ℝ)*(harmonic k : ℝ) :=
  reset_absolute_work_bound N hk _ (fun _ => midpoint_phase_abs_bound _)

end NField.ResetForests.ResetGrid
