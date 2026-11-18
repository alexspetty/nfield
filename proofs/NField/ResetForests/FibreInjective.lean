/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreIntegral
import NField.ResetForests.FibreSampling
/-! # The complete fibre path determines the original source -/

noncomputable section

namespace NField.ResetForests.FibreReconstruction

open scoped BigOperators
open NField.Alignment CommonResetGram SourceMetrics

theorem fibre_path_zero_source {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (c : ℕ → ℝ)
    (hz : ∀ u : ℝ, ∀ v : Fin p, fibrePath p c u v=0) :
    ∀ j ∈ Finset.Icc 1 (p-1), c j=0 := by
  have hpair : fibrePair p c c = fun _ => 0 := by
    funext u
    simp [fibrePair, hz]
  have henergy := continuous_fibre_reconstruction hp c c
  rw [hpair] at henergy
  simp only [intervalIntegral.integral_zero] at henergy
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hi : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpR).mpr (by linarith)
  have hfactor : (p : ℝ)-(p : ℝ)⁻¹ ≠ 0 := by linarith
  have he : continuousWork (p-1) c c=0 := (mul_eq_zero.mp henergy.symm).resolve_left hfactor
  intro j hj
  by_contra hne
  have hN : 2 ≤ p-1 := by have := hp.two_le; omega
  have hQ : (p-1)^2 < p^2 := by nlinarith [Nat.sub_add_cancel hp.one_le]
  have hpos := continuous_work_positive hN hQ c
    (fun j hj => prime_square_source_units hp hj) ⟨j, hj, hne⟩
  have hwork : 0 < continuousWork (p-1) c c := by
    simpa only [continuousWork, pow_two] using hpos
  rw [he] at hwork
  exact (lt_irrefl 0) hwork

theorem fibre_path_source_injective {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (c e : ℕ → ℝ) (h : ∀ u : ℝ, ∀ v : Fin p, fibrePath p c u v=fibrePath p e u v) :
    ∀ j ∈ Finset.Icc 1 (p-1), c j=e j := by
  have hz : ∀ u : ℝ, ∀ v : Fin p, fibrePath p (c-e) u v=0 := by
    intro u v
    rw [fibre_path_sub, h, sub_self]
  have hc := fibre_path_zero_source hp hodd (c-e) hz
  intro j hj
  exact sub_eq_zero.mp (hc j hj)

theorem complete_fibre_map_injective {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    Function.Injective (fun c : Fin (p-1) → ℝ => fibrePath p (cutoffCoefficients (p-1) c)) := by
  intro c e he
  have hc := fibre_path_source_injective hp hodd (cutoffCoefficients (p-1) c)
    (cutoffCoefficients (p-1) e) (fun u v => congrFun (congrFun he u) v)
  funext i
  have hi := hc (i.val+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  simpa only [cutoff_coefficients_succ] using hi

end NField.ResetForests.FibreReconstruction
