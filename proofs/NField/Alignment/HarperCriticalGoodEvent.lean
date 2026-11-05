/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFrequencyCodes

/-!
# The actual critical good event and its exact countable representation

The event is quantified over the entire unit frequency interval and every
remaining block scale. At each scale only attainable integer codes are
used; equality of codes determines all subsequent approximations. This
gives the exact event, not a stronger event on an unrelated full grid.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperCriticalGoodEvent
open scoped BigOperators
open MeasureTheory Set SteinhausMoment HarperFrequencyRounding HarperFrequencyMesh
  HarperFrequencyCodes HarperPrimeBlockLaw

def suffixLog (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) (ω : PhaseSpace) : ℝ :=
  ∑ l ∈ Finset.Icc j M, blockLog x l (approximation x t l) ω

def suffixProduct (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) (ω : PhaseSpace) : ℂ :=
  ∏ l ∈ Finset.Icc j M, blockProduct x l (approximation x t l) ω

def goodEvent (x : ℝ) (M : ℕ) (A : ℕ → ℝ) : Set PhaseSpace :=
  {ω | ∀ t : ℝ, |t| ≤ 1/2 → ∀ j ≤ M, |suffixLog x M t j ω| ≤ A j}

def sourceAllowance (x a : ℝ) (j : ℕ) : ℝ :=
  Real.log (logScale x j)+a+2*Real.log (Real.log (logScale x j))

def sourceGoodEvent (x : ℝ) (M : ℕ) (a : ℝ) : Set PhaseSpace :=
  goodEvent x M (sourceAllowance x a)

theorem suffixLog_measurable (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) :
    Measurable (suffixLog x M t j) :=
  Finset.measurable_sum _ (fun l _ => blockLog_measurable x l _)

theorem suffixProduct_ne_zero (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) (ω : PhaseSpace) :
    suffixProduct x M t j ω ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun l _ => blockProduct_ne_zero x l _ ω)

theorem suffixLog_eq_log_norm (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) (ω : PhaseSpace) :
    suffixLog x M t j ω = Real.log ‖suffixProduct x M t j ω‖ := by
  rw [suffixProduct,norm_prod,Real.log_prod (fun l _ => norm_ne_zero_iff.mpr (blockProduct_ne_zero x l _ ω))]
  rfl

theorem suffix_barrier_iff (x : ℝ) (M : ℕ) (t : ℝ) (j : ℕ) (ω : PhaseSpace) (A : ℝ) :
    |suffixLog x M t j ω| ≤ A ↔
      Real.exp (-A) ≤ ‖suffixProduct x M t j ω‖ ∧ ‖suffixProduct x M t j ω‖ ≤ Real.exp A := by
  rw [abs_le,suffixLog_eq_log_norm]
  have hp : 0 < ‖suffixProduct x M t j ω‖ := norm_pos_iff.mpr (suffixProduct_ne_zero x M t j ω)
  constructor
  · rintro ⟨hl,hu⟩
    constructor
    · simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hl
    · simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hu
  · rintro ⟨hl,hu⟩
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hl
    · simpa only [Real.log_exp] using Real.log_le_log hp hu

theorem suffixLog_eq_of_code {x s t : ℝ} (M j : ℕ)
    (h : roundCode (mesh x) s j = roundCode (mesh x) t j) (ω : PhaseSpace) :
    suffixLog x M s j ω = suffixLog x M t j ω := by
  apply Finset.sum_congr rfl
  intro l hl
  have ht := rounded_tail_from_code (Finset.mem_Icc.mp hl).1 h
  change blockLog x l (rounded (mesh x) s (l+1)) ω = blockLog x l (rounded (mesh x) t (l+1)) ω
  rw [ht]

theorem goodEvent_iff_codes (x : ℝ) (M : ℕ) (A : ℕ → ℝ) (ω : PhaseSpace) :
    ω ∈ goodEvent x M A ↔ ∀ j ≤ M, ∀ k ∈ attainableCodes (mesh x) j,
      |suffixLog x M (representative (mesh x) j k) j ω| ≤ A j := by
  constructor
  · intro h j hj k hk
    exact h _ (representative_spec hk).1 j hj
  · intro h t ht j hj
    have hk : roundCode (mesh x) t j ∈ attainableCodes (mesh x) j := ⟨t,ht,rfl⟩
    have hs := h j hj _ hk
    rwa [suffixLog_eq_of_code M j (representative_spec hk).2 ω] at hs

theorem goodEvent_eq_iInter (x : ℝ) (M : ℕ) (A : ℕ → ℝ) :
    goodEvent x M A = ⋂ j ≤ M, ⋂ k ∈ attainableCodes (mesh x) j,
      {ω | |suffixLog x M (representative (mesh x) j k) j ω| ≤ A j} := by
  ext ω
  simp only [Set.mem_iInter,Set.mem_setOf_eq,goodEvent_iff_codes]

theorem goodEvent_measurable (x : ℝ) (M : ℕ) (A : ℕ → ℝ) : MeasurableSet (goodEvent x M A) := by
  rw [goodEvent_eq_iInter]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (suffixLog_measurable x M _ j).abs measurable_const

theorem goodEvent_product_iff (x : ℝ) (M : ℕ) (A : ℕ → ℝ) (ω : PhaseSpace) :
    ω ∈ goodEvent x M A ↔ ∀ t : ℝ, |t| ≤ 1/2 → ∀ j ≤ M,
      Real.exp (-A j) ≤ ‖suffixProduct x M t j ω‖ ∧
        ‖suffixProduct x M t j ω‖ ≤ Real.exp (A j) := by
  simp only [goodEvent,Set.mem_setOf_eq,suffix_barrier_iff]

theorem exp_sourceAllowance {x : ℝ} (a : ℝ) (j : ℕ) (hj : 1 < logScale x j) :
    Real.exp (sourceAllowance x a j) =
      logScale x j*Real.exp a*(Real.log (logScale x j))^2 := by
  unfold sourceAllowance
  rw [Real.exp_add,Real.exp_add,Real.exp_log (by linarith : 0 < logScale x j)]
  rw [show 2*Real.log (Real.log (logScale x j)) =
    Real.log (Real.log (logScale x j))+Real.log (Real.log (logScale x j)) by ring,
    Real.exp_add,Real.exp_log (Real.log_pos hj)]
  ring

theorem sourceGoodEvent_measurable (x : ℝ) (M : ℕ) (a : ℝ) :
    MeasurableSet (sourceGoodEvent x M a) := goodEvent_measurable _ _ _

theorem sourceGoodEvent_product_iff {x : ℝ} (hx : 1 < x) (M : ℕ)
    (hM : 1 < logScale x M) (a : ℝ) (ω : PhaseSpace) :
    ω ∈ sourceGoodEvent x M a ↔ ∀ t : ℝ, |t| ≤ 1/2 → ∀ j ≤ M,
      (logScale x j*Real.exp a*(Real.log (logScale x j))^2)⁻¹ ≤ ‖suffixProduct x M t j ω‖ ∧
      ‖suffixProduct x M t j ω‖ ≤ logScale x j*Real.exp a*(Real.log (logScale x j))^2 := by
  rw [sourceGoodEvent,goodEvent_product_iff]
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro hj
  rw [Real.exp_neg,exp_sourceAllowance a j (hM.trans_le (logScale_antitone hx hj))]

end NField.Alignment.HarperCriticalGoodEvent
