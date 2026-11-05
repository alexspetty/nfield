/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSourceBarrier

/-!
# Uniform upper bound for the critical weighted source barrier

The amplitude-sized prefix leaves a comparable suffix length. This closes
both comparison-radius obligations, including small lengths and large
amplitudes, for the actual critical tilted law.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSourceBarrierBound
open MeasureTheory ProbabilityTheory Set HarperPrimeBlocks HarperPrimeBlockPath
  HarperSourceBarrier HarperLogarithmicBarrier HarperCenteredPath HarperTiltedMeasure HarperEulerIntegral

def sourceBarrierConstant (b : ℝ) : ℝ := 8*logSurvivalConstant*(b+13+centeredPathAllowance)

theorem sourceBarrierConstant_ge_two {b : ℝ} (hb : 0 ≤ b) : 2 ≤ sourceBarrierConstant b := by
  unfold sourceBarrierConstant
  have h := mul_le_mul logSurvivalConstant_one_le
    (show (1 : ℝ) ≤ b+13+centeredPathAllowance by linarith [centeredPathAllowance_pos])
    (by norm_num : (0 : ℝ) ≤ 1) (by linarith [logSurvivalConstant_one_le] : 0 ≤ logSurvivalConstant)
  nlinarith

theorem exists_amplitude_split {N : ℕ} (hN : 4 ≤ N) {a : ℝ} (ha : 1 ≤ a)
    (haN : a < Real.sqrt (N : ℝ)) :
    ∃ m n : ℕ, N = (m+1)+(n+1) ∧ (m+1 : ℕ) ≤ a ∧ a ≤ (m+1 : ℕ)+1 ∧
      Real.sqrt (N : ℝ) ≤ 2*Real.sqrt ((n+1 : ℕ) : ℝ) := by
  let p := ⌊a⌋₊
  have hp : 1 ≤ p := (Nat.one_le_floor_iff a).mpr ha
  have hpa : (p : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hap : a ≤ (p : ℝ)+1 := (Nat.lt_floor_add_one a).le
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot : Real.sqrt (N : ℝ) ≤ (N : ℝ)/2 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have hn := Real.sqrt_nonneg (N : ℝ)
    nlinarith [sq_nonneg ((N : ℝ)-2)]
  have hpN : p < N := by
    exact_mod_cast (show (p : ℝ) < N by linarith)
  have hsplit : N = ((p-1)+1)+((N-p-1)+1) := by omega
  have he1 : p-1+1 = p := by omega
  have he2 : N-p-1+1 = N-p := by omega
  refine ⟨p-1,N-p-1,hsplit,?_,?_,?_⟩
  · simpa only [he1] using hpa
  · simpa only [he1] using hap
  · have he : (N : ℝ) = (p : ℝ)+(N-p : ℕ) := by exact_mod_cast (show N=p+(N-p) by omega)
    rw [he2]
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (N-p))
    have hn := Real.sqrt_nonneg ((N-p : ℕ) : ℝ)
    have hfull := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have hfull0 := Real.sqrt_nonneg (N : ℝ)
    nlinarith

theorem actual_source_barrier_scale {b : ℝ} (hb : 0 ≤ b) :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ t : Fin (n+1) → ℝ,
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        ∀ a : ℝ, 1 ≤ a →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (sourceBarrierEvent x l t a b) ≤
          sourceBarrierConstant b*a/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  obtain ⟨X₀,hX₀⟩ := actual_source_barrier_suffix hb
  refine ⟨X₀,fun x hx n l hl hfirst t ht a ha => ?_⟩
  letI := tiltedMeasure_probability (sourceCutoff x) (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  have hC := sourceBarrierConstant_ge_two hb
  have hs : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hp : (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
      (sourceBarrierEvent x l t a b) ≤ 1 := measureReal_le_one
  by_cases hsmall : n+1 < 4
  · apply hp.trans
    apply (le_div_iff₀ hs).mpr
    have hnr : ((n+1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hsmall.le
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
    have hroot : Real.sqrt ((n+1 : ℕ) : ℝ) ≤ 2 := by nlinarith
    nlinarith
  by_cases hlarge : Real.sqrt ((n+1 : ℕ) : ℝ) ≤ a
  · apply hp.trans
    apply (le_div_iff₀ hs).mpr
    nlinarith
  obtain ⟨m,k,hN,hma,ham,hsplit⟩ := exists_amplitude_split (Nat.le_of_not_gt hsmall) ha (lt_of_not_ge hlarge)
  have hn : n = (m+1)+k := by omega
  subst n
  have h := hX₀ x hx m k l hl hfirst t ht a ha hma ham
  have hsuf : 0 < Real.sqrt ((k+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hnum : (b+13)*a+centeredPathAllowance ≤ (b+13+centeredPathAllowance)*a := by
    nlinarith [centeredPathAllowance_pos]
  have hnum0 : 0 ≤ (b+13+centeredPathAllowance)*a := by
    apply mul_nonneg <;> linarith [centeredPathAllowance_pos]
  calc
    _ ≤ _ := h
    _ ≤ (4*logSurvivalConstant)*
        (((b+13)*a+centeredPathAllowance)/Real.sqrt ((k+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith [logSurvivalConstant_one_le])
    _ ≤ (4*logSurvivalConstant)*
        (((b+13+centeredPathAllowance)*a)/Real.sqrt ((k+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hsuf.le)
        (by linarith [logSurvivalConstant_one_le])
    _ ≤ sourceBarrierConstant b*a/Real.sqrt (((m+1)+k+1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hsuf hs).mpr
      unfold sourceBarrierConstant
      have hm := mul_le_mul_of_nonneg_left hsplit
        (mul_nonneg (show 0 ≤ 4*logSurvivalConstant by linarith [logSurvivalConstant_one_le]) hnum0)
      nlinarith

theorem actual_source_barrier_upper {b : ℝ} (hb : 0 ≤ b) :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ t : Fin (n+1) → ℝ,
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        ∀ a : ℝ, 1 ≤ a →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (sourceBarrierEvent x l t a b) ≤
          sourceBarrierConstant b*min 1 (a/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := actual_source_barrier_scale hb
  refine ⟨X₀,fun x hx n l hl hfirst t ht a ha => ?_⟩
  by_cases h : a/Real.sqrt ((n+1 : ℕ) : ℝ) ≤ 1
  · rw [min_eq_right h,← mul_div_assoc]
    exact hX₀ x hx n l hl hfirst t ht a ha
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    letI := tiltedMeasure_probability (sourceCutoff x) (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
    exact measureReal_le_one.trans (by linarith [sourceBarrierConstant_ge_two hb])

theorem actual_source_barrier_array {b : ℝ} (hb : 0 ≤ b) :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ (t u v : Fin (n+1) → ℝ),
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        ∀ a : ℝ, 1 ≤ a →
        (∀ j, -a-b*((j.val : ℝ)+1) ≤ u j) →
        (∀ j, v j ≤ a+((j.val : ℝ)+1)+10*Real.log ((j.val : ℝ)+1)) →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (blockPathEvent x l t u v) ≤
          sourceBarrierConstant b*min 1 (a/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := actual_source_barrier_upper hb
  refine ⟨X₀,fun x hx n l hl hfirst t u v ht a ha hu hv => ?_⟩
  letI := tiltedMeasure_probability (sourceCutoff x) (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  have hsub : blockPathEvent x l t u v ⊆ sourceBarrierEvent x l t a b := by
    intro ω hω j
    exact ⟨(hu j).trans (hω j).1,((hω j).2).trans (hv j)⟩
  exact (measureReal_mono hsub (by finiteness)).trans (hX₀ x hx n l hl hfirst t ht a ha)

end NField.Alignment.HarperSourceBarrierBound
