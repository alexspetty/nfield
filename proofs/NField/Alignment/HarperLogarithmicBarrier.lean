/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLogarithmicContraction

/-!
# The logarithmic Gaussian upper barrier

The uniform moving-deficit budget and the half-time contraction give an
inverse-square-root survival bound at every positive length. All small
lengths, arbitrary upper barrier arrays, and source variances are handled.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperLogarithmicBarrier
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperMovingKilledPath HarperLogarithmicDrift
  HarperGaussianMovingSplit HarperLogarithmicContraction HarperGaussianBarrier
  HarperGaussianBarrierPerturbation HarperSourceKilledPath HarperCenteredPath
  HarperPrimeBlocks HarperPrimeBlockGaussian

def logSurvivalConstant : ℝ := 900*(logDeficitConstant+1)

theorem logSurvivalConstant_one_le : 1 ≤ logSurvivalConstant := by
  unfold logSurvivalConstant
  linarith [logDeficitConstant_pos]

theorem gaussian_logarithmic_dyadic_bound (k : ℕ) :
    ∀ n : ℕ, n = 2^k → ∀ (v : Fin n → NNReal) (a : ℝ), 0 ≤ a →
      (∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) →
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent (logBoundary a)) ≤
        600*(logDeficitConstant+1)*(a+1)/Real.sqrt (n : ℝ) := by
  induction k with
  | zero =>
    intro n hn v a ha hv
    have hn1 : n = 1 := by simpa using hn
    have hp : (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent (logBoundary a)) ≤ 1 :=
      measureReal_le_one
    have hs : Real.sqrt (n : ℝ) = 1 := by rw [hn1]; norm_num
    rw [hs,div_one]
    nlinarith [logDeficitConstant_pos,mul_nonneg logDeficitConstant_pos.le ha]
  | succ k ih =>
    intro n hn v a ha hv
    have he : n = 2^k+2^k := by rw [hn,pow_succ]; omega
    clear hn
    subst n
    have hm : 0 < 2^k := pow_pos (by norm_num) _
    have hs : 0 < Real.sqrt ((2^k : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    have hs2 : 0 < Real.sqrt ((2^k+2^k : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < 2^k+2^k by omega))
    by_cases hlarge : 160000 ≤ 2^k
    · have hrec := gaussian_logarithmic_half_recurrence hlarge v ha hv
      have hpre := ih (2^k) rfl (fun i => v (Fin.castAdd (2^k) i)) a ha (fun i => hv _)
      have hd : Real.sqrt ((2^k+2^k : ℕ) : ℝ) ≤ (3/2)*Real.sqrt ((2^k : ℕ) : ℝ) := by
        apply sqrt_double_le_three_halves (by positivity) (by positivity)
        push_cast
        linarith
      have hf : 400*(logDeficitConstant+1)*(a+1)/Real.sqrt ((2^k : ℕ) : ℝ) ≤
          600*(logDeficitConstant+1)*(a+1)/Real.sqrt ((2^k+2^k : ℕ) : ℝ) := by
        apply (div_le_div_iff₀ hs hs2).mpr
        have hm := mul_le_mul_of_nonneg_right hd
          (mul_nonneg (by linarith [logDeficitConstant_pos] : 0 ≤ logDeficitConstant+1)
            (by linarith : 0 ≤ a+1))
        nlinarith
      calc
        _ ≤ _ := hrec
        _ ≤ 40*logDeficitConstant*(a+1)/Real.sqrt ((2^k : ℕ) : ℝ)+
            (3/5)*(600*(logDeficitConstant+1)*(a+1)/Real.sqrt ((2^k : ℕ) : ℝ)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hpre (by norm_num))
        _ = (400*logDeficitConstant+360)*(a+1)/Real.sqrt ((2^k : ℕ) : ℝ) := by ring
        _ ≤ 400*(logDeficitConstant+1)*(a+1)/Real.sqrt ((2^k : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (by nlinarith) hs.le
        _ ≤ _ := hf
    · have hsmall : ((2^k+2^k : ℕ) : ℝ) ≤ 320000 := by exact_mod_cast (show 2^k+2^k ≤ 320000 by omega)
      have hroot : Real.sqrt ((2^k+2^k : ℕ) : ℝ) ≤ 600 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2^k+2^k : ℕ) by positivity)]
      apply measureReal_le_one.trans
      apply (le_div_iff₀ hs2).mpr
      nlinarith [logDeficitConstant_pos,mul_nonneg logDeficitConstant_pos.le ha]

theorem gaussian_logarithmic_scale_bound {n : ℕ} (hn : 0 < n)
    (v : Fin n → NNReal) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent (logBoundary a)) ≤
      logSurvivalConstant*(a+1)/Real.sqrt (n : ℝ) := by
  let k := Nat.log 2 n
  let m := 2^k
  have hm : 0 < m := pow_pos (by norm_num) _
  have hmn : m ≤ n := Nat.pow_log_le_self 2 (ne_of_gt hn)
  have hnm : n < 2*m := by
    have h := Nat.lt_pow_of_log_lt (by norm_num : 1 < 2) (Nat.lt_succ_self (Nat.log 2 n))
    simpa only [pow_succ,mul_comm,k,m] using h
  have hp := gaussian_moving_prefix_castLE hmn v (logBoundary a)
  have hd := gaussian_logarithmic_dyadic_bound k m rfl
    (fun i => v (Fin.castLE hmn i)) a ha (fun i => hv _)
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hratio : Real.sqrt (n : ℝ) ≤ (3/2)*Real.sqrt (m : ℝ) := by
    apply sqrt_double_le_three_halves (by positivity) (by positivity)
    exact_mod_cast hnm.le
  have hf : 600*(logDeficitConstant+1)*(a+1)/Real.sqrt (m : ℝ) ≤
      logSurvivalConstant*(a+1)/Real.sqrt (n : ℝ) := by
    apply (div_le_div_iff₀ hsm hsn).mpr
    unfold logSurvivalConstant
    have hmul := mul_le_mul_of_nonneg_right hratio
      (mul_nonneg (by linarith [logDeficitConstant_pos] : 0 ≤ logDeficitConstant+1)
        (by linarith : 0 ≤ a+1))
    nlinarith
  exact hp.trans (hd.trans hf)

theorem gaussian_logarithmic_barrier_upper {n : ℕ} (hn : 0 < n)
    (v : Fin n → NNReal) {a : ℝ} (ha : 1 ≤ a)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent (logBoundary a)) ≤
      (2*logSurvivalConstant)*min 1 (a/Real.sqrt (n : ℝ)) := by
  by_cases h : a/Real.sqrt (n : ℝ) ≤ 1
  · rw [min_eq_right h]
    calc
      _ ≤ _ := gaussian_logarithmic_scale_bound hn v (by linarith : 0 ≤ a) hv
      _ ≤ logSurvivalConstant*(2*a)/Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by linarith [logSurvivalConstant_one_le]))
          (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact measureReal_le_one.trans (by linarith [logSurvivalConstant_one_le])

theorem gaussian_logarithmic_barrier_array {n : ℕ} (hn : 0 < n)
    (v : Fin n → NNReal) {a : ℝ} (ha : 1 ≤ a)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1)
    (h : Fin n → ℝ) (hh : ∀ j, h j ≤ a+10*Real.log ((j.val : ℝ)+1)) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (barrierEvent h) ≤
      (2*logSurvivalConstant)*min 1 (a/Real.sqrt (n : ℝ)) := by
  have hsub : barrierEvent h ⊆ movingEvent (logBoundary a) := by
    apply barrierEvent_mono
    intro j
    rw [logBoundary_positive_time a (by omega : 0 < j.val+1)]
    simpa only [Nat.cast_add,Nat.cast_one] using hh j
  exact (measureReal_mono hsub (by finiteness)).trans (gaussian_logarithmic_barrier_upper hn v ha hv)

theorem source_logarithmic_barrier_upper :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ a : ℝ, 1 ≤ a →
        (centeredNormalProductLaw x l).real (movingEvent (logBoundary a)) ≤
          (2*logSurvivalConstant)*min 1 (a/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst a ha => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  exact gaussian_logarithmic_barrier_upper (by omega : 0 < n+1)
    (fun i => blockNormalVariance x (l i)) ha (fun i => ⟨(hi i).1,by linarith [(hi i).2]⟩)

theorem source_logarithmic_barrier_array :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ a : ℝ, 1 ≤ a →
      ∀ h : Fin (n+1) → ℝ, (∀ j, h j ≤ a+10*Real.log ((j.val : ℝ)+1)) →
        (centeredNormalProductLaw x l).real (barrierEvent h) ≤
          (2*logSurvivalConstant)*min 1 (a/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst a ha h hh => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  exact gaussian_logarithmic_barrier_array (by omega : 0 < n+1)
    (fun i => blockNormalVariance x (l i)) ha (fun i => ⟨(hi i).1,by linarith [(hi i).2]⟩) h hh

end NField.Alignment.HarperLogarithmicBarrier
