/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianSurvivalContraction
import Mathlib.Data.Nat.Log

/-!
# A constant upper barrier for Gaussian walks with unequal variances

The actual half-time contraction gives inverse-square-root survival
at dyadic lengths. Prefix monotonicity extends it to every positive
length. The constants are explicit and uniform over the variance vector.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianBarrier
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperKilledPath HarperGaussianPathSplit
  HarperGaussianSurvivalContraction HarperCenteredPath HarperSourceKilledPath
  HarperPrimeBlocks HarperPrimeBlockGaussian

theorem sqrt_double_le_three_halves {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hba : b ≤ 2*a) : Real.sqrt b ≤ (3/2)*Real.sqrt a := by
  nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sqrt_nonneg a,Real.sqrt_nonneg b]

theorem gaussian_dyadic_survival_bound (k : ℕ) :
    ∀ n : ℕ, n = 2^k → ∀ (v : Fin n → NNReal) (c : ℝ), 0 ≤ c →
      (∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) →
      (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
        300*(c+2)/Real.sqrt (n : ℝ) := by
  induction k with
  | zero =>
    intro n hn v c hc hv
    have hn1 : n = 1 := by simpa using hn
    have hp : (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤ 1 :=
      measureReal_le_one
    have hs : Real.sqrt (n : ℝ) = 1 := by rw [hn1]; norm_num
    rw [hs]
    norm_num
    linarith
  | succ k ih =>
    intro n hn v c hc hv
    have he : n = 2^k+2^k := by rw [hn,pow_succ]; omega
    clear hn
    subst n
    have hm : 0 < 2^k := pow_pos (by norm_num) _
    have hrec := gaussian_half_survival_recurrence hm v hc hv
    have hpre := ih (2^k) rfl (fun i => v (Fin.castAdd (2^k) i)) c hc (fun i => hv _)
    have hs : 0 < Real.sqrt ((2^k : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    have hs2 : 0 < Real.sqrt ((2^k+2^k : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < 2^k+2^k by omega))
    have hd : Real.sqrt ((2^k+2^k : ℕ) : ℝ) ≤ (3/2)*Real.sqrt ((2^k : ℕ) : ℝ) := by
      apply sqrt_double_le_three_halves (by positivity) (by positivity)
      push_cast
      linarith
    have hf : 200*(c+2)/Real.sqrt ((2^k : ℕ) : ℝ) ≤
        300*(c+2)/Real.sqrt ((2^k+2^k : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hs hs2).mpr
      have hmul := mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ c+2)
      nlinarith
    have heq : 20*(c+2)/Real.sqrt ((2^k : ℕ) : ℝ) +
        (3/5)*(300*(c+2)/Real.sqrt ((2^k : ℕ) : ℝ)) =
          200*(c+2)/Real.sqrt ((2^k : ℕ) : ℝ) := by ring
    nlinarith

theorem gaussian_survival_deficit_scale_bound {n : ℕ} (hn : 0 < n)
    (v : Fin n → NNReal) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      450*(c+2)/Real.sqrt (n : ℝ) := by
  let k := Nat.log 2 n
  let m := 2^k
  have hm : 0 < m := pow_pos (by norm_num) _
  have hmn : m ≤ n := Nat.pow_log_le_self 2 (ne_of_gt hn)
  have hnm : n < 2*m := by
    have h := Nat.lt_pow_of_log_lt (by norm_num : 1 < 2) (Nat.lt_succ_self (Nat.log 2 n))
    simpa only [pow_succ,mul_comm,k,m] using h
  have hp := gaussian_survival_prefix_castLE hmn v c
  have hd := gaussian_dyadic_survival_bound k m rfl
    (fun i => v (Fin.castLE hmn i)) c hc (fun i => hv _)
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hratio : Real.sqrt (n : ℝ) ≤ (3/2)*Real.sqrt (m : ℝ) := by
    apply sqrt_double_le_three_halves (by positivity) (by positivity)
    exact_mod_cast hnm.le
  have hf : 300*(c+2)/Real.sqrt (m : ℝ) ≤ 450*(c+2)/Real.sqrt (n : ℝ) := by
    apply (div_le_div_iff₀ hsm hsn).mpr
    have hmul := mul_le_mul_of_nonneg_right hratio (by linarith : 0 ≤ c+2)
    nlinarith
  exact hp.trans (hd.trans hf)

theorem gaussian_constant_barrier_upper {n : ℕ} (hn : 0 < n)
    (v : Fin n → NNReal) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      900*(c+1)/Real.sqrt (n : ℝ) := by
  apply (gaussian_survival_deficit_scale_bound hn v hc hv).trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith

theorem source_constant_barrier_upper :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ c : ℝ, 0 ≤ c →
        (centeredNormalProductLaw x l).real (survivalEvent c) ≤
          900*(c+1)/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst c hc => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  apply gaussian_constant_barrier_upper (by omega : 0 < n+1)
    (fun i => blockNormalVariance x (l i)) hc
  intro i
  exact ⟨(hi i).1,by linarith [(hi i).2]⟩

end NField.Alignment.HarperGaussianBarrier
