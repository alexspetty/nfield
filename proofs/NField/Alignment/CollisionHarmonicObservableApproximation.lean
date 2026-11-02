/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicLocalSummability
import NField.Alignment.CollisionCylinderMeans
import NField.Alignment.CollisionResolutionLaw

/-!
# Uniform harmonic approximations of the reset and alignment observables

The exceptional coefficient at one is kept explicitly as minus gamma.
The other errors are absolutely summable, with a bound independent of
the divisor set and of the alignment modulus. All infinite series below
are proved summable before their totals are rearranged.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicObservableApproximation

open scoped Classical
open CollisionHarmonicLocalExpansion CollisionHarmonicLocalSummability
open CollisionZetaMoments CollisionRemainderDynamics CollisionCylinderMeans
open CollisionMassReadout CollisionConductorArithmetic

def harmonicGlobalError (k : ℕ) : ℝ := if 2 ≤ k then harmonicLocalError k else 0

theorem harmonic_global_formula (k : ℕ) :
    (k : ℝ)*collisionWeight k=harmonicLocalMain k-
      (if k=1 then Real.eulerMascheroniConstant else 0)+harmonicGlobalError k := by
  by_cases hk : 2 ≤ k
  · rw [if_neg (by omega : k ≠ 1),sub_zero,harmonicGlobalError,if_pos hk]
    exact harmonic_local_formula hk
  · have hcases : k=0 ∨ k=1 := by omega
    rcases hcases with rfl|rfl <;>
      simp [harmonicGlobalError,harmonicLocalMain,nu]

theorem harmonicGlobalError_bound (k : ℕ) :
    ‖harmonicGlobalError k‖ ≤ harmonicLocalErrorBound k := by
  by_cases hk : 2 ≤ k
  · simpa only [harmonicGlobalError,if_pos hk,Real.norm_eq_abs] using harmonic_local_error_bound k
  · simpa only [harmonicGlobalError,if_neg hk,norm_zero] using harmonicLocalErrorBound_nonneg k

theorem harmonicGlobalError_summable : Summable harmonicGlobalError :=
  Summable.of_norm_bounded harmonicLocalErrorBound_hasSum.summable harmonicGlobalError_bound

theorem harmonicGlobalError_finite_bound (s : Finset ℕ) :
    |∑ k ∈ s, harmonicGlobalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  calc
    _ ≤ ∑ k ∈ s, |harmonicGlobalError k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, harmonicLocalErrorBound k := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [Real.norm_eq_abs] using harmonicGlobalError_bound k
    _ ≤ ∑' k : ℕ, harmonicLocalErrorBound k :=
      harmonicLocalErrorBound_hasSum.summable.sum_le_tsum s
        (fun k _ => harmonicLocalErrorBound_nonneg k)
    _ = _ := harmonicLocalErrorBound_hasSum.tsum_eq

theorem reset_harmonic_approximation {n : ℕ} (hn : 0 < n) :
    (∑' k, CollisionResolutionLaw.resetTerm n k)=
      (∑ k ∈ n.divisors, harmonicLocalMain k)-Real.eulerMascheroniConstant+
        ∑ k ∈ n.divisors, harmonicGlobalError k ∧
      |∑ k ∈ n.divisors, harmonicGlobalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  refine ⟨?_,harmonicGlobalError_finite_bound _⟩
  rw [CollisionResolutionLaw.resetTerm_tsum hn]
  simp_rw [harmonic_global_formula]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp [Nat.one_mem_divisors.mpr hn.ne']

theorem alignment_global_error_bound (L k : ℕ) :
    ‖(k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k‖ ≤ harmonicLocalErrorBound k := by
  rw [norm_mul,Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul (alignment_gcd_ratio_bound L k)
    (harmonicGlobalError_bound k) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem alignment_global_error_summable (L : ℕ) :
    Summable (fun k : ℕ => (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k) :=
  Summable.of_norm_bounded harmonicLocalErrorBound_hasSum.summable (alignment_global_error_bound L)

theorem alignment_global_error_uniform (L : ℕ) :
    |∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  simpa only [Real.norm_eq_abs] using
    tsum_of_norm_bounded harmonicLocalErrorBound_hasSum (alignment_global_error_bound L)

theorem alignment_harmonic_term (L k : ℕ) :
    collisionWeight k*(k.gcd L : ℝ)=(k.gcd L : ℝ)/(k : ℝ)*harmonicLocalMain k-
      (if k=1 then Real.eulerMascheroniConstant else 0)+
      (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k := by
  by_cases hk0 : k=0
  · simp [hk0]
  by_cases hk1 : k=1
  · simp [hk1,harmonicLocalMain,harmonicGlobalError,nu]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  rw [if_neg hk1]
  calc
    _ = (k.gcd L : ℝ)/(k : ℝ)*((k : ℝ)*collisionWeight k) := by field_simp
    _ = _ := by
      rw [harmonic_global_formula,if_neg hk1]
      ring

theorem alignment_gcd_series_summable {L : ℕ} (hL : 0 < L) :
    Summable (fun k : ℕ => collisionWeight k*(k.gcd L : ℝ)) := by
  apply Summable.of_norm_bounded (collisionWeight_summable.mul_right (L : ℝ))
  intro k
  have hd : (k.gcd L : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.gcd_le_right k hL
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (collisionWeight_nonneg k),
    abs_of_nonneg (by positivity : 0 ≤ (k.gcd L : ℝ))]
  exact mul_le_mul_of_nonneg_left hd (collisionWeight_nonneg k)

theorem alignment_gcd_series_value {L : ℕ} (hL : 0 < L) :
    (∑' k : ℕ, collisionWeight k*(k.gcd L : ℝ))=3*alignmentConstant L+1 := by
  have h := (alignment_gcd_series_summable hL).tsum_sub collisionWeight_summable
  have he : (∑' k : ℕ, collisionWeight k*((k.gcd L : ℝ)-1))=
      (∑' k : ℕ, collisionWeight k*(k.gcd L : ℝ))-1 := by
    simpa only [mul_sub,mul_one,collisionWeight_hasSum.tsum_eq] using h
  unfold alignmentConstant
  rw [he]
  ring

theorem alignment_harmonic_main_summable {L : ℕ} (hL : 0 < L) :
    Summable (fun k : ℕ => (k.gcd L : ℝ)/(k : ℝ)*harmonicLocalMain k) := by
  have hgamma : Summable (fun k : ℕ => if k=1 then Real.eulerMascheroniConstant else 0) :=
    (hasSum_ite_eq 1 Real.eulerMascheroniConstant).summable
  apply ((alignment_gcd_series_summable hL).add hgamma).sub
    (alignment_global_error_summable L) |>.congr
  intro k
  have he := alignment_harmonic_term L k
  linarith

theorem alignment_harmonic_approximation {L : ℕ} (hL : 0 < L) :
    3*alignmentConstant L+1=
      (∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicLocalMain k)-Real.eulerMascheroniConstant+
        (∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k) ∧
      |∑' k : ℕ, (k.gcd L : ℝ)/(k : ℝ)*harmonicGlobalError k| ≤ zetaNat 2*zetaNat 3/12 := by
  refine ⟨?_,alignment_global_error_uniform L⟩
  rw [← alignment_gcd_series_value hL]
  have hgamma : Summable (fun k : ℕ => if k=1 then Real.eulerMascheroniConstant else 0) :=
    (hasSum_ite_eq 1 Real.eulerMascheroniConstant).summable
  have h := ((alignment_harmonic_main_summable hL).sub hgamma).tsum_add
    (alignment_global_error_summable L)
  rw [(alignment_harmonic_main_summable hL).tsum_sub hgamma] at h
  simp only [tsum_ite_eq] at h
  rw [← h]
  exact tsum_congr (alignment_harmonic_term L)

end NField.Alignment.CollisionHarmonicObservableApproximation
