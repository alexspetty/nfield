/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperMovingKilledPath

/-!
# Gaussian surviving deficit with a moving barrier

Each increase of the barrier contributes its size times the preceding
survival probability. Bounding that probability by the constant endpoint
barrier gives an explicit finite drift budget under the actual product.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianMovingPotential
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperKilledPath HarperMovingKilledPath
  HarperGaussianOvershoot HarperGaussianKilledPath HarperGaussianBarrier

def survivalEnvelope (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else 900*(B n+1)/Real.sqrt (n : ℝ)

def driftBudget (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  B 0+2+∑ j ∈ Finset.range n, (B (j+1)-B j)*survivalEnvelope B j

theorem gaussian_moving_survival_upper {n : ℕ} (B : ℕ → ℝ) (hB0 : 0 ≤ B 0)
    (hB : Monotone B) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent B) ≤ survivalEnvelope B n := by
  by_cases hn : n = 0
  · simp only [survivalEnvelope,hn,ite_true]
    exact measureReal_le_one
  · simp only [survivalEnvelope,hn,ite_false]
    have hs := measureReal_mono (μ := Measure.pi (fun i => gaussianReal 0 (v i)))
      (movingEvent_subset_constant (n := n) hB) (by finiteness)
    exact hs.trans (gaussian_constant_barrier_upper (Nat.pos_of_ne_zero hn) v
      (hB0.trans (hB (Nat.zero_le n))) hv)

theorem gaussian_movingPotential_step {n : ℕ} (B : ℕ → ℝ) (hB0 : 0 ≤ B 0)
    (hB : Monotone B) {v : NNReal} (hv : 0 < v) (hv1 : (v : ℝ) ≤ 1) (y : Fin n → ℝ) :
    (∫ z, movingPotential B (Fin.snoc y z) ∂gaussianReal 0 v) ≤
      movingPotential B y+(B (n+1)-B n)*(movingEvent B).indicator (1 : (Fin n → ℝ) → ℝ) y := by
  simp_rw [movingPotential_snoc]
  by_cases hy : y ∈ movingEvent B
  · simp only [Set.indicator_of_mem hy,movingPotential,Pi.one_apply,mul_one]
    have hd : 0 ≤ B (n+1)-∑ i, y i := by
      linarith [sum_le_of_moving hB0 hy,hB (Nat.le_succ n)]
    calc
      _ ≤ B (n+1)-(∑ i, y i)+2 := gaussian_killedPotential_one_step hv hv1 hd
      _ = _ := by ring
  · simp only [Set.indicator_of_notMem hy,movingPotential,integral_zero,mul_zero,add_zero]
    exact le_rfl

theorem gaussian_movingPotential_recurrence {n : ℕ} (B : ℕ → ℝ) (hB0 : 0 ≤ B 0)
    (hB : Monotone B) (v : Fin (n+1) → NNReal)
    (hv : 0 < v (Fin.last n)) (hv1 : (v (Fin.last n) : ℝ) ≤ 1) :
    (∫ z, movingPotential B z ∂Measure.pi (fun i => gaussianReal 0 (v i))) ≤
      (∫ y, movingPotential B y ∂Measure.pi (fun i : Fin n => gaussianReal 0 (v i.castSucc)))+
        (B (n+1)-B n)*(Measure.pi (fun i : Fin n => gaussianReal 0 (v i.castSucc))).real
          (movingEvent B) := by
  let μ := Measure.pi (fun i : Fin n => gaussianReal 0 (v i.castSucc))
  have hp := gaussian_movingPotential_integrable B (fun i : Fin n => v i.castSucc)
  have hi : Integrable ((movingEvent B).indicator (1 : (Fin n → ℝ) → ℝ)) μ :=
    (integrable_const 1).indicator (measurableSet_movingEvent B)
  rw [gaussian_integral_snoc v (gaussian_movingPotential_integrable B v)]
  calc
    _ ≤ ∫ y, movingPotential B y+(B (n+1)-B n)*
        (movingEvent B).indicator (1 : (Fin n → ℝ) → ℝ) y ∂μ := by
      apply integral_mono
        (gaussian_snoc_integrable v (gaussian_movingPotential_integrable B v)).integral_prod_right
        (hp.add (hi.const_mul _))
      exact gaussian_movingPotential_step B hB0 hB hv hv1
    _ = _ := by
      rw [integral_add hp (hi.const_mul _),integral_const_mul,
        integral_indicator_one (measurableSet_movingEvent B)]

theorem gaussian_movingPotential_budget {n : ℕ} (B : ℕ → ℝ) (hB0 : 0 ≤ B 0)
    (hB : Monotone B) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) :
    (∫ z, movingPotential B z ∂Measure.pi (fun i => gaussianReal 0 (v i))) ≤ driftBudget B n := by
  induction n with
  | zero =>
    have he (z : Fin 0 → ℝ) : movingPotential B z = B 0+2 := by
      unfold movingPotential
      rw [Set.indicator_of_mem (show z ∈ movingEvent B from fun j => Fin.elim0 j)]
      simp
    simp only [he,integral_const,probReal_univ,one_smul,driftBudget,Finset.range_zero,
      Finset.sum_empty,add_zero,le_refl]
  | succ n ih =>
    have hstep := gaussian_movingPotential_recurrence B hB0 hB v
      (show 0 < v (Fin.last n) from by exact_mod_cast (show (0 : ℝ) < v (Fin.last n) by linarith [(hv (Fin.last n)).1]))
      (hv (Fin.last n)).2
    have hi := ih (fun i => v i.castSucc) (fun i => hv i.castSucc)
    have hs := gaussian_moving_survival_upper B hB0 hB (fun i => v i.castSucc) (fun i => hv i.castSucc)
    have hd : 0 ≤ B (n+1)-B n := sub_nonneg.mpr (hB (Nat.le_succ n))
    have hm := mul_le_mul_of_nonneg_left hs hd
    unfold driftBudget at hi ⊢
    rw [Finset.sum_range_succ]
    linarith

theorem gaussian_moving_deficit_tail {n : ℕ} (B : ℕ → ℝ) (hB0 : 0 ≤ B 0)
    (hB : Monotone B) (v : Fin n → NNReal)
    (hv : ∀ i, (1/4 : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      (movingEvent B ∩ {z | R ≤ B n-∑ i, z i}) ≤ driftBudget B n/(R+2) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  have hsub : movingEvent (n := n) B ∩ {z | R ≤ B n-∑ i, z i} ⊆
      {z | R+2 ≤ movingPotential B z} := by
    intro z hz
    change R+2 ≤ (movingEvent B).indicator (fun y => B n-(∑ i, y i)+2) z
    rw [Set.indicator_of_mem hz.1]
    have hzR : R ≤ B n-∑ i, z i := hz.2
    linarith
  have hm : μ.real (movingEvent B ∩ {z | R ≤ B n-∑ i, z i}) ≤
      μ.real {z | R+2 ≤ movingPotential B z} := measureReal_mono hsub (by finiteness)
  have hi := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (ae_of_all _ (movingPotential_nonneg hB0)) (gaussian_movingPotential_integrable B v) (R+2)
  have hb := gaussian_movingPotential_budget B hB0 hB v hv
  have ht := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ R+2)
  apply (le_div_iff₀ (by linarith : 0 < R+2)).mpr
  change _ ≤ driftBudget B n
  change (∫ z, movingPotential B z ∂μ) ≤ driftBudget B n at hb
  linarith

end NField.Alignment.HarperGaussianMovingPotential
