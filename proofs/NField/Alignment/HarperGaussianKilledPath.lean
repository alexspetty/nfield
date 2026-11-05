/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperKilledPath

/-!
# The finite Gaussian killed-potential bound

Independent centered increments may have different variances. Splitting
an actual finite Gaussian product and applying the proved one-step bound
controls the expected surviving deficit uniformly in the path length.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianKilledPath
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperKilledPath HarperGaussianOvershoot

theorem gaussian_snoc_integrable {n : ℕ} (v : Fin (n+1) → NNReal)
    {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi (fun i => gaussianReal 0 (v i)))) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.snoc p.2 p.1))
      ((gaussianReal 0 (v (Fin.last n))).prod
        (Measure.pi (fun i => gaussianReal 0 (v i.castSucc)))) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun i => gaussianReal 0 (v i)) (Fin.last n)).symm.integrable_comp_of_integrable hf
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Function.comp_def,Fin.insertNth_last',Fin.succAbove_last,Equiv.coe_fn_mk] using h

theorem gaussian_integral_snoc {n : ℕ} (v : Fin (n+1) → NNReal)
    {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi (fun i => gaussianReal 0 (v i)))) :
    (∫ z, f z ∂Measure.pi (fun i => gaussianReal 0 (v i))) =
      ∫ y, ∫ z, f (Fin.snoc y z) ∂gaussianReal 0 (v (Fin.last n))
        ∂Measure.pi (fun i => gaussianReal 0 (v i.castSucc)) := by
  have he := (measurePreserving_piFinSuccAbove
    (fun i => gaussianReal 0 (v i)) (Fin.last n)).symm.integral_comp' f
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_last',Fin.succAbove_last] at he
  rw [← he]
  exact integral_prod_symm _ (gaussian_snoc_integrable v hf)

theorem gaussian_pathPotential_step {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {v : NNReal} (hv : 0 < v) (hv1 : (v : ℝ) ≤ 1) (y : Fin n → ℝ) :
    (∫ z, pathPotential c (Fin.snoc y z) ∂gaussianReal 0 v) ≤ pathPotential c y := by
  simp_rw [pathPotential_snoc]
  by_cases hy : y ∈ survivalEvent c
  · simp only [Set.indicator_of_mem hy,pathPotential]
    exact gaussian_killedPotential_one_step hv hv1 (by linarith [sum_le_of_survival hc hy])
  · simp only [Set.indicator_of_notMem hy,pathPotential,integral_zero]
    exact le_rfl

theorem gaussian_pathPotential_bound {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (v : Fin n → NNReal) (hv : ∀ i, 0 < v i) (hv1 : ∀ i, (v i : ℝ) ≤ 1) :
    (∫ z, pathPotential c z ∂Measure.pi (fun i => gaussianReal 0 (v i))) ≤ c+2 := by
  induction n with
  | zero =>
    have he (z : Fin 0 → ℝ) : pathPotential c z = c+2 := by
      unfold pathPotential
      rw [Set.indicator_of_mem (show z ∈ survivalEvent c from fun j => Fin.elim0 j)]
      simp
    simp only [he,integral_const,probReal_univ,one_smul]
    exact le_rfl
  | succ n ih =>
    rw [gaussian_integral_snoc v (gaussian_pathPotential_integrable c v)]
    calc
      _ ≤ ∫ y, pathPotential c y
          ∂Measure.pi (fun i : Fin n => gaussianReal 0 (v i.castSucc)) := by
        apply integral_mono
          (gaussian_snoc_integrable v (gaussian_pathPotential_integrable c v)).integral_prod_right
          (gaussian_pathPotential_integrable c (fun i => v i.castSucc))
        intro y
        exact gaussian_pathPotential_step hc (hv _) (hv1 _) y
      _ ≤ c+2 := ih (fun i => v i.castSucc) (fun i => hv _) (fun i => hv1 _)

theorem gaussian_survival_deficit_tail {n : ℕ} {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R)
    (v : Fin n → NNReal) (hv : ∀ i, 0 < v i) (hv1 : ∀ i, (v i : ℝ) ≤ 1) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      (survivalEvent c ∩ {z | R ≤ c-∑ i, z i}) ≤ (c+2)/(R+2) := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  have hsub : survivalEvent (n := n) c ∩ {z | R ≤ c-∑ i, z i} ⊆
      {z | R+2 ≤ pathPotential c z} := by
    intro z hz
    change R+2 ≤ (survivalEvent c).indicator (fun y => c-(∑ i, y i)+2) z
    rw [Set.indicator_of_mem hz.1]
    have hRz : R ≤ c-∑ i, z i := hz.2
    linarith
  have hm : μ.real (survivalEvent c ∩ {z | R ≤ c-∑ i, z i}) ≤
      μ.real {z | R+2 ≤ pathPotential c z} := measureReal_mono hsub (by finiteness)
  have hi := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all _ (pathPotential_nonneg hc))
    (gaussian_pathPotential_integrable c v) (R+2)
  have hb := gaussian_pathPotential_bound hc v hv hv1
  have ht := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ R+2)
  apply (le_div_iff₀ (by linarith : 0 < R+2)).mpr
  change _ ≤ c+2
  change (∫ z, pathPotential c z ∂μ) ≤ c+2 at hb
  nlinarith

end NField.Alignment.HarperGaussianKilledPath
