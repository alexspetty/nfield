/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianEndpoint

/-!
# Exact Gaussian laws for finite endpoint sums

The sum under the actual finite Gaussian product has the centered Gaussian
law with the sum of its variances. This supplies the endpoint contraction
without an identical-distribution assumption.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianEndpointLaw
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperGaussianEndpoint

theorem gaussian_snoc_measurePreserving {n : ℕ} (v : Fin (n+1) → NNReal) :
    MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => Fin.snoc p.2 p.1)
      ((gaussianReal 0 (v (Fin.last n))).prod
        (Measure.pi (fun i => gaussianReal 0 (v i.castSucc))))
      (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun i => gaussianReal 0 (v i)) (Fin.last n)).symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_last',Fin.succAbove_last,Equiv.coe_fn_mk] using h

theorem gaussian_sum_law {n : ℕ} (v : Fin n → NNReal) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).map (fun z => ∑ i, z i) =
      gaussianReal 0 (∑ i, v i) := by
  induction n with
  | zero => simp [Measure.map_const,gaussianReal_zero_var]
  | succ n ih =>
    let μ := gaussianReal 0 (v (Fin.last n))
    let ν := Measure.pi (fun i : Fin n => gaussianReal 0 (v i.castSucc))
    have hm : Measurable (fun y : Fin n → ℝ => ∑ i, y i) := by fun_prop
    have hY : (μ.prod ν).map (fun p => ∑ i, p.2 i) = gaussianReal 0 (∑ i : Fin n, v i.castSucc) := by
      rw [show (fun p : ℝ × (Fin n → ℝ) => ∑ i, p.2 i) =
        (fun y : Fin n → ℝ => ∑ i, y i) ∘ Prod.snd from rfl,
        ← Measure.map_map hm measurable_snd,measurePreserving_snd.map_eq]
      exact ih _
    have h := gaussianReal_add_gaussianReal_of_indepFun
      (indepFun_prod (μ := μ) (ν := ν) (X := fun z : ℝ => z)
        (Y := fun y : Fin n → ℝ => ∑ i, y i) measurable_id hm)
      (show (μ.prod ν).map (fun p => p.1) = μ from measurePreserving_fst.map_eq) hY
    change (μ.prod ν).map (fun p : ℝ × (Fin n → ℝ) => p.1+∑ i, p.2 i) =
      gaussianReal (0+0) (v (Fin.last n)+∑ i : Fin n, v i.castSucc) at h
    have hsum : Measurable (fun z : Fin (n+1) → ℝ => ∑ i, z i) := by fun_prop
    rw [← (gaussian_snoc_measurePreserving v).map_eq,
      Measure.map_map hsum (gaussian_snoc_measurePreserving v).measurable]
    simpa only [Function.comp_def,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
      zero_add,add_comm,μ,ν] using h

theorem gaussian_sum_endpoint_mass {n : ℕ} (v : Fin n → NNReal) (R : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real {z | (∑ i, z i) ≤ R} =
      (gaussianReal 0 (∑ i, v i)).real (Iic R) := by
  have hm : Measurable (fun z : Fin n → ℝ => ∑ i, z i) := by fun_prop
  simp only [measureReal_def]
  rw [← gaussian_sum_law v,Measure.map_apply hm measurableSet_Iic]
  rfl

theorem gaussian_sum_endpoint_contraction {n : ℕ} (hn : 0 < n)
    (v : Fin n → NNReal) (hv : ∀ i, (1/4 : ℝ) ≤ v i) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real
      {z | (∑ i, z i) ≤ Real.sqrt (n : ℝ)/20} ≤ 3/5 := by
  rw [gaussian_sum_endpoint_mass]
  apply gaussian_endpoint_contraction (by exact_mod_cast hn)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hv i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    NNReal.coe_sum,div_eq_mul_inv,one_mul] using h

end NField.Alignment.HarperGaussianEndpointLaw
