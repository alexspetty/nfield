/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSourceKilledPath

/-!
# Exact prefix and suffix splitting of a finite Gaussian path

Concatenation is measure preserving for the actual Gaussian products.
Full survival is covered by a large-deficit prefix event or a surviving
prefix together with a low suffix endpoint. The latter is a product event.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianPathSplit
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperKilledPath

def appendEquiv (m n : ℕ) : ((Fin m → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin (m+n) → ℝ) where
  toFun p := Fin.append p.1 p.2
  invFun z := (fun i => z (Fin.castAdd n i),fun i => z (Fin.natAdd m i))
  left_inv p := by
    apply Prod.ext <;> funext i <;> simp
  right_inv z := Fin.append_castAdd_natAdd
  measurable_toFun := by
    change Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append p.1 p.2)
    apply measurable_pi_lambda
    intro i
    induction i using Fin.addCases with
    | left i => simp only [Fin.append_left]; fun_prop
    | right i => simp only [Fin.append_right]; fun_prop
  measurable_invFun := by
    change Measurable (fun z : Fin (m+n) → ℝ =>
      (fun i => z (Fin.castAdd n i),fun i => z (Fin.natAdd m i)))
    fun_prop

theorem gaussian_append_measurePreserving {m n : ℕ} (v : Fin (m+n) → NNReal) :
    MeasurePreserving (appendEquiv m n)
      ((Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
        (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i)))))
      (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  refine ⟨(appendEquiv m n).measurable,?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (appendEquiv m n).measurable
    (MeasurableSet.pi Set.countable_univ (fun i _ => hs i))]
  have he : (appendEquiv m n) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (fun i => s (Fin.castAdd n i))) ×ˢ
        (Set.univ.pi (fun i => s (Fin.natAdd m i))) := by
    ext p
    change (Fin.append p.1 p.2 ∈ Set.univ.pi s) ↔ _
    simp only [Set.mem_pi,Set.mem_univ,forall_const,Fin.forall_fin_add,
      Fin.append_left,Fin.append_right,Set.mem_prod]
  rw [he,Measure.prod_prod,Measure.pi_pi,Measure.pi_pi,Fin.prod_univ_add]

theorem partialSum_append_left {m n : ℕ} (y : Fin m → ℝ) (z : Fin n → ℝ) (j : Fin m) :
    partialSum (Fin.append y z) (Fin.castAdd n j) = partialSum y j := by
  have hn (i : Fin n) : ¬ Fin.natAdd m i ≤ Fin.castAdd n j := by
    simp only [Fin.le_def,Fin.val_natAdd,Fin.val_castAdd]
    omega
  simp [partialSum_eq_sum_ite,Fin.sum_univ_add,hn]
  simp only [Fin.le_def,Fin.val_castAdd]

theorem survival_append_prefix {m n : ℕ} {c : ℝ}
    {y : Fin m → ℝ} {z : Fin n → ℝ} (h : Fin.append y z ∈ survivalEvent c) :
    y ∈ survivalEvent c := by
  intro j
  rw [← partialSum_append_left y z j]
  exact h _

theorem survival_append_cover {m n : ℕ} {c : ℝ} (hc : 0 ≤ c) (R : ℝ) :
    (appendEquiv m n) ⁻¹' survivalEvent c ⊆
      ((survivalEvent c ∩ {y | R ≤ c-∑ i, y i}) ×ˢ (Set.univ : Set (Fin n → ℝ))) ∪
        (survivalEvent c ×ˢ {z | (∑ i, z i) ≤ R}) := by
  intro p hp
  have hsurv : Fin.append p.1 p.2 ∈ survivalEvent c := hp
  have hy := survival_append_prefix hsurv
  have hs : (∑ i, p.1 i)+(∑ i, p.2 i) ≤ c := by
    simpa only [Fin.sum_univ_add,Fin.append_left,Fin.append_right] using
      sum_le_of_survival hc hsurv
  by_cases hR : R ≤ c-∑ i, p.1 i
  · exact Or.inl ⟨⟨hy,hR⟩,Set.mem_univ _⟩
  · exact Or.inr ⟨hy,by change (∑ i, p.2 i) ≤ R; linarith⟩

theorem gaussian_survival_prefix {m n : ℕ} (v : Fin (m+n) → NNReal) (c : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real (survivalEvent c) := by
  have he : (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) =
      ((Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
        (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))).real
        ((appendEquiv m n) ⁻¹' survivalEvent c) := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv m n).measurable (measurableSet_survivalEvent c)]
  rw [he]
  have hsub : (appendEquiv m n) ⁻¹' survivalEvent c ⊆
      survivalEvent c ×ˢ (Set.univ : Set (Fin n → ℝ)) := by
    intro p hp
    exact ⟨survival_append_prefix (show Fin.append p.1 p.2 ∈ survivalEvent c from hp),
      Set.mem_univ _⟩
  have h := measureReal_mono (μ :=
    (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))) hsub (by finiteness)
  simpa only [measureReal_prod_prod,probReal_univ,mul_one] using h

theorem gaussian_survival_prefix_castLE {m n : ℕ} (hmn : m ≤ n)
    (v : Fin n → NNReal) (c : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castLE hmn i)))).real (survivalEvent c) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact gaussian_survival_prefix v c

theorem gaussian_survival_split {m n : ℕ} (v : Fin (m+n) → NNReal)
    {c : ℝ} (hc : 0 ≤ c) (R : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) ≤
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real
        (survivalEvent c ∩ {y | R ≤ c-∑ i, y i}) +
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real (survivalEvent c) *
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i)))).real
        {z | (∑ i, z i) ≤ R} := by
  have he : (Measure.pi (fun i => gaussianReal 0 (v i))).real (survivalEvent c) =
      ((Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
        (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))).real
        ((appendEquiv m n) ⁻¹' survivalEvent c) := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv m n).measurable (measurableSet_survivalEvent c)]
  rw [he]
  apply (measureReal_mono (survival_append_cover hc R) (by finiteness)).trans
  have h := measureReal_union_le
    (μ := (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i)))))
    ((survivalEvent c ∩ {y | R ≤ c-∑ i, y i}) ×ˢ (Set.univ : Set (Fin n → ℝ)))
    (survivalEvent c ×ˢ {z | (∑ i, z i) ≤ R})
  simpa only [measureReal_prod_prod,probReal_univ,mul_one] using h

end NField.Alignment.HarperGaussianPathSplit
