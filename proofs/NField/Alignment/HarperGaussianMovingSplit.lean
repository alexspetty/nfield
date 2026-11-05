/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLogarithmicDrift

/-!
# Exact splitting for moving Gaussian barriers

The prefix retains its original time indices. The suffix endpoint
allowance includes the entire boundary increase between the two times.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperGaussianMovingSplit
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperMovingKilledPath HarperGaussianPathSplit

theorem moving_append_prefix {m n : ℕ} {B : ℕ → ℝ}
    {y : Fin m → ℝ} {z : Fin n → ℝ} (h : Fin.append y z ∈ movingEvent B) :
    y ∈ movingEvent B := by
  intro j
  rw [← partialSum_append_left y z j]
  exact h _

theorem moving_append_cover {m n : ℕ} {B : ℕ → ℝ} (hB0 : 0 ≤ B 0) (R : ℝ) :
    (appendEquiv m n) ⁻¹' movingEvent B ⊆
      ((movingEvent B ∩ {y | R ≤ B m-∑ i, y i}) ×ˢ (Set.univ : Set (Fin n → ℝ))) ∪
        (movingEvent B ×ˢ {z | (∑ i, z i) ≤ R+(B (m+n)-B m)}) := by
  intro p hp
  have hsurv : Fin.append p.1 p.2 ∈ movingEvent B := hp
  have hy := moving_append_prefix hsurv
  have hs : (∑ i, p.1 i)+(∑ i, p.2 i) ≤ B (m+n) := by
    simpa only [Fin.sum_univ_add,Fin.append_left,Fin.append_right] using
      sum_le_of_moving hB0 hsurv
  by_cases hR : R ≤ B m-∑ i, p.1 i
  · exact Or.inl ⟨⟨hy,hR⟩,Set.mem_univ _⟩
  · exact Or.inr ⟨hy,by change (∑ i, p.2 i) ≤ R+(B (m+n)-B m); linarith⟩

theorem gaussian_moving_prefix {m n : ℕ} (v : Fin (m+n) → NNReal) (B : ℕ → ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent B) ≤
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real (movingEvent B) := by
  have he : (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent B) =
      ((Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
        (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))).real
        ((appendEquiv m n) ⁻¹' movingEvent B) := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv m n).measurable (measurableSet_movingEvent B)]
  rw [he]
  have hsub : (appendEquiv m n) ⁻¹' movingEvent B ⊆
      movingEvent B ×ˢ (Set.univ : Set (Fin n → ℝ)) := by
    intro p hp
    exact ⟨moving_append_prefix (show Fin.append p.1 p.2 ∈ movingEvent B from hp),
      Set.mem_univ _⟩
  have h := measureReal_mono (μ :=
    (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))) hsub (by finiteness)
  simpa only [measureReal_prod_prod,probReal_univ,mul_one] using h

theorem gaussian_moving_prefix_castLE {m n : ℕ} (hmn : m ≤ n)
    (v : Fin n → NNReal) (B : ℕ → ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent B) ≤
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castLE hmn i)))).real (movingEvent B) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact gaussian_moving_prefix v B

theorem gaussian_moving_split {m n : ℕ} (v : Fin (m+n) → NNReal)
    {B : ℕ → ℝ} (hB0 : 0 ≤ B 0) (R : ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent B) ≤
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real
        (movingEvent B ∩ {y | R ≤ B m-∑ i, y i}) +
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).real (movingEvent B) *
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i)))).real
        {z | (∑ i, z i) ≤ R+(B (m+n)-B m)} := by
  have he : (Measure.pi (fun i => gaussianReal 0 (v i))).real (movingEvent B) =
      ((Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
        (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i))))).real
        ((appendEquiv m n) ⁻¹' movingEvent B) := by
    simp only [measureReal_def]
    rw [← (gaussian_append_measurePreserving v).map_eq,
      Measure.map_apply (appendEquiv m n).measurable (measurableSet_movingEvent B)]
  rw [he]
  apply (measureReal_mono (moving_append_cover hB0 R) (by finiteness)).trans
  have h := measureReal_union_le
    (μ := (Measure.pi (fun i => gaussianReal 0 (v (Fin.castAdd n i)))).prod
      (Measure.pi (fun i => gaussianReal 0 (v (Fin.natAdd m i)))))
    ((movingEvent B ∩ {y | R ≤ B m-∑ i, y i}) ×ˢ (Set.univ : Set (Fin n → ℝ)))
    (movingEvent B ×ˢ {z | (∑ i, z i) ≤ R+(B (m+n)-B m)})
  simpa only [measureReal_prod_prod,probReal_univ,mul_one] using h


end NField.Alignment.HarperGaussianMovingSplit
