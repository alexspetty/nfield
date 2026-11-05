/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialTheorem

/-!
# A finite perturbation of the collision mass

The perturbation has zero mass and first moment. Its nonzero Haar potential
is retained exactly in the infinite limit and in every integer readout.
-/

noncomputable section

namespace NField.Alignment.CollisionMassPerturbation

open scoped BigOperators
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialConvergence

def perturbation (k : ℕ) : ℝ :=
  if k = 2 then 1 else if k = 3 then -2 else if k = 4 then 1 else 0

def perturbedWeight (ε : ℝ) (k : ℕ) : ℝ := collisionWeight k + ε * perturbation k

theorem perturbation_eq_indicators (k : ℕ) :
    perturbation k = (if k=2 then (1 : ℝ) else 0) -
      2*(if k=3 then (1 : ℝ) else 0) + (if k=4 then (1 : ℝ) else 0) := by
  by_cases h2 : k = 2
  · simp [h2, perturbation]
  by_cases h3 : k = 3
  · norm_num [h3, perturbation]
  by_cases h4 : k = 4
  · simp [h4, perturbation]
  simp [perturbation, h2, h3, h4]

theorem perturbation_support {k : ℕ} (hk : k ∉ Finset.Icc 2 4) : perturbation k = 0 := by
  have h2 : k ≠ 2 := by intro h; subst k; norm_num at hk
  have h3 : k ≠ 3 := by intro h; subst k; norm_num at hk
  have h4 : k ≠ 4 := by intro h; subst k; norm_num at hk
  simp [perturbation, h2, h3, h4]

theorem perturbation_finite_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : ℕ → E) {M : ℕ} (hM : 4 ≤ M) :
    (∑ k ∈ Finset.Icc 2 M, perturbation k • F k) = F 2 - (2 : ℝ) • F 3 + F 4 := by
  have hs : (∑ k ∈ Finset.Icc 2 4, perturbation k • F k) =
      ∑ k ∈ Finset.Icc 2 M, perturbation k • F k := by
    apply Finset.sum_subset
    · exact Finset.Icc_subset_Icc le_rfl hM
    · intro k _ hk
      rw [perturbation_support hk, zero_smul]
  rw [← hs, show Finset.Icc 2 4 = {2,3,4} from by decide]
  norm_num [perturbation, sub_eq_add_neg]
  abel

theorem perturbedWeight_pos {ε : ℝ} (hε : |ε| < 1/24) {k : ℕ} (hk : 2 ≤ k) :
    0 < perturbedWeight ε k := by
  have he := abs_lt.mp hε
  by_cases h2 : k = 2
  · subst k
    rw [perturbedWeight, collisionWeight_two]
    norm_num [perturbation]
    linarith
  by_cases h3 : k = 3
  · subst k
    rw [perturbedWeight, collisionWeight_three]
    norm_num [perturbation]
    linarith
  by_cases h4 : k = 4
  · subst k
    rw [perturbedWeight, collisionWeight_four]
    norm_num [perturbation]
    linarith
  simpa [perturbedWeight, perturbation, h2, h3, h4] using collisionWeight_pos hk

theorem perturbation_hasSum : HasSum perturbation 0 := by
  have h : HasSum perturbation (∑ k ∈ Finset.Icc 2 4, perturbation k) :=
    hasSum_sum_of_ne_finset_zero (f := perturbation) (s := Finset.Icc 2 4)
    (fun k hk => perturbation_support hk)
  norm_num [show Finset.Icc 2 4 = {2,3,4} from by decide, perturbation] at h
  exact h

theorem perturbedWeight_hasSum (ε : ℝ) : HasSum (perturbedWeight ε) 1 := by
  change HasSum (fun k => collisionWeight k + ε * perturbation k) 1
  simpa using collisionWeight_hasSum.add (perturbation_hasSum.mul_left ε)

def perturbationPotential : HaarL2 := finitePotential perturbation 4

theorem finitePotential_perturbed (ε : ℝ) {M : ℕ} (hM : 4 ≤ M) :
    finitePotential (perturbedWeight ε) M =
      finitePotential collisionWeight M + ε • perturbationPotential := by
  simp only [finitePotential, perturbedWeight, add_smul, mul_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  rw [perturbation_finite_sum remainderVector hM]
  unfold perturbationPotential finitePotential
  rw [perturbation_finite_sum remainderVector le_rfl]
  module

theorem perturbed_potential_tendsto (ε : ℝ) :
    Tendsto (finitePotential (perturbedWeight ε)) atTop
      (nhds (collisionPotential + ε • perturbationPotential)) := by
  apply Tendsto.congr' (f₁ := fun M => finitePotential collisionWeight M + ε • perturbationPotential)
  · filter_upwards [eventually_ge_atTop 4] with M hM
    exact (finitePotential_perturbed ε hM).symm
  · exact tendsto_collisionPotential.add_const _

theorem perturbationPotential_mean : ∫ x, perturbationPotential x ∂phaseHaar = 0 := by
  rw [← mean_inner_eq_integral]
  exact finitePotential_mean_inner perturbation 4

theorem perturbationPotential_variance : ‖perturbationPotential‖^2 = (56/27 : ℝ) := by
  rw [perturbationPotential, finite_potential_norm_sq]
  rw [show Finset.Icc 2 4 = {2,3,4} from by decide]
  norm_num [perturbation]

theorem perturbationPotential_ne_zero : perturbationPotential ≠ 0 := by
  intro h
  have hv := perturbationPotential_variance
  norm_num [h] at hv

theorem perturbed_stationaryAge (ε : ℝ) {M : ℕ} (hM : 4 ≤ M) :
    stationaryAge (perturbedWeight ε) M = stationaryAge collisionWeight M := by
  unfold stationaryAge perturbedWeight
  simp only [add_mul, Finset.sum_add_distrib]
  have hz : (∑ k ∈ Finset.Icc 2 M, perturbation k * ((k : ℝ)-1)) = 0 := by
    have h := perturbation_finite_sum (fun k => (k : ℝ)-1) hM
    norm_num [smul_eq_mul] at h
    exact h
  simp only [mul_assoc, ← Finset.mul_sum, hz, mul_zero, add_zero]

def perturbationReadout (n : ℕ) : ℝ :=
  (2/3 : ℝ) * (((n%2 : ℕ) : ℝ) - 2 * ((n%3 : ℕ) : ℝ) + ((n%4 : ℕ) : ℝ))

theorem perturbation_finite_age {M : ℕ} (hM : 4 ≤ M) (n : ℕ) :
    finiteAge perturbation M n = perturbationReadout n := by
  unfold finiteAge
  have h := perturbation_finite_sum (fun k => centeredRemainder k n) hM
  simp only [smul_eq_mul] at h
  rw [h]
  unfold centeredRemainder perturbationReadout
  push_cast
  ring

theorem perturbationPotential_coe :
    (fun x => perturbationPotential x) =ᵐ[phaseHaar]
      (fun x => (2/3 : ℝ) * (centered 2 x - 2 * centered 3 x + centered 4 x)) := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (potentialMap perturbation 4)
  rw [← finitePotential_toLp] at h
  filter_upwards [h] with x hx
  rw [show perturbationPotential x = potentialMap perturbation 4 x from hx]
  simp only [potentialMap, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    remainderMap, ContinuousMap.coe_mk, smul_eq_mul]
  have hs := perturbation_finite_sum (fun k => centered k x) (M := 4) le_rfl
  simpa only [smul_eq_mul] using congrArg (fun z : ℝ => (2/3 : ℝ)*z) hs

theorem perturbation_readout_hasSum (n : ℕ) :
    HasSum (fun k => perturbation k * ((n%k : ℕ) : ℝ))
      (((n%2 : ℕ) : ℝ) - 2 * ((n%3 : ℕ) : ℝ) + ((n%4 : ℕ) : ℝ)) := by
  have h : HasSum (fun k => perturbation k * ((n%k : ℕ) : ℝ))
      (∑ k ∈ Finset.Icc 2 4, perturbation k * ((n%k : ℕ) : ℝ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    rw [perturbation_support hk, zero_mul]
  have he := perturbation_finite_sum (fun k => ((n%k : ℕ) : ℝ)) (M := 4) le_rfl
  simp only [smul_eq_mul] at he
  rwa [he] at h

def perturbedDeficit (ε : ℝ) (n : ℕ) : ℝ :=
  (2/3 : ℝ) * ∑' k, perturbedWeight ε k * ((n%k : ℕ) : ℝ)

theorem perturbed_deficit_eq (ε : ℝ) (n : ℕ) :
    perturbedDeficit ε n = deficit n + ε * perturbationReadout n := by
  unfold perturbedDeficit
  have hs : Summable (fun k => collisionWeight k * ((n%k : ℕ) : ℝ)) :=
    remainder_age_summable n
  have ht := (perturbation_readout_hasSum n).mul_left ε
  have he : (fun k => perturbedWeight ε k * ((n%k : ℕ) : ℝ)) =
      (fun k => collisionWeight k * ((n%k : ℕ) : ℝ) +
        ε * (perturbation k * ((n%k : ℕ) : ℝ))) := by
    funext k
    unfold perturbedWeight
    ring
  rw [he, hs.tsum_add ht.summable, ht.tsum_eq]
  rw [mul_add]
  unfold perturbationReadout deficit
  ring

theorem perturbed_potential_ne {ε : ℝ} (hε : ε ≠ 0) :
    collisionPotential + ε • perturbationPotential ≠ collisionPotential := by
  intro h
  have hz : ε • perturbationPotential = 0 :=
    add_left_cancel (show collisionPotential + ε • perturbationPotential =
      collisionPotential + 0 by simpa using h)
  exact (smul_ne_zero hε perturbationPotential_ne_zero) hz

theorem perturbationReadout_periodic (n : ℕ) :
    perturbationReadout (n+12) = perturbationReadout n := by
  simp [perturbationReadout, Nat.add_mod]

/-- The positive unit family, its actual limiting potential and all its readouts. -/
theorem mass_perturbation {ε : ℝ} (hε : |ε| < 1/24) :
    (∀ k, 2 ≤ k → 0 < perturbedWeight ε k) ∧
    HasSum (perturbedWeight ε) 1 ∧
    Tendsto (finitePotential (perturbedWeight ε)) atTop
      (nhds (collisionPotential + ε • perturbationPotential)) ∧
    (∫ x, perturbationPotential x ∂phaseHaar) = 0 ∧
    ‖perturbationPotential‖^2 = (56/27 : ℝ) ∧
    (∀ n, perturbedDeficit ε n = deficit n + ε * perturbationReadout n) ∧
    (∀ M, 4 ≤ M → stationaryAge (perturbedWeight ε) M = stationaryAge collisionWeight M) := by
  exact ⟨fun _ hk => perturbedWeight_pos hε hk, perturbedWeight_hasSum ε,
    perturbed_potential_tendsto ε, perturbationPotential_mean,
    perturbationPotential_variance, perturbed_deficit_eq ε,
    fun _ hM => perturbed_stationaryAge ε hM⟩

end NField.Alignment.CollisionMassPerturbation
