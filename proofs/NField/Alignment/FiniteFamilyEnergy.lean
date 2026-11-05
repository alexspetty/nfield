/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteFamilyTransversality

/-! # Weighted energy and recovery for arbitrary finite coordinate families -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteFamilyEnergy
open scoped BigOperators ComplexConjugate Classical
open DoubleTransversality FiniteFamilyTransversality

theorem finiteMean_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (f : ι → α → ℂ) :
    finiteMean (fun x => ∑ i, f i x) = ∑ i, finiteMean (f i) := by
  unfold finiteMean
  rw [Finset.sum_comm, Finset.mul_sum]

theorem finiteMean_mul_const {α : Type*} [Fintype α] (f : α → ℂ) (w : ℂ) :
    finiteMean (fun x => w * f x) = w * finiteMean f := by
  unfold finiteMean
  rw [← Finset.mul_sum]
  ring

theorem finiteInner_sum_left {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℂ) (g : α → ℂ) :
    finiteInner (fun x => ∑ i, f i x) g = ∑ i, finiteInner (f i) g := by
  unfold finiteInner
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem finiteInner_sum_right {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : α → ℂ) (g : ι → α → ℂ) :
    finiteInner f (fun x => ∑ i, g i x) = ∑ i, finiteInner f (g i) := by
  unfold finiteInner
  simp_rw [star_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem finiteInner_mul_left_mul_right {α : Type*} [Fintype α]
    (f g : α → ℂ) (w v : ℂ) :
    finiteInner (fun x => w * f x) (fun x => v * g x) =
      (w * star v) * finiteInner f g := by
  have hp (x : α) : (w * f x) * star (v * g x) = (w * star v) * (f x * star (g x)) := by
    rw [star_mul]
    ring
  simp only [finiteInner, hp, ← Finset.mul_sum]
  ring

theorem weighted_energy_of_orthogonal {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℂ) (w : ι → ℂ) (hf : ∀ i j, i ≠ j → finiteInner (f i) (f j) = 0) :
    finiteEnergy (fun x => ∑ i, w i * f i x) = ∑ i, (w i * star (w i)) * finiteEnergy (f i) := by
  unfold finiteEnergy
  rw [finiteInner_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteInner_sum_right]
  simp_rw [finiteInner_mul_left_mul_right]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hf i j (Ne.symm hji), mul_zero]
  · simp

/-- The complete finite-family Pythagorean identity for arbitrary complex weights. -/
theorem coordinate_weighted_energy {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (f : ∀ i, α i → ℂ) (hf : ∀ i, ∑ x, f i x = 0) (w : ι → ℂ) :
    finiteEnergy (fun x : ∀ i, α i => ∑ i, w i * f i (x i)) =
      ∑ i, (w i * star (w i)) * finiteEnergy (f i) := by
  have h := weighted_energy_of_orthogonal (fun i (x : ∀ i, α i) => f i (x i)) w
    (fun i j hij => coordinate_orthogonal hij (f i) (f j) (hf i) (hf j))
  simpa only [coordinate_energy] using h

/-- Averaging every other coordinate recovers exactly the selected weighted signal. -/
theorem recover_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (f : ∀ i, α i → ℂ) (hf : ∀ i, ∑ x, f i x = 0) (w : ι → ℂ) (i : ι) (a : α i) :
    finiteMean (fun y : ∀ j : {j // j ≠ i}, α j =>
      ∑ j, w j * f j ((Equiv.piSplitAt i α).symm (a, y) j)) = w i * f i a := by
  classical
  rw [finiteMean_sum]
  rw [Finset.sum_eq_single i]
  · simp [Equiv.piSplitAt_symm_apply, finiteMean_const]
  · intro j _ hji
    have hz : finiteMean (fun y : ∀ k : {k : ι // k ≠ i}, α k => f j (y ⟨j, hji⟩)) = 0 := by
      have h := finiteMean_pi_coordinate
        (α := fun k : {k : ι // k ≠ i} => α k.val) ⟨j, hji⟩ (f j)
      simpa only [finiteMean, hf j, mul_zero] using h
    simp only [Equiv.piSplitAt_symm_apply, dif_neg hji]
    rw [finiteMean_mul_const, hz, mul_zero]
  · simp

end NField.Alignment.FiniteFamilyEnergy
