/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteFamilyEnergy
import Mathlib.Algebra.BigOperators.Pi

/-! # Character factorization and disjoint coordinate-axis supports -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteFamilyFourier
open scoped BigOperators ComplexConjugate Classical
open CenteredCollisionSum FiniteFamilyTransversality

theorem prod_split_coordinate {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (i : ι) (f : ι → M) : ∏ j, f j = f i * ∏ j : {j // j ≠ i}, f j := by
  classical
  rw [← Finset.mul_prod_erase _ f (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_subtype _ (by simp) f

/-- The coefficient formula, with every inactive-coordinate average displayed. -/
theorem coordinate_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (i : ι) (f : α i → ℂ) (χ : ∀ i, α i → ℂ) :
    finiteCoefficient (fun x : ∀ j, α j => f (x i)) (fun x => ∏ j, χ j (x j)) =
      finiteCoefficient f (χ i) *
        ∏ j : {j // j ≠ i}, finiteMean (fun a => star (χ j a)) := by
  classical
  let β := ∀ j : {j // j ≠ i}, α j
  have hp (x : ∀ j, α j) :
      f (x i) * star (∏ j, χ j (x j)) =
        (f (x i) * star (χ i (x i))) * ∏ j : {j // j ≠ i}, star (χ j (x j)) := by
    rw [star_prod, prod_split_coordinate i]
    ring
  change finiteMean (fun x : ∀ j, α j => f (x i) * star (∏ j, χ j (x j))) = _
  simp_rw [hp]
  calc
    _ = finiteMean (fun x : α i × β =>
        (f x.1 * star (χ i x.1)) * ∏ j : {j // j ≠ i}, star (χ j (x.2 j))) :=
      finiteMean_equiv (Equiv.piSplitAt i α) _
    _ = _ := by
      rw [finiteMean_prod (fun a : α i => f a * star (χ i a))
        (fun y : β => ∏ j : {j // j ≠ i}, star (χ j (y j)))]
      have h := finiteMean_pi_prod
        (α := fun j : {j : ι // j ≠ i} => α j.val) (fun j a => star (χ j a))
      change finiteMean (fun a => f a * star (χ i a)) * _ = _
      congr 1

/-- Mathlib's homomorphism equivalence gives existence and uniqueness of all factors. -/
theorem character_factorization {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type*}
    [∀ i, CommMonoid (G i)] (χ : (∀ i, G i) →* ℂ) :
    ∃! ψ : ∀ i, G i →* ℂ, ∀ x, χ x = ∏ i, ψ i (x i) := by
  classical
  let e := Pi.monoidHomMulEquiv G ℂ
  have he (ψ : ∀ i, G i →* ℂ) (x : ∀ i, G i) : e.symm ψ x = ∏ i, ψ i (x i) := by
    simp [e, Pi.monoidHomMulEquiv]
  refine ⟨e χ, ?_, ?_⟩
  · intro x
    rw [← he, e.symm_apply_apply]
  · intro ψ hψ
    apply e.symm.injective
    apply MonoidHom.ext
    intro x
    rw [he, e.symm_apply_apply]
    exact (hψ x).symm

theorem character_sum_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : χ ≠ 1) : ∑ a, χ a = 0 := by
  classical
  have hex : ∃ a, χ a ≠ 1 := by
    by_contra h
    apply hχ
    ext a
    simpa using not_exists_not.mp h a
  obtain ⟨a, ha⟩ := hex
  apply eq_zero_of_mul_eq_self_left ha
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun x => (map_mul χ a x).symm)

theorem character_star_mean_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : χ ≠ 1) : finiteMean (fun a => star (χ a)) = 0 := by
  simp only [finiteMean, ← star_sum, character_sum_zero χ hχ, star_zero, mul_zero]

theorem off_axis_coefficient_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] (i : ι) (f : G i → ℂ)
    (χ : ∀ i, G i →* ℂ) {j : ι} (hji : j ≠ i) (hχ : χ j ≠ 1) :
    finiteCoefficient (fun x : ∀ k, G k => f (x i)) (fun x => ∏ k, χ k (x k)) = 0 := by
  classical
  rw [coordinate_coefficient]
  have hz : (∏ k : {k // k ≠ i}, finiteMean (fun a => star (χ k a))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {k : ι // k ≠ i}))
    exact character_star_mean_zero (χ j) hχ
  rw [hz, mul_zero]

theorem principal_coefficient_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] (i : ι) (f : G i → ℂ)
    (hf : ∑ a, f a = 0) :
    finiteCoefficient (fun x : ∀ k, G k => f (x i)) (fun _ => 1) = 0 := by
  simp only [finiteCoefficient, star_one, mul_one, coordinate_sum_zero i f hf, mul_zero]

/-- Two different coordinate lifts cannot share a nonzero Fourier coefficient. -/
theorem disjoint_coordinate_support {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] {i j : ι} (hij : i ≠ j)
    (f : G i → ℂ) (g : G j → ℂ) (hf : ∑ a, f a = 0)
    (χ : ∀ i, G i →* ℂ) :
    finiteCoefficient (fun x : ∀ k, G k => f (x i)) (fun x => ∏ k, χ k (x k)) = 0 ∨
      finiteCoefficient (fun x : ∀ k, G k => g (x j)) (fun x => ∏ k, χ k (x k)) = 0 := by
  classical
  by_cases h : ∃ k, k ≠ i ∧ χ k ≠ 1
  · obtain ⟨k, hki, hk⟩ := h
    exact Or.inl (off_axis_coefficient_zero i f χ hki hk)
  · by_cases hi : χ i = 1
    · have hall (k : ι) : χ k = 1 := by
        by_cases hk : k = i
        · subst k
          exact hi
        · by_contra hn
          exact h ⟨k, hk, hn⟩
      left
      simpa only [hall, MonoidHom.one_apply, Finset.prod_const_one] using
        principal_coefficient_zero i f hf
    · exact Or.inr (off_axis_coefficient_zero j g χ hij hi)

end NField.Alignment.FiniteFamilyFourier
