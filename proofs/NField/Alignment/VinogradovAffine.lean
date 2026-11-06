/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovDiagonal

/-!
# Affine invariance of the integer Vinogradov system

Mathlib's binomial theorem transports all power-sum equations under a common
translation. A nonzero integer dilation can then be cancelled. The resulting
finite counting identity retains repetitions and arbitrary moment order.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovAffine
open scoped BigOperators Classical
open VinogradovDiagonal

/-- Translation preserves the first `k` equations, for any number of coordinates. -/
theorem power_sums_add {R : Type*} [CommRing R] {s k : ℕ}
    (u v : Fin s → R) (a : R)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, u i ^ j = ∑ i, v i ^ j) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, (u i + a) ^ j = ∑ i, (v i + a) ^ j := by
  have hzero (j : ℕ) (hj : j ≤ k) : ∑ i, u i ^ j = ∑ i, v i ^ j := by
    by_cases hj0 : j = 0
    · simp [hj0]
    · exact h j (by omega) hj
  intro j _ hjk
  simp_rw [add_pow]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro l hl
  simp_rw [← Finset.sum_mul]
  rw [hzero l (by have := Finset.mem_range.mp hl; omega)]

/-- A common nonzero affine change preserves and reflects every power-sum equation. -/
theorem power_sums_affine_iff {s k : ℕ} (u v : Fin s → ℤ) (c a : ℤ) (hc : c ≠ 0) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i, (c * u i + a) ^ j = ∑ i, (c * v i + a) ^ j) ↔
    (∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, u i ^ j = ∑ i, v i ^ j) := by
  constructor
  · intro h j hj hjk
    have ht := power_sums_add (fun i => c * u i + a) (fun i => c * v i + a) (-a)
      h j hj hjk
    simp only [add_neg_cancel_right, mul_pow, ← Finset.mul_sum] at ht
    exact mul_left_cancel₀ (pow_ne_zero j hc) ht
  · intro h
    apply power_sums_add (fun i => c * u i) (fun i => c * v i) a
    intro j hj hjk
    simp only [mul_pow, ← Finset.mul_sum, h j hj hjk]

/-- The finite-index form matches the equations in `momentFiber`. -/
theorem power_sums_affine_fin_iff {s k : ℕ} (u v : Fin s → ℤ)
    (c a : ℤ) (hc : c ≠ 0) :
    (∀ j : Fin k, ∑ i, (c * u i + a) ^ (j.val + 1) =
      ∑ i, (c * v i + a) ^ (j.val + 1)) ↔
    (∀ j : Fin k, ∑ i, u i ^ (j.val + 1) = ∑ i, v i ^ (j.val + 1)) := by
  have hindices (x y : Fin s → ℤ) :
      (∀ j : Fin k, ∑ i, x i ^ (j.val + 1) = ∑ i, y i ^ (j.val + 1)) ↔
      (∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) := by
    constructor
    · intro h j hj hjk
      simpa only [Nat.sub_add_cancel hj] using h ⟨j - 1, by omega⟩
    · intro h j
      exact h (j.val + 1) (by omega) (by omega)
  rw [hindices, hindices]
  exact power_sums_affine_iff u v c a hc

/-- The actual affine bijection of coordinate sets. -/
def affineEquiv (S : Finset ℤ) (c a : ℤ) (hc : c ≠ 0) :
    {z // z ∈ S} ≃ {z // z ∈ S.image (fun x => c * x + a)} :=
  Equiv.ofBijective
    (fun z => ⟨c * z.val + a, Finset.mem_image_of_mem _ z.property⟩) (by
      constructor
      · intro x y hxy
        exact Subtype.ext (mul_left_cancel₀ hc
          (add_right_cancel (congrArg Subtype.val hxy)))
      · intro y
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

/-- Nonzero affine changes preserve the literal ordered-pair count. -/
theorem momentCount_affine_image (S : Finset ℤ) (s k : ℕ)
    (c a : ℤ) (hc : c ≠ 0) :
    momentCount (S.image fun x => c * x + a) s k = momentCount S s k := by
  let e : IntegerTuple S s ≃ IntegerTuple (S.image fun x => c * x + a) s :=
    Equiv.piCongrRight fun _ => affineEquiv S c a hc
  rw [momentCount_eq_pair_count, momentCount_eq_pair_count]
  symm
  apply Finset.card_equiv (Equiv.prodCongr e e)
  intro uv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (power_sums_affine_fin_iff (fun i => (uv.2 i).val)
    (fun i => (uv.1 i).val) c a hc).symm

/-- Moving an integer interval does not change its Vinogradov moment count. -/
theorem momentCount_interval_translate (a : ℤ) (H s k : ℕ) :
    momentCount (Finset.Ico a (a + H)) s k =
      momentCount (Finset.Ico 0 (H : ℤ)) s k := by
  have himage : (Finset.Ico 0 (H : ℤ)).image (fun x => (1 : ℤ) * x + a) =
      Finset.Ico a (a + H) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_Ico, one_mul]
    constructor
    · rintro ⟨x, hx, rfl⟩
      omega
    · intro hz
      exact ⟨z - a, by omega, by omega⟩
  rw [← himage]
  exact momentCount_affine_image _ s k 1 a one_ne_zero

/-- Quotient intervals containing zero have the same count as `{1,...,H}`. -/
theorem momentCount_zero_interval_eq_initial (H s k : ℕ) :
    momentCount (Finset.Ico 0 (H : ℤ)) s k =
      momentCount (Finset.Icc 1 (H : ℤ)) s k := by
  have heq : Finset.Icc 1 (H : ℤ) = Finset.Ico 1 (1 + (H : ℤ)) := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [heq]
  exact (momentCount_interval_translate 1 H s k).symm

end NField.Alignment.VinogradovAffine
