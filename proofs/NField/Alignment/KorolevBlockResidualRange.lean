/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalPrimeSlices

/-! # Exact residual support imposed by the product cutoff in a prime block -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevBlockResidualRange
open KorolevCanonicalPrimeSlices KorolevLogarithmicPartition
open scoped BigOperators Classical

def residualBound (l X : ℕ) (u v : ℝ) : ℕ := min X ⌊(X : ℝ)/((l : ℝ)^2*u*v)⌋₊

/-- Block lower endpoints give a lower bound for the actual represented integer. -/
theorem lower_product_le_value (l p q h : ℕ) {u v : ℝ}
    (_hu : 0 ≤ u) (hv : 0 ≤ v) (hp : u ≤ p) (hq : v ≤ q) :
    (l : ℝ)^2*u*v*h ≤ (l^2*p*q*h : ℕ) := by
  have hpq := mul_le_mul hp hq hv (Nat.cast_nonneg p)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpq (sq_nonneg (l : ℝ))) (Nat.cast_nonneg h)
  push_cast
  nlinarith only [hh]

/-- A contributing product forces its residual factor into the endpoint-based range. -/
theorem residual_le_bound {l p q h X : ℕ} {u v : ℝ} (hl : 0 < l)
    (hu : 0 < u) (hv : 0 < v) (hp : u ≤ p) (hq : v ≤ q)
    (hh : h ≤ X) (hcap : l^2*p*q*h ≤ X) : h ≤ residualBound l X u v := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hd : 0 < (l : ℝ)^2*u*v := by positivity
  have hval := lower_product_le_value l p q h hu.le hv.le hp hq
  have hcapR : ((l^2*p*q*h : ℕ) : ℝ) ≤ X := by exact_mod_cast hcap
  have hr : (h : ℝ) ≤ (X : ℝ)/((l : ℝ)^2*u*v) :=
    (le_div_iff₀ hd).mpr (by nlinarith only [hval, hcapR])
  exact le_min hh (Nat.le_floor hr)

/-- The support range never enlarges the original residual interval. -/
theorem residualBound_le_X (l X : ℕ) (u v : ℝ) : residualBound l X u v ≤ X := min_le_left _ _

/-- The number of residual candidates is bounded by the normalized product capacity. -/
theorem residualBound_le_ratio (l X : ℕ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (residualBound l X u v : ℝ) ≤ (X : ℝ)/((l : ℝ)^2*u*v) := by
  have hr : 0 ≤ (X : ℝ)/((l : ℝ)^2*u*v) := by positivity
  exact (show (residualBound l X u v : ℝ) ≤ ⌊(X : ℝ)/((l : ℝ)^2*u*v)⌋₊ by
    exact Nat.cast_le.mpr (min_le_right X ⌊(X : ℝ)/((l : ℝ)^2*u*v)⌋₊)).trans (Nat.floor_le hr)

/-- Above the support range every summand vanishes, retaining all ambient canonical cutoffs. -/
theorem primeSliceOn_eq_zero {G : Type*} [AddCommMonoid G]
    (P Q P₀ Q₀ : Finset ℕ) (l h X m : ℕ) (f : ℕ → G)
    {u v : ℝ} (hl : 0 < l) (hu : 0 < u) (hv : 0 < v)
    (hP : ∀ p ∈ P₀, u ≤ (p : ℝ)) (hQ : ∀ q ∈ Q₀, v ≤ (q : ℝ))
    (hh : h ≤ X) (hlarge : residualBound l X u v < h) :
    primeSliceOn P Q P₀ Q₀ l h X m f = 0 := by
  unfold primeSliceOn
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  have hn : ¬l^2*p*q*h ≤ X := fun hc =>
    (not_lt_of_ge (residual_le_bound hl hu hv (hP p hp) (hQ q hq) hh hc)) hlarge
  simp only [hn, and_false, ite_false]

/-- Exact truncation of the unit/squarefree residual sum, with no change to its summands. -/
theorem sum_residual_truncated {G : Type*} [AddCommMonoid G]
    (P Q P₀ Q₀ : Finset ℕ) (l X m : ℕ) (f : ℕ → G)
    {u v : ℝ} (hl : 0 < l) (hu : 0 < u) (hv : 0 < v)
    (hP : ∀ p ∈ P₀, u ≤ (p : ℝ)) (hQ : ∀ q ∈ Q₀, v ≤ (q : ℝ)) :
    (∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
      primeSliceOn P Q P₀ Q₀ l h X m f) =
      ∑ h ∈ (Finset.Icc 1 (residualBound l X u v)).filter (fun h => Squarefree h ∧ h.Coprime m),
        primeSliceOn P Q P₀ Q₀ l h X m f := by
  symm
  apply Finset.sum_subset
  · intro h hh
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2.trans (residualBound_le_X l X u v)⟩, hc⟩
  · intro h hh hn
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hh
    have hlarge : residualBound l X u v < h := by
      by_contra hf
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hr).1, by omega⟩, hc⟩)
    exact primeSliceOn_eq_zero P Q P₀ Q₀ l h X m f hl hu hv hP hQ
      (Finset.mem_Icc.mp hr).2 hlarge

/-- Actual logarithmic blocks satisfy the lower-endpoint hypotheses of exact residual truncation. -/
theorem sum_block_residual_truncated {G : Type*} [AddCommMonoid G]
    (P Q : Finset ℕ) (l X m : ℕ) (f : ℕ → G) (lp lq Dp Dq A : ℝ) (i j : ℕ)
    (hl : 0 < l) :
    (∑ h ∈ (Finset.Icc 1 X).filter (fun h => Squarefree h ∧ h.Coprime m),
      primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f) =
      ∑ h ∈ (Finset.Icc 1 (residualBound l X (point lp Dp A i) (point lq Dq A j))).filter
        (fun h => Squarefree h ∧ h.Coprime m),
        primeSliceOn P Q (block lp Dp A i) (block lq Dq A j) l h X m f := by
  apply sum_residual_truncated P Q _ _ l X m f hl (Real.exp_pos _) (Real.exp_pos _)
  · intro p hp
    exact (KorolevPrimeIntervals.intervalPrimes_mem.mp hp).2.1.le
  · intro q hq
    exact (KorolevPrimeIntervals.intervalPrimes_mem.mp hq).2.1.le

end NField.Alignment.KorolevBlockResidualRange
