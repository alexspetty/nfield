/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StationaryPeriodicMoments
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # The bounded-variation weighted first moment, with its actual variation constant -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.StationaryWeightedMoments
open scoped BigOperators
open Set CollisionRemainderDynamics StationaryDiagonalDefinitions StationaryPeriodicBounds
  StationaryPeriodicMoments

theorem finite_age_prefix_bound (L N : ℕ) :
    |∑ n ∈ Finset.range N, finiteAge collisionWeight L n| ≤ (1 / 3 : ℝ) * squareWeightedMass L := by
  have he : (∑ n ∈ Finset.range N, finiteAge collisionWeight L n) =
      (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 L, collisionWeight k * ∑ n ∈ Finset.range N, centeredRemainder k n := by
    simp only [finiteAge, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  calc
    _ ≤ (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 L,
        |collisionWeight k * ∑ n ∈ Finset.range N, centeredRemainder k n| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (2 / 3 : ℝ) * ∑ k ∈ Finset.Icc 2 L, collisionWeight k * ((k : ℝ) ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
      have hh := periodic_prefix_bound hk0 (centered_remainder_periodic k)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2) (centered_remainder_abs hk0) (centered_cycle_sum hk0) N
      have hh' : |∑ n ∈ Finset.range N, centeredRemainder k n| ≤ (k : ℝ) ^ 2 / 2 := by convert hh using 1 <;> ring
      rw [abs_mul, abs_of_nonneg (collisionWeight_nonneg k)]
      exact mul_le_mul_of_nonneg_left hh' (collisionWeight_nonneg k)
    _ = _ := by
      unfold squareWeightedMass
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem weighted_interval_bound {f g : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hf : ∀ N, |∑ n ∈ Finset.range N, f n| ≤ A)
    {a b : ℕ} (hab : a < b) :
    |∑ n ∈ Finset.Ioc a b, g n * f n| ≤
      A * (|g b| + |g (a + 1)| + ∑ n ∈ Finset.Ioc a (b - 1), |g (n + 1) - g n|) := by
  have he := Finset.sum_Ioc_by_parts g f hab
  simp only [smul_eq_mul] at he
  rw [he]
  calc
    _ ≤ |g b * ∑ n ∈ Finset.range (b + 1), f n| +
        |g (a + 1) * ∑ n ∈ Finset.range (a + 1), f n| +
        |∑ n ∈ Finset.Ioc a (b - 1), (g (n + 1) - g n) * ∑ i ∈ Finset.range (n + 1), f i| := by
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ |g b| * A + |g (a + 1)| * A +
        ∑ n ∈ Finset.Ioc a (b - 1), |g (n + 1) - g n| * A := by
      apply add_le_add
      · apply add_le_add <;> rw [abs_mul]
        · exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n hn => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem variation_dyadic_grid_bound {h : ℝ → ℝ} (hh : BoundedVariationOn h (Icc 1 2))
    {X : ℕ} (hX : 0 < X) :
    (∑ n ∈ Finset.Ioc X (2 * X - 1), |h ((n + 1 : ℕ) / (X : ℝ)) - h (n / (X : ℝ))|) ≤
      (eVariationOn h (Icc 1 2)).toReal := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hmono : MonotoneOn (fun n : ℕ => (n : ℝ) / X) (Icc (X + 1) (2 * X)) := by
    intro i hi j hj hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hX0.le
  have hmem : ∀ i ∈ Icc (X + 1) (2 * X), (i : ℝ) / X ∈ Icc 1 2 := by
    intro i hi
    have hi1 : X + 1 ≤ i := hi.1
    refine ⟨(le_div_iff₀ hX0).mpr ?_, (div_le_iff₀ hX0).mpr ?_⟩
    · have h : (X : ℝ) ≤ i := by exact_mod_cast (show X ≤ i by omega)
      simpa using h
    · exact_mod_cast hi.2
  have hv := eVariationOn.sum_le_of_monotoneOn_Icc (f := h) hmono hmem
  have hr := ENNReal.toReal_mono hh hv
  rw [ENNReal.toReal_sum (by simp [edist_ne_top])] at hr
  simp only [edist_dist, Real.dist_eq, ENNReal.toReal_ofReal (abs_nonneg _)] at hr
  have he : Finset.Ioc X (2 * X - 1) = Finset.Ico (X + 1) (2 * X) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  simpa only [he] using hr

def weightedMomentConstant (h : ℝ → ℝ) : ℝ :=
  2 * |h 1| + 3 * (eVariationOn h (Icc 1 2)).toReal

/-- Title: `A bounded-variation macroscopic weight preserves the periodic first-moment rate`. -/
theorem weighted_periodic_first_moment {h : ℝ → ℝ} (hh : BoundedVariationOn h (Icc 1 2))
    {L X : ℕ} (hL : 1 ≤ L) (hX : 0 < X) :
    |dyadicMean X (fun n => h (n / (X : ℝ)) * finiteAge collisionWeight L n)| ≤
      (1 / 3 : ℝ) * weightedMomentConstant h * (L : ℝ) * (1 + Real.log L) / X := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hS := squareWeightedMass_nonneg L
  have hb {t : ℝ} (ht : t ∈ Icc 1 2) : |h t| ≤ |h 1| + (eVariationOn h (Icc 1 2)).toReal := by
    have hd := hh.dist_le ht (by norm_num : (1 : ℝ) ∈ Icc 1 2)
    rw [Real.dist_eq] at hd
    calc
      _ ≤ |h t - h 1| + |h 1| := by simpa using abs_add_le (h t - h 1) (h 1)
      _ ≤ _ := by linarith
  have hb2 := hb (t := ((2 * X : ℕ) : ℝ) / X) (by
    have he : ((2 * X : ℕ) : ℝ) / X = 2 := by push_cast; field_simp
    rw [he]; norm_num)
  have hb1 := hb (t := ((X + 1 : ℕ) : ℝ) / X) (by
    constructor
    · apply (le_div_iff₀ hX0).mpr; push_cast; linarith
    · apply (div_le_iff₀ hX0).mpr; push_cast; linarith)
  have hg := weighted_interval_bound (g := fun n => h (n / (X : ℝ)))
    (by positivity : 0 ≤ (1 / 3 : ℝ) * squareWeightedMass L)
    (finite_age_prefix_bound L) (by omega : X < 2 * X)
  have hc : 0 ≤ weightedMomentConstant h := by unfold weightedMomentConstant; positivity
  have hbracket : |h (((2 * X : ℕ) : ℝ) / X)| + |h (((X + 1 : ℕ) : ℝ) / X)| +
      (∑ n ∈ Finset.Ioc X (2 * X - 1), |h (((n + 1 : ℕ) : ℝ) / X) - h ((n : ℝ) / X)|) ≤
      weightedMomentConstant h := by
    unfold weightedMomentConstant
    linarith [variation_dyadic_grid_bound hh hX]
  unfold dyadicMean
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hX0.le)]
  calc
    _ ≤ (X : ℝ)⁻¹ * ((1 / 3 : ℝ) * squareWeightedMass L * weightedMomentConstant h) := by
      exact mul_le_mul_of_nonneg_left (hg.trans (mul_le_mul_of_nonneg_left hbracket
        (by positivity : 0 ≤ (1 / 3 : ℝ) * squareWeightedMass L))) (inv_nonneg.mpr hX0.le)
    _ ≤ (X : ℝ)⁻¹ * ((1 / 3 : ℝ) * ((L : ℝ) * (1 + Real.log L)) * weightedMomentConstant h) := by
      gcongr
      exact squareWeightedMass_bound hL
    _ = _ := by ring

end NField.Alignment.StationaryWeightedMoments
