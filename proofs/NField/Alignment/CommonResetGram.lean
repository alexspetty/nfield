/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRampEnergy

/-! # The weighted continuous clock energy

The published real-weight statement follows from the already proved literal
midpoint sawtooth integral. All cross terms are kept before integration.
-/

noncomputable section

namespace NField.Alignment.CommonResetGram

open scoped BigOperators
open MeasureTheory CollisionRampEnergy

def weightedProfile (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.Icc 1 N, c j * midpointRow j x

theorem midpointProduct_intervalIntegrable {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (a b : ℝ) :
    IntervalIntegrable (fun x => midpointRow r x * midpointRow s x) volume a b := by
  apply (affineProduct_intervalIntegrable r s a b).congr_ae
  apply ae_restrict_of_ae
  filter_upwards [midpointRow_ae_affineRow hr, midpointRow_ae_affineRow hs]
    with x hx hy
  simp only [hx, hy]

theorem weightedProfile_square (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    weightedProfile N c x ^ 2 =
      4 * ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (c j * c k) * (midpointRow j x * midpointRow k x) := by
  rw [weightedProfile, mul_pow, show (2 : ℝ)^2 = 4 by norm_num,
    pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Title: `The weighted clock energy is its GCD quadratic form`. -/
theorem weighted_gram (N : ℕ) (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, weightedProfile N c x ^ 2) =
      (1 / 3 : ℝ) * ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (j.gcd k : ℝ)^2 / ((j : ℝ) * (k : ℝ)) := by
  have hint (j k : ℕ) (hj : j ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
      IntervalIntegrable (fun x => (c j*c k)*(midpointRow j x*midpointRow k x))
        volume 0 1 :=
    (midpointProduct_intervalIntegrable (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hk).1 0 1).const_mul _
  have hrow (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      IntervalIntegrable (fun x => ∑ k ∈ Finset.Icc 1 N,
        (c j*c k)*(midpointRow j x*midpointRow k x)) volume 0 1 :=
    ⟨integrable_finsetSum _ (fun k hk => (hint j k hj hk).1),
      integrable_finsetSum _ (fun k hk => (hint j k hj hk).2)⟩
  simp only [weightedProfile_square]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum hrow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_finsetSum (fun k hk => hint j k hj hk),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_const_mul,
    midpoint_ramp_gram (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1]
  ring

/-- Title: `Unit clock weights give the continuous energy profile`. -/
theorem unit_weights (N : ℕ) : weightedProfile N (fun _ => 1) = boundaryResponse N := by
  ext x
  simp [weightedProfile, boundaryResponse]

/-- Title: `The continuous energy retains every pair of clocks`. -/
theorem unweighted_gram (N : ℕ) :
    (∫ x in (0 : ℝ)..1, boundaryResponse N x ^ 2) =
      (1 / 3 : ℝ) * ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (j.gcd k : ℝ)^2 / ((j : ℝ) * (k : ℝ)) := by
  simpa only [unit_weights, one_mul] using weighted_gram N (fun _ => 1)

end NField.Alignment.CommonResetGram
