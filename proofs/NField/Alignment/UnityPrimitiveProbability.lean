/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeWeights
import NField.Alignment.CollisionPrimitiveMassDisplays

/-!
# Primitive collision probability and the native unity slice

The normalization reuses the already proved Conservation primitive-pair
series. Conditioning retains the actual reciprocal native weights.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityPrimitiveProbability
open scoped BigOperators
open UnityNativeWeights CollisionPrimitivePairAmplitude CollisionPrimitiveMassDisplays

/-- The literal primitive collision probability kernel. -/
def kernel (a b : ℕ) : ℝ := (1/2 : ℝ) * primitivePairMass (a,b)

theorem kernel_formula {a b : ℕ} (hc : a.Coprime b) :
    kernel a b = 1/(2*(a : ℝ)*(b : ℝ)*(a+b)) := by
  simp only [kernel, primitivePairMass, if_pos hc, Nat.cast_add, one_div, mul_inv_rev]
  ring

theorem kernel_nonneg (a b : ℕ) : 0≤kernel a b :=
  mul_nonneg (by norm_num) (primitivePairMass_nonneg (a,b))

theorem kernel_summable : Summable (fun p : ℕ×ℕ => kernel p.1 p.2) :=
  primitivePairMass_summable.mul_left (1/2 : ℝ)

/-- Title: `The primitive collision kernel has total mass one`.

 The actual primitive kernel has total probability one. -/
theorem kernel_total : (∑' p : ℕ×ℕ, kernel p.1 p.2) = 1 := by
  simp only [kernel, tsum_mul_left]
  change (1/2 : ℝ) * (∑' p : ℕ×ℕ, primitivePairMass p) = 1
  rw [primitivePairMass_total]
  norm_num

theorem kernel_one (m : ℕ) : kernel 1 m = weight m / 2 := by
  rw [kernel_formula (Nat.coprime_one_left m)]
  simp only [Nat.cast_one, weight, one_div, mul_inv_rev, div_eq_mul_inv]
  rw [add_comm (1 : ℝ) (m : ℝ)]
  ring

/-- Title: `The unity observation has probability one half`.

 The unity observation has probability exactly one half. -/
theorem first_coordinate_one_mass : (∑' m : ℕ, kernel 1 m) = 1/2 := by
  have hw : HasSum weight 1 := by
    simpa using ((hasSum_nat_add_iff 1).mp weights_hasSum)
  simp_rw [kernel_one]
  rw [tsum_div_const, hw.tsum_eq]

/-- Title: `Conditioning on unity gives the native reciprocal weights`.

 Conditioning the primitive probability on the unity observation gives
exactly the paper's native Hilbert weights. -/
theorem unity_conditional_weight (m : ℕ) :
    kernel 1 m / (∑' n : ℕ, kernel 1 n) = weight m := by
  rw [kernel_one, first_coordinate_one_mass]
  ring

/-- Period weighting yields the conservative mass. -/
def periodMass (a b : ℕ) : ℝ := 1/(2*(a : ℝ)*(b : ℝ))

/-- Title: `Period weighting gives the conservative primitive mass`. -/
theorem period_weighted_kernel {a b : ℕ} (ha : 0<a) (hb : 0<b) (hc : a.Coprime b) :
    ((a+b : ℕ) : ℝ) * kernel a b = periodMass a b := by
  rw [kernel_formula hc]
  unfold periodMass
  have ha0 : (a : ℝ)≠0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℝ)≠0 := by exact_mod_cast hb.ne'
  have hab : (a : ℝ)+(b : ℝ)≠0 := by positivity
  push_cast
  field_simp

/-- Title: `Primitive period mass splits conservatively`.

 Exact conservative splitting on the two primitive-tree children. -/
theorem period_mass_conservation {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    periodMass a b = periodMass a (a+b) + periodMass (a+b) b := by
  have ha0 : (a : ℝ)≠0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℝ)≠0 := by exact_mod_cast hb.ne'
  have hab : (a : ℝ)+(b : ℝ)≠0 := by positivity
  unfold periodMass
  push_cast
  field_simp
  ring

/-- Title: `Exact positive defect in primitive probability splitting`.

 The probability itself loses positive mass under one child split; it
is the period-weighted mass above which is conservative. -/
theorem probability_split_defect {a b : ℕ} (ha : 0<a) (hb : 0<b) (hc : a.Coprime b) :
    kernel a b-kernel a (a+b)-kernel (a+b) b =
      3/(2*((a+b : ℕ) : ℝ)*((2*a+b : ℕ) : ℝ)*((a+2*b : ℕ) : ℝ)) := by
  have hcl : a.Coprime (a+b) := by simpa using hc
  have hcr : (a+b).Coprime b := by simpa using hc
  rw [kernel_formula hc, kernel_formula hcl, kernel_formula hcr]
  have ha0 : (a : ℝ)≠0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℝ)≠0 := by exact_mod_cast hb.ne'
  have hab : (a : ℝ)+(b : ℝ)≠0 := by positivity
  have haab : (a : ℝ)+((a : ℝ)+(b : ℝ))≠0 := by positivity
  have habb : (a : ℝ)+(b : ℝ)+(b : ℝ)≠0 := by positivity
  have h2ab : 2*(a : ℝ)+(b : ℝ)≠0 := by positivity
  have ha2b : (a : ℝ)+2*(b : ℝ)≠0 := by positivity
  push_cast
  field_simp
  ring

theorem probability_split_defect_pos {a b : ℕ} (ha : 0<a) (hb : 0<b) (hc : a.Coprime b) :
    0 < kernel a b-kernel a (a+b)-kernel (a+b) b := by
  rw [probability_split_defect ha hb hc]
  positivity

/-- Title: `The primitive antidiagonal equals the collision marginal`.

 The primitive antidiagonal is the existing collision marginal. -/
theorem kernel_antidiagonal (n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, kernel p.1 p.2) =
      CollisionRemainderDynamics.collisionWeight n := by
  simp only [kernel, ← Finset.mul_sum]
  change (1/2 : ℝ) * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
    primitivePairMass p) = _
  rw [primitivePairMass_antidiagonal]
  ring

end NField.Alignment.UnityPrimitiveProbability
