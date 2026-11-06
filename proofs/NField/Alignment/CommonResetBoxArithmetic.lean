/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBoxSummation

/-! # Uniform small-power arithmetic cost for the complete box -/

noncomputable section

namespace NField.Alignment.CommonResetBoxArithmetic

open scoped BigOperators
open CommonResetBoxSummation CommonResetBoxRows CommonResetBandWeighted CommonResetSmallConductors
open CommonResetBandCosts CommonResetDivisorFibers CommonResetTailGrowth

def boxArithmeticCost (p : ℕ) : ℝ := (divisorMaximum p : ℝ)^2*(harmonic p : ℝ)^5

def boxConstant : ℝ := 4*harmonicLiftMass+harmonicLiftMass*rootCubeMass^2+4

theorem boxConstant_pos : 0 < boxConstant := by
  have hT := harmonicLiftMass_nonneg
  unfold boxConstant
  positivity

/-- Title: `The full box divisor maximum and all five harmonic factors cost an arbitrary positive power`. -/
theorem box_arithmetic_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 1 ≤ p → boxArithmeticCost p ≤ C*(p : ℝ)^ε := by
  obtain ⟨D, hD, hd⟩ := divisorMaximum_small_power (ε/4) (by positivity)
  let H : ℝ := 1+1/(ε/10)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨D^2*H^5, by positivity, ?_⟩
  intro p hp
  have hdiv := hd p hp
  have hh := harmonic_small_power (ε/10) (by positivity) hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  calc
    boxArithmeticCost p ≤ (D*(p : ℝ)^(ε/4))^2*(H*(p : ℝ)^(ε/10))^5 := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv 2
      · exact pow_le_pow_left₀ (harmonic_nonneg _) hh 5
      · exact pow_nonneg (harmonic_nonneg _) _
      · positivity
    _ = (D^2*H^5)*(((p : ℝ)^(ε/4))^2*((p : ℝ)^(ε/10))^5) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hpR.le, ← Real.rpow_mul_natCast hpR.le, ← Real.rpow_add hpR]
      congr 2
      ring

theorem absorb_box_harmonics {H s : ℝ} (hH : 1 ≤ H) (hs : 0 ≤ s) :
    H*(harmonicLiftMass*(4*s+rootCubeMass^2)+4*H^4) ≤
      boxConstant*H^5*(s+1) := by
  have hT := harmonicLiftMass_nonneg
  have hTz : 0 ≤ harmonicLiftMass*rootCubeMass^2 := mul_nonneg hT (sq_nonneg _)
  have hH5 : H ≤ H^5 := by
    calc
      _ = H*1 := by ring
      _ ≤ H*H^4 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH) (by linarith)
      _ = _ := by ring
  have hmain : harmonicLiftMass*(4*s+rootCubeMass^2) ≤
      (4*harmonicLiftMass+harmonicLiftMass*rootCubeMass^2)*(s+1) := by
    nlinarith [mul_nonneg hTz hs]
  calc
    _ = H*(harmonicLiftMass*(4*s+rootCubeMass^2))+4*H^5 := by ring
    _ ≤ H^5*((4*harmonicLiftMass+harmonicLiftMass*rootCubeMass^2)*(s+1))+4*H^5 := by
      apply add_le_add (mul_le_mul hH5 hmain (by positivity) (by positivity)) (le_refl _)
    _ ≤ H^5*((4*harmonicLiftMass+harmonicLiftMass*rootCubeMass^2)*(s+1))+4*H^5*(s+1) := by
      exact add_le_add (le_refl _) (le_mul_of_one_le_right (by positivity) (by linarith))
    _ = _ := by unfold boxConstant; ring

/-- Title: `The full rectangular majorant has the printed three-halves box scale`. -/
theorem full_box_majorant {p V J : ℕ} (hp : 1 ≤ p) (hV : V ≤ p) (hJ : J ≤ p) :
    (∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
      (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, ∑ u ∈ Finset.Icc 1 p,
        (u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j)) ≤
      boxConstant*boxArithmeticCost p*((p : ℝ)*Real.sqrt (p : ℝ))*(Real.sqrt ((J : ℝ)*V)+1) := by
  have hD : 0 ≤ (divisorMaximum p : ℝ) := Nat.cast_nonneg _
  have hH := harmonic_nonneg p
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
        (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J,
          (divisorMaximum p : ℝ)^2*(harmonic p : ℝ)*rowCost p m v j) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (harmonic_nonneg _)
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro j hj
      exact sum_complete_band_cost hp (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hv).1
        (Finset.mem_Icc.mp hj).1 ((Finset.mem_Icc.mp hv).2.trans hV) ((Finset.mem_Icc.mp hj).2.trans hJ)
    _ = (divisorMaximum p : ℝ)^2*(harmonic p : ℝ)*
        (∑ m ∈ Finset.Icc 1 p, (harmonic m : ℝ)*
          (∑ v ∈ Finset.Icc 1 V, ∑ j ∈ Finset.Icc 1 J, rowCost p m v j)) := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ (divisorMaximum p : ℝ)^2*(harmonic p : ℝ)*
        ((p : ℝ)*Real.sqrt (p : ℝ)*
          (harmonicLiftMass*(4*Real.sqrt ((J : ℝ)*V)+rootCubeMass^2)+4*(harmonic p : ℝ)^4)) :=
      mul_le_mul_of_nonneg_left (harmonic_box_cost hV hJ) (by positivity)
    _ = (divisorMaximum p : ℝ)^2*((p : ℝ)*Real.sqrt (p : ℝ))*
        ((harmonic p : ℝ)*(harmonicLiftMass*(4*Real.sqrt ((J : ℝ)*V)+rootCubeMass^2)+4*(harmonic p : ℝ)^4)) := by ring
    _ ≤ (divisorMaximum p : ℝ)^2*((p : ℝ)*Real.sqrt (p : ℝ))*
        (boxConstant*(harmonic p : ℝ)^5*(Real.sqrt ((J : ℝ)*V)+1)) :=
      mul_le_mul_of_nonneg_left (absorb_box_harmonics (harmonic_one_le hp) (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by unfold boxArithmeticCost; ring

end NField.Alignment.CommonResetBoxArithmetic
