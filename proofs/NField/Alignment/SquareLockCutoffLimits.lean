/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SquareLockAsymptoticScales

/-! # The two manuscript localization cutoffs and their actual limits -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SquareLockCutoffLimits
open scoped Topology
open Filter Asymptotics SquareLockCarrierMass SquareLockAsymptoticScales

def logarithmicCutoff (j p : ℕ) : ℕ := ⌊(p : ℝ)/Real.log p^j⌋₊

theorem logarithmicCutoff_valid {j : ℕ} (hj : j ≠ 0) :
    ∀ᶠ p : ℕ in atTop, 1 ≤ logarithmicCutoff j p ∧ 2*logarithmicCutoff j p ≤ p := by
  have hs := (Real.isLittleO_pow_log_id_atTop (n := j)).natCast_atTop.bound
    (by norm_num : (0 : ℝ) < 1)
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 : ℝ)
  filter_upwards [hs,hl,eventually_ge_atTop (1 : ℕ)] with p hs hl hp
  change 2 ≤ Real.log (p : ℝ) at hl
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log (p : ℝ) := by linarith
  have hpow : 0 < Real.log (p : ℝ)^j := pow_pos hlog _
  have hlog2 : 2 ≤ Real.log (p : ℝ)^j :=
    hl.trans (le_self_pow₀ (by linarith) hj)
  have hpowle : Real.log (p : ℝ)^j ≤ p := by
    simpa only [Function.comp_apply, id_eq, Real.norm_of_nonneg hpow.le,
      Real.norm_of_nonneg hpR.le, one_mul] using hs
  have hone : (1 : ℝ) ≤ (p : ℝ)/Real.log p^j :=
    (le_div_iff₀ hpow).mpr (by simpa using hpowle)
  have hfloor : (logarithmicCutoff j p : ℝ) ≤ (p : ℝ)/Real.log p^j :=
    Nat.floor_le (by positivity)
  constructor
  · exact Nat.le_floor (by simpa using hone)
  · have : 2*(logarithmicCutoff j p : ℝ) ≤ p := by
      calc
        _ ≤ 2*((p : ℝ)/Real.log p^j) := by gcongr
        _ ≤ p := by rw [← mul_div_assoc]; apply (div_le_iff₀ hpow).mpr; nlinarith
    exact_mod_cast this

theorem fine_cutoff_isLittleO :
    (fun p => (fineSquareLockCutoff p : ℝ)) =o[atTop]
      (fun p => (p : ℝ)/Real.log p^3) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
    exact fun h => (ne_of_gt (div_pos hpR (pow_pos hl 3)) h).elim
  · have hi : Tendsto (fun p : ℕ => (Real.log (p : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
      have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
      positivity
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
      have hf : (fineSquareLockCutoff p : ℝ) ≤ (p : ℝ)/Real.log p^4 :=
        Nat.floor_le (by positivity)
      calc
        _ ≤ ((p : ℝ)/Real.log p^4)/((p : ℝ)/Real.log p^3) := by gcongr
        _ = (Real.log (p : ℝ))⁻¹ := by field_simp

/-- Title: `The fine localization cutoff has vanishing collar mass`. -/
theorem fine_collar_tendsto_zero :
    Tendsto (fun p => squareLockCollarMass p (fineSquareLockCutoff p)) primeAtTop (𝓝 0) :=
  collarMass_tendsto_zero fineSquareLockCutoff
    ((logarithmicCutoff_valid (j := 4) (by norm_num)).filter_mono inf_le_left)
    fine_cutoff_isLittleO

theorem coefficient_cutoff_isLittleO :
    (fun p => (coefficientSquareLockCutoff p : ℝ)) =o[atTop]
      (fun p => (p : ℝ)/Real.log p) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
    exact fun h => (ne_of_gt (div_pos hpR hl) h).elim
  · have hi : Tendsto (fun p : ℕ => (Real.log (p : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
      have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
      positivity
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
      have hf : (coefficientSquareLockCutoff p : ℝ) ≤ (p : ℝ)/Real.log p^2 :=
        Nat.floor_le (by positivity)
      calc
        _ ≤ ((p : ℝ)/Real.log p^2)/((p : ℝ)/Real.log p) := by gcongr
        _ = (Real.log (p : ℝ))⁻¹ := by field_simp

/-- Title: `The coefficient cutoff is negligible for the secondary coefficient`. -/
theorem coefficient_collar_isLittleO_log_square :
    (fun p => squareLockCollarMass p (coefficientSquareLockCutoff p)) =o[primeAtTop]
      (fun p => Real.log (p : ℝ)^2) :=
  collarMass_isLittleO_log_square coefficientSquareLockCutoff
    (coefficientSquareLockCutoff_valid_eventually.filter_mono inf_le_left)
    coefficient_cutoff_isLittleO

/-- Title: `The coefficient collar has logarithmic mass`. -/
theorem coefficient_collar_isBigO_log :
    (fun p => squareLockCollarMass p (coefficientSquareLockCutoff p)) =O[primeAtTop]
      (fun p => Real.log (p : ℝ)) := by
  have hone : (fun _ : ℕ => (1 : ℝ)) =O[atTop] (fun p => Real.log (p : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 : ℝ)] with p hp
    change 1 ≤ Real.log (p : ℝ) at hp
    simpa only [norm_one, one_mul, Real.norm_of_nonneg (by linarith : 0 ≤ Real.log (p : ℝ))] using hp
  have hr : countRemainder =O[atTop] (fun p => Real.log (p : ℝ)) :=
    (((isLittleO_one_iff ℝ).mpr countRemainder_tendsto).trans_isBigO hone).isBigO
  have hw : (fun p => (coefficientSquareLockCutoff p : ℝ)/(p : ℝ)*Real.log p^3)
      =O[atTop] (fun p => Real.log (p : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hl.le, one_mul]
    have hf : (coefficientSquareLockCutoff p : ℝ) ≤ (p : ℝ)/Real.log p^2 :=
      Nat.floor_le (by positivity)
    calc
      _ ≤ ((p : ℝ)/Real.log p^2)/(p : ℝ)*Real.log p^3 := by gcongr
      _ = Real.log (p : ℝ) := by field_simp
  exact (collarMass_isBigO coefficientSquareLockCutoff
    (coefficientSquareLockCutoff_valid_eventually.filter_mono inf_le_left)).trans
      ((hw.add hr).mono inf_le_left)

end NField.Alignment.SquareLockCutoffLimits
