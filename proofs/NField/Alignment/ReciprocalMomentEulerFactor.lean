/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.ReciprocalDivisorMomentBound
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The literal three-variable local factor for the reciprocal-divisor moment -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalMomentEulerFactor
open scoped BigOperators Classical

def exponent (v : ℕ × ℕ × ℕ) : ℕ := v.1+v.2.1+v.2.2+max v.1 (max v.2.1 v.2.2)
def localTerm (r : ℝ) (v : ℕ × ℕ × ℕ) : ℝ := r^exponent v
def geometricTerm (r : ℝ) (v : ℕ × ℕ × ℕ) : ℝ := r^(v.1+v.2.1+v.2.2)

theorem triple_geometric_hasSum {r : ℝ} (hr : 0≤r) (hr1 : r<1) :
    HasSum (geometricTerm r) (((1-r)⁻¹)^3) := by
  have h := hasSum_geometric_of_norm_lt_one (ξ := r)
    (by simpa only [Real.norm_eq_abs,abs_of_nonneg hr] using hr1)
  have hs2 := h.summable.mul_of_nonneg h.summable (fun n => pow_nonneg hr n) (fun n => pow_nonneg hr n)
  have h2 := h.mul h hs2
  have hs3 := h.summable.mul_of_nonneg h2.summable (fun n => pow_nonneg hr n)
    (fun v => mul_nonneg (pow_nonneg hr v.1) (pow_nonneg hr v.2))
  have h3 : HasSum (fun v : ℕ × ℕ × ℕ => r^v.1*(r^v.2.1*r^v.2.2))
      ((1-r)⁻¹*((1-r)⁻¹*(1-r)⁻¹)) := h.mul h2 hs3
  change HasSum (fun v : ℕ × ℕ × ℕ => r^(v.1+v.2.1+v.2.2)) (((1-r)⁻¹)^3)
  simpa only [pow_add,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using h3

theorem local_term_summable {r : ℝ} (hr : 0≤r) (hr1 : r<1) : Summable (localTerm r) := by
  apply (triple_geometric_hasSum hr hr1).summable.of_nonneg_of_le
  · intro v; exact pow_nonneg hr _
  · intro v
    exact pow_le_pow_of_le_one hr hr1.le (by dsimp [exponent]; omega)

theorem local_term_majorant {r : ℝ} (hr : 0≤r) (hr1 : r≤1) (v : ℕ × ℕ × ℕ) :
    localTerm r v≤r*geometricTerm r v+(if v=(0,0,0) then 1-r else 0) := by
  by_cases hv : v=(0,0,0)
  · subst v
    simp [localTerm,geometricTerm,exponent]
  · have hmax : 1 ≤ max v.1 (max v.2.1 v.2.2) := by
      by_contra hn
      have ha : v.1=0 := by omega
      have hb : v.2.1=0 := by omega
      have hc : v.2.2=0 := by omega
      apply hv
      exact Prod.ext ha (Prod.ext hb hc)
    have hp := pow_le_pow_of_le_one hr hr1
      (show v.1+v.2.1+v.2.2+1≤exponent v by dsimp [exponent]; omega)
    simpa only [localTerm,geometricTerm,if_neg hv,pow_succ,add_zero,mul_comm] using hp

theorem geometric_remainder_bound {r : ℝ} (hr : 0≤r) (hrh : r≤1/2) :
    r*(((1-r)⁻¹)^3-1)≤24*r^2 := by
  have hpos : 0<1-r := by linarith
  have hden : (1/8 : ℝ)≤(1-r)^3 := by nlinarith [sq_nonneg (r-1/2)]
  have he : r*(((1-r)⁻¹)^3-1)=(r*(1-(1-r)^3))/(1-r)^3 := by field_simp
  rw [he]
  apply (div_le_iff₀ (pow_pos hpos 3)).mpr
  have hnum : r*(1-(1-r)^3)≤3*r^2 := by
    have hr2 : r^2≥0 := sq_nonneg r
    have hr3 : 0≤r^3 := pow_nonneg hr 3
    have hprod := mul_nonneg hr3 (show 3-r≥0 by linarith)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hden (show 0≤24*r^2 by positivity)
  nlinarith

theorem local_factor_bound {r : ℝ} (hr : 0≤r) (hrh : r≤1/2) :
    |(∑' v : ℕ × ℕ × ℕ,localTerm r v)-1|≤24*r^2 := by
  have hr1 : r<1 := by linarith
  have hs := local_term_summable hr hr1
  have hlo := hs.le_tsum (0,0,0) (fun v _ => pow_nonneg hr (exponent v))
  simp only [localTerm,exponent,max_self,add_zero,pow_zero] at hlo
  change 1≤∑' v : ℕ × ℕ × ℕ,localTerm r v at hlo
  have hgeo := triple_geometric_hasSum hr hr1
  have hmajor := (hgeo.mul_left r).add (hasSum_ite_eq (0,0,0) (1-r))
  have hhi := hs.tsum_le_tsum (local_term_majorant hr hr1.le) hmajor.summable
  rw [hmajor.tsum_eq] at hhi
  rw [abs_of_nonneg (by linarith : 0≤(∑' v : ℕ × ℕ × ℕ,localTerm r v)-1)]
  have hb := geometric_remainder_bound hr hrh
  nlinarith

def localFactor (ℓ : ℕ) : ℝ :=
  ∑' v : ℕ × ℕ × ℕ,(ℓ : ℝ)^(- (exponent v : ℤ))

/-- Title: `The local Euler factor is one plus a square-decaying error`. -/
theorem local_euler_factor {ℓ : ℕ} (hℓ : 2≤ℓ) :
    Summable (fun v : ℕ × ℕ × ℕ => (ℓ : ℝ)^(- (exponent v : ℤ))) ∧
      |localFactor ℓ-1|≤24/(ℓ : ℝ)^2 := by
  have hℓ0 : (0 : ℝ)<ℓ := by exact_mod_cast (by omega : 0<ℓ)
  have hr : 0≤1/(ℓ : ℝ) := by positivity
  have hrh : 1/(ℓ : ℝ)≤1/2 := one_div_le_one_div_of_le (by norm_num)
    (by exact_mod_cast hℓ)
  have he : (fun v : ℕ × ℕ × ℕ => (ℓ : ℝ)^(- (exponent v : ℤ)))=
      localTerm (1/(ℓ : ℝ)) := by
    ext v
    simp only [localTerm,zpow_neg,zpow_natCast,one_div,inv_pow]
  refine ⟨by rw [he]; exact local_term_summable hr (by linarith),?_⟩
  unfold localFactor
  rw [he]
  convert local_factor_bound hr hrh using 1 <;> ring

end NField.Alignment.ReciprocalMomentEulerFactor
