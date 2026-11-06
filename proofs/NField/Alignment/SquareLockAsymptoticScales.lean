/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryLocalizationUnconditional

/-! # The exact logarithmic scales in square-lock localization -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SquareLockAsymptoticScales
open scoped Topology
open Filter Asymptotics SquareLockCarrierMass

def primeAtTop : Filter ℕ := atTop ⊓ principal {p | p.Prime}
def countRemainder (p : ℕ) : ℝ := (p : ℝ)^(-1/3 : ℝ)*Real.log p^3
def collarScale (C : ℕ → ℕ) (p : ℕ) : ℝ :=
  ((C p : ℕ) : ℝ)/(p : ℝ)*Real.log p^3+countRemainder p

theorem log_double_le {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ Real.log (2*(p : ℝ)) ∧ Real.log (2*(p : ℝ)) ≤ 2*Real.log p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  constructor
  · exact Real.log_nonneg (by nlinarith [show (2 : ℝ) ≤ p by exact_mod_cast hp])
  · rw [Real.log_mul (by norm_num) hp0.ne']
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hp : (2 : ℝ) ≤ p)
    linarith

theorem countRemainder_nonneg (p : ℕ) : 0 ≤ countRemainder p := by
  by_cases hp : p=0
  · simp [hp, countRemainder]
  · have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)
    unfold countRemainder
    positivity

theorem countRemainder_tendsto : Tendsto countRemainder atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 1/3)).natCast_atTop.tendsto_div_nhds_zero
  convert h using 1
  ext p
  simp only [countRemainder, Real.rpow_ofNat]
  rw [show (-1/3 : ℝ) = -(1/3 : ℝ) by ring, Real.rpow_neg (Nat.cast_nonneg p)]
  ring

theorem collarMass_nonneg (p C : ℕ) : 0 ≤ squareLockCollarMass p C := by
  unfold squareLockCollarMass carrierAbsoluteCollar
  positivity

theorem localization_scale_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p C, p.Prime → 1 ≤ C → 2*C ≤ p →
      squareLockCollarMass p C ≤ K*((C : ℝ)/(p : ℝ)*Real.log p^3+countRemainder p) := by
  rcases SecondaryLocalizationUnconditional.square_lock_localization with ⟨K,hK,hbound⟩
  refine ⟨8*K, by positivity, ?_⟩
  intro p C hp hC hhalf
  have hl := log_double_le hp.two_le
  have hcube : Real.log (2*(p : ℝ))^3 ≤ 8*Real.log p^3 := by
    calc
      _ ≤ (2*Real.log p)^3 := pow_le_pow_left₀ hl.1 hl.2 _
      _ = _ := by ring
  calc
    _ ≤ K*((C : ℝ)/(p : ℝ)*Real.log (2*p)^3+
        Real.rpow p (-1/3 : ℝ)*Real.log (2*p)^3) := hbound p C hp hC hhalf
    _ ≤ K*((C : ℝ)/(p : ℝ)*(8*Real.log p^3)+
        Real.rpow p (-1/3 : ℝ)*(8*Real.log p^3)) := by
      gcongr
      exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    _ = _ := by change K*(_+ (p : ℝ)^(-1/3 : ℝ)*_) = _; unfold countRemainder; ring

theorem collarMass_isBigO (C : ℕ → ℕ)
    (hC : ∀ᶠ p in primeAtTop, 1 ≤ C p ∧ 2*C p ≤ p) :
    (fun p => squareLockCollarMass p (C p)) =O[primeAtTop] collarScale C := by
  rcases localization_scale_bound with ⟨K,hK,hbound⟩
  apply IsBigO.of_bound K
  have hp : ∀ᶠ p in primeAtTop, p.Prime := by
    exact eventually_inf_principal.mpr (Eventually.of_forall fun _ hp => hp)
  filter_upwards [hp,hC] with p hp hC
  rw [Real.norm_of_nonneg (collarMass_nonneg _ _)]
  have hscale : 0 ≤ collarScale C p := by
    unfold collarScale
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg
      (by exact_mod_cast hp.one_lt.le)
    positivity [countRemainder_nonneg p]
  rw [Real.norm_of_nonneg hscale]
  exact hbound p (C p) hp hC.1 hC.2

theorem weighted_cutoff_tendsto (C : ℕ → ℕ)
    (hC : (fun p => (C p : ℝ)) =o[atTop] (fun p => (p : ℝ)/Real.log p^3)) :
    Tendsto (fun p => (C p : ℝ)/(p : ℝ)*Real.log p^3) atTop (𝓝 0) := by
  convert hC.tendsto_div_nhds_zero using 1
  ext p
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Title: `Vanishing collar mass below the fine threshold`. -/
theorem collarMass_tendsto_zero (C : ℕ → ℕ)
    (hvalid : ∀ᶠ p in primeAtTop, 1 ≤ C p ∧ 2*C p ≤ p)
    (hC : (fun p => (C p : ℝ)) =o[atTop] (fun p => (p : ℝ)/Real.log p^3)) :
    Tendsto (fun p => squareLockCollarMass p (C p)) primeAtTop (𝓝 0) := by
  have hs : Tendsto (collarScale C) atTop (𝓝 0) := by
    change Tendsto (fun p : ℕ => (C p : ℝ)/(p : ℝ)*Real.log (p : ℝ)^3+countRemainder p) atTop (𝓝 0)
    simpa only [add_zero] using
      (weighted_cutoff_tendsto C hC).add countRemainder_tendsto
  exact (isLittleO_one_iff ℝ).mp ((collarMass_isBigO C hvalid).trans_isLittleO
    (((isLittleO_one_iff ℝ).mpr hs).mono inf_le_left))

theorem one_isBigO_log_square : (fun _ : ℕ => (1 : ℝ)) =O[atTop]
    (fun p => Real.log (p : ℝ)^2) := by
  apply IsBigO.of_bound 1
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 : ℝ)] with p hp
  change 1 ≤ Real.log (p : ℝ) at hp
  rw [norm_one, one_mul, Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith

/-- Title: `Negligible collar mass at the coefficient scale`. -/
theorem collarMass_isLittleO_log_square (C : ℕ → ℕ)
    (hvalid : ∀ᶠ p in primeAtTop, 1 ≤ C p ∧ 2*C p ≤ p)
    (hC : (fun p => (C p : ℝ)) =o[atTop] (fun p => (p : ℝ)/Real.log p)) :
    (fun p => squareLockCollarMass p (C p)) =o[primeAtTop] (fun p => Real.log (p : ℝ)^2) := by
  have hw : (fun p => (C p : ℝ)/(p : ℝ)*Real.log p^3) =o[atTop]
      (fun p => Real.log (p : ℝ)^2) := by
    have h := hC.mul_isBigO (isBigO_refl (fun p : ℕ => Real.log (p : ℝ)^3/(p : ℝ)) atTop)
    apply h.congr'
    · exact Eventually.of_forall (fun p => by ring)
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hl : 0 < Real.log (p : ℝ) := Real.log_pos
        (by exact_mod_cast (show 1 < p by omega))
      field_simp
  have hr : countRemainder =o[atTop] (fun p => Real.log (p : ℝ)^2) :=
    ((isLittleO_one_iff ℝ).mpr countRemainder_tendsto).trans_isBigO one_isBigO_log_square
  exact (collarMass_isBigO C hvalid).trans_isLittleO ((hw.add hr).mono inf_le_left)

end NField.Alignment.SquareLockAsymptoticScales
