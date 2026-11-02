/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRoundedCutoff

/-!
# Decay of the complete conditioning-box error factor

The definitions retain the actual rounded Harper parameters and all A
partition factors. The logarithmic identity and eventual negative bound
are proved before the two fractional powers are estimated. No analytic
comparison error or positive lower bound on individual box weights is
assumed. Deriving those errors from the actual partition remains separate.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperConditioningDecay

open Filter Asymptotics
open scoped Topology
open HarperParameterBounds HarperRoundedCutoff

def alpha : ℝ := 3/4

def boxCount (ell : ℝ) : ℝ :=
  (2*(rangeCount ell : ℝ)+2)^(partitionCount ell)

def boxError (ell : ℝ) : ℝ :=
  ((rangeCount ell : ℝ)*ell)^(-partitionCount ell * precision ell^(-2 : ℝ))

def errorMass (ell : ℝ) : ℝ := boxCount ell * boxError ell

theorem box_count_cardinality (x : ℝ) :
    (Fintype.card (Fin (factorCount x) →
      Fin (2*rangeCount (cutoffLog x)+2)) : ℝ) = boxCount (cutoffLog x) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [← Real.rpow_natCast, factorCount_eq]
  rfl

theorem parameter_definitions (ell : ℝ) :
    alpha = 3/4 ∧
    boxError ell = ((rangeCount ell : ℝ)*ell)^(-partitionCount ell * precision ell^(-2 : ℝ)) ∧
    boxCount ell = (2*(rangeCount ell : ℝ)+2)^(partitionCount ell) :=
  ⟨rfl, rfl, rfl⟩

theorem boxCount_pos (ell : ℝ) : 0 < boxCount ell := by
  apply Real.rpow_pos_of_pos
  positivity

theorem errorMass_pos {ell : ℝ} (hell : 0 < ell) (hlog : 1 ≤ Real.log ell) :
    0 < errorMass ell := by
  have hj : (0 : ℝ) < rangeCount ell := lt_of_lt_of_le zero_lt_one
    (rangeCount_bounds hell hlog).1
  exact mul_pos (boxCount_pos ell) (Real.rpow_pos_of_pos (mul_pos hj hell) _)

theorem precision_inverse_square {ell : ℝ} (hell : 0 ≤ ell) :
    precision ell^(-2 : ℝ) = ell^(13/5 : ℝ) := by
  rw [precision, ← Real.rpow_mul hell]
  norm_num

theorem log_errorMass {ell : ℝ} (hell : 0 < ell) (hlog : 1 ≤ Real.log ell) :
    Real.log (errorMass ell) = partitionCount ell *
      (Real.log (2*(rangeCount ell : ℝ)+2) -
        precision ell^(-2 : ℝ)*Real.log ((rangeCount ell : ℝ)*ell)) := by
  have hj : (0 : ℝ) < rangeCount ell := lt_of_lt_of_le zero_lt_one
    (rangeCount_bounds hell hlog).1
  have hb : 0 < 2*(rangeCount ell : ℝ)+2 := by positivity
  have hp : 0 < (rangeCount ell : ℝ)*ell := mul_pos hj hell
  have he : 0 < boxError ell := Real.rpow_pos_of_pos hp _
  rw [errorMass, Real.log_mul (boxCount_pos ell).ne' he.ne', boxCount, boxError,
    Real.log_rpow hb, Real.log_rpow hp]
  ring

theorem log_box_alphabet_bound {ell : ℝ} (hell : 2 ≤ ell)
    (hlog : 1 ≤ Real.log ell) :
    Real.log (2*(rangeCount ell : ℝ)+2) ≤ 2*Real.log ((rangeCount ell : ℝ)*ell) := by
  have hj := (rangeCount_bounds (by linarith : 0 < ell) hlog).1
  have hb : 0 < 2*(rangeCount ell : ℝ)+2 := by positivity
  have hs : (4 : ℝ) ≤ ell^2 := by nlinarith
  have hj2 : (rangeCount ell : ℝ) ≤ (rangeCount ell : ℝ)^2 := by nlinarith
  have hprod : 2*(rangeCount ell : ℝ)+2 ≤ ((rangeCount ell : ℝ)*ell)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (rangeCount ell : ℝ))]
  calc
    _ ≤ Real.log (((rangeCount ell : ℝ)*ell)^2) := Real.log_le_log hb hprod
    _ = _ := by rw [Real.log_pow]; norm_num

theorem log_errorMass_bound {ell : ℝ} (hell : 4 ≤ ell)
    (hlog : 1 ≤ Real.log ell) :
    Real.log (errorMass ell) ≤
      -(1/2 : ℝ)*partitionCount ell*precision ell^(-2 : ℝ)*
        Real.log ((rangeCount ell : ℝ)*ell) := by
  have hellp : 0 < ell := by linarith
  have ha := (partitionCount_pos hellp.le).le
  have hjlog := (log_range_product_bound hellp hlog).1
  have hb := log_box_alphabet_bound (by linarith : 2 ≤ ell) hlog
  have hd : 4 ≤ precision ell^(-2 : ℝ) := by
    rw [precision_inverse_square hellp.le]
    calc
      _ ≤ ell := hell
      _ ≤ ell^(13/5 : ℝ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (by linarith : 1 ≤ ell) (by norm_num : (1 : ℝ) ≤ 13/5)
  have ht : Real.log (2*(rangeCount ell : ℝ)+2) -
      precision ell^(-2 : ℝ)*Real.log ((rangeCount ell : ℝ)*ell) ≤
      -(1/2 : ℝ)*precision ell^(-2 : ℝ)*Real.log ((rangeCount ell : ℝ)*ell) := by
    nlinarith [mul_le_mul_of_nonneg_right hd hjlog]
  rw [log_errorMass hellp hlog]
  nlinarith [mul_le_mul_of_nonneg_left ht ha]

theorem eventual_log_errorMass : ∀ᶠ ell : ℝ in atTop,
    Real.log (errorMass ell) = partitionCount ell *
      (Real.log (2*(rangeCount ell : ℝ)+2) -
        precision ell^(-2 : ℝ)*Real.log ((rangeCount ell : ℝ)*ell)) ∧
    Real.log (errorMass ell) ≤
      -(1/2 : ℝ)*partitionCount ell*precision ell^(-2 : ℝ)*
        Real.log ((rangeCount ell : ℝ)*ell) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with ell hell hlog
  exact ⟨log_errorMass (by linarith) hlog, log_errorMass_bound hell hlog⟩

theorem eventual_errorMass_le_rpow (t : ℝ) :
    ∀ᶠ ell : ℝ in atTop, errorMass ell ≤ ell^(-t) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13/5)).eventually_ge_atTop (2*t)]
    with ell hell hlog hdelta
  have hellp : 0 < ell := by linarith
  have hj := (rangeCount_bounds hellp hlog).1
  have ha : 1 ≤ partitionCount ell := by
    unfold partitionCount
    have h := Real.rpow_nonneg hellp.le (51/50 : ℝ)
    linarith
  have hd : 0 ≤ precision ell^(-2 : ℝ) :=
    (Real.rpow_pos_of_pos (precision_pos hellp) _).le
  have hdt : 2*t ≤ precision ell^(-2 : ℝ) := by
    simpa only [precision_inverse_square hellp.le] using hdelta
  have hlogle : Real.log ell ≤ Real.log ((rangeCount ell : ℝ)*ell) := by
    apply Real.log_le_log hellp
    nlinarith
  have hjlog := (log_range_product_bound hellp hlog).1
  have hcost : 2*t*Real.log ell ≤
      partitionCount ell * precision ell^(-2 : ℝ)*Real.log ((rangeCount ell : ℝ)*ell) := by
    calc
      _ ≤ precision ell^(-2 : ℝ)*Real.log ell :=
        mul_le_mul_of_nonneg_right hdt (by linarith)
      _ ≤ precision ell^(-2 : ℝ)*Real.log ((rangeCount ell : ℝ)*ell) :=
        mul_le_mul_of_nonneg_left hlogle hd
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right ha (mul_nonneg hd hjlog)]
  have hbound : Real.log (errorMass ell) ≤ -t*Real.log ell := by
    have h := log_errorMass_bound hell hlog
    nlinarith
  have h := Real.exp_le_exp.mpr hbound
  rw [Real.exp_log (errorMass_pos hellp hlog)] at h
  simpa only [Real.rpow_def_of_pos hellp, mul_comm] using h

theorem eventual_powered_errorMass_le_rpow {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) :
    ∀ᶠ ell : ℝ in atTop, (errorMass ell)^beta ≤ ell^(-t) := by
  filter_upwards [eventual_errorMass_le_rpow (t/beta), eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with ell hmass hell hlog
  have h := Real.rpow_le_rpow (errorMass_pos hell hlog).le hmass hbeta.le
  rw [← Real.rpow_mul hell.le] at h
  have he : (-(t/beta))*beta = -t := by field_simp
  simpa only [he] using h

theorem powered_errorMass_isBigO_inverse {beta : ℝ} (hbeta : 0 < beta) :
    (fun ell => (errorMass ell)^beta) =O[atTop] (fun ell : ℝ => ell⁻¹) := by
  apply IsBigO.of_bound'
  filter_upwards [eventual_powered_errorMass_le_rpow hbeta 1,
    eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with ell hmass hell hlog
  rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos (errorMass_pos hell hlog) _).le,
    Real.norm_of_nonneg (inv_nonneg.mpr hell.le)]
  simpa only [Real.rpow_neg_one] using hmass

theorem inverse_cutoff_isLittleO_loglog :
    (fun x => (cutoffLog x)⁻¹) =o[atTop]
      (fun x => (Real.log (Real.log x))^(-(3/8 : ℝ))) := by
  have hsmall : (fun x => (Real.log (Real.log x))^(3/8 : ℝ)) =o[atTop] cutoffLog :=
    ((isLittleO_log_rpow_rpow_atTop (3/8 : ℝ) (by norm_num : (0 : ℝ) < 1/6)).comp_tendsto
      Real.tendsto_log_atTop).trans_isBigO cutoffLog_asymptotic.symm.isBigO
  have hi := hsmall.inv_rev (by
    filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
      with x hx
    dsimp only [Function.comp_apply] at hx
    intro hz
    exact ((Real.rpow_pos_of_pos hx (3/8 : ℝ)).ne' hz).elim)
  apply hi.congr' Filter.EventuallyEq.rfl
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with x hx
  dsimp only [Function.comp_apply] at hx
  rw [Real.rpow_neg hx.le]

theorem rounded_powered_errorMass_isLittleO {beta : ℝ} (hbeta : 0 < beta) :
    (fun x => (errorMass (cutoffLog x))^beta) =o[atTop]
      (fun x => (Real.log (Real.log x))^(-(3/8 : ℝ))) :=
  ((powered_errorMass_isBigO_inverse hbeta).comp_tendsto cutoffLog_tendsto).trans_isLittleO
    inverse_cutoff_isLittleO_loglog

def polynomialLossScale (x : ℝ) : ℝ := x^alpha * (errorMass (cutoffLog x))^alpha

def weightLossScale (x : ℝ) : ℝ := x^alpha * (errorMass (cutoffLog x))^(1-alpha)

def targetScale (x : ℝ) : ℝ := x^(3/4 : ℝ) * (Real.log (Real.log x))^(-(3/8 : ℝ))

theorem accumulated_loss_scales_decay :
    polynomialLossScale =o[atTop] targetScale ∧ weightLossScale =o[atTop] targetScale := by
  constructor
  · exact (isBigO_refl (fun x : ℝ => x^(3/4 : ℝ)) atTop).mul_isLittleO
      (rounded_powered_errorMass_isLittleO (by norm_num [alpha] : 0 < alpha))
  · exact (isBigO_refl (fun x : ℝ => x^(3/4 : ℝ)) atTop).mul_isLittleO
      (rounded_powered_errorMass_isLittleO (by norm_num [alpha] : 0 < 1-alpha))

theorem prime_square_log_errorMass : ∀ᶠ p : ℕ in atTop,
    let ell := cutoffLog ((p : ℝ)-1)
    Real.log (errorMass ell) = partitionCount ell *
      (Real.log (2*(rangeCount ell : ℝ)+2) -
        precision ell^(-2 : ℝ)*Real.log ((rangeCount ell : ℝ)*ell)) ∧
    Real.log (errorMass ell) ≤
      -(1/2 : ℝ)*partitionCount ell*precision ell^(-2 : ℝ)*
        Real.log ((rangeCount ell : ℝ)*ell) :=
  base_minus_one_tendsto.eventually (cutoffLog_tendsto.eventually eventual_log_errorMass)

theorem prime_square_loss_scales_decay :
    (fun p : ℕ => polynomialLossScale ((p : ℝ)-1)) =o[atTop]
      (fun p : ℕ => targetScale ((p : ℝ)-1)) ∧
    (fun p : ℕ => weightLossScale ((p : ℝ)-1)) =o[atTop]
      (fun p : ℕ => targetScale ((p : ℝ)-1)) :=
  ⟨accumulated_loss_scales_decay.1.comp_tendsto base_minus_one_tendsto,
    accumulated_loss_scales_decay.2.comp_tendsto base_minus_one_tendsto⟩

end NField.Alignment.HarperConditioningDecay
