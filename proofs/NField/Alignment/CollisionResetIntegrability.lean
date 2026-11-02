/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialTheorem
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.PSeries

/-!
# Integrability of the infinite divisor-reset function

Each reset cylinder has Haar probability 1/k. The collision mass therefore
gives an absolutely summable family in every finite L^p, p >= 1.
-/

noncomputable section

namespace NField.Alignment.CollisionResetIntegrability

open scoped BigOperators ENNReal
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout

def resetSet (k : ℕ) : Set Phase :=
  if hk : 0 < k then
    letI : NeZero k := ⟨hk.ne'⟩
    {x | (residueHom k x).toAdd = 0}
  else ∅

theorem resetSet_measurable (k : ℕ) : MeasurableSet (resetSet k) := by
  unfold resetSet
  split_ifs with hk
  · letI : NeZero k := ⟨hk.ne'⟩
    exact (isClosed_eq ((continuous_of_discreteTopology).comp
      (residueHom k).continuous_toFun) continuous_const).measurableSet
  · exact MeasurableSet.empty

theorem resetSet_measure_real {k : ℕ} (hk : 0 < k) :
    phaseHaar.real (resetSet k) = 1 / (k : ℝ) := by
  letI : NeZero k := ⟨hk.ne'⟩
  rw [← integral_indicator_one (resetSet_measurable k)]
  have he : (resetSet k).indicator (1 : Phase → ℝ) =
      fun x => if (residueHom k x).toAdd.val = 0 then 1 else 0 := by
    funext x
    simp [resetSet, hk, Set.indicator_apply, ZMod.val_eq_zero]
  rw [he]
  simpa [hk] using (integral_residue k (fun j => if j = 0 then (1 : ℝ) else 0))

def resetTerm (k : ℕ) : Phase → ℝ :=
  (resetSet k).indicator (fun _ => (k : ℝ) * collisionWeight k)

def resetVector (p : ℝ≥0∞) (k : ℕ) : Lp ℝ p phaseHaar :=
  indicatorConstLp p (resetSet_measurable k) (measure_ne_top phaseHaar _)
    ((k : ℝ) * collisionWeight k)

theorem resetVector_coe (p : ℝ≥0∞) (k : ℕ) :
    (fun x => resetVector p k x) =ᵐ[phaseHaar] resetTerm k :=
  indicatorConstLp_coeFn

@[simp] theorem resetTerm_zero : resetTerm 0 = 0 := by
  funext x
  simp [resetTerm]

@[simp] theorem resetTerm_one : resetTerm 1 = 0 := by
  funext x
  simp [resetTerm]

@[simp] theorem resetVector_zero (p : ℝ≥0∞) : resetVector p 0 = 0 := by
  apply Lp.ext
  exact (resetVector_coe p 0).trans (by
    rw [resetTerm_zero]
    exact (Lp.coeFn_zero ℝ p phaseHaar).symm)

@[simp] theorem resetVector_one (p : ℝ≥0∞) : resetVector p 1 = 0 := by
  apply Lp.ext
  exact (resetVector_coe p 1).trans (by
    rw [resetTerm_one]
    exact (Lp.coeFn_zero ℝ p phaseHaar).symm)

theorem resetVector_norm (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ∞) (k : ℕ) :
    ‖resetVector p k‖ = (k : ℝ) * collisionWeight k * (k : ℝ)^(-(1 / p.toReal)) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos := Nat.pos_of_ne_zero hk
  rw [resetVector, norm_indicatorConstLp hp0 hpt, resetSet_measure_real hkpos,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (collisionWeight_nonneg k))]
  rw [one_div, Real.inv_rpow (Nat.cast_nonneg k), Real.rpow_neg (Nat.cast_nonneg k)]

theorem weighted_power_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => (k : ℝ) * collisionWeight k * (k : ℝ)^(-t)) := by
  have hs : Summable (fun k : ℕ => (1 + 1 / (t/2)) * (k : ℝ)^(-1 - t/2)) :=
    ((Real.summable_nat_rpow).mpr (by linarith)).mul_left _
  apply Summable.of_nonneg_of_le (fun k => by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (collisionWeight_nonneg k))
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)) _ hs
  intro k
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_mul]
    have : 0 ≤ 1 + 1 / (t / 2) := by positivity
    positivity
  have hkpos := Nat.pos_of_ne_zero hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have ht2 : 0 < t/2 := by linarith
  have hroot : 1 ≤ (k : ℝ)^(t/2) := Real.one_le_rpow (by exact_mod_cast hkpos) ht2.le
  have hlog := Real.log_le_rpow_div hkR.le ht2
  have hnum : 1 + Real.log (k : ℝ) ≤ (1 + 1/(t/2)) * (k : ℝ)^(t/2) := by
    calc
      _ ≤ (k : ℝ)^(t/2) + (k : ℝ)^(t/2) / (t/2) := add_le_add hroot hlog
      _ = _ := by ring
  calc
    _ ≤ ((1 + Real.log (k : ℝ)) / (k : ℝ)) * (k : ℝ)^(-t) := by
      have hw := mul_le_mul_of_nonneg_left (collisionWeight_log_bound hkpos) hkR.le
      have he : (k : ℝ) * ((1 + Real.log (k : ℝ)) / (k : ℝ)^2) =
          (1 + Real.log (k : ℝ)) / (k : ℝ) := by field_simp
      rw [he] at hw
      exact mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hkR.le _)
    _ ≤ (((1 + 1/(t/2)) * (k : ℝ)^(t/2)) / (k : ℝ)) * (k : ℝ)^(-t) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnum hkR.le)
        (Real.rpow_nonneg hkR.le _)
    _ = _ := by
      rw [show (-1 - t/2) = (t/2 - 1) + (-t) by ring,
        Real.rpow_add hkR, Real.rpow_sub hkR, Real.rpow_one]
      ring

theorem resetVector_norm_summable (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    Summable (fun k => ‖resetVector p k‖) := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have ht : 0 < 1 / p.toReal := one_div_pos.mpr (ENNReal.toReal_pos hp0 hpt)
  simpa only [resetVector_norm p hp0 hpt] using weighted_power_summable ht

def resetFunction (x : Phase) : ℝ := ∑' k, resetTerm k x

theorem resetVector_tsum_coe (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hpt : p ≠ ∞) :
    (fun x => (∑' k, resetVector p k) x) =ᵐ[phaseHaar] resetFunction := by
  have he : (∑' k, ‖resetVector p k‖ₑ) ≠ ∞ := by
    simpa only [ofReal_norm] using (resetVector_norm_summable p hp.out hpt).tsum_ofReal_ne_top
  have hsum := Lp.coeFn_tsum he
  have hterms : ∀ᵐ x ∂phaseHaar, ∀ k, resetVector p k x = resetTerm k x :=
    ae_all_iff.mpr (resetVector_coe p)
  filter_upwards [hsum, hterms] with x hx ht
  exact hx.trans (tsum_congr ht)

theorem resetFunction_memLp (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    MemLp resetFunction p phaseHaar := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact MemLp.ae_eq (resetVector_tsum_coe p hpt) (Lp.memLp (∑' k, resetVector p k))

theorem resetFunction_integrable : Integrable resetFunction phaseHaar :=
  memLp_one_iff_integrable.mp (resetFunction_memLp 1 le_rfl (by norm_num))

theorem resetTerm_nonneg (k : ℕ) (x : Phase) : 0 ≤ resetTerm k x := by
  exact Set.indicator_nonneg (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg k) (collisionWeight_nonneg k)) x

theorem resetTerm_integrable (k : ℕ) : Integrable (resetTerm k) phaseHaar := by
  exact (integrable_const ((k : ℝ) * collisionWeight k)).indicator (resetSet_measurable k)

theorem integral_resetTerm (k : ℕ) : ∫ x, resetTerm k x ∂phaseHaar = collisionWeight k := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos := Nat.pos_of_ne_zero hk
  rw [resetTerm, integral_indicator_const _ (resetSet_measurable k),
    resetSet_measure_real hkpos, smul_eq_mul]
  field_simp

theorem resetFunction_mean : ∫ x, resetFunction x ∂phaseHaar = 1 := by
  have hs : Summable (fun k => ∫ x, ‖resetTerm k x‖ ∂phaseHaar) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (resetTerm_nonneg _ _), integral_resetTerm]
      using collisionWeight_summable
  have h := integral_tsum_of_summable_integral_norm resetTerm_integrable hs
  change (∫ x, ∑' k, resetTerm k x ∂phaseHaar) = 1
  rw [← h]
  simpa only [integral_resetTerm] using collisionWeight_tsum

end NField.Alignment.CollisionResetIntegrability
