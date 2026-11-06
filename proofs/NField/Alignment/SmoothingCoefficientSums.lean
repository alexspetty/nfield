/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SmoothingSeriesBounds
import NField.Alignment.BernoulliSmoothingFourier
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Explicit frequency mass for the smoothed sawtooth -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SmoothingCoefficientSums
open scoped BigOperators
open SmoothingSeriesBounds BernoulliSmoothingFourier

theorem square_weight_identity {x : ℝ} (hx : 0 < x) (A : ℝ) :
    A/x^2*Real.sqrt x=A*(1/(x*Real.sqrt x)) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  field_simp
  ring_nf
  rw [Real.sq_sqrt hx.le]

theorem coefficient_mass_bounds {H : ℕ} (hH : 1 ≤ H) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hh : ∀ n, 1 ≤ n → a n ≤ 1/(n : ℝ))
    (hs : ∀ n, 1 ≤ n → a n ≤ (H : ℝ)/(n : ℝ)^2) :
    Summable (fun n : ℕ => a (n+1)) ∧
    Summable (fun n : ℕ => a (n+1)*Real.sqrt (n+1 : ℕ)) ∧
    (∑' n : ℕ, a (n+1)) ≤ (harmonic H : ℝ)+1 ∧
    (∑' n : ℕ, a (n+1)*Real.sqrt (n+1 : ℕ)) ≤ 4*Real.sqrt (H : ℝ) := by
  have hH0 : (0 : ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have hsq : Summable (fun n : ℕ => 1/(n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hthree : Summable (fun n : ℕ => (n : ℝ)^(-(3/2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hsqs : Summable (fun n : ℕ => (H : ℝ)*(1/(n+1 : ℕ)^2)) :=
    (hsq.comp_injective (fun i j h => by omega)).mul_left (H : ℝ)
  have has : Summable (fun n : ℕ => a (n+1)) :=
    Summable.of_nonneg_of_le (fun _ => ha _) (fun n => by
      simpa only [mul_one_div] using hs (n+1) (by omega)) hsqs
  have hw (n : ℕ) (hn : 1 ≤ n) :
      a n*Real.sqrt (n : ℝ) ≤ (H : ℝ)*(1/((n : ℝ)*Real.sqrt (n : ℝ))) := by
    calc
      _ ≤ ((H : ℝ)/(n : ℝ)^2)*Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right (hs n hn) (Real.sqrt_nonneg _)
      _ = _ := square_weight_identity (by exact_mod_cast (by omega : 0<n)) H
  have hthrees : Summable (fun n : ℕ => (H : ℝ)*(1/((n+1 : ℕ)*Real.sqrt (n+1 : ℕ)))) := by
    have he (n : ℕ) := inverse_three_halves ((n+1 : ℕ) : ℝ) (by positivity)
    simp_rw [he]
    exact (hthree.comp_injective (fun i j h => by omega)).mul_left (H : ℝ)
  have haw : Summable (fun n : ℕ => a (n+1)*Real.sqrt (n+1 : ℕ)) :=
    Summable.of_nonneg_of_le (fun _ => mul_nonneg (ha _) (Real.sqrt_nonneg _))
      (fun n => hw (n+1) (by omega)) hthrees
  refine ⟨has,haw,?_,?_⟩
  · rw [← has.sum_add_tsum_nat_add H]
    have hhead : (∑ n ∈ Finset.range H, a (n+1)) ≤ (harmonic H : ℝ) := by
      unfold harmonic
      push_cast
      apply Finset.sum_le_sum
      intro n hn
      simpa only [one_div,Nat.cast_add,Nat.cast_one] using hh (n+1) (by omega)
    have htail : (∑' n : ℕ, a (n+H+1)) ≤ 1 := by
      have hts : Summable (fun n : ℕ => (H : ℝ)*(1/((n+H+1 : ℕ) : ℝ)^2)) :=
        (hsq.comp_injective (fun i j h => by omega)).mul_left (H : ℝ)
      calc
        _ ≤ ∑' n : ℕ, (H : ℝ)*(1/((n+H+1 : ℕ) : ℝ)^2) :=
          Summable.tsum_le_tsum (fun n => by simpa only [Function.comp_apply,mul_one_div] using hs (n+H+1) (by omega))
            (has.comp_injective (fun i j h => by omega)) hts
        _ = (H : ℝ)*(∑' n : ℕ, 1/((n+H+1 : ℕ) : ℝ)^2) := tsum_mul_left
        _ ≤ (H : ℝ)*(1/(H : ℝ)) :=
          mul_le_mul_of_nonneg_left (reciprocal_square_tail hH) hH0.le
        _ = 1 := by field_simp
    exact add_le_add hhead htail
  · rw [← haw.sum_add_tsum_nat_add H]
    have hhead : (∑ n ∈ Finset.range H, a (n+1)*Real.sqrt (n+1 : ℕ)) ≤
        2*Real.sqrt (H : ℝ) := by
      apply le_trans _ (CollisionRootSumBounds.inverse_sqrt_sum H)
      apply Finset.sum_le_sum
      intro n hn
      have hx : (0 : ℝ)<(n+1 : ℕ) := by positivity
      calc
        _ ≤ (1/(n+1 : ℕ))*Real.sqrt (n+1 : ℕ) :=
          mul_le_mul_of_nonneg_right (hh (n+1) (by omega)) (Real.sqrt_nonneg _)
        _ = 1/Real.sqrt (n+1 : ℕ) := by
          have hroot := Real.sq_sqrt hx.le
          have hsroot := (Real.sqrt_pos.mpr hx).ne'
          field_simp
          nlinarith
    have htail : (∑' n : ℕ, a (n+H+1)*Real.sqrt (n+H+1 : ℕ)) ≤
        2*Real.sqrt (H : ℝ) := by
      have hts : Summable (fun n : ℕ => (H : ℝ)*(1/((n+H+1 : ℕ)*Real.sqrt (n+H+1 : ℕ)))) :=
        hthrees.comp_injective (fun i j h => by omega)
      calc
        _ ≤ ∑' n : ℕ, (H : ℝ)*(1/((n+H+1 : ℕ)*Real.sqrt (n+H+1 : ℕ))) :=
          Summable.tsum_le_tsum (fun n => by simpa only [Function.comp_apply] using hw (n+H+1) (by omega))
            (haw.comp_injective (fun i j h => by omega)) hts
        _ = (H : ℝ)*(∑' n : ℕ, 1/((n+H+1 : ℕ)*Real.sqrt (n+H+1 : ℕ))) := tsum_mul_left
        _ ≤ (H : ℝ)*(2/Real.sqrt (H : ℝ)) :=
          mul_le_mul_of_nonneg_left (reciprocal_three_halves_tail hH) hH0.le
        _ = 2*Real.sqrt (H : ℝ) := by
          have hsroot := (Real.sqrt_pos.mpr hH0).ne'
          field_simp
          nlinarith [Real.sq_sqrt hH0.le]
    linarith

end NField.Alignment.SmoothingCoefficientSums
