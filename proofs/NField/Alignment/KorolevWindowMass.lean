/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeWindows
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Reciprocal mass in the actual disjoint selected windows

The main logarithmic increment dominates a telescoping half-logarithm.
Both the 1/4 normalization and the Mertens errors are retained explicitly.
The finite size condition below is not yet deduced from Korolev's full
source parameter range.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevWindowMass
open scoped BigOperators Classical
open KorolevPrimeWindows KorolevPrimeIntervals

def lossConstant : ℝ := 4 * Real.log 4 + 6 * errorConstant

theorem lossConstant_pos : 0 < lossConstant := by
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc := errorConstant_pos
  unfold lossConstant
  positivity

theorem log_one_sub_lower {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1/2) :
    -2 * z ≤ Real.log (1-z) := by
  have hp : 0 < 1-z := by linarith
  have hi : (1-z)⁻¹ ≤ 1+2*z := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hz (show 0 ≤ 1-2*z by linarith)]
  have h := Real.one_sub_inv_le_log_of_pos hp
  linarith

theorem half_log_increment {k : ℝ} (hk : 0 < k) :
    (Real.log (k+1) - Real.log k)/2 ≤ Real.log (1+1/(2*k)) := by
  have he : (k+1)/k = 1+2*(1/(2*k)) := by field_simp
  have hsq : (k+1)/k ≤ (1+1/(2*k))^2 := by
    rw [he]
    nlinarith [sq_nonneg (1/(2*k))]
  have h := Real.log_le_log (div_pos (by linarith) hk) hsq
  rw [Real.log_div (by linarith : k+1 ≠ 0) hk.ne', Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem log_ratio_identity {L : ℝ} (hL : 0 < L) {k : ℕ} (hk : 1 ≤ k) :
    Real.log (upperEndpoint L k) / Real.log (lowerEndpoint L k) =
      (1+1/(2*(k : ℝ))) * (1-(2*(k : ℝ)-1)*Real.log 4/L) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have h1 : 2*(k : ℝ)-1 ≠ 0 := by linarith
  have h2 : 2*(k : ℝ)+1 ≠ 0 := by linarith
  rw [log_upper, log_lower]
  field_simp

/-- Explicit sufficient conditions for the actual finite window. -/
theorem window_conditions {L : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hsize : 8*(k : ℝ)^2*(Real.log 4+1) ≤ L) :
    0 < L ∧ lowerEndpoint L k ≤ upperEndpoint L k ∧ 2 ≤ lowerEndpoint L k ∧
      (2*(k : ℝ)-1)*Real.log 4/L ≤ 1/2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hk2 : (k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  have hkc := mul_le_mul_of_nonneg_right hk2 hl4.le
  have hL : 0 < L := by nlinarith [sq_nonneg (k : ℝ)]
  have horder : (4*(k : ℝ)^2-1)*Real.log 4 ≤ L := by
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hl4.le]
  have hl2 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have htwo : (2*(k : ℝ)+1)*Real.log 2 ≤ L := by
    have hh := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 2*(k : ℝ)+1 by positivity)
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hl4.le]
  refine ⟨hL, endpoint_order hk horder, lowerEndpoint_ge_two hL.le hk htwo, ?_⟩
  apply (div_le_iff₀ hL).mpr
  nlinarith

theorem window_mass_lower {L : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hsize : 8*(k : ℝ)^2*(Real.log 4+1) ≤ L) :
    (Real.log ((k : ℝ)+1)-Real.log k)/2 - lossConstant*(k : ℝ)/L ≤
      ∑ p ∈ windowPrimes L k, (1 : ℝ)/p := by
  obtain ⟨hL, horder, htwo, hz⟩ := window_conditions hk hsize
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let z := (2*(k : ℝ)-1)*Real.log 4/L
  have hz0 : 0 ≤ z := div_nonneg (mul_nonneg (by linarith) hl4.le) hL.le
  have hz1 : 0 < 1-z := by dsimp [z]; linarith
  have hgrowth := half_log_increment hk0
  have hnorm := log_one_sub_lower hz0 hz
  have hlow : 0 < Real.log (lowerEndpoint L k) := Real.log_pos (by linarith)
  have hupp : 0 < Real.log (upperEndpoint L k) := Real.log_pos (by linarith)
  have hid : Real.log (Real.log (upperEndpoint L k)) - Real.log (Real.log (lowerEndpoint L k)) =
      Real.log (1+1/(2*(k : ℝ))) + Real.log (1-z) := by
    rw [← Real.log_div hupp.ne' hlow.ne', log_ratio_identity hL hk,
      Real.log_mul (by positivity : 1+1/(2*(k : ℝ)) ≠ 0) hz1.ne']
  have hm := (abs_le.mp (interval_reciprocal_error htwo horder)).1
  change -(2*errorConstant/Real.log (lowerEndpoint L k)) ≤
    (∑ p ∈ windowPrimes L k, (1 : ℝ)/p) -
      (Real.log (Real.log (upperEndpoint L k))-Real.log (Real.log (lowerEndpoint L k))) at hm
  rw [hid] at hm
  have hden : 0 < 2*(k : ℝ)+1 := by positivity
  have hlower := log_lower_ge hL.le hk
  have herr : 2*errorConstant/Real.log (lowerEndpoint L k) ≤ 6*errorConstant*(k : ℝ)/L := by
    calc
      _ ≤ 2*errorConstant/(L/(2*(k : ℝ)+1)) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) errorConstant_pos.le) (div_pos hL hden) hlower
      _ = 2*errorConstant*(2*(k : ℝ)+1)/L := by field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hL.le
        nlinarith [errorConstant_pos]
  have hzbound : 2*z ≤ 4*Real.log 4*(k : ℝ)/L := by
    dsimp [z]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith
  have he : lossConstant*(k : ℝ)/L = 4*Real.log 4*(k : ℝ)/L + 6*errorConstant*(k : ℝ)/L := by
    unfold lossConstant
    ring
  rw [he]
  linarith

theorem log_increment_sum {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc a b, (Real.log ((k : ℝ)+1)-Real.log k)/2) =
      (Real.log ((b : ℝ)+1)-Real.log a)/2 := by
  rw [← Finset.sum_div]
  congr 1
  have he : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sub _ (by omega : a ≤ b+1)]
  simp_rw [show (fun k : ℕ => Real.log ((k : ℝ)+1)-Real.log k) =
    (fun k : ℕ => Real.log (k+1 : ℕ)-Real.log k) by funext k; simp]
  rw [Finset.sum_range_sub (fun k : ℕ => Real.log (k : ℝ)),
    Finset.sum_range_sub (fun k : ℕ => Real.log (k : ℝ))]
  simp

theorem index_sum_le (a b : ℕ) : (∑ k ∈ Finset.Icc a b, (k : ℝ)) ≤ ((b : ℝ)+1)^2 := by
  have h := Finset.sum_le_sum (s := Finset.Icc a b)
    (f := fun k : ℕ => (k : ℝ)) (g := fun _ => (b : ℝ))
    (fun k hk => by exact_mod_cast (Finset.mem_Icc.mp hk).2)
  have hc : ((Finset.Icc a b).card : ℝ) ≤ (b : ℝ)+1 := by
    rw [Nat.card_Icc]
    exact_mod_cast Nat.sub_le (b+1) a
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  nlinarith [Nat.cast_nonneg (α := ℝ) b]

/-- Actual union mass, with its finite size condition and accumulated
error explicit. No selected-window mass hypothesis is assumed. -/
theorem selected_mass_lower {L : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hsize : 8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L) :
    (Real.log ((b : ℝ)+1)-Real.log a)/2 - lossConstant*((b : ℝ)+1)^2/L ≤
      ∑ p ∈ selectedPrimes L a b, (1 : ℝ)/p := by
  have hb : 1 ≤ b := ha.trans hab
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hL : 0 < L := by nlinarith [sq_nonneg ((b : ℝ)+1)]
  rw [selected_reciprocal_sum hL.le ha]
  have hm : ∀ k ∈ Finset.Icc a b,
      (Real.log ((k : ℝ)+1)-Real.log k)/2 - lossConstant*(k : ℝ)/L ≤
        ∑ p ∈ windowPrimes L k, (1 : ℝ)/p := by
    intro k hk
    have hklo := ha.trans (Finset.mem_Icc.mp hk).1
    have hkhi : (k : ℝ) ≤ b := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have hsq : (k : ℝ)^2 ≤ ((b : ℝ)+1)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) 2
    apply window_mass_lower hklo
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)).trans hsize
  have hsum := Finset.sum_le_sum hm
  rw [Finset.sum_sub_distrib, log_increment_sum hab] at hsum
  have herr : (∑ k ∈ Finset.Icc a b, lossConstant*(k : ℝ)/L) ≤
      lossConstant*((b : ℝ)+1)^2/L := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (index_sum_le a b) lossConstant_pos.le)
      (inv_nonneg.mpr hL.le)
  linarith

/-- The other selected family is the single contiguous interval between
two U endpoints. Its mass has a full logarithmic increment. -/
theorem contiguous_mass_lower {L : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hsize : 8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L) :
    Real.log ((b : ℝ)+1)-Real.log a - 12*errorConstant*((b : ℝ)+1)/L ≤
      ∑ p ∈ intervalPrimes (upperEndpoint L (b+1)) (upperEndpoint L a), (1 : ℝ)/p := by
  have hc := window_conditions (k := b+1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hsize)
  obtain ⟨hL, hbottomOrder, hbottomTwo, hz⟩ := hc
  have htwo : 2 ≤ upperEndpoint L (b+1) := hbottomTwo.trans hbottomOrder
  have horder := upper_antitone hL.le ha (by omega : a ≤ b+1)
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha0 : (0 : ℝ) < a := by linarith
  have hd : 0 < 2*(b : ℝ)+1 := by positivity
  have hA : 0 < 2*(a : ℝ)-1 := by linarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog : Real.log (upperEndpoint L (b+1)) = L/(2*(b : ℝ)+1)-Real.log 4 := by
    rw [log_upper, Nat.cast_add, Nat.cast_one]
    congr 2; ring
  have hnorm : (2*(b : ℝ)+1)*Real.log 4 ≤ L/2 := by
    have hh := (div_le_iff₀ hL).mp hz
    push_cast at hh
    nlinarith
  have hsmall : Real.log 4 ≤ L/(2*(2*(b : ℝ)+1)) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hlower : L/(2*(2*(b : ℝ)+1)) ≤ Real.log (upperEndpoint L (b+1)) := by
    rw [hlog]
    have he : L/(2*(b : ℝ)+1) = 2*(L/(2*(2*(b : ℝ)+1))) := by field_simp
    linarith
  have hlpos : 0 < Real.log (upperEndpoint L (b+1)) := Real.log_pos (by linarith)
  have hup : 0 < Real.log (upperEndpoint L a) := Real.log_pos (by linarith)
  have hratio1 : 1 ≤ (2*(b : ℝ)+1)/(2*(a : ℝ)-1) := (le_div_iff₀ hA).mpr (by linarith)
  have hratio : (2*(b : ℝ)+1)/(2*(a : ℝ)-1) ≤
      Real.log (upperEndpoint L a)/Real.log (upperEndpoint L (b+1)) := by
    apply (le_div_iff₀ hlpos).mpr
    rw [hlog, log_upper]
    have he : ((2*(b : ℝ)+1)/(2*(a : ℝ)-1))*(L/(2*(b : ℝ)+1)-Real.log 4) =
        L/(2*(a : ℝ)-1)-((2*(b : ℝ)+1)/(2*(a : ℝ)-1))*Real.log 4 := by field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hratio1 hl4.le]
  have hsimpler : ((b : ℝ)+1)/(a : ℝ) ≤ (2*(b : ℝ)+1)/(2*(a : ℝ)-1) := by
    apply (div_le_div_iff₀ ha0 hA).mpr
    nlinarith
  have hmain := Real.log_le_log (div_pos (by positivity) ha0) (hsimpler.trans hratio)
  rw [Real.log_div (by positivity : (b : ℝ)+1 ≠ 0) ha0.ne',
    Real.log_div hup.ne' hlpos.ne'] at hmain
  have hm := (abs_le.mp (interval_reciprocal_error htwo horder)).1
  have herr : 2*errorConstant/Real.log (upperEndpoint L (b+1)) ≤
      12*errorConstant*((b : ℝ)+1)/L := by
    calc
      _ ≤ 2*errorConstant/(L/(2*(2*(b : ℝ)+1))) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) errorConstant_pos.le)
          (div_pos hL (by positivity)) hlower
      _ = 4*errorConstant*(2*(b : ℝ)+1)/L := by field_simp; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hL.le
        nlinarith [errorConstant_pos, Nat.cast_nonneg (α := ℝ) b]
  linarith

end NField.Alignment.KorolevWindowMass
