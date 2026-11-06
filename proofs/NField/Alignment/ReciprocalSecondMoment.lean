/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalDifferenceBound
import NField.Alignment.FiniteDifferenceRows
import NField.Alignment.ReciprocalBoundedLogPrefix
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # A quadratic bound for real reciprocal sums by finite differencing -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalSecondMoment
open scoped BigOperators ComplexConjugate
open FiniteDifferenceRows ReciprocalDifferenceBound ReciprocalWeightedBlocks
  ReciprocalFirstDerivativeBound ReciprocalBoundedLogPrefix

theorem phase_correlation (p h i : ℕ) (Q : ℝ) :
    reciprocalPhase Q (p+(i+h)+1)*conj (reciprocalPhase Q (p+i+1)) =
      differencePhase p h Q i := by
  have hconj (t : ℝ) : conj (fourier 1 (t:AddCircle (1:ℝ))) =
      fourier 1 ((-t:ℝ):AddCircle (1:ℝ)) := by
    symm
    rw [AddCircle.coe_neg,fourier_apply,smul_neg,← neg_smul,← fourier_apply,fourier_neg]
  unfold reciprocalPhase
  rw [hconj,← character_add]
  unfold differencePhase
  congr 2
  push_cast
  ring

theorem prefix_energy (p M R : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hR : R ≤ p) (hQ : 0 < Q)
    (hsmall : 4*Q*(R:ℝ) ≤ (p:ℝ)^3) :
    (R:ℝ)^2*‖reciprocalPrefix p M Q‖^2 ≤
      (M+R:ℕ)*(R:ℝ)*((M:ℝ)+128*(p:ℝ)^3/Q*(harmonic R:ℝ)) := by
  let B := fun d : ℕ => 64*(p:ℝ)^3/(Q*(d:ℝ))
  have hc (d : ℕ) (hd : d ∈ Finset.Icc 1 R) :
      ‖correlation (fun i => reciprocalPhase Q (p+i+1)) M d‖ ≤ B d := by
    have hd' := Finset.mem_Icc.mp hd
    unfold correlation
    simp_rw [phase_correlation]
    exact difference_prefix_bound p d (M-d) Q hp hd'.1 (hd'.2.trans hR)
      (by omega) hQ ((mul_le_mul_of_nonneg_left (by exact_mod_cast hd'.2)
        (show 0 ≤ 4*Q by positivity)).trans hsmall)
  have he : (∑ d ∈ Finset.Icc 1 R, B d) = 64*(p:ℝ)^3/Q*(harmonic R:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [B]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hb := difference_energy_bound (fun i => reciprocalPhase Q (p+i+1)) M R B
    (fun i _ => (Circle.norm_coe _).le) (fun d _ => by dsimp [B]; positivity) hc
  rw [he] at hb
  change (R:ℝ)^2*‖reciprocalPrefix p M Q‖^2 ≤ _ at hb
  convert hb using 1 <;> ring

theorem reciprocal_prefix_sq_bound (p M : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hPQ : (p:ℝ)^2 ≤ Q) :
    ‖reciprocalPrefix p M Q‖^2 ≤
      32*Q/(p:ℝ)+4096*(p:ℝ)*(1+Real.log (p:ℝ)) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hQ : 0 < Q := (sq_pos_of_pos hp0).trans_le hPQ
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg hp1
  by_cases hlarge : (p:ℝ)^3 ≤ 16*Q
  · have hb := pow_le_pow_left₀ (norm_nonneg _) (reciprocal_prefix_trivial p M Q hM) 2
    have hq : (p:ℝ)^2 ≤ 32*Q/(p:ℝ) := by
      apply (le_div_iff₀ hp0).mpr
      nlinarith
    exact hb.trans (hq.trans (le_add_of_nonneg_right (by positivity)))
  let a := (p:ℝ)^3/(8*Q)
  let R : ℕ := ⌊a⌋₊
  have ha2 : 2 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ (by positivity : 0 < 8*Q)).mpr
    linarith
  have ha0 : 0 ≤ a := by linarith
  have hRa : (R:ℝ) ≤ a := Nat.floor_le ha0
  have haR : a < (R:ℝ)+1 := Nat.lt_floor_add_one a
  have hR1 : 1 ≤ R := by
    have : (1:ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hR0 : (0:ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have haP : a ≤ p := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 8*Q)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hPQ hp0.le]
  have hRp : R ≤ p := by exact_mod_cast hRa.trans haP
  have hlo : (p:ℝ)^3/(16*Q) ≤ (R:ℝ) := by
    have he : (p:ℝ)^3/(16*Q) = a/2 := by dsimp [a]; ring
    rw [he]
    linarith
  have hsmall : 4*Q*(R:ℝ) ≤ (p:ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_left hRa (show 0 ≤ 4*Q by positivity)
    have he : 4*Q*a = (p:ℝ)^3/2 := by dsimp [a]; field_simp; ring
    rw [he] at h
    nlinarith
  have hharm : (harmonic R:ℝ) ≤ 1+Real.log (p:ℝ) :=
    (harmonic_le_one_add_log R).trans (add_le_add (le_refl (1:ℝ))
      (Real.log_le_log hR0 (by exact_mod_cast hRp)))
  have hharm0 : (0:ℝ) ≤ harmonic R := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_nonneg (fun d _ => by positivity)
  let T := (p:ℝ)+128*(p:ℝ)^3/Q*(1+Real.log (p:ℝ))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have he := prefix_energy p M R Q hp hM hRp hQ hsmall
  have he' : (R:ℝ)*‖reciprocalPrefix p M Q‖^2 ≤ 2*(p:ℝ)*T := by
    apply (mul_le_mul_iff_left₀ hR0).mp
    calc
      _ = (R:ℝ)^2*‖reciprocalPrefix p M Q‖^2 := by ring
      _ ≤ (M+R:ℕ)*(R:ℝ)*((M:ℝ)+128*(p:ℝ)^3/Q*(harmonic R:ℝ)) := he
      _ ≤ (2*(p:ℝ))*(R:ℝ)*T := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ hR0.le
          exact_mod_cast (show M+R ≤ 2*p by omega)
        · dsimp [T]
          exact add_le_add (by exact_mod_cast hM)
            (mul_le_mul_of_nonneg_left hharm (by positivity))
        · positivity
        · positivity
      _ = _ := by ring
  have hfactor : 2*(p:ℝ)/(R:ℝ) ≤ 32*Q/(p:ℝ)^2 := by
    calc
      _ ≤ 2*(p:ℝ)/((p:ℝ)^3/(16*Q)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
      _ = _ := by field_simp; ring
  calc
    _ ≤ 2*(p:ℝ)*T/(R:ℝ) := by
      apply (le_div_iff₀ hR0).mpr
      simpa only [mul_comm (R:ℝ)] using he'
    _ = (2*(p:ℝ)/(R:ℝ))*T := by ring
    _ ≤ (32*Q/(p:ℝ)^2)*T := mul_le_mul_of_nonneg_right hfactor hT
    _ = _ := by dsimp [T]; field_simp; ring

end NField.Alignment.ReciprocalSecondMoment
