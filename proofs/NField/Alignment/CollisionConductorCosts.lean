/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeCandidate
import NField.Alignment.CollisionWeightMultiples
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Lower costs of nonzero conductor coordinates

The bounds concern the actual full-amplitude gap. They will be compared
with the prime candidates to classify restricted minimizers.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorCosts

open scoped BigOperators Classical
open SecondaryCapacityLedger CollisionRemainderDynamics CollisionWeightMultiples
open CollisionRestrictedGap CollisionConductorExtrema CollisionFiniteRegrouping
open CollisionPositiveRegrouping

theorem primitiveNumerators_prime {p : ℕ} (hp : Nat.Prime p) :
    primitiveNumerators p=Finset.Ico 1 p := by
  unfold primitiveNumerators
  apply Finset.filter_eq_self.mpr
  intro a ha
  have hm := Finset.mem_Ico.mp ha
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hpa
  have hle := Nat.le_of_dvd (by omega : 0 < a) hpa
  omega

theorem reducedHarmonicStar_prime {p : ℕ} (hp : Nat.Prime p) :
    reducedHarmonicStar p=(harmonic (p-1) : ℝ) := by
  change (∑ a ∈ primitiveNumerators p, (a : ℝ)⁻¹)=_
  rw [primitiveNumerators_prime hp]
  exact harmonic_predecessor_Ico (by have := hp.two_le; omega)

theorem log_le_harmonic_predecessor {d : ℕ} (hd : 1 ≤ d) :
    Real.log d ≤ (harmonic (d-1) : ℝ) := by
  simpa only [Nat.sub_add_cancel hd] using log_add_one_le_harmonic (d-1)

theorem collisionWeight_prime_formula {p : ℕ} (hp : Nat.Prime p) :
    collisionWeight p=(harmonic (p-1) : ℝ)/(p : ℝ)^2 := by
  rw [collisionWeight,reducedHarmonicStar_prime hp]

theorem collisionWeight_prime_lower {p : ℕ} (hp : Nat.Prime p) :
    Real.log p/(p : ℝ)^2 ≤ collisionWeight p := by
  rw [collisionWeight_prime_formula hp]
  exact div_le_div_of_nonneg_right
    (log_le_harmonic_predecessor (by have := hp.two_le; omega)) (sq_nonneg _)

theorem conductorGap_row_lower {Q d a : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    (2/3 : ℝ)*beta d Q*((a%d : ℕ) : ℝ) ≤ conductorGap Q a := by
  have hsum := Finset.single_le_sum
    (s := Finset.Icc 2 Q) (f := fun j => beta j Q*((a%j : ℕ) : ℝ))
    (fun j hj => mul_nonneg (beta_pos (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).le
      (Nat.cast_nonneg _)) (Finset.mem_Icc.mpr ⟨hd,hdQ⟩)
  rw [conductorGap_formula]
  nlinarith

theorem conductorGap_weight_lower {Q d a : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    (1/3 : ℝ)*collisionWeight d*((a%d : ℕ) : ℝ) ≤ conductorGap Q a := by
  have hrow := conductorGap_row_lower (a := a) hd hdQ
  have hbeta := beta_strict_half hd hdQ
  have hm : (0 : ℝ) ≤ ((a%d : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem conductorGap_nondivisor_lower {Q d a : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q)
    (hda : ¬d ∣ a) : collisionWeight d/3 ≤ conductorGap Q a := by
  have hrow := conductorGap_weight_lower (a := a) hd hdQ
  have hn : 1 ≤ a%d := by
    by_contra h
    exact hda (Nat.dvd_of_mod_eq_zero (by omega))
  have hr : (1 : ℝ) ≤ ((a%d : ℕ) : ℝ) := by exact_mod_cast hn
  have hw := collisionWeight_nonneg d
  nlinarith

theorem conductorGap_prime_lower {Q p a : ℕ} (hp : Nat.Prime p) (hpQ : p ≤ Q)
    (hpa : ¬p ∣ a) : Real.log p/(3*(p : ℝ)^2) ≤ conductorGap Q a := by
  have h := conductorGap_nondivisor_lower hp.two_le hpQ hpa
  have hw := collisionWeight_prime_lower hp
  have he : Real.log p/(3*(p : ℝ)^2)=(Real.log p/(p : ℝ)^2)/3 := by ring
  rw [he]
  linarith

theorem reciprocal_multiple_sum {p m : ℕ} (hp : 0 < p) (hm : 1 ≤ m) :
    (∑ a ∈ (Finset.Ico 1 (p*m)).filter (fun a => p ∣ a), (a : ℝ)⁻¹)=
      (p : ℝ)⁻¹*(harmonic (m-1) : ℝ) := by
  have he : (∑ k ∈ Finset.Ico 1 m, ((p*k : ℕ) : ℝ)⁻¹)=
      ∑ a ∈ (Finset.Ico 1 (p*m)).filter (fun a => p ∣ a), (a : ℝ)⁻¹ := by
    apply Finset.sum_bij (fun k _ => p*k)
    · intro k hk
      have hb := Finset.mem_Ico.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨by nlinarith,?_⟩,dvd_mul_right _ _⟩
      exact Nat.mul_lt_mul_of_pos_left hb.2 hp
    · intro a _ b _ he
      exact Nat.mul_left_cancel hp he
    · intro a ha
      obtain ⟨haI,hpa⟩ := Finset.mem_filter.mp ha
      have hb := Finset.mem_Ico.mp haI
      have ha0 : 0 < a := by omega
      have hle := Nat.le_of_dvd ha0 hpa
      refine ⟨a/p,Finset.mem_Ico.mpr ⟨?_,?_⟩,?_⟩
      · exact Nat.div_pos hle hp
      · apply (Nat.div_lt_iff_lt_mul hp).mpr
        simpa only [Nat.mul_comm m p] using hb.2
      · exact Nat.mul_div_cancel' hpa
    · intro k _
      rfl
  rw [← he,← harmonic_predecessor_Ico hm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.cast_mul,mul_inv_rev]
  ring

theorem reducedHarmonicStar_prime_power {p : ℕ} (hp : Nat.Prime p) (j : ℕ) :
    reducedHarmonicStar (p^(j+1))=(harmonic (p^(j+1)-1) : ℝ)-
      (p : ℝ)⁻¹*(harmonic (p^j-1) : ℝ) := by
  have hcop (a : ℕ) : a.Coprime (p^(j+1)) ↔ ¬p ∣ a := by
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j),Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 (p^(j+1)))
    (fun a => p ∣ a) (fun a => (a : ℝ)⁻¹)
  have hdiv : (∑ a ∈ (Finset.Ico 1 (p^(j+1))).filter (fun a => p ∣ a), (a : ℝ)⁻¹)=
      (p : ℝ)⁻¹*(harmonic (p^j-1) : ℝ) := by
    simpa only [pow_succ'] using reciprocal_multiple_sum hp.pos
      (show 1 ≤ p^j from Nat.one_le_pow _ _ hp.pos)
  have hstar : (∑ a ∈ (Finset.Ico 1 (p^(j+1))).filter (fun a => ¬p ∣ a), (a : ℝ)⁻¹)=
      reducedHarmonicStar (p^(j+1)) := by
    unfold reducedHarmonicStar
    simp only [hcop]
  rw [hdiv,hstar,harmonic_predecessor_Ico (Nat.one_le_pow _ _ hp.pos)] at hs
  linarith

theorem harmonic_predecessor_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (harmonic (a-1) : ℝ) ≤ (harmonic (b-1) : ℝ) := by
  rw [← harmonic_predecessor_Ico ha,← harmonic_predecessor_Ico (ha.trans hab)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hab)
    (fun _ _ _ => by positivity)

theorem reducedHarmonicStar_prime_power_lower {p : ℕ} (hp : Nat.Prime p) (j : ℕ) :
    Real.log (p^(j+1) : ℕ)/2 ≤ reducedHarmonicStar (p^(j+1)) := by
  have hp1 : 1 ≤ p^j := Nat.one_le_pow _ _ hp.pos
  have hpp : p^j ≤ p^(j+1) := by
    rw [pow_succ]
    have := hp.two_le
    nlinarith
  have hmon := harmonic_predecessor_mono hp1 hpp
  have hlog := log_le_harmonic_predecessor (hp1.trans hpp)
  have hH : (0 : ℝ) ≤ (harmonic (p^j-1) : ℝ) := by unfold harmonic; positivity
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (1/2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpR
  have hprod := mul_le_mul hinv hmon hH (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [reducedHarmonicStar_prime_power hp j]
  linarith

theorem collisionWeight_prime_power_lower {p : ℕ} (hp : Nat.Prime p) (j : ℕ) :
    Real.log (p^(j+1) : ℕ)/(2*((p^(j+1) : ℕ) : ℝ)^2) ≤ collisionWeight (p^(j+1)) := by
  have h := div_le_div_of_nonneg_right (reducedHarmonicStar_prime_power_lower hp j)
    (sq_nonneg (((p^(j+1) : ℕ) : ℝ)))
  unfold collisionWeight
  convert! h using 1
  ring

theorem first_missing_power_remainder {p j a : ℕ} (hprev : p^j ∣ a)
    (hmiss : ¬p^(j+1) ∣ a) : p^j ≤ a%(p^(j+1)) := by
  have hdiv : p^j ∣ a%(p^(j+1)) :=
    (Nat.dvd_mod_iff (Nat.pow_dvd_pow p (Nat.le_succ j))).mpr hprev
  have hpos : 0 < a%(p^(j+1)) := by
    by_contra h
    exact hmiss (Nat.dvd_of_mod_eq_zero (by omega))
  exact Nat.le_of_dvd hpos hdiv

theorem conductorGap_first_missing_power {Q p j a : ℕ} (hp : Nat.Prime p)
    (hpQ : p^(j+1) ≤ Q) (hprev : p^j ∣ a) (hmiss : ¬p^(j+1) ∣ a) :
    Real.log (p^(j+1) : ℕ)/(6*(p : ℝ)^(j+2)) ≤ conductorGap Q a := by
  have hq2 : 2 ≤ p^(j+1) := by
    have hpow : 1 ≤ p^j := Nat.one_le_pow _ _ hp.pos
    rw [pow_succ]
    have := hp.two_le
    nlinarith
  have hrow := conductorGap_weight_lower (a := a) hq2 hpQ
  have hr : (((p^j : ℕ) : ℝ)) ≤ (((a%(p^(j+1)) : ℕ) : ℝ)) := by
    exact_mod_cast first_missing_power_remainder hprev hmiss
  have hw := collisionWeight_prime_power_lower hp j
  have h1 := mul_le_mul_of_nonneg_left hr (collisionWeight_nonneg (p^(j+1)))
  have h2 := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg (p^j) : (0 : ℝ) ≤ (p^j : ℕ))
  have he : (Real.log (p^(j+1) : ℕ)/(2*((p^(j+1) : ℕ) : ℝ)^2))*((p^j : ℕ) : ℝ)/3=
      Real.log (p^(j+1) : ℕ)/(6*(p : ℝ)^(j+2)) := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    simp only [Nat.cast_pow,pow_succ,Nat.cast_mul]
    field_simp
    ring
  rw [← he]
  nlinarith

theorem exp_half_le_two : Real.exp ((2 : ℝ)⁻¹) ≤ 2 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mp
  have h := Real.log_two_gt_d9
  norm_num
  linarith

theorem conductorGap_small_prime_lower {Q p a : ℕ} (hp : Nat.Prime p)
    (hpQ : 2*p ≤ Q) (hpa : ¬p ∣ a) :
    (4/3 : ℝ)*Real.log ((Q : ℝ)/2)/(Q : ℝ)^2 ≤ conductorGap Q a := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpQ' : (p : ℝ) ≤ (Q : ℝ)/2 := by
    have h : 2*(p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpQ
    linarith
  have hx : Real.exp ((2 : ℝ)⁻¹) ≤ p := exp_half_le_two.trans hp2
  have hmono := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 2)
    hx (hx.trans hpQ') hpQ'
  simp only [Real.rpow_two] at hmono
  have hg := conductorGap_prime_lower hp (by omega : p ≤ Q) hpa
  calc
    _ = (Real.log ((Q : ℝ)/2)/((Q : ℝ)/2)^2)/3 := by ring
    _ ≤ (Real.log p/(p : ℝ)^2)/3 :=
      div_le_div_of_nonneg_right hmono (by norm_num)
    _ = Real.log p/(3*(p : ℝ)^2) := by ring
    _ ≤ _ := hg

theorem exp_two_thirds_le_two : Real.exp (((3 : ℝ)/2)⁻¹) ≤ 2 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mp
  have h := Real.log_two_gt_d9
  norm_num
  linarith

theorem prime_power_denominator_le {p j : ℕ} (hp : Nat.Prime p) (hj : 1 ≤ j) :
    (p : ℝ)^(j+2) ≤ ((p^(j+1) : ℕ) : ℝ)^((3 : ℝ)/2) := by
  have hpq : p^2 ≤ p^(j+1) := Nat.pow_le_pow_right hp.pos (by omega)
  have hpq' : (p : ℝ)^2 ≤ ((p^(j+1) : ℕ) : ℝ) := by exact_mod_cast hpq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < ((p^(j+1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos (j+1)
  have hsqrt := Real.le_sqrt_of_sq_le hpq'
  have h := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg (p^(j+1)) :
    (0 : ℝ) ≤ ((p^(j+1) : ℕ) : ℝ))
  have he : ((p^(j+1) : ℕ) : ℝ)^((3 : ℝ)/2)=
      ((p^(j+1) : ℕ) : ℝ)*Real.sqrt ((p^(j+1) : ℕ) : ℝ) := by
    rw [show (3 : ℝ)/2=1+1/2 by norm_num,Real.rpow_add hqR,Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [he]
  simpa only [Nat.cast_pow,pow_succ,Nat.cast_mul] using h

theorem conductorGap_higher_power_lower {Q p j a : ℕ} (hp : Nat.Prime p)
    (hj : 1 ≤ j) (hpQ : p^(j+1) ≤ Q) (hprev : p^j ∣ a) (hmiss : ¬p^(j+1) ∣ a) :
    Real.log Q/(6*(Q : ℝ)^((3 : ℝ)/2)) ≤ conductorGap Q a := by
  have hq2 : 2 ≤ p^(j+1) := by
    have hpow : 1 ≤ p^j := Nat.one_le_pow _ _ hp.pos
    rw [pow_succ]
    have := hp.two_le
    nlinarith
  have hq2' : (2 : ℝ) ≤ ((p^(j+1) : ℕ) : ℝ) := by exact_mod_cast hq2
  have hqQ : ((p^(j+1) : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpQ
  have hx := exp_two_thirds_le_two.trans hq2'
  have hmono := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 3/2)
    hx (hx.trans hqQ) hqQ
  have hlog : 0 ≤ Real.log (p^(j+1) : ℕ) := Real.log_nonneg (by linarith)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hden0 : (0 : ℝ) < (p : ℝ)^(j+2) := by positivity
  have hden := div_le_div_of_nonneg_left hlog hden0 (prime_power_denominator_le hp hj)
  have hcost := conductorGap_first_missing_power hp hpQ hprev hmiss
  calc
    _ = (Real.log Q/(Q : ℝ)^((3 : ℝ)/2))/6 := by ring
    _ ≤ (Real.log (p^(j+1) : ℕ)/(((p^(j+1) : ℕ) : ℝ)^((3 : ℝ)/2)))/6 :=
      div_le_div_of_nonneg_right hmono (by norm_num)
    _ ≤ (Real.log (p^(j+1) : ℕ)/(p : ℝ)^(j+2))/6 :=
      div_le_div_of_nonneg_right hden (by norm_num)
    _ = Real.log (p^(j+1) : ℕ)/(6*(p : ℝ)^(j+2)) := by ring
    _ ≤ _ := hcost

end NField.Alignment.CollisionConductorCosts
