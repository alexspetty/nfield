/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBernoulliLifts
import NField.Alignment.GeneralNeutrality

/-! # The literal conductor-four Bernoulli lift calculation -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ConductorFourLifts

open scoped BigOperators
open NField.Alignment.DedekindReciprocity
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.CommonResetBernoulliLifts
open NField.Alignment.GeneralNeutrality

def conductorFourLift (L k : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (4 * L), (chiFourSign a : ℚ) * rationalSawtooth (k * a) (4 * L)

theorem chiFourSign_add_four_mul (r t : ℕ) :
    chiFourSign (r + t * 4) = chiFourSign r := by
  simp only [chiFourSign, Nat.add_mul_mod_self_right]

theorem conductorFourLift_two_lifts (L k : ℕ) :
    conductorFourLift L k =
      (∑ t ∈ Finset.range L, rationalSawtooth (k * (1 + t * 4)) (4 * L)) -
      ∑ t ∈ Finset.range L, rationalSawtooth (k * (3 + t * 4)) (4 * L) := by
  unfold conductorFourLift
  rw [show 4 * L = L * 4 by omega,
    sum_range_mul_blocks (by decide : 0 < 4)]
  simp only [chiFourSign_add_four_mul, ← Finset.mul_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [chiFourSign, sub_eq_add_neg]

theorem sawtooth_repeated_coprime_lifts {d L c : ℕ}
    (hd : 0 < d) (hL : 0 < L) (hc : c.Coprime L) (r : ℕ) :
    (∑ t ∈ Finset.range (d * L),
      rationalSawtooth ((d * c) * (r + t * 4)) (4 * (d * L))) =
      (d : ℚ) * rationalSawtooth (c * r) 4 := by
  rw [sum_range_mul_blocks hL]
  have hpoint (y j : ℕ) :
      rationalSawtooth ((d * c) * (r + (y + j * L) * 4)) (4 * (d * L)) =
        rationalSawtooth (c * (r + y * 4)) (L * 4) := by
    rw [show (d * c) * (r + (y + j * L) * 4) = d * (c * (r + (y + j * L) * 4)) by ring,
      show 4 * (d * L) = d * (L * 4) by ring,
      rationalSawtooth_scale hd (by positivity)]
    apply rationalSawtooth_eq_of_mod_eq
    rw [show c * (r + (y + j * L) * 4) = c * (r + y * 4) + (L * 4) * (c * j) by ring,
      Nat.add_mul_mod_self_left]
  simp only [hpoint, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, sawtooth_coprime_lifts hL (by decide : 0 < 4) hc]

theorem quarter_sawtooth_difference (k : ℕ) :
    rationalSawtooth k 4 - rationalSawtooth (3 * k) 4 =
      -(1 / 2 : ℚ) * (chiFourSign k : ℚ) := by
  have hk := Nat.mod_lt k (by decide : 0 < 4)
  interval_cases h : k % 4 <;>
    norm_num [rationalSawtooth, chiFourSign, Nat.mul_mod, h]

/-- Title: `The conductor four lift has the exact reduced numerator formula`. -/
theorem conductorFourLift_factored {d L c : ℕ}
    (hd : 0 < d) (hL : 0 < L) (hc : c.Coprime L) :
    conductorFourLift (d * L) (d * c) = -(d : ℚ) / 2 * (chiFourSign c : ℚ) := by
  rw [conductorFourLift_two_lifts, sawtooth_repeated_coprime_lifts hd hL hc,
    sawtooth_repeated_coprime_lifts hd hL hc]
  simp only [mul_one]
  rw [show c * 3 = 3 * c by omega, ← mul_sub, quarter_sawtooth_difference]
  ring

/-- Title: `The full conductor four sum has its exact greatest common divisor factor`. -/
theorem conductorFourLift_gcd {L : ℕ} (hL : 0 < L) (k : ℕ) :
    conductorFourLift L k =
      -(k.gcd L : ℚ) / 2 * (chiFourSign (k / k.gcd L) : ℚ) := by
  have hd := Nat.gcd_pos_of_pos_right k hL
  have h := conductorFourLift_factored hd (Nat.div_gcd_pos_of_pos_right k hL)
    (Nat.coprime_div_gcd_div_gcd hd)
  simpa only [Nat.mul_div_cancel' (Nat.gcd_dvd_left k L),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right k L)] using h

/-- The odd extension of the periodic Bernoulli sawtooth to integer numerators. -/
def signedSawtooth (k : ℤ) (q : ℕ) : ℚ :=
  if k < 0 then -rationalSawtooth k.natAbs q else rationalSawtooth k.natAbs q

def signedChiFour (k : ℤ) : ℤ :=
  if k < 0 then -chiFourSign k.natAbs else chiFourSign k.natAbs

def signedConductorFourLift (L : ℕ) (k : ℤ) : ℚ :=
  ∑ a ∈ Finset.range (4 * L), (chiFourSign a : ℚ) * signedSawtooth (k * a) (4 * L)

theorem signedSawtooth_natCast (k q : ℕ) :
    signedSawtooth k q = rationalSawtooth k q := by
  simp [signedSawtooth]

theorem signedSawtooth_neg_natCast (k q : ℕ) :
    signedSawtooth (-(k : ℤ)) q = -rationalSawtooth k q := by
  by_cases hk : k = 0
  · subst k
    simp [signedSawtooth, rationalSawtooth_zero]
  · simp [signedSawtooth, hk]

theorem signedChiFour_natCast (k : ℕ) : signedChiFour k = chiFourSign k := by
  simp [signedChiFour]

theorem signedChiFour_neg_natCast (k : ℕ) :
    signedChiFour (-(k : ℤ)) = -chiFourSign k := by
  by_cases hk : k = 0
  · subst k
    norm_num [signedChiFour, chiFourSign]
  · simp [signedChiFour, hk]

theorem signedChiFour_eq_residue (k : ℤ) :
    signedChiFour k = chiFourSign ((k % 4).toNat) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · have hrem : (n : ℤ) % 4 = ((n % 4 : ℕ) : ℤ) :=
      (Int.natCast_emod n 4).symm
    rw [signedChiFour_natCast, hrem, Int.toNat_natCast]
    simp [chiFourSign]
  · rw [signedChiFour_neg_natCast, Int.neg_emod]
    have hd : (4 : ℤ) ∣ (n : ℤ) ↔ n % 4 = 0 := by
      constructor
      · intro h
        have hn : 4 ∣ n := by exact_mod_cast h
        exact Nat.dvd_iff_mod_eq_zero.mp hn
      · intro h
        have hn : 4 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr h
        exact_mod_cast hn
    have hrem : (n : ℤ) % 4 = ((n % 4 : ℕ) : ℤ) :=
      (Int.natCast_emod n 4).symm
    simp only [hd, hrem]
    have hn := Nat.mod_lt n (by decide : 0 < 4)
    interval_cases h : n % 4 <;> norm_num [chiFourSign, h] <;> decide

theorem signedConductorFourLift_natCast (L k : ℕ) :
    signedConductorFourLift L k = conductorFourLift L k := by
  simp only [signedConductorFourLift, conductorFourLift, ← Nat.cast_mul,
    signedSawtooth_natCast]

theorem signedConductorFourLift_neg_natCast (L k : ℕ) :
    signedConductorFourLift L (-(k : ℤ)) = -conductorFourLift L k := by
  simp only [signedConductorFourLift, conductorFourLift, neg_mul, ← Nat.cast_mul,
    signedSawtooth_neg_natCast, mul_neg, Finset.sum_neg_distrib]

/-- The signed extension agrees with the existing periodic Bernoulli function. -/
theorem signedSawtooth_eq_centeredSawtooth {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (k : ℤ) :
    (signedSawtooth k q : ℂ) = CarryBoundarySpectra.centeredSawtooth (k : ZMod q) := by
  have hnat (n : ℕ) : (rationalSawtooth n q : ℂ) =
      CarryBoundarySpectra.centeredSawtooth (n : ZMod q) := by
    have h := rationalSawtooth_val_eq_centeredSawtooth (n : ZMod q)
    simpa only [ZMod.val_natCast, rationalSawtooth, Nat.mod_mod] using h
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa only [signedSawtooth_natCast, Int.cast_natCast] using hnat n
  · rw [signedSawtooth_neg_natCast, Rat.cast_neg, Int.cast_neg, Int.cast_natCast,
      CarryBoundarySpectra.centeredSawtooth_neg hq, hnat]

/-- Title: `The conductor four greatest common divisor formula holds for every integer frequency`. -/
theorem signedConductorFourLift_gcd {L : ℕ} (hL : 0 < L) (k : ℤ) :
    signedConductorFourLift L k =
      -(k.natAbs.gcd L : ℚ) / 2 * (signedChiFour (k / (k.natAbs.gcd L : ℤ)) : ℚ) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa only [signedConductorFourLift_natCast, Int.natAbs_natCast,
      ← Int.natCast_ediv, signedChiFour_natCast] using conductorFourLift_gcd hL n
  · have hd : (n.gcd L : ℤ) ∣ (n : ℤ) := by exact_mod_cast Nat.gcd_dvd_left n L
    simp only [signedConductorFourLift_neg_natCast, Int.natAbs_neg, Int.natAbs_natCast,
      Int.neg_ediv_of_dvd hd, ← Int.natCast_ediv, signedChiFour_neg_natCast, Int.cast_neg]
    rw [conductorFourLift_gcd hL]
    ring

theorem signed_quarter_sawtooth_difference (k : ℤ) :
    signedSawtooth k 4 - signedSawtooth (3 * k) 4 =
      -(1 / 2 : ℚ) * (signedChiFour k : ℚ) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · have hmul : (3 : ℤ) * (n : ℤ) = ((3 * n : ℕ) : ℤ) := by push_cast; ring
    rw [hmul, signedSawtooth_natCast, signedSawtooth_natCast, signedChiFour_natCast]
    exact quarter_sawtooth_difference n
  · have hmul : (3 : ℤ) * -(n : ℤ) = -((3 * n : ℕ) : ℤ) := by push_cast; ring
    rw [hmul, signedSawtooth_neg_natCast, signedSawtooth_neg_natCast,
      signedChiFour_neg_natCast, Int.cast_neg]
    have h := quarter_sawtooth_difference n
    linarith

theorem signedConductorFourLift_two_quarter_values {L : ℕ} (hL : 0 < L) (k : ℤ) :
    signedConductorFourLift L k = (k.natAbs.gcd L : ℚ) *
      (signedSawtooth (k / (k.natAbs.gcd L : ℤ)) 4 -
        signedSawtooth (3 * (k / (k.natAbs.gcd L : ℤ))) 4) := by
  rw [signedConductorFourLift_gcd hL, signed_quarter_sawtooth_difference]
  ring

theorem signedConductorFourLift_odd_sum (L : ℕ) (k : ℤ) :
    signedConductorFourLift L k =
      ∑ a ∈ (Finset.range (4 * L)).filter Odd,
        (chiFourSign a : ℚ) * signedSawtooth (k * a) (4 * L) := by
  unfold signedConductorFourLift
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hnot
  have hodd : ¬Odd a := by simpa [Finset.mem_filter, ha] using hnot
  have hpar : a % 2 ≠ 1 := by simpa only [Nat.odd_iff] using hodd
  have hmod2 : (a % 4) % 2 = a % 2 := Nat.mod_mod_of_dvd a (by decide : 2 ∣ 4)
  have hz : chiFourSign a = 0 := by
    have h1 : a % 4 ≠ 1 := by omega
    have h3 : a % 4 ≠ 3 := by omega
    simp [chiFourSign, h1, h3]
  simp [hz]

end NField.Alignment.ConductorFourLifts
