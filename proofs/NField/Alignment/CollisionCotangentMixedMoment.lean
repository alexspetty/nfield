/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCotangentLValue

/-!
# The all-character cotangent mixed moment

Finite character orthogonality is used on the actual unit group. The
L(1) factors are already identified by ordered limits; only the absolutely
convergent reciprocal-square series is rearranged here.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCotangentMixedMoment

open scoped BigOperators Classical
open CollisionCotangentLValue CollisionCotangentSeries CollisionCharacterStructure

def cotangentSignal {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) : ℂ :=
  (Real.cot (Real.pi*(a.val.val : ℝ)/(q : ℝ)) : ℂ)

def mixedMomentScale (q : ℕ) : ℂ := 2*(q : ℂ)/((Real.pi : ℂ)*(q.totient : ℂ))

def cotangentCharacterMoment (q : ℕ) [NeZero q] : ℂ :=
  ∑ χ : DirichletCharacter ℂ q, if χ.Odd then
    DirichletCharacter.LFunction χ⁻¹ 1*DirichletCharacter.LFunction χ 2 else 0

theorem conjugated_character_reconstruction {q : ℕ} [NeZero q]
    (F : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      χ a.val * ∑ b : (ZMod q)ˣ, star (χ b.val)*F b = F a := by
  have he : (∑ χ : DirichletCharacter ℂ q,
      χ a.val * ∑ b : (ZMod q)ˣ, star (χ b.val)*F b)=
      ∑ b : (ZMod q)ˣ, (∑ χ : DirichletCharacter ℂ q, star (χ b.val)*χ a.val)*F b := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro _ _
    ring
  rw [he]
  simp_rw [unit_character_orthogonality]
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp [ite_mul,htot]

theorem even_inverse_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Even) : χ⁻¹.Even := by
  change χ⁻¹ (-1)=1
  rw [conjugate_character_value, show χ (-1)=1 from hχ]
  simp

theorem cotangent_signal_coefficient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ a : (ZMod q)ˣ, star (χ a.val)*cotangentSignal a)=
      if χ.Odd then (2*(q : ℂ)/(Real.pi : ℂ))*DirichletCharacter.LFunction χ⁻¹ 1
      else 0 := by
  by_cases hχ : χ.Odd
  · rw [if_pos hχ]
    exact literal_odd_character_cotangent χ hχ
  · rw [if_neg hχ]
    have he := χ.even_or_odd.resolve_right hχ
    simpa only [conjugate_character_value,cotangentSignal] using
      even_character_unit_cotangent χ⁻¹ (even_inverse_character χ he)

theorem cotangent_signal_expansion {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) :
    cotangentSignal a=mixedMomentScale q * ∑ χ : DirichletCharacter ℂ q,
      if χ.Odd then DirichletCharacter.LFunction χ⁻¹ 1*χ a.val else 0 := by
  rw [← conjugated_character_reconstruction cotangentSignal a]
  simp_rw [cotangent_signal_coefficient]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hχ : χ.Odd
  · simp only [if_pos hχ,mixedMomentScale]
    ring
  · simp [hχ]

theorem unitCotangentTerm_character_expansion {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (n : ℕ) :
    (unitCotangentTerm q n : ℂ)=mixedMomentScale q *
      ∑ χ : DirichletCharacter ℂ q, if χ.Odd then
        DirichletCharacter.LFunction χ⁻¹ 1*(χ (n : ZMod q)/(n : ℂ)^2) else 0 := by
  by_cases hc : n.Coprime q
  · have hn : ¬ q ∣ n := by
      intro hd
      have hg : n.gcd q=q := Nat.gcd_eq_right_iff_dvd.mpr hd
      rw [hc.gcd_eq_one] at hg
      omega
    let a := ZMod.unitOfCoprime n hc
    have ha : a.val=(n : ZMod q) := ZMod.coe_unitOfCoprime n hc
    have hav : a.val.val=n%q := by rw [ha,ZMod.val_natCast]
    have hcot : (Real.cot (Real.pi*(n : ℝ)/(q : ℝ)) : ℂ)=cotangentSignal a := by
      rw [cotangentSignal,hav,CollisionFiniteSineTransform.cotangent_mod (NeZero.pos q) n]
    simp only [unitCotangentTerm,if_pos hc,cotangentTerm,if_neg hn,
      Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
    rw [hcot,cotangent_signal_expansion]
    rw [mul_div_assoc,Finset.sum_div,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hχ : χ.Odd
    · simp only [if_pos hχ,ha]
      ring
    · simp [hχ]
  · have hz (χ : DirichletCharacter ℂ q) : χ (n : ZMod q)=0 :=
      MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime n q).not.mpr hc)
    simp [unitCotangentTerm,hc,hz]

theorem character_L_two_hasSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    HasSum (fun n : ℕ => χ (n : ZMod q)/(n : ℂ)^2)
      (DirichletCharacter.LFunction χ 2) := by
  have hs := χ.LSeriesSummable_of_one_lt_re (s := 2) (by norm_num)
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by norm_num : 1 < (2 : ℂ).re)]
  convert hs.hasSum using 1
  · ext n
    rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0),Complex.cpow_ofNat]
  · rfl

theorem literal_unit_cotangent_mixed_moment {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    (unitCotangentSum q : ℂ)=mixedMomentScale q*cotangentCharacterMoment q := by
  have hs (χ : DirichletCharacter ℂ q) : Summable (fun n : ℕ => if χ.Odd then
      DirichletCharacter.LFunction χ⁻¹ 1*(χ (n : ZMod q)/(n : ℂ)^2) else 0) := by
    by_cases hχ : χ.Odd
    · simpa only [if_pos hχ] using
        (character_L_two_hasSum χ).summable.mul_left (DirichletCharacter.LFunction χ⁻¹ 1)
    · simp only [if_neg hχ,summable_zero]
  rw [unitCotangentSum,Complex.ofReal_tsum]
  simp_rw [unitCotangentTerm_character_expansion hq]
  rw [tsum_mul_left,Summable.tsum_finsetSum (fun χ _ => hs χ),cotangentCharacterMoment]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hχ : χ.Odd
  · simp only [if_pos hχ]
    rw [tsum_mul_left,(character_L_two_hasSum χ).tsum_eq]
  · simp [hχ]

theorem mixedMomentScale_real (q : ℕ) :
    mixedMomentScale q=((2*(q : ℝ)/(Real.pi*(q.totient : ℝ)) : ℝ) : ℂ) := by
  unfold mixedMomentScale
  push_cast
  rfl

theorem cotangentCharacterMoment_real {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    (cotangentCharacterMoment q).im=0 := by
  have he := congrArg Complex.im (literal_unit_cotangent_mixed_moment hq)
  rw [mixedMomentScale_real] at he
  simp only [Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,zero_mul,add_zero] at he
  have hp : 0 < 2*(q : ℝ)/(Real.pi*(q.totient : ℝ)) :=
    div_pos (mul_pos (by norm_num) (by exact_mod_cast (NeZero.pos q)))
      (mul_pos Real.pi_pos (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))))
  exact (mul_eq_zero.mp he.symm).resolve_left hp.ne'

theorem no_odd_character_two (χ : DirichletCharacter ℂ 2) : ¬ χ.Odd := by
  intro hχ
  change χ (-1)= -1 at hχ
  rw [show (-1 : ZMod 2)=1 by decide,χ.map_one] at hχ
  norm_num at hχ

theorem cotangentCharacterMoment_two : cotangentCharacterMoment 2=0 := by
  simp [cotangentCharacterMoment,no_odd_character_two]

theorem unitCotangentSum_two : unitCotangentSum 2=0 := by
  have he := literal_unit_cotangent_mixed_moment (q := 2) (by norm_num)
  rw [cotangentCharacterMoment_two,mul_zero] at he
  exact_mod_cast he

end NField.Alignment.CollisionCotangentMixedMoment
