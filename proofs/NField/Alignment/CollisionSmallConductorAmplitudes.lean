/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSmallConductorCharacters

/-!
# The literal conductor-three, four and six examples

The finite residue tables are lifted through the absolutely convergent
L(2) series. The modulus-six value uses the actual induced character and
its Euler factor, before substitution into the original amplitude.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSmallConductorAmplitudes

open scoped BigOperators
open CollisionSmallConductorCharacters CollisionCotangentPositivity
open CollisionCotangentSeries CollisionCotangentMixedMoment CollisionCotangentLValue
open CollisionAmplitudeCotangent CollisionAmplitudeArithmetic CollisionHarmonicSeed
open CollisionJordanVariance

theorem unitCotangentTerm_eq_residue {q : ℕ} (hq : 0 < q) (n : ℕ) :
    unitCotangentTerm q n=unitCotangentResidue q (n%q)/(n : ℝ)^2 := by
  by_cases hd : q∣n
  · simp [unitCotangentTerm,cotangentTerm,unitCotangentResidue,hd,
      Nat.mod_eq_zero_of_dvd hd,Real.cot_eq_cos_div_sin]
  · simp only [unitCotangentTerm,cotangentTerm,unitCotangentResidue,
      ZMod.coprime_mod_iff_coprime,if_neg hd,CollisionFiniteSineTransform.cotangent_mod hq]
    split_ifs <;> simp

theorem unitCotangentSum_of_character_table {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℂ)
    (hres : ∀ a : ℕ, a<q → (unitCotangentResidue q a : ℂ)=c*χ (a : ZMod q)) :
    (unitCotangentSum q : ℂ)=c*DirichletCharacter.LFunction χ 2 := by
  rw [unitCotangentSum,Complex.ofReal_tsum]
  have hterm (n : ℕ) : (unitCotangentTerm q n : ℂ)=c*(χ (n : ZMod q)/(n : ℂ)^2) := by
    rw [unitCotangentTerm_eq_residue (NeZero.pos q),Complex.ofReal_div,
      hres (n%q) (Nat.mod_lt n (NeZero.pos q)),ZMod.natCast_mod]
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_mul_left,(character_L_two_hasSum χ).tsum_eq]

theorem cotangent_pi_third : Real.cot (Real.pi/3)=1/Real.sqrt 3 := by
  rw [Real.cot_eq_cos_div_sin,Real.cos_pi_div_three,Real.sin_pi_div_three]
  ring

theorem cotangent_pi_fourth : Real.cot (Real.pi/4)=1 := by
  rw [Real.cot_eq_cos_div_sin,Real.cos_pi_div_four,Real.sin_pi_div_four]
  exact div_self (by positivity)

theorem cotangent_pi_sixth : Real.cot (Real.pi/6)=Real.sqrt 3 := by
  rw [Real.cot_eq_cos_div_sin,Real.cos_pi_div_six,Real.sin_pi_div_six]
  ring

theorem cotangent_three_table (a : ℕ) (ha : a<3) :
    (unitCotangentResidue 3 a : ℂ)=(1/(Real.sqrt 3 : ℂ))*chiMinusThree (a : ZMod 3) := by
  have hcomp : Real.cot (Real.pi*2/3)= -Real.cot (Real.pi/3) := by
    simpa using cotangent_complement (q := 3) (u := 1) (by norm_num) (by norm_num)
  interval_cases a <;>
    norm_num [unitCotangentResidue,chiMinusThree,MulChar.ringHomComp_apply,
      chiMinusThreeInt,hcomp,cotangent_pi_third]

theorem cotangent_four_table (a : ℕ) (ha : a<4) :
    (unitCotangentResidue 4 a : ℂ)=chiMinusFour (a : ZMod 4) := by
  have hcomp : Real.cot (Real.pi*3/4)= -Real.cot (Real.pi/4) := by
    simpa using cotangent_complement (q := 4) (u := 1) (by norm_num) (by norm_num)
  interval_cases a <;>
    norm_num [unitCotangentResidue,chiMinusFour,MulChar.ringHomComp_apply,
      ZMod.χ₄,hcomp,cotangent_pi_fourth]

theorem cotangent_six_table (a : ℕ) (ha : a<6) :
    (unitCotangentResidue 6 a : ℂ)=(Real.sqrt 3 : ℂ)*chiInducedSix (a : ZMod 6) := by
  have hcomp : Real.cot (Real.pi*5/6)= -Real.cot (Real.pi/6) := by
    simpa using cotangent_complement (q := 6) (u := 1) (by norm_num) (by norm_num)
  rw [chiInducedSix_nat]
  interval_cases a <;>
    norm_num [unitCotangentResidue,chiMinusThree,MulChar.ringHomComp_apply,
      chiMinusThreeInt,hcomp,cotangent_pi_sixth]

theorem unitCotangentSum_three :
    (unitCotangentSum 3 : ℂ)=(1/(Real.sqrt 3 : ℂ))*DirichletCharacter.LFunction chiMinusThree 2 :=
  unitCotangentSum_of_character_table chiMinusThree _ cotangent_three_table

theorem unitCotangentSum_four :
    (unitCotangentSum 4 : ℂ)=DirichletCharacter.LFunction chiMinusFour 2 := by
  simpa only [one_mul] using unitCotangentSum_of_character_table chiMinusFour 1
    (fun a ha => (cotangent_four_table a ha).trans (one_mul _).symm)

theorem unitCotangentSum_six :
    (unitCotangentSum 6 : ℂ)=(Real.sqrt 3 : ℂ)*DirichletCharacter.LFunction chiInducedSix 2 :=
  unitCotangentSum_of_character_table chiInducedSix _ cotangent_six_table

theorem L_three_eq_real_cotangent : DirichletCharacter.LFunction chiMinusThree 2=
    ((Real.sqrt 3*unitCotangentSum 3 : ℝ) : ℂ) := by
  have hs : (Real.sqrt 3 : ℂ)≠0 := by exact_mod_cast (show Real.sqrt (3 : ℝ)≠0 by positivity)
  rw [Complex.ofReal_mul,unitCotangentSum_three]
  field_simp

theorem L_four_eq_real_cotangent : DirichletCharacter.LFunction chiMinusFour 2=
    (unitCotangentSum 4 : ℂ) := unitCotangentSum_four.symm

theorem small_L_values_real :
    (DirichletCharacter.LFunction chiMinusThree 2).im=0 ∧
    (DirichletCharacter.LFunction chiMinusFour 2).im=0 := by
  rw [L_three_eq_real_cotangent,L_four_eq_real_cotangent]
  simp

theorem unitCotangentSum_six_three : unitCotangentSum 6=(15/4 : ℝ)*unitCotangentSum 3 := by
  have he := unitCotangentSum_six
  rw [induced_six_L_two_factor,L_three_eq_real_cotangent] at he
  have hr := congrArg Complex.re he
  norm_num [Complex.mul_re] at hr
  rw [hr]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
  ring

theorem deltaThree_three : deltaThree 3=26/27 := by
  norm_num [deltaThree,Nat.prime_three.primeFactors]

theorem deltaThree_four : deltaThree 4=7/8 := by
  have hp : Nat.primeFactors 4={2} := by
    simpa using Nat.primeFactors_prime_pow (p := 2) (k := 2) (by norm_num) Nat.prime_two
  norm_num [deltaThree,hp]

theorem deltaThree_six : deltaThree 6=91/108 := by
  have hp : Nat.primeFactors 6={2,3} := by
    rw [show 6=2*3 from rfl,Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_two.primeFactors,Nat.prime_three.primeFactors]
    decide
  norm_num [deltaThree,hp]

theorem literal_amplitude_three : amplitude 3=
    1/2-(3*Real.sqrt 3*Real.pi/(52*zetaThree))*(DirichletCharacter.LFunction chiMinusThree 2).re := by
  rw [literal_amplitude_cotangent (by norm_num),deltaThree_three,L_three_eq_real_cotangent,
    Complex.ofReal_re]
  have hz := zetaThree_pos.ne'
  norm_num
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
  ring

theorem literal_amplitude_four : amplitude 4=
    1/2-Real.pi*(DirichletCharacter.LFunction chiMinusFour 2).re/(7*zetaThree) := by
  rw [literal_amplitude_cotangent (by norm_num),deltaThree_four,L_four_eq_real_cotangent,
    Complex.ofReal_re]
  ring

theorem literal_amplitude_six : amplitude 6=(15*amplitude 3-4)/7 := by
  rw [literal_amplitude_cotangent (q := 6) (by norm_num),
    literal_amplitude_cotangent (q := 3) (by norm_num),
    deltaThree_six,deltaThree_three,unitCotangentSum_six_three]
  ring

theorem literal_small_conductor_examples :
    (amplitude 3 : ℂ)=1/2-(3*(Real.sqrt 3 : ℂ)*(Real.pi : ℂ)/(52*(zetaThree : ℂ)))*
      DirichletCharacter.LFunction chiMinusThree 2 ∧
    (amplitude 4 : ℂ)=1/2-(Real.pi : ℂ)*DirichletCharacter.LFunction chiMinusFour 2/
      (7*(zetaThree : ℂ)) ∧
    amplitude 6=(15*amplitude 3-4)/7 := by
  refine ⟨?_,?_,literal_amplitude_six⟩
  · have h := congrArg Complex.ofReal literal_amplitude_three
    rw [L_three_eq_real_cotangent] at h ⊢
    simp only [Complex.ofReal_re] at h
    push_cast at h ⊢
    exact h
  · have h := congrArg Complex.ofReal literal_amplitude_four
    rw [L_four_eq_real_cotangent] at h ⊢
    simp only [Complex.ofReal_re] at h
    push_cast at h ⊢
    exact h

end NField.Alignment.CollisionSmallConductorAmplitudes
