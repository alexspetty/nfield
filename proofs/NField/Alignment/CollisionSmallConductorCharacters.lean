/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMixedMomentCharacterization
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# The characters in the small-conductor examples

The character of discriminant -3 has its literal residue table. The
character of discriminant -4 is Mathlib's canonical quadratic character.
The modulus-six character is the actual change of level from three, and
its L(2) Euler factor is retained explicitly.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSmallConductorCharacters

def chiMinusThreeInt : MulChar (ZMod 3) ℤ where
  toFun a := match a with
    | 0 => 0
    | 1 => 1
    | 2 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

def chiMinusThree : DirichletCharacter ℂ 3 :=
  chiMinusThreeInt.ringHomComp (Int.castRingHom ℂ)

def chiMinusFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def chiInducedSix : DirichletCharacter ℂ 6 :=
  DirichletCharacter.changeLevel (by norm_num : 3∣6) chiMinusThree

theorem chiMinusThreeInt_quadratic : chiMinusThreeInt.IsQuadratic := by
  unfold MulChar.IsQuadratic chiMinusThreeInt
  decide

theorem chiMinusThree_odd : chiMinusThree.Odd := by
  change chiMinusThree (-1 : ZMod 3)= -1
  rw [show (-1 : ZMod 3)=2 by decide]
  norm_num [chiMinusThree,MulChar.ringHomComp_apply,chiMinusThreeInt]

theorem chiMinusFour_odd : chiMinusFour.Odd := by
  change chiMinusFour (-1 : ZMod 4)= -1
  rw [show (-1 : ZMod 4)=3 by decide]
  norm_num [chiMinusFour,MulChar.ringHomComp_apply,ZMod.χ₄]

theorem chiInducedSix_nat (n : ℕ) : chiInducedSix (n : ZMod 6)=
    if n.Coprime 6 then chiMinusThree (n : ZMod 3) else 0 := by
  classical
  by_cases hn : n.Coprime 6
  · rw [if_pos hn]
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd chiMinusThree
      (by norm_num : 3∣6) (ZMod.unitOfCoprime n hn)
    simpa only [chiInducedSix,ZMod.coe_unitOfCoprime,ZMod.cast_natCast (by norm_num : 3∣6)] using h
  · rw [if_neg hn]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hn)

theorem chiInducedSix_odd : chiInducedSix.Odd := by
  change chiInducedSix (-1 : ZMod 6)= -1
  rw [show (-1 : ZMod 6)=(5 : ℕ) by decide,chiInducedSix_nat]
  norm_num [chiMinusThree,MulChar.ringHomComp_apply,chiMinusThreeInt]

theorem induced_six_L_two_factor :
    DirichletCharacter.LFunction chiInducedSix 2=
      (5/4 : ℂ)*DirichletCharacter.LFunction chiMinusThree 2 := by
  have h := DirichletCharacter.LFunction_changeLevel (by norm_num : 3∣6) chiMinusThree
    (Or.inr (by norm_num : (2 : ℂ)≠1))
  have hfactor : (∏ p ∈ Nat.primeFactors 6,
      (1-chiMinusThree (p : ZMod 3)*(p : ℂ)^(-(2 : ℂ))))=(5/4 : ℂ) := by
    have hp : Nat.primeFactors 6={2,3} := by
      rw [show 6=2*3 from rfl,Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.prime_two.primeFactors,Nat.prime_three.primeFactors]
      decide
    norm_num [hp,
      chiMinusThree,MulChar.ringHomComp_apply,chiMinusThreeInt,
      Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hfactor] at h
  simpa only [chiInducedSix,mul_comm] using h

end NField.Alignment.CollisionSmallConductorCharacters
