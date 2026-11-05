/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeBernoulliMoment
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex
import NField.Alignment.MagnitudeBaseSevenPolynomial

/-!
# The actual base-seven character

The residue three generates the complete unit group modulo 49. A primitive
fourteenth root specifies a character on that group. Its parity, conductor
and values are proved from the generator, with finite arithmetic checked by
the kernel.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeBaseSeven

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.PrimeSquareMagnitudeFamily
open NField.Alignment.CollisionSpectrumLandscape

def generator : UnitClass 49 := ZMod.unitOfCoprime 3 (by decide)

theorem generator_val : generator.val = (3 : ZMod 49) := rfl

theorem generator_order : orderOf generator = 42 := by
  apply (orderOf_eq_iff (by decide : 0 < 42)).2
  constructor
  · apply Units.ext
    decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

theorem unit49_card : Fintype.card (UnitClass 49) = 42 := by
  rw [ZMod.card_units_eq_totient]
  decide

theorem generator_pow_injective : Function.Injective (fun j : Fin 42 => generator^j.val) := by
  intro i j hij
  apply Fin.ext
  have hg : IsPrimitiveRoot generator 42 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact generator_order
  exact hg.pow_inj i.isLt j.isLt hij

noncomputable def generatorEquiv : Fin 42 ≃ UnitClass 49 :=
  Equiv.ofBijective (fun j => generator^j.val)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨generator_pow_injective, by rw [Fintype.card_fin, unit49_card]⟩)

theorem generator_generates (x : UnitClass 49) : x ∈ Subgroup.zpowers generator := by
  obtain ⟨j, rfl⟩ := generatorEquiv.surjective x
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers generator) j.val

/-- This character has value `z` at three; its inverse is the manuscript's
character with conjugate value `z`. -/
noncomputable def rootCharacter (z : ℂ) (hz : IsPrimitiveRoot z 14) : Character 49 :=
  MulChar.ofUnitHom (monoidHomOfForallMemZpowers generator_generates
    (g' := Units.mk0 z (hz.ne_zero (by decide))) (by
      rw [generator_order, orderOf_dvd_iff_pow_eq_one]
      apply Units.ext
      change z^42 = 1
      calc
        z^42 = (z^14)^3 := by ring
        _ = 1 := by rw [hz.pow_eq_one]; norm_num))

theorem rootCharacter_generator {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    rootCharacter z hz (3 : ZMod 49) = z := by
  rw [← generator_val]
  unfold rootCharacter
  rw [MulChar.ofUnitHom_coe, monoidHomOfForallMemZpowers_apply_gen]
  rfl

theorem rootCharacter_pow {z : ℂ} (hz : IsPrimitiveRoot z 14) (j : ℕ) :
    rootCharacter z hz ((3 : ZMod 49)^j) = z^j := by
  rw [map_pow, rootCharacter_generator hz]

theorem rootCharacter_odd {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    (rootCharacter z hz).Odd := by
  have hminus : (3 : ZMod 49)^21 = -1 := by decide
  unfold DirichletCharacter.Odd
  rw [← hminus, rootCharacter_pow, show 21 = 7*3 from rfl, pow_mul,
    primitive_fourteen_pow_seven hz]
  norm_num

theorem rootCharacter_primitive {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    (rootCharacter z hz).IsPrimitive := by
  by_contra hnot
  have hfactor : (rootCharacter z hz).FactorsThrough 7 := by
    have h := (nonprimitive_iff_factorsThrough_previous (by decide : Nat.Prime 7)
      (by decide : 2 ≤ 2) (rootCharacter z hz)).1 hnot
    simpa using h
  obtain ⟨hd, ψ, heq⟩ := hfactor
  have h36 : generator^6 = ZMod.unitOfCoprime 43 (by decide : Nat.Coprime 43 49) := by
    apply Units.ext
    decide
  have hred : (ZMod.unitsMap hd (generator^6)).val = (1 : ZMod 7) := by
    rw [h36]
    change ZMod.cast ((43 : ℕ) : ZMod 49) = (1 : ZMod 7)
    rw [ZMod.cast_natCast hd]
    decide
  have hone : rootCharacter z hz ((3 : ZMod 49)^6) = 1 := by
    have h := liftedCharacter_apply_unit hd ψ (generator^6)
    rw [← heq, hred, map_one] at h
    exact h
  rw [rootCharacter_pow] at hone
  exact hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) hone

theorem rootCharacter_inverse_odd {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    (rootCharacter z hz)⁻¹.Odd := by
  change ((rootCharacter z hz)⁻¹) (-1) = -1
  rw [MulChar.inv_apply_eq_inv', rootCharacter_odd hz]
  norm_num

theorem rootCharacter_inverse_primitive {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    (rootCharacter z hz)⁻¹.IsPrimitive := by
  by_contra hnot
  have hfactor : ((rootCharacter z hz)⁻¹).FactorsThrough 7 := by
    have h := (nonprimitive_iff_factorsThrough_previous (by decide : Nat.Prime 7)
      (by decide : 2 ≤ 2) ((rootCharacter z hz)⁻¹)).1 hnot
    simpa using h
  have hback : (rootCharacter z hz).FactorsThrough 7 := by
    obtain ⟨hd, ψ, heq⟩ := hfactor
    refine ⟨hd, ψ⁻¹, ?_⟩
    have h := congrArg Inv.inv heq
    simpa only [inv_inv, map_inv] using h
  have hnot' : ¬ (rootCharacter z hz).IsPrimitive := by
    exact (nonprimitive_iff_factorsThrough_previous (by decide : Nat.Prime 7)
      (by decide : 2 ≤ 2) (rootCharacter z hz)).2 (by simpa using hback)
  exact hnot' (rootCharacter_primitive hz)

noncomputable def witness (z : ℂ) (hz : IsPrimitiveRoot z 14) : PrimitiveOddFamily 7 :=
  ⟨(rootCharacter z hz)⁻¹, rootCharacter_inverse_primitive hz, rootCharacter_inverse_odd hz⟩

theorem witness_conjugate_value {z : ℂ} (hz : IsPrimitiveRoot z 14) (x : ZMod 49) :
    star ((witness z hz).val x) = rootCharacter z hz x := by
  change star ((rootCharacter z hz)⁻¹ x) = _
  rw [MulChar.star_apply', inv_inv]

theorem witness_spec {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    (witness z hz).val.IsPrimitive ∧ (witness z hz).val.Odd ∧
      star ((witness z hz).val (3 : ZMod 49)) = z := by
  refine ⟨(witness z hz).property.1, (witness z hz).property.2, ?_⟩
  rw [witness_conjugate_value, rootCharacter_generator]

theorem primitive_fourteen_pow_mod {z : ℂ} (hz : IsPrimitiveRoot z 14) (j : ℕ) :
    z^j = z^(j%14) := by
  have h := pow_mod_orderOf z j
  rw [← hz.eq_orderOf] at h
  exact h.symm

theorem witness_short_sum {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    shortSum 7 (witness z hz) = shortPolynomial z := by
  unfold shortSum
  simp only [witness_conjugate_value]
  norm_num [Finset.sum_Icc_succ_top]
  have htwo : (2 : ZMod 49) = 3^26 := by decide
  have hfour : (4 : ZMod 49) = 3^10 := by decide
  have hfive : (5 : ZMod 49) = 3^29 := by decide
  have hsix : (6 : ZMod 49) = 3^27 := by decide
  rw [htwo, hfour, hfive, hsix]
  simp only [rootCharacter_pow, rootCharacter_generator]
  rw [primitive_fourteen_pow_mod hz 26, primitive_fourteen_pow_mod hz 29,
    primitive_fourteen_pow_mod hz 27]
  norm_num [shortPolynomial]
  ring

theorem witness_bernoulli_sum {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    bernoulliSum 7 (witness z hz) = bernoulliPolynomial z := by
  have hreindex :
      (∑ x : UnitClass 49, (x.val.val : ℂ)*rootCharacter z hz x.val) =
        ∑ j : Fin 42, (((3^j.val)%49 : ℕ) : ℂ)*z^(j.val%14) := by
    symm
    apply Fintype.sum_equiv generatorEquiv
    intro j
    change _ = ((generator^j.val).val.val : ℂ)*rootCharacter z hz (generator^j.val).val
    rw [Units.val_pow_eq_pow_val, generator_val, rootCharacter_pow,
      primitive_fourteen_pow_mod hz j.val]
    congr 2
    have hcast : (3 : ZMod 49)^j.val = ((3^j.val : ℕ) : ZMod 49) := by push_cast; rfl
    rw [hcast, ZMod.val_natCast]
  unfold bernoulliSum witness
  simp only [inv_inv]
  unfold generalizedBernoulliOne
  change (49 : ℂ)⁻¹ * (∑ a : UnitClass 49,
    (a.val.val : ℂ)*rootCharacter z hz a.val) = bernoulliPolynomial z
  rw [hreindex, Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (((3^j)%49 : ℕ) : ℂ)*z^(j%14)) 42]
  have hphi := primitive_fourteen_cyclotomic hz
  unfold cyclotomicFourteenValue at hphi
  rw [bernoulliPolynomial_expanded]
  norm_num [Finset.sum_range_succ]
  linear_combination
    (1+2*z+2*z^2+2*z^3+2*z^4+2*z^5+2*z^6+z^7) * hphi

theorem witness_square_discrepancy {z : ℂ} (hz : IsPrimitiveRoot z 14) :
    8*Complex.normSq (shortSum 7 (witness z hz)) -
      7*Complex.normSq (bernoulliSum 7 (witness z hz)) ≠ 0 := by
  rw [witness_short_sum, witness_bernoulli_sum]
  exact normSq_discrepancy_ne_zero hz

end NField.Alignment.MagnitudeBaseSeven
