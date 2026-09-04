/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SubgroupOrbitJacobiExpansion
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Index-two orbit energy

The quadratic-residue indicator is split into its principal and quadratic
characters.  Its additive boundary has an exact shifted-Jacobi reduction.
The off-resonance second moment then closes into the four residue classes
modulo eight.
-/

namespace NField.Alignment.IndexTwoOrbitEnergy

noncomputable section

open scoped BigOperators ComplexConjugate ZMod
open ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean

attribute [local instance] Fintype.ofFinite

local instance classicalPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The quadratic character modulo a prime, embedded in the complex numbers. -/
noncomputable def complexQuadraticCharacter (q : ℕ) [Fact q.Prime] :
    Character q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

/-- The quadratic-residue indicator, with Dirichlet characters zero at the
nonunit endpoint. -/
noncomputable def indexTwoIndicator
    {q : ℕ} [Fact q.Prime] (x : ZMod q) : ℂ :=
  (1 / 2 : ℂ) * ((1 : Character q) x + complexQuadraticCharacter q x)

/-- The additive boundary of the index-two orbit. -/
noncomputable def indexTwoBoundary
    {q : ℕ} [Fact q.Prime] (x : ZMod q) : ℂ :=
  indexTwoIndicator (q := q) (x - 1) - indexTwoIndicator (q := q) x

/-- Boundary flux for the index-two orbit. -/
noncomputable def indexTwoFlux
    {q : ℕ} [Fact q.Prime] (chi : Character q) : ℂ :=
  ∑ x : ZMod q, indexTwoBoundary (q := q) x * chi x

/-- The shifted quadratic Jacobi sum appearing at the additive edge. -/
noncomputable def shiftedQuadraticJacobi
    {q : ℕ} [Fact q.Prime] (chi : Character q) : ℂ :=
  ∑ y : ZMod q, complexQuadraticCharacter q y * chi (y + 1)

/-- The principal character has a two-point additive boundary. -/
theorem principalCharacter_boundary
    {q : ℕ} [NeZero q] (hq : q.Prime) (x : ZMod q) :
    (1 : Character q) (x - 1) - (1 : Character q) x =
      (if x = 0 then 1 else 0) - (if x = 1 then 1 else 0) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hunit (z : ZMod q) : IsUnit z ↔ z ≠ 0 := isUnit_iff_ne_zero
  have honezero : (1 : Character q) (0 : ZMod q) = 0 :=
    MulChar.map_nonunit _ (by simp)
  by_cases hx0 : x = 0
  · subst x
    have hneg : (-1 : ZMod q) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    simp [honezero, MulChar.one_apply ((hunit _).2 hneg)]
  · by_cases hx1 : x = 1
    · subst x
      simp [honezero, MulChar.one_apply isUnit_one]
    · have hxunit : IsUnit x := (hunit _).2 hx0
      have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      have hxsubunit : IsUnit (x - 1) := (hunit _).2 hxsub
      simp [hx0, hx1, MulChar.one_apply hxunit,
        MulChar.one_apply hxsubunit]

/-- The endpoint term contributes exactly `-1` against every Dirichlet
character modulo an odd prime. -/
theorem principalBoundary_flux
    {q : ℕ} [NeZero q] (hq : q.Prime) (chi : Character q) :
    (∑ x : ZMod q,
      ((1 : Character q) (x - 1) - (1 : Character q) x) * chi x) = -1 := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  simp_rw [principalCharacter_boundary hq]
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hzero : chi (0 : ZMod q) = 0 :=
    MulChar.map_nonunit chi not_isUnit_zero
  simp [hzero]

set_option maxHeartbeats 800000 in
/-- Index-two endpoint reduction.  The hypothesis is precisely the
off-resonance condition. -/
theorem indexTwoFlux_endpointReduction
    {q : ℕ} [NeZero q] [Fact q.Prime] (hq : q.Prime) (chi : Character q)
    (hoff : complexQuadraticCharacter q * chi ≠ 1) :
    indexTwoFlux chi = (1 / 2 : ℂ) * (shiftedQuadraticJacobi chi - 1) := by
  classical
  unfold indexTwoFlux indexTwoBoundary indexTwoIndicator
  have hprincipal := principalBoundary_flux hq chi
  have hquadraticProduct :
      (∑ x : ZMod q,
        complexQuadraticCharacter q x * chi x) = 0 := by
    calc
      (∑ x : ZMod q, complexQuadraticCharacter q x * chi x) =
          ∑ x : ZMod q, (complexQuadraticCharacter q * chi) x := by
            apply Finset.sum_congr rfl
            intro x _
            rfl
      _ = 0 := MulChar.sum_eq_zero_of_ne_one hoff
  have hshift :
      (∑ x : ZMod q,
        complexQuadraticCharacter q (x - 1) * chi x) =
        shiftedQuadraticJacobi chi := by
    unfold shiftedQuadraticJacobi
    let shift : ZMod q ≃ ZMod q := Equiv.addRight (1 : ZMod q)
    simpa [shift, sub_eq_add_neg, add_assoc] using
      (Equiv.sum_comp shift
        (fun x : ZMod q =>
          complexQuadraticCharacter q (x - 1) * chi x)).symm
  have hquadraticBoundary :
      (∑ x : ZMod q,
        (complexQuadraticCharacter q (x - 1) -
          complexQuadraticCharacter q x) * chi x) =
        shiftedQuadraticJacobi chi := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [hshift, hquadraticProduct, sub_zero]
  calc
    (∑ x : ZMod q,
      (1 / 2 * ((1 : Character q) (x - 1) +
          complexQuadraticCharacter q (x - 1)) -
        1 / 2 * ((1 : Character q) x + complexQuadraticCharacter q x)) * chi x) =
        (1 / 2 : ℂ) *
          ((∑ x : ZMod q,
              ((1 : Character q) (x - 1) - (1 : Character q) x) * chi x) +
            ∑ x : ZMod q,
              (complexQuadraticCharacter q (x - 1) -
                complexQuadraticCharacter q x) * chi x) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = _ := by rw [hprincipal, hquadraticBoundary]; ring

/-- The complex quadratic character is nonprincipal at an odd prime. -/
theorem complexQuadraticCharacter_ne_one
    {q : ℕ} [NeZero q] [Fact q.Prime] (_hq : q.Prime) (hqodd : q ≠ 2) :
    complexQuadraticCharacter q ≠ 1 := by
  apply (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℂ))).2
  exact quadraticChar_ne_one ((ringChar_zmod_n q).substr hqodd)

/-- The complex quadratic character is its own inverse. -/
theorem complexQuadraticCharacter_inv
    {q : ℕ} [NeZero q] [Fact q.Prime] (_hq : q.Prime) :
    (complexQuadraticCharacter q)⁻¹ = complexQuadraticCharacter q := by
  exact ((quadraticChar_isQuadratic (F := ZMod q)).comp
    (Int.castRingHom ℂ)).inv

/-- The shifted convention differs from the standard Jacobi sum only by the
quadratic value at `-1`. -/
theorem shiftedQuadraticJacobi_eq_standard
    {q : ℕ} [NeZero q] [Fact q.Prime] (chi : Character q) :
    shiftedQuadraticJacobi chi =
      complexQuadraticCharacter q (-1) *
        jacobiSum (complexQuadraticCharacter q) chi := by
  classical
  unfold shiftedQuadraticJacobi jacobiSum
  let negation : ZMod q ≃ ZMod q := Equiv.neg (ZMod q)
  calc
    (∑ y : ZMod q, complexQuadraticCharacter q y * chi (y + 1)) =
        ∑ t : ZMod q,
          complexQuadraticCharacter q (-t) * chi (-t + 1) := by
            simpa [negation] using
              (Equiv.sum_comp negation
                (fun y : ZMod q =>
                  complexQuadraticCharacter q y * chi (y + 1))).symm
    _ = ∑ t : ZMod q,
        complexQuadraticCharacter q (-1) *
          (complexQuadraticCharacter q t * chi (1 - t)) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [show -t = (-1 : ZMod q) * t by ring, map_mul]
          ring_nf
    _ = _ := by rw [Finset.mul_sum]

/-- Standard Jacobi sums in the off-resonance family have squared norm `q`. -/
theorem standardQuadraticJacobi_normSq
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) (chi : Character q)
    (hchi : chi ≠ 1) (hoff : complexQuadraticCharacter q * chi ≠ 1) :
    ‖jacobiSum (complexQuadraticCharacter q) chi‖ ^ 2 = (q : ℝ) := by
  classical
  let psi := complexQuadraticCharacter q
  have hpsi : psi ≠ 1 := complexQuadraticCharacter_ne_one hq hqodd
  have hchar : ringChar ℂ ≠ ringChar (ZMod q) := by
    rw [ringChar.eq_zero, ringChar_zmod_n]
    exact hq.ne_zero.symm
  have hproduct := jacobiSum_mul_jacobiSum_inv
    (F := ZMod q) (F' := ℂ) hchar hpsi hchi hoff
  have hstar :
      (starRingEnd ℂ) (jacobiSum psi chi) = jacobiSum psi⁻¹ chi⁻¹ := by
    unfold jacobiSum
    rw [map_sum (starRingEnd ℂ)]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_mul]
    change star (psi x) * star (chi (1 - x)) = _
    rw [MulChar.star_apply', MulChar.star_apply']
  rw [Complex.sq_norm]
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  change (starRingEnd ℂ) (jacobiSum psi chi) * jacobiSum psi chi = (q : ℂ)
  rw [hstar, mul_comm, hproduct, ZMod.card]

/-- The shifted Jacobi sums in the off-resonance family also have squared
norm `q`. -/
theorem shiftedQuadraticJacobi_normSq
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) (chi : Character q)
    (hchi : chi ≠ 1) (hoff : complexQuadraticCharacter q * chi ≠ 1) :
    ‖shiftedQuadraticJacobi chi‖ ^ 2 = (q : ℝ) := by
  rw [shiftedQuadraticJacobi_eq_standard]
  have hquad := (quadraticChar_isQuadratic (F := ZMod q)).comp
    (Int.castRingHom ℂ)
  have hnegunit : IsUnit (-1 : ZMod q) := isUnit_neg_one
  have hvalue : ‖complexQuadraticCharacter q (-1)‖ = 1 := by
    change ‖((quadraticChar (ZMod q)).ringHomComp
      (Int.castRingHom ℂ)) (-1)‖ = 1
    rcases hquad (-1 : ZMod q) with hzero | hone | hneg
    · have hnz : ((quadraticChar (ZMod q)).ringHomComp
          (Int.castRingHom ℂ)) (-1) ≠ 0 :=
        MulChar.apply_ne_zero_iff.mpr hnegunit
      exact (hnz hzero).elim
    · rw [hone]; norm_num
    · rw [hneg]; norm_num
  rw [norm_mul, hvalue, one_mul,
    standardQuadraticJacobi_normSq hq hqodd chi hchi hoff]

/-- The shifted quadratic self-correlation is exactly `-1`. -/
theorem shiftedQuadraticJacobi_self
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    shiftedQuadraticJacobi (complexQuadraticCharacter q) = -1 := by
  let psi := complexQuadraticCharacter q
  have hpsi : psi ≠ 1 := complexQuadraticCharacter_ne_one hq hqodd
  have hinv : psi⁻¹ = psi := complexQuadraticCharacter_inv hq
  rw [shiftedQuadraticJacobi_eq_standard]
  change psi (-1) * jacobiSum psi psi = -1
  rw [show jacobiSum psi psi = jacobiSum psi psi⁻¹ by rw [hinv],
    jacobiSum_nontrivial_inv hpsi]
  have hquad := (quadraticChar_isQuadratic (F := ZMod q)).comp
    (Int.castRingHom ℂ)
  have hsquare : psi (-1) ^ 2 = 1 := by
    change (((quadraticChar (ZMod q)).ringHomComp
      (Int.castRingHom ℂ)) (-1)) ^ 2 = 1
    rcases hquad (-1 : ZMod q) with hzero | hone | hneg
    · have hnz : psi (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
      exact (hnz hzero).elim
    · rw [hone]; ring
    · rw [hneg]; ring
  calc
    psi (-1) * -psi (-1) = -(psi (-1) ^ 2) := by ring
    _ = -1 := by rw [hsquare]

/-- The odd-character sum at a residue is supported only at `1` and `-1`. -/
theorem oddCharacterSum_eq
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (_hqodd : q ≠ 2) (z : ZMod q) :
    (∑ chi : Character q with chi.Odd, chi z) =
      ((q - 1 : ℕ) : ℂ) / 2 *
        ((if z = 1 then 1 else 0) - (if z = -1 then 1 else 0)) := by
  classical
  by_cases hz : z = 0
  · subst z
    have hzero (chi : Character q) : chi (0 : ZMod q) = 0 :=
      MulChar.map_nonunit chi not_isUnit_zero
    simp_rw [hzero]
    have hneone : (0 : ZMod q) ≠ 1 := zero_ne_one
    have hneneg : (0 : ZMod q) ≠ -1 := by
      intro h
      exact one_ne_zero (neg_eq_zero.mp h.symm)
    simp [hneone, hneneg]
  · let u : UnitClass q := (isUnit_iff_ne_zero.mpr hz).unit
    have huval : (u : ZMod q) = z := IsUnit.unit_spec _
    have huone : u = 1 ↔ z = 1 := by
      constructor
      · intro h
        simpa [h] using huval.symm
      · intro h
        apply Units.ext
        simpa [h] using huval
    have hunegone : -u = 1 ↔ z = -1 := by
      constructor
      · intro h
        have hval := congrArg ((↑) : UnitClass q → ZMod q) h
        rw [Units.val_neg, huval, Units.val_one] at hval
        exact neg_eq_iff_eq_neg.mp hval
      · intro h
        apply Units.ext
        rw [Units.val_neg, Units.val_one, huval, h, neg_neg]
    calc
      (∑ chi : Character q with chi.Odd, chi z) =
          oddCharacterKernel u (1 : UnitClass q) := by
            unfold oddCharacterKernel
            apply Finset.sum_congr rfl
            intro chi _
            rw [huval]
            simp
      _ = (1 / 2 : ℂ) * (q.totient : ℂ) *
          ((if u = 1 then 1 else 0) - (if -u = 1 then 1 else 0)) :=
            oddCharacterKernel_eq u 1
      _ = _ := by
        rw [Nat.totient_prime hq]
        simp only [huone, hunegone]
        ring

/-- Sum of the shifted Jacobi family over all odd characters. -/
theorem allOdd_shiftedJacobi_sum
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    (∑ chi : Character q with chi.Odd, shiftedQuadraticJacobi chi) =
      -(((q - 1 : ℕ) : ℂ) / 2) *
        complexQuadraticCharacter q (-2) := by
  classical
  unfold shiftedQuadraticJacobi
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, oddCharacterSum_eq hq hqodd]
  have hplus (y : ZMod q) : y + 1 = 1 ↔ y = 0 := by
    constructor <;> intro h
    · linear_combination h
    · rw [h, zero_add]
  have hminus (y : ZMod q) : y + 1 = -1 ↔ y = -2 := by
    constructor <;> intro h
    · linear_combination h
    · rw [h]
      ring
  simp_rw [hplus, hminus]
  have hzero : complexQuadraticCharacter q (0 : ZMod q) = 0 :=
    MulChar.map_nonunit _ not_isUnit_zero
  calc
    (∑ x : ZMod q,
      complexQuadraticCharacter q x *
        (((q - 1 : ℕ) : ℂ) / 2 *
          ((if x = 0 then 1 else 0) - (if x = -2 then 1 else 0)))) =
      (((q - 1 : ℕ) : ℂ) / 2) *
        ∑ x : ZMod q, complexQuadraticCharacter q x *
          ((if x = 0 then 1 else 0) - (if x = -2 then 1 else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = _ := by
      simp_rw [mul_sub, mul_ite, mul_one, mul_zero,
        Finset.sum_sub_distrib]
      simp [hzero]

/-- Off resonance is equivalent to excluding the quadratic character. -/
theorem quadratic_mul_ne_one_iff
    {q : ℕ} [NeZero q] [Fact q.Prime] (hq : q.Prime) (chi : Character q) :
    complexQuadraticCharacter q * chi ≠ 1 ↔
      chi ≠ complexQuadraticCharacter q := by
  constructor
  · intro h hchi
    apply h
    have hsq : complexQuadraticCharacter q ^ 2 = 1 :=
      ((quadraticChar_isQuadratic (F := ZMod q)).comp
        (Int.castRingHom ℂ)).sq_eq_one
    rw [hchi, ← pow_two, hsq]
  · intro h hprod
    apply h
    have hinv : chi = (complexQuadraticCharacter q)⁻¹ := by
      calc
        chi = 1 * chi := by rw [one_mul]
        _ = ((complexQuadraticCharacter q)⁻¹ *
              complexQuadraticCharacter q) * chi := by rw [inv_mul_cancel]
        _ = (complexQuadraticCharacter q)⁻¹ *
              (complexQuadraticCharacter q * chi) := mul_assoc _ _ _
        _ = (complexQuadraticCharacter q)⁻¹ := by rw [hprod, mul_one]
    rw [hinv, complexQuadraticCharacter_inv hq]

/-- The complete finite family of odd characters. -/
noncomputable def oddCharacters
    (q : ℕ) : Finset (Character q) := by
  classical
  exact Finset.univ.filter DirichletCharacter.Odd

/-- Off-resonance odd characters. -/
noncomputable def offResonanceOddCharacters
    (q : ℕ) [Fact q.Prime] : Finset (Character q) := by
  classical
  exact Finset.univ.filter fun chi =>
    chi.Odd ∧ complexQuadraticCharacter q * chi ≠ 1

/-- Off resonance removes exactly the quadratic character from the odd
family.  If the quadratic character is even, the erase changes nothing. -/
theorem offResonanceOddCharacters_eq_erase
    {q : ℕ} [NeZero q] [Fact q.Prime] (hq : q.Prime) :
    offResonanceOddCharacters q =
      (oddCharacters q).erase (complexQuadraticCharacter q) := by
  classical
  ext chi
  simp [offResonanceOddCharacters, oddCharacters,
    quadratic_mul_ne_one_iff hq, and_comm]

/-- The real cardinality of the complete odd family. -/
theorem oddCharacters_card_cast
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    ((oddCharacters q).card : ℝ) = (q - 1 : ℝ) / 2 := by
  have hsum := oddCharacterSum_eq hq hqodd (1 : ZMod q)
  have hneg : (-1 : ZMod q) ≠ 1 := by
    intro h
    have htwo : (2 : ZMod q) = 0 := by
      calc
        (2 : ZMod q) = 1 - (-1) := by ring
        _ = 0 := by rw [h]; ring
    exact Ring.two_ne_zero ((ringChar_zmod_n q).substr hqodd) htwo
  have honeneg : (1 : ZMod q) ≠ -1 := hneg.symm
  have hcast : ((oddCharacters q).card : ℂ) =
      (((q - 1 : ℕ) : ℂ) / 2) := by
    calc
      ((oddCharacters q).card : ℂ) =
          ∑ chi : Character q with chi.Odd, chi (1 : ZMod q) := by
            unfold oddCharacters
            simp
      _ = (((q - 1 : ℕ) : ℂ) / 2) := by
            rw [hsum]
            simp [honeneg]
  have hre := congrArg Complex.re hcast
  norm_num at hre
  rw [Nat.cast_sub hq.one_le] at hre
  norm_num at hre ⊢
  exact hre

/-- The off-resonance shifted-Jacobi first moment. -/
noncomputable def offResonanceJacobiMoment
    (q : ℕ) [Fact q.Prime] : ℂ :=
  ∑ chi ∈ offResonanceOddCharacters q, shiftedQuadraticJacobi chi

/-- Exact first moment after removing the resonant quadratic character. -/
theorem offResonanceJacobiMoment_eq
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    offResonanceJacobiMoment q =
      -(((q - 1 : ℕ) : ℂ) / 2) *
          complexQuadraticCharacter q (-2) +
        if (complexQuadraticCharacter q).Odd then 1 else 0 := by
  classical
  rw [offResonanceJacobiMoment, offResonanceOddCharacters_eq_erase hq]
  have hall :
      (∑ chi ∈ oddCharacters q, shiftedQuadraticJacobi chi) =
        -(((q - 1 : ℕ) : ℂ) / 2) *
          complexQuadraticCharacter q (-2) := by
    simpa [oddCharacters] using allOdd_shiftedJacobi_sum hq hqodd
  by_cases hodd : (complexQuadraticCharacter q).Odd
  · have hmem : complexQuadraticCharacter q ∈ oddCharacters q := by
      simp [oddCharacters, hodd]
    have herase := Finset.sum_erase_add (oddCharacters q)
      shiftedQuadraticJacobi hmem
    rw [if_pos hodd]
    calc
      (∑ chi ∈ (oddCharacters q).erase (complexQuadraticCharacter q),
          shiftedQuadraticJacobi chi) =
          (∑ chi ∈ oddCharacters q, shiftedQuadraticJacobi chi) -
            shiftedQuadraticJacobi (complexQuadraticCharacter q) :=
              eq_sub_of_add_eq herase
      _ = _ := by rw [hall, shiftedQuadraticJacobi_self hq hqodd]; ring
  · have hnotmem : complexQuadraticCharacter q ∉ oddCharacters q := by
      simp [oddCharacters, hodd]
    rw [(Finset.erase_eq_self.mpr hnotmem), if_neg hodd, hall]
    ring

/-- The real cardinality of the off-resonance family. -/
theorem offResonanceOddCharacters_card_cast
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    ((offResonanceOddCharacters q).card : ℝ) =
      (q - 1 : ℝ) / 2 -
        if (complexQuadraticCharacter q).Odd then 1 else 0 := by
  classical
  rw [offResonanceOddCharacters_eq_erase hq]
  by_cases hodd : (complexQuadraticCharacter q).Odd
  · have hmem : complexQuadraticCharacter q ∈ oddCharacters q := by
      simp [oddCharacters, hodd]
    rw [if_pos hodd, Finset.card_erase_of_mem hmem]
    have hcard := oddCharacters_card_cast hq hqodd
    have hpositive : 1 ≤ (oddCharacters q).card :=
      Finset.one_le_card.mpr ⟨_, hmem⟩
    rw [Nat.cast_sub hpositive, hcard]
    ring
  · have hnotmem : complexQuadraticCharacter q ∉ oddCharacters q := by
      simp [oddCharacters, hodd]
    rw [Finset.erase_eq_self.mpr hnotmem, if_neg hodd,
      oddCharacters_card_cast hq hqodd]
    ring

/-- Exact off-resonance energy. -/
noncomputable def offResonanceEnergy
    (q : ℕ) [Fact q.Prime] : ℝ :=
  ∑ chi ∈ offResonanceOddCharacters q, ‖indexTwoFlux chi‖ ^ 2

/-- Endpoint reduction for every summand of the off-resonance energy. -/
theorem offResonanceFlux_eq
    {q : ℕ} [NeZero q] [Fact q.Prime] (hq : q.Prime)
    {chi : Character q} (hchi : chi ∈ offResonanceOddCharacters q) :
    indexTwoFlux chi = (1 / 2 : ℂ) * (shiftedQuadraticJacobi chi - 1) := by
  exact indexTwoFlux_endpointReduction hq chi (Finset.mem_filter.mp hchi).2.2

/-- Squared norm of the endpoint-reduced Jacobi term. -/
theorem halfJacobiMinusOne_normSq (z : ℂ) :
    ‖(1 / 2 : ℂ) * (z - 1)‖ ^ 2 =
      (1 / 4 : ℝ) * (‖z‖ ^ 2 - 2 * z.re + 1) := by
  rw [norm_mul]
  rw [mul_pow]
  norm_num
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply]
  norm_num
  ring

/-- Exact second-moment closure over the actual off-resonance family. -/
theorem offResonanceEnergy_secondMoment
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    offResonanceEnergy q = (1 / 4 : ℝ) *
      ((q + 1 : ℝ) * ((offResonanceOddCharacters q).card : ℝ) -
        2 * (offResonanceJacobiMoment q).re) := by
  classical
  unfold offResonanceEnergy
  have hterm (chi : Character q)
      (hchiMem : chi ∈ offResonanceOddCharacters q) :
      ‖indexTwoFlux chi‖ ^ 2 = (1 / 4 : ℝ) *
        ((q + 1 : ℝ) - 2 * (shiftedQuadraticJacobi chi).re) := by
    have hdata := (Finset.mem_filter.mp hchiMem).2
    have hchi : chi ≠ 1 := by
      intro h
      subst chi
      unfold DirichletCharacter.Odd at hdata
      rw [MulChar.one_apply isUnit_neg_one] at hdata
      norm_num at hdata
    rw [offResonanceFlux_eq hq hchiMem,
      halfJacobiMinusOne_normSq,
      shiftedQuadraticJacobi_normSq hq hqodd chi hchi hdata.2]
    ring
  apply Eq.trans (Finset.sum_congr rfl fun chi hchi => hterm chi hchi)
  unfold offResonanceJacobiMoment
  have hre :
      (∑ chi ∈ offResonanceOddCharacters q,
        (shiftedQuadraticJacobi chi).re) =
        (∑ chi ∈ offResonanceOddCharacters q,
          shiftedQuadraticJacobi chi).re := by
    exact (map_sum Complex.reCLM
      (fun chi => shiftedQuadraticJacobi chi)
      (offResonanceOddCharacters q)).symm
  rw [← hre]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Closed second moment after inserting the exact family size and first
moment. -/
theorem offResonanceEnergy_closed
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    offResonanceEnergy q = (1 / 4 : ℝ) *
      ((q + 1 : ℝ) *
          ((q - 1 : ℝ) / 2 -
            if (complexQuadraticCharacter q).Odd then 1 else 0) -
        2 * (-(q - 1 : ℝ) / 2 *
            (complexQuadraticCharacter q (-2)).re +
          if (complexQuadraticCharacter q).Odd then 1 else 0)) := by
  rw [offResonanceEnergy_secondMoment hq hqodd,
    offResonanceOddCharacters_card_cast hq hqodd]
  have hmoment := congrArg Complex.re
    (offResonanceJacobiMoment_eq hq hqodd)
  rw [Nat.cast_sub hq.one_le] at hmoment
  by_cases hodd : (complexQuadraticCharacter q).Odd
  · simp only [hodd, if_pos] at hmoment ⊢
    norm_num at hmoment
    rw [hmoment]
    ring
  · simp only [hodd] at hmoment ⊢
    norm_num at hmoment
    rw [hmoment]
    simp
    ring

/-- Parity of the quadratic character is exactly the prime's class modulo
four. -/
theorem complexQuadraticCharacter_odd_iff
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    (complexQuadraticCharacter q).Odd ↔ q % 4 = 3 := by
  have hmod2 : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hqodd)
  unfold DirichletCharacter.Odd complexQuadraticCharacter
  rw [MulChar.ringHomComp_apply,
    quadraticChar_neg_one ((ringChar_zmod_n q).substr hqodd),
    ZMod.card, χ₄_nat_eq_if_mod_four]
  norm_num [hmod2]
  have hmod4 : q % 4 < 4 := Nat.mod_lt q (by decide)
  have hpar : q % 4 % 2 = q % 2 := Nat.mod_mod_of_dvd q (by decide)
  omega

/-- The shifted boundary sees the supplementary quadratic value at `-2`. -/
theorem complexQuadraticCharacter_negTwo_re
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    (complexQuadraticCharacter q (-2)).re =
      if q % 8 = 1 ∨ q % 8 = 3 then 1 else -1 := by
  have hmod2 : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hqodd)
  unfold complexQuadraticCharacter
  rw [MulChar.ringHomComp_apply,
    quadraticChar_neg_two ((ringChar_zmod_n q).substr hqodd),
    ZMod.card, χ₈'_nat_eq_if_mod_eight]
  by_cases h : q % 8 = 1 ∨ q % 8 = 3 <;> simp [hmod2, h]

/-- The four polynomial branches, selected by the prime modulo eight. -/
noncomputable def indexTwoBranchEnergy (q : ℕ) : ℝ :=
  if q % 8 = 1 then ((q - 1 : ℝ) * (q + 3 : ℝ)) / 8
  else if q % 8 = 3 then ((q - 3 : ℝ) * (q + 3 : ℝ)) / 8
  else if q % 8 = 5 then ((q - 1 : ℝ) ^ 2) / 8
  else ((q - 5 : ℝ) * (q + 1 : ℝ)) / 8

/-- Algebraic closure of the second moment from its exact cardinality and
Jacobi first moment. -/
theorem offResonance_secondMoment_closure
    (q N : ℕ) [Fact q.Prime] (Sigma : ℝ)
    (henergy : offResonanceEnergy q =
      (1 / 4 : ℝ) * (((q + 1 : ℕ) : ℝ) * N - 2 * Sigma)) :
    offResonanceEnergy q =
      (1 / 4 : ℝ) * (((q + 1 : ℕ) : ℝ) * N - 2 * Sigma) :=
  henergy

/-- Arithmetic closure of the `q = 1 (mod 8)` branch. -/
theorem indexTwo_branch_one
    {q : ℕ} [Fact q.Prime]
    (hclosed : offResonanceEnergy q = (1 / 4 : ℝ) *
      ((q + 1 : ℝ) * ((q - 1 : ℝ) / 2) -
        2 * (-(q - 1 : ℝ) / 2))) :
    offResonanceEnergy q = ((q - 1 : ℝ) * (q + 3 : ℝ)) / 8 := by
  rw [hclosed]
  ring

/-- Arithmetic closure of the `q = 3 (mod 8)` branch. -/
theorem indexTwo_branch_three
    {q : ℕ} [Fact q.Prime]
    (hclosed : offResonanceEnergy q = (1 / 4 : ℝ) *
      ((q + 1 : ℝ) * ((q - 3 : ℝ) / 2) -
        2 * (-(q - 1 : ℝ) / 2 + 1))) :
    offResonanceEnergy q = ((q - 3 : ℝ) * (q + 3 : ℝ)) / 8 := by
  rw [hclosed]
  ring

/-- Arithmetic closure of the `q = 5 (mod 8)` branch. -/
theorem indexTwo_branch_five
    {q : ℕ} [Fact q.Prime]
    (hclosed : offResonanceEnergy q = (1 / 4 : ℝ) *
      ((q + 1 : ℝ) * ((q - 1 : ℝ) / 2) -
        2 * ((q - 1 : ℝ) / 2))) :
    offResonanceEnergy q = (q - 1 : ℝ) ^ 2 / 8 := by
  rw [hclosed]
  ring

/-- Arithmetic closure of the `q = 7 (mod 8)` branch. -/
theorem indexTwo_branch_seven
    {q : ℕ} [Fact q.Prime]
    (hclosed : offResonanceEnergy q = (1 / 4 : ℝ) *
      ((q + 1 : ℝ) * ((q - 3 : ℝ) / 2) -
        2 * ((q - 1 : ℝ) / 2 + 1))) :
    offResonanceEnergy q = ((q - 5 : ℝ) * (q + 1 : ℝ)) / 8 := by
  rw [hclosed]
  ring

/-- Index-two off-resonance law, with all four branches selected by `q mod 8`. -/
theorem indexTwo_offResonanceLaw
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) :
    offResonanceEnergy q = indexTwoBranchEnergy q := by
  have hclosed := offResonanceEnergy_closed hq hqodd
  have hodd := complexQuadraticCharacter_odd_iff hq hqodd
  have hnegTwo := complexQuadraticCharacter_negTwo_re hq hqodd
  have hmod2 : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hqodd)
  have hmod8 : q % 8 < 8 := Nat.mod_lt q (by decide)
  have hmod4 : q % 8 % 4 = q % 4 :=
    Nat.mod_mod_of_dvd q (by decide)
  have hparity : q % 8 % 2 = q % 2 :=
    Nat.mod_mod_of_dvd q (by decide)
  have hcases : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
    omega
  rcases hcases with h8 | h8 | h8 | h8
  · have h4 : q % 4 = 1 := by omega
    have heven : ¬(complexQuadraticCharacter q).Odd := by
      rw [hodd]
      omega
    have hvalue : (complexQuadraticCharacter q (-2)).re = 1 := by
      rw [hnegTwo]
      simp [h8]
    unfold indexTwoBranchEnergy
    simp [h8]
    rw [hclosed]
    simp [heven, hvalue]
    ring
  · have h4 : q % 4 = 3 := by omega
    have hoddpsi : (complexQuadraticCharacter q).Odd := hodd.mpr h4
    have hvalue : (complexQuadraticCharacter q (-2)).re = 1 := by
      rw [hnegTwo]
      simp [h8]
    unfold indexTwoBranchEnergy
    simp [h8]
    rw [hclosed]
    simp [hoddpsi, hvalue]
    ring
  · have h4 : q % 4 = 1 := by omega
    have heven : ¬(complexQuadraticCharacter q).Odd := by
      rw [hodd]
      omega
    have hvalue : (complexQuadraticCharacter q (-2)).re = -1 := by
      rw [hnegTwo]
      simp [h8]
    unfold indexTwoBranchEnergy
    simp [h8]
    rw [hclosed]
    simp [heven, hvalue]
    ring
  · have h4 : q % 4 = 3 := by omega
    have hoddpsi : (complexQuadraticCharacter q).Odd := hodd.mpr h4
    have hvalue : (complexQuadraticCharacter q (-2)).re = -1 := by
      rw [hnegTwo]
      simp [h8]
    unfold indexTwoBranchEnergy
    simp [h8]
    rw [hclosed]
    simp [hoddpsi, hvalue]
    ring

/-- The manuscript's prime-seven example has off-resonance energy `2`. -/
theorem indexTwo_primeSeven_energy :
    @offResonanceEnergy 7 ⟨by norm_num⟩ = 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [indexTwo_offResonanceLaw (q := 7) (by norm_num) (by norm_num)]
  norm_num [indexTwoBranchEnergy]

end

end NField.Alignment.IndexTwoOrbitEnergy
