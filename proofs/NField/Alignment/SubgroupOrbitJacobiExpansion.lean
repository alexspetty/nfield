/-
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePowerFullOrbitBoundary
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Subgroup-orbit Jacobi expansion

For a multiplicative subgroup of the unit group, quotient characters give the
exact indicator of the subgroup.  Taking its additive boundary and pairing
with a Dirichlet character yields the finite Jacobi-type expansion.
-/

namespace NField.Alignment.SubgroupOrbitJacobiExpansion

noncomputable section

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure

attribute [local instance] Fintype.ofFinite

local instance classicalPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Complete multiplicative character sum on a finite commutative group. -/
noncomputable def dualEvaluationSum
    (G : Type*) [CommGroup G] [Fintype G] (g : G) : ℂ := by
  classical
  letI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  exact ∑ χ : G →* ℂˣ, (χ g : ℂ)

/-- Finite sum over the character group of a quotient. -/
noncomputable def quotientDualSum
    {G : Type*} [CommGroup G] [Fintype G]
    (H : Subgroup G) (F : ((G ⧸ H) →* ℂˣ) → ℂ) : ℂ := by
  classical
  letI : Fintype ((G ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  exact ∑ ρ : (G ⧸ H) →* ℂˣ, F ρ

/-- Orthogonality of the complete dual of a finite commutative group. -/
theorem dualEvaluationSum_eq
    (G : Type*) [CommGroup G] [Fintype G] (g : G) :
    dualEvaluationSum G g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  letI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  by_cases hg : g = 1
  · subst g
    unfold dualEvaluationSum
    rw [if_pos rfl]
    simp only [map_one, Units.val_one, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.card_univ]
    exact_mod_cast (by
      simpa only [Nat.card_eq_fintype_card] using
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ)
  · obtain ⟨η, hη⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
    let shift : (G →* ℂˣ) ≃ (G →* ℂˣ) := Equiv.mulLeft η
    have hshift : dualEvaluationSum G g =
        ∑ χ : G →* ℂˣ, (((η * χ) g : ℂ)) := by
      unfold dualEvaluationSum
      symm
      exact Equiv.sum_comp shift (fun χ : G →* ℂˣ => (χ g : ℂ))
    have hscale :
        (∑ χ : G →* ℂˣ, (((η * χ) g : ℂ))) =
          (η g : ℂ) * dualEvaluationSum G g := by
      unfold dualEvaluationSum
      change (∑ χ : G →* ℂˣ,
        ((η g : ℂ) * (χ g : ℂ))) = _
      rw [Finset.mul_sum]
    have hzero : ((η g : ℂ) - 1) * dualEvaluationSum G g = 0 := by
      rw [sub_mul, one_mul, ← hscale, ← hshift]
      ring
    have hηc : (η g : ℂ) ≠ 1 := by
      intro h
      apply hη
      exact Units.ext h
    rw [if_neg hg]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hηc)

/-- Quotient-dual orthogonality is the exact indicator of a subgroup. -/
theorem subgroup_indicator_as_quotient_average
    {G : Type*} [CommGroup G] [Fintype G]
    (H : Subgroup G) (g : G) :
    (Nat.card (G ⧸ H) : ℂ)⁻¹ *
        quotientDualSum H
          (fun ρ => (ρ (QuotientGroup.mk' H g) : ℂ)) =
      if g ∈ H then 1 else 0 := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  rw [show quotientDualSum H
      (fun ρ => (ρ (QuotientGroup.mk' H g) : ℂ)) =
      dualEvaluationSum (G ⧸ H) (QuotientGroup.mk' H g) by
    rfl]
  rw [dualEvaluationSum_eq]
  by_cases hg : g ∈ H
  · have hq : QuotientGroup.mk' H g = 1 :=
      (QuotientGroup.eq_one_iff g).mpr hg
    rw [if_pos hq, if_pos hg]
    have hcard : (Nat.card (G ⧸ H) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    rw [Nat.card_eq_fintype_card]
    field_simp
  · have hq : QuotientGroup.mk' H g ≠ 1 := by
      intro hq
      exact hg ((QuotientGroup.eq_one_iff g).mp hq)
    rw [if_neg hq, if_neg hg]
    simp

variable {q : ℕ} [NeZero q]

/-- Lift a character of the quotient unit group to a Dirichlet character. -/
noncomputable def quotientDirichletCharacter
    (H : Subgroup (UnitClass q))
    (ρ : (UnitClass q ⧸ H) →* ℂˣ) : Character q :=
  MulChar.ofUnitHom (ρ.comp (QuotientGroup.mk' H))

/-- Indicator of a multiplicative subgroup, extended by zero to nonunits. -/
noncomputable def subgroupOrbitIndicator
    (H : Subgroup (UnitClass q)) (x : ZMod q) : ℂ := by
  classical
  exact if hx : IsUnit x then if hx.unit ∈ H then 1 else 0 else 0

/-- Additive signed boundary of the subgroup orbit. -/
noncomputable def subgroupOrbitBoundary
    (H : Subgroup (UnitClass q)) (x : ZMod q) : ℂ :=
  subgroupOrbitIndicator H (x - 1) - subgroupOrbitIndicator H x

/-- Boundary flux paired with a Dirichlet character. -/
noncomputable def subgroupOrbitFlux
    (H : Subgroup (UnitClass q)) (χ : Character q) : ℂ :=
  ∑ x : ZMod q, subgroupOrbitBoundary H x * χ x

/-- The shifted Jacobi-type sum used by the orbit formula. -/
noncomputable def shiftedJacobiSum
    (ρ χ : Character q) : ℂ :=
  ∑ y : ZMod q, ρ y * χ (y + 1)

/-- Quotient characters reproduce the orbit indicator on every residue,
including the nonunit endpoint. -/
theorem subgroupOrbitIndicator_eq_quotientAverage
    (H : Subgroup (UnitClass q)) (x : ZMod q) :
    subgroupOrbitIndicator H x =
      (Nat.card (UnitClass q ⧸ H) : ℂ)⁻¹ *
        quotientDualSum H
          (fun ρ => quotientDirichletCharacter H ρ x) := by
  classical
  letI : Fintype (UnitClass q ⧸ H) := Fintype.ofFinite _
  letI : NeZero (Monoid.exponent (UnitClass q ⧸ H)) :=
    @Monoid.neZero_exponent_of_finite (UnitClass q ⧸ H) _ _
  letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (UnitClass q ⧸ H)) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ _
  letI : Fintype ((UnitClass q ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  by_cases hx : IsUnit x
  · let u : UnitClass q := hx.unit
    have hxu : (u : ZMod q) = x := IsUnit.unit_spec hx
    have heval (rho : (UnitClass q ⧸ H) →* ℂˣ) :
        quotientDirichletCharacter H rho x =
          (rho (QuotientGroup.mk' H u) : ℂ) := by
      rw [← hxu]
      simp [quotientDirichletCharacter, MulChar.ofUnitHom_eq,
        MulChar.equivToUnitHom_symm_coe, MonoidHom.comp_apply]
    have havg := subgroup_indicator_as_quotient_average H u
    simp_rw [heval]
    simpa [subgroupOrbitIndicator, hx, u] using havg.symm
  · unfold subgroupOrbitIndicator
    rw [dif_neg hx]
    apply Eq.symm
    unfold quotientDualSum
    rw [Finset.sum_eq_zero]
    · simp
    · intro ρ _
      rw [MulChar.map_nonunit (quotientDirichletCharacter H ρ) hx]

/-- Product-character orthogonality over a prime field. -/
theorem productCharacterSum_eq
    (hq : q.Prime) (ρ χ : Character q) :
    (∑ x : ZMod q, ρ x * χ x) =
      if ρ * χ = 1 then (q - 1 : ℂ) else 0 := by
  classical
  calc
    (∑ x : ZMod q, ρ x * χ x) = ∑ x : ZMod q, (ρ * χ) x := by
      apply Finset.sum_congr rfl
      intro x _
      rfl
    _ = if ρ * χ = 1 then (q - 1 : ℂ) else 0 := by
      by_cases hprod : ρ * χ = 1
      · rw [if_pos hprod, hprod, MulChar.sum_one_eq_card_units]
        simp [Nat.totient_prime hq, Nat.cast_sub hq.one_le]
      · rw [if_neg hprod, MulChar.sum_eq_zero_of_ne_one hprod]

/-- Higher-index Jacobi expansion of a subgroup-orbit boundary flux. -/
theorem subgroupOrbitFlux_jacobiExpansion
    (hq : q.Prime) (H : Subgroup (UnitClass q)) (χ : Character q) :
    subgroupOrbitFlux H χ =
      (Nat.card (UnitClass q ⧸ H) : ℂ)⁻¹ *
        quotientDualSum H (fun ρ =>
          shiftedJacobiSum (quotientDirichletCharacter H ρ) χ -
            (q - 1 : ℂ) *
              if quotientDirichletCharacter H ρ * χ = 1 then 1 else 0) := by
  classical
  letI : Fintype (UnitClass q ⧸ H) := Fintype.ofFinite _
  letI : NeZero (Monoid.exponent (UnitClass q ⧸ H)) :=
    @Monoid.neZero_exponent_of_finite (UnitClass q ⧸ H) _ _
  letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (UnitClass q ⧸ H)) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ _
  letI : Fintype ((UnitClass q ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  unfold subgroupOrbitFlux subgroupOrbitBoundary shiftedJacobiSum quotientDualSum
  simp_rw [subgroupOrbitIndicator_eq_quotientAverage H]
  calc
    (∑ x : ZMod q,
        ((Nat.card (UnitClass q ⧸ H) : ℂ)⁻¹ *
              ∑ ρ : (UnitClass q ⧸ H) →* ℂˣ,
                quotientDirichletCharacter H ρ (x - 1) -
            (Nat.card (UnitClass q ⧸ H) : ℂ)⁻¹ *
              ∑ ρ : (UnitClass q ⧸ H) →* ℂˣ,
                quotientDirichletCharacter H ρ x) * χ x) =
      (Nat.card (UnitClass q ⧸ H) : ℂ)⁻¹ *
        ∑ ρ : (UnitClass q ⧸ H) →* ℂˣ,
          ((∑ x : ZMod q,
              quotientDirichletCharacter H ρ (x - 1) * χ x) -
            ∑ x : ZMod q,
              quotientDirichletCharacter H ρ x * χ x) := by
        simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
          Finset.sum_mul]
        congr 1 <;> rw [Finset.sum_comm] <;> simp [mul_assoc]
    _ = (Nat.card (UnitClass q ⧸ H) : ℂ)⁻¹ *
        ∑ ρ : (UnitClass q ⧸ H) →* ℂˣ,
          ((∑ y : ZMod q,
              quotientDirichletCharacter H ρ y * χ (y + 1)) -
            ∑ x : ZMod q,
              quotientDirichletCharacter H ρ x * χ x) := by
        congr 1
        apply Finset.sum_congr rfl
        intro ρ _
        congr 1
        let shift : ZMod q ≃ ZMod q := Equiv.addRight (1 : ZMod q)
        simpa [shift, sub_eq_add_neg, add_assoc] using
          (Equiv.sum_comp shift
            (fun y : ZMod q =>
              quotientDirichletCharacter H ρ (y - 1) * χ y)).symm
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ρ _
      rw [productCharacterSum_eq hq]
      by_cases hprod : quotientDirichletCharacter H ρ * χ = 1
      · rw [if_pos hprod, if_pos hprod]
        ring
      · rw [if_neg hprod, if_neg hprod]
        ring

end

end NField.Alignment.SubgroupOrbitJacobiExpansion
