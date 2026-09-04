/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorBoundaryLedger

/-!
# Exact-conductor boundary energy

This module gives the nonnegative conductor decomposition for an arbitrary
unit-visible boundary.  The energy at level `d` is defined in the ambient
character family by the exact equation `conductor = d`.  A finite equivalence
then identifies it with the primitive-character sum formed after pushing the
boundary down to level `d`.
-/

namespace NField.Alignment.ExactConductorEnergy

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.ConductorBoundaryLedger

variable {m : ℕ} [NeZero m]

/-- Squared odd boundary flux over every character at the ambient level. -/
noncomputable def fullOddBoundaryEnergy
    (μ : UnitClass m → ℂ) : ℝ := by
  classical
  exact ∑ χ : Character m with χ.Odd, ‖boundaryFlux μ χ‖ ^ 2

/-- The nonnegative boundary energy carried by characters of exact conductor
`d` inside the ambient level `m`. -/
noncomputable def exactConductorEnergy
    (d : ℕ) (μ : UnitClass m → ℂ) : ℝ := by
  classical
  exact ∑ χ : Character m with χ.Odd ∧ χ.conductor = d,
    ‖boundaryFlux μ χ‖ ^ 2

theorem exactConductorEnergy_nonneg
    (d : ℕ) (μ : UnitClass m → ℂ) :
    0 ≤ exactConductorEnergy d μ := by
  classical
  unfold exactConductorEnergy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Every odd ambient character occurs at exactly one divisor conductor. -/
theorem fullOddBoundaryEnergy_eq_sum_exactConductor
    (μ : UnitClass m → ℂ) :
    fullOddBoundaryEnergy μ =
      ∑ d ∈ m.divisors, exactConductorEnergy d μ := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  unfold fullOddBoundaryEnergy exactConductorEnergy
  rw [Finset.sum_filter]
  calc
    (∑ χ : Character m,
        if χ.Odd then ‖boundaryFlux μ χ‖ ^ 2 else 0) =
      ∑ χ : Character m, ∑ d ∈ m.divisors,
        if χ.Odd ∧ χ.conductor = d then
          ‖boundaryFlux μ χ‖ ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro χ _
            by_cases hodd : χ.Odd
            · rw [if_pos hodd]
              have hcdvd : χ.conductor ∣ m := χ.conductor_dvd_level
              have hcpos : 0 < χ.conductor := by
                exact Nat.pos_of_ne_zero (fun hzero =>
                  NeZero.ne m
                    (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp hzero))
              rw [Finset.sum_eq_single χ.conductor]
              · simp [hodd]
              · intro d hd hne
                simp [hne.symm]
              · intro hnot
                exact (hnot (Nat.mem_divisors.mpr ⟨hcdvd, hmpos.ne'⟩)).elim
            · rw [if_neg hodd]
              symm
              apply Finset.sum_eq_zero
              intro d _
              simp [hodd]
    _ = ∑ d ∈ m.divisors, ∑ χ : Character m,
        if χ.Odd ∧ χ.conductor = d then
          ‖boundaryFlux μ χ‖ ^ 2 else 0 := by
            rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_filter]

/-- Primitive odd characters at `d` are exactly the odd ambient characters of
conductor `d`. -/
noncomputable def primitiveSourceEquivExactConductor
    {d : ℕ} (hd : d ∣ m) (_hdpos : 0 < d) :
    {ψ : Character d // ψ.IsPrimitive ∧ ψ.Odd} ≃
      {χ : Character m // χ.Odd ∧ χ.conductor = d} := by
  letI : NeZero d := ⟨_hdpos.ne'⟩
  let lift : {ψ : Character d // ψ.IsPrimitive ∧ ψ.Odd} →
      {χ : Character m // χ.Odd ∧ χ.conductor = d} := fun ψ =>
    ⟨DirichletCharacter.changeLevel hd ψ.val,
      ⟨(changeLevel_odd_iff hd ψ.val).2 ψ.property.2,
        (ψ.val.conductor_changeLevel hd).trans ψ.property.1⟩⟩
  exact Equiv.ofBijective lift ⟨by
    intro ψ₁ ψ₂ heq
    apply Subtype.ext
    apply DirichletCharacter.changeLevel_injective hd
    exact congrArg Subtype.val heq, by
    intro χ
    have hfactor : χ.val.FactorsThrough d :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ.val hd).2
        (by rw [χ.property.2])
    obtain ⟨ψ, hψ, _⟩ := hfactor.existsUnique
    have hcond : ψ.conductor = d := by
      calc
        ψ.conductor =
            (DirichletCharacter.changeLevel hd ψ).conductor :=
          (ψ.conductor_changeLevel hd).symm
        _ = χ.val.conductor := congrArg DirichletCharacter.conductor hψ.symm
        _ = d := χ.property.2
    have hodd : ψ.Odd := by
      apply (changeLevel_odd_iff hd ψ).1
      rw [← hψ]
      exact χ.property.1
    refine ⟨⟨ψ, hcond, hodd⟩, ?_⟩
    apply Subtype.ext
    exact hψ.symm⟩

/-- The manuscript's primitive-source energy at a divisor level. -/
noncomputable def primitiveSourceEnergy
    {d : ℕ} (hd : d ∣ m) (_hdpos : 0 < d)
    (μ : UnitClass m → ℂ) : ℝ := by
  classical
  letI : NeZero d := ⟨_hdpos.ne'⟩
  exact ∑ ψ : Character d with ψ.IsPrimitive ∧ ψ.Odd,
    ‖∑ x : UnitClass m, μ x * ψ (pushdownUnit hd x).val‖ ^ 2

/-- Pushing the unit boundary down before pairing gives the same source flux
as pairing in the ambient unit group. -/
theorem boundaryFlux_unitPushdown
    {d : ℕ} [NeZero d] (hd : d ∣ m) (μ : UnitClass m → ℂ)
    (ψ : Character d) :
    boundaryFlux (unitPushdown hd μ) ψ =
      ∑ x : UnitClass m, μ x * ψ (pushdownUnit hd x).val := by
  classical
  unfold boundaryFlux unitPushdown
  calc
    (∑ r : UnitClass d,
        (∑ x : UnitClass m with pushdownUnit hd x = r, μ x) * ψ r.val) =
      ∑ r : UnitClass d, ∑ x : UnitClass m with pushdownUnit hd x = r,
        μ x * ψ (pushdownUnit hd x).val := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      exact Finset.sum_fiberwise Finset.univ (pushdownUnit hd)
        (fun x => μ x * ψ (pushdownUnit hd x).val)

/-- The real primitive-source energy is the real value of the existing
primitive odd boundary moment of the pushed-down chain. -/
theorem primitiveSourceEnergy_cast_eq_primitiveOddBoundaryMoment
    {d : ℕ} [NeZero d] (hd : d ∣ m) (hdpos : 0 < d)
    (μ : UnitClass m → ℂ) :
    ((primitiveSourceEnergy hd hdpos μ : ℝ) : ℂ) =
      primitiveOddBoundaryMoment (unitPushdown hd μ) := by
  classical
  unfold primitiveSourceEnergy primitiveOddBoundaryMoment
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [boundaryFlux_unitPushdown hd μ ψ]
  rw [← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]
  rfl

/-- The ambient exact-conductor energy is exactly the primitive-source sum
after pushdown.  This is the finite identification used to define `P_d`. -/
theorem exactConductorEnergy_eq_primitiveSourceEnergy
    {d : ℕ} (hd : d ∣ m) (hdpos : 0 < d)
    (μ : UnitClass m → ℂ) :
    exactConductorEnergy d μ = primitiveSourceEnergy hd hdpos μ := by
  classical
  letI : NeZero d := ⟨hdpos.ne'⟩
  let e := primitiveSourceEquivExactConductor (m := m) hd hdpos
  unfold exactConductorEnergy primitiveSourceEnergy
  calc
    (∑ χ : Character m with χ.Odd ∧ χ.conductor = d,
        ‖boundaryFlux μ χ‖ ^ 2) =
      ∑ χ : {χ : Character m // χ.Odd ∧ χ.conductor = d},
        ‖boundaryFlux μ χ.val‖ ^ 2 := by
          rw [← Finset.sum_subtype
            ((Finset.univ : Finset (Character m)).filter
              (fun χ => χ.Odd ∧ χ.conductor = d)) (by intro χ; simp)
            (fun χ => ‖boundaryFlux μ χ‖ ^ 2)]
    _ = ∑ ψ : {ψ : Character d // ψ.IsPrimitive ∧ ψ.Odd},
        ‖∑ x : UnitClass m,
          μ x * ψ.val (pushdownUnit hd x).val‖ ^ 2 := by
          symm
          apply Fintype.sum_equiv e
          intro ψ
          congr 2
          unfold boundaryFlux
          apply Finset.sum_congr rfl
          intro x _
          change μ x * ψ.val (pushdownUnit hd x).val =
            μ x * DirichletCharacter.changeLevel hd ψ.val x.val
          simp [liftedCharacter_apply_unit, pushdownUnit]
    _ = ∑ ψ : Character d with ψ.IsPrimitive ∧ ψ.Odd,
        ‖∑ x : UnitClass m,
          μ x * ψ (pushdownUnit hd x).val‖ ^ 2 := by
          rw [← Finset.sum_subtype
            ((Finset.univ : Finset (Character d)).filter
              (fun ψ => ψ.IsPrimitive ∧ ψ.Odd)) (by intro ψ; simp)
            (fun ψ =>
              ‖∑ x : UnitClass m,
                μ x * ψ (pushdownUnit hd x).val‖ ^ 2)]

/-- Energy outside the top conductor. -/
noncomputable def properConductorEnergy
    (μ : UnitClass m → ℂ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d => d ≠ m), exactConductorEnergy d μ

theorem fullOddBoundaryEnergy_eq_top_add_proper
    (μ : UnitClass m → ℂ) :
    fullOddBoundaryEnergy μ =
      exactConductorEnergy m μ + properConductorEnergy μ := by
  classical
  rw [fullOddBoundaryEnergy_eq_sum_exactConductor]
  unfold properConductorEnergy
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmem : m ∈ m.divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl m, hmpos.ne'⟩
  have hfilter : m.divisors.filter (fun d => d ≠ m) =
      m.divisors.erase m := by
    ext d
    simp [and_comm]
  rw [hfilter]
  exact (Finset.add_sum_erase m.divisors
    (fun d => exactConductorEnergy d μ) hmem).symm

/-- Top-conductor concentration is equivalent to the vanishing of every
proper exact-conductor energy. -/
theorem topConductorConcentration_iff
    (μ : UnitClass m → ℂ) :
    exactConductorEnergy m μ = fullOddBoundaryEnergy μ ↔
      ∀ d ∈ m.divisors, d ≠ m → exactConductorEnergy d μ = 0 := by
  classical
  rw [fullOddBoundaryEnergy_eq_top_add_proper]
  constructor
  · intro h d hd hne
    have hproper : properConductorEnergy μ = 0 := by linarith
    unfold properConductorEnergy at hproper
    have hdmem : d ∈ m.divisors.filter (fun e => e ≠ m) := by simp [hd, hne]
    have hle : exactConductorEnergy d μ ≤
        ∑ e ∈ m.divisors.filter (fun e => e ≠ m),
          exactConductorEnergy e μ :=
      Finset.single_le_sum
        (fun e he => exactConductorEnergy_nonneg e μ) hdmem
    have hnonneg := exactConductorEnergy_nonneg d μ
    rw [hproper] at hle
    linarith
  · intro h
    have hproper : properConductorEnergy μ = 0 := by
      unfold properConductorEnergy
      apply Finset.sum_eq_zero
      intro d hd
      have hd' := (Finset.mem_filter.mp hd)
      exact h d hd'.1 hd'.2
    rw [hproper, add_zero]

end NField.Alignment.ExactConductorEnergy
