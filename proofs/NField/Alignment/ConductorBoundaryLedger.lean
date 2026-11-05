/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveOddBoundaryMean
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace NField.Alignment.ConductorBoundaryLedger

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean

variable {m : ℕ} [NeZero m]

noncomputable def factoringCharacterEquiv {d m : ℕ} [NeZero m]
    (hd : d ∣ m) :
    Character d ≃ {χ : Character m // χ.FactorsThrough d} := by
  let liftCharacter : Character d →
      {χ : Character m // χ.FactorsThrough d} := fun ψ =>
    ⟨DirichletCharacter.changeLevel hd ψ,
      DirichletCharacter.changeLevel_factorsThrough ψ hd⟩
  exact Equiv.ofBijective liftCharacter ⟨by
    intro ψ₁ ψ₂ heq
    apply DirichletCharacter.changeLevel_injective hd
    exact congrArg Subtype.val heq, by
    intro χ
    obtain ⟨ψ, hψ, _⟩ := χ.property.existsUnique
    refine ⟨ψ, ?_⟩
    apply Subtype.ext
    exact hψ.symm⟩

noncomputable def factoringKernel (d : ℕ)
    (x y : UnitClass m) : ℂ := by
  classical
  exact ∑ χ : Character m with χ.FactorsThrough d,
    χ x.val * star (χ y.val)

noncomputable def conductorKernel (d : ℕ)
    (x y : UnitClass m) : ℂ := by
  classical
  exact ∑ χ : Character m with χ.conductor = d,
    χ x.val * star (χ y.val)

theorem conductor_factors_iff_dvd
    {d : ℕ} (hd : d ∣ m) (χ : Character m) :
    χ.FactorsThrough d ↔ χ.conductor ∣ d := by
  exact DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd

theorem factoringKernel_eq_sum_conductorKernel
    {n : ℕ} (hn : n ∣ m) (hnpos : 0 < n)
    (x y : UnitClass m) :
    factoringKernel n x y =
      ∑ d ∈ n.divisors, conductorKernel d x y := by
  classical
  unfold factoringKernel conductorKernel
  rw [Finset.sum_filter]
  calc
    (∑ χ : Character m,
      if χ.FactorsThrough n then χ x.val * star (χ y.val) else 0) =
      ∑ χ : Character m, ∑ d ∈ n.divisors,
        if χ.conductor = d then χ x.val * star (χ y.val) else 0 := by
          apply Finset.sum_congr rfl
          intro χ _
          by_cases hf : χ.FactorsThrough n
          · rw [if_pos hf]
            have hcdvd : χ.conductor ∣ n :=
              (conductor_factors_iff_dvd hn χ).mp hf
            have hcpos : 0 < χ.conductor := by
              exact Nat.pos_of_ne_zero (fun h =>
                NeZero.ne m (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp h))
            rw [Finset.sum_eq_single χ.conductor]
            · simp
            · intro d hdmem hdne
              simp [Ne.symm hdne]
            · intro hnot
              exact (hnot (Nat.mem_divisors.mpr ⟨hcdvd, hnpos.ne'⟩)).elim
          · rw [if_neg hf]
            symm
            apply Finset.sum_eq_zero
            intro d hdmem
            have hnot : χ.conductor ≠ d := by
              intro heq
              apply hf
              apply (conductor_factors_iff_dvd hn χ).mpr
              rw [heq]
              exact Nat.dvd_of_mem_divisors hdmem
            simp [hnot]
    _ = ∑ d ∈ n.divisors, ∑ χ : Character m,
        if χ.conductor = d then χ x.val * star (χ y.val) else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_filter]

theorem conductorKernel_moebius
    (x y : UnitClass m) :
    conductorKernel m x y =
      ∑ d ∈ m.divisors,
        (ArithmeticFunction.moebius (m / d) : ℂ) * factoringKernel d x y := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let f : ℕ → ℂ := fun n => if n ∣ m then conductorKernel n x y else 0
  let g : ℕ → ℂ := fun n => if n ∣ m then factoringKernel n x y else 0
  have hsum : ∀ n > 0, n ∣ m →
      (∑ d ∈ n.divisors, f d) = g n := by
    intro n hnpos hnm
    simp only [f, g, if_pos hnm]
    calc
      (∑ d ∈ n.divisors,
          if d ∣ m then conductorKernel d x y else 0) =
          ∑ d ∈ n.divisors, conductorKernel d x y := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [if_pos (dvd_trans (Nat.dvd_of_mem_divisors hd) hnm)]
      _ = factoringKernel n x y :=
        (factoringKernel_eq_sum_conductorKernel hnm hnpos x y).symm
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
      {n : ℕ | n ∣ m} (by
        intro a b hab hbm
        exact dvd_trans hab hbm)).mp hsum m hmpos (dvd_refl m)
  simp only [f, if_pos (dvd_refl m)] at hinv
  rw [← hinv]
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun a d => (ArithmeticFunction.moebius a : ℂ) * g d)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [show g d = factoringKernel d x y by
    simp [g, Nat.dvd_of_mem_divisors hd]]

noncomputable def pushdownUnit {d m : ℕ} (hd : d ∣ m)
    (x : UnitClass m) : UnitClass d :=
  ZMod.unitsMap hd x

theorem factoringKernel_eq_orthogonality
    {d : ℕ} (hd : d ∣ m) (hdpos : 0 < d)
    (x y : UnitClass m) :
    factoringKernel d x y =
      if pushdownUnit hd x = pushdownUnit hd y
      then (d.totient : ℂ) else 0 := by
  classical
  letI : NeZero d := ⟨hdpos.ne'⟩
  let e := factoringCharacterEquiv hd
  unfold factoringKernel
  calc
    (∑ χ : Character m with χ.FactorsThrough d,
        χ x.val * star (χ y.val)) =
      ∑ χ : {χ : Character m // χ.FactorsThrough d},
        χ.val x.val * star (χ.val y.val) := by
          rw [← Finset.sum_subtype
            ((Finset.univ : Finset (Character m)).filter
              (fun χ => χ.FactorsThrough d)) (by intro χ; simp)
            (fun χ => χ x.val * star (χ y.val))]
    _ = ∑ ψ : Character d,
        ψ (pushdownUnit hd x).val *
          star (ψ (pushdownUnit hd y).val) := by
          symm
          apply Fintype.sum_equiv e
          intro ψ
          change ψ (pushdownUnit hd x).val *
              star (ψ (pushdownUnit hd y).val) =
            DirichletCharacter.changeLevel hd ψ x.val *
              star (DirichletCharacter.changeLevel hd ψ y.val)
          rw [liftedCharacter_apply_unit hd ψ x,
            liftedCharacter_apply_unit hd ψ y]
          rfl
    _ = _ := allCharacterKernel _ _

noncomputable def primitiveKernel
    (x y : UnitClass m) : ℂ := by
  classical
  exact ∑ χ : Character m with χ.IsPrimitive,
    χ x.val * star (χ y.val)

omit [NeZero m] in
theorem primitiveKernel_eq_conductorKernel
    (x y : UnitClass m) :
    primitiveKernel x y = conductorKernel m x y := by
  classical
  unfold primitiveKernel conductorKernel
  simp only [DirichletCharacter.IsPrimitive]

theorem primitiveKernel_moebius
    (x y : UnitClass m) :
    primitiveKernel x y =
      ∑ d ∈ m.divisors,
        (ArithmeticFunction.moebius (m / d) : ℂ) * factoringKernel d x y := by
  rw [primitiveKernel_eq_conductorKernel, conductorKernel_moebius]

omit [NeZero m] in
theorem primitiveOddKernel_eq_oddProjection
    (x y : UnitClass m) :
    primitiveOddKernel x y =
      (1 / 2 : ℂ) * (primitiveKernel x y - primitiveKernel (-x) y) := by
  classical
  unfold primitiveOddKernel primitiveKernel
  simp_rw [Finset.sum_filter]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  have hneg : χ (-x).val = χ (-1 : ZMod m) * χ x.val := by
    rw [Units.val_neg]
    rw [show -x.val = (-1 : ZMod m) * x.val by ring]
    exact map_mul χ _ _
  rw [hneg]
  rcases χ.even_or_odd with heven | hodd
  · have hnotodd : ¬χ.Odd := by
      exact not_and.mp χ.not_even_and_odd heven
    rw [if_neg (fun h : χ.IsPrimitive ∧ χ.Odd => hnotodd h.2)]
    by_cases hp : χ.IsPrimitive
    · rw [if_pos hp, if_pos hp, heven]
      ring
    · simp [hp]
  · by_cases hp : χ.IsPrimitive
    · rw [if_pos ⟨hp, hodd⟩, if_pos hp, if_pos hp, hodd]
      ring
    · simp [hp]

theorem primitiveOddKernel_moebius
    (x y : UnitClass m) :
    primitiveOddKernel x y =
      (1 / 2 : ℂ) * ∑ d ∈ m.divisors,
        (ArithmeticFunction.moebius (m / d) : ℂ) *
          (factoringKernel d x y - factoringKernel d (-x) y) := by
  rw [primitiveOddKernel_eq_oddProjection,
    primitiveKernel_moebius, primitiveKernel_moebius]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

abbrev residueCongruent (d : ℕ) (x y : UnitClass m) : Prop :=
  x.val.val % d = y.val.val % d

theorem pushdownUnit_eq_iff_residueCongruent
    {d : ℕ} (hd : d ∣ m) (x y : UnitClass m) :
    pushdownUnit hd x = pushdownUnit hd y ↔
      residueCongruent d x y := by
  rw [Units.ext_iff]
  unfold pushdownUnit residueCongruent
  simp only [ZMod.unitsMap_val]
  calc
    ZMod.cast x.val = ZMod.cast y.val ↔
        ZMod.cast (x.val.val : ZMod m) =
          ZMod.cast (y.val.val : ZMod m) := by
            rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    _ ↔ ((x.val.val : ℕ) : ZMod d) =
        ((y.val.val : ℕ) : ZMod d) := by
          rw [ZMod.cast_natCast hd, ZMod.cast_natCast hd]
    _ ↔ _ := ZMod.natCast_eq_natCast_iff' _ _ _

theorem primitiveOddKernel_congruenceFormula
    (x y : UnitClass m) :
    primitiveOddKernel x y =
      (1 / 2 : ℂ) * ∑ d ∈ m.divisors,
        (ArithmeticFunction.moebius (m / d) : ℂ) * (d.totient : ℂ) *
          ((if residueCongruent d x y then 1 else 0) -
           (if residueCongruent d (-x) y then 1 else 0)) := by
  classical
  rw [primitiveOddKernel_moebius]
  congr 1
  apply Finset.sum_congr rfl
  intro d hdmem
  have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hdmem
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
  rw [factoringKernel_eq_orthogonality hdvd hdpos,
    factoringKernel_eq_orthogonality hdvd hdpos]
  simp only [pushdownUnit_eq_iff_residueCongruent]
  split_ifs <;> ring

noncomputable def unitPushdown
    {d : ℕ} (hd : d ∣ m) (μ : UnitClass m → ℂ)
    (r : UnitClass d) : ℂ :=
  ∑ x : UnitClass m with pushdownUnit hd x = r, μ x

theorem fiberPairing_eq_pushdown
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ρ : ι → κ) (μ : ι → ℂ) :
    (∑ x : ι, ∑ y : ι,
      μ x * star (μ y) * (if ρ x = ρ y then 1 else 0)) =
      ∑ r : κ,
        (∑ x : ι with ρ x = r, μ x) *
          star (∑ x : ι with ρ x = r, μ x) := by
  classical
  have hstar (r : κ) :
      star (∑ y : ι with ρ y = r, μ y) =
        ∑ y : ι with ρ y = r, star (μ y) := by
    change (starRingEnd ℂ) (∑ y : ι with ρ y = r, μ y) = _
    rw [map_sum]
    rfl
  calc
    (∑ x : ι, ∑ y : ι,
      μ x * star (μ y) * (if ρ x = ρ y then 1 else 0)) =
      ∑ x : ι, μ x * star (∑ y : ι with ρ y = ρ x, μ y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hstar, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hxy : ρ x = ρ y
        · have hyx : ρ y = ρ x := hxy.symm
          rw [if_pos hxy, if_pos hyx]
          ring
        · have hyx : ¬ρ y = ρ x := fun h => hxy h.symm
          rw [if_neg hxy, if_neg hyx]
          ring
    _ = ∑ r : κ, ∑ x : ι with ρ x = r,
        μ x * star (∑ y : ι with ρ y = r, μ y) := by
          symm
          calc
            (∑ r : κ, ∑ x : ι with ρ x = r,
                μ x * star (∑ y : ι with ρ y = r, μ y)) =
              ∑ r : κ, ∑ x : ι with ρ x = r,
                μ x * star (∑ y : ι with ρ y = ρ x, μ y) := by
                  apply Finset.sum_congr rfl
                  intro r _
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [(Finset.mem_filter.mp hx).2]
            _ = _ := Finset.sum_fiberwise Finset.univ ρ
              (fun x => μ x * star (∑ y : ι with ρ y = ρ x, μ y))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]

theorem antipodalFiberPairing_eq_pushdown
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Neg κ]
    (ρ : ι → κ) (μ : ι → ℂ) :
    (∑ x : ι, ∑ y : ι,
      μ x * star (μ y) * (if -(ρ x) = ρ y then 1 else 0)) =
      ∑ r : κ,
        (∑ x : ι with ρ x = r, μ x) *
          star (∑ x : ι with ρ x = -r, μ x) := by
  classical
  have hstar (r : κ) :
      star (∑ y : ι with ρ y = r, μ y) =
        ∑ y : ι with ρ y = r, star (μ y) := by
    change (starRingEnd ℂ) (∑ y : ι with ρ y = r, μ y) = _
    rw [map_sum]
    rfl
  calc
    (∑ x : ι, ∑ y : ι,
      μ x * star (μ y) * (if -(ρ x) = ρ y then 1 else 0)) =
      ∑ x : ι, μ x * star (∑ y : ι with ρ y = -(ρ x), μ y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hstar, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hxy : -(ρ x) = ρ y
        · have hyx : ρ y = -(ρ x) := hxy.symm
          rw [if_pos hxy, if_pos hyx]
          ring
        · have hyx : ¬ρ y = -(ρ x) := fun h => hxy h.symm
          rw [if_neg hxy, if_neg hyx]
          ring
    _ = ∑ r : κ, ∑ x : ι with ρ x = r,
        μ x * star (∑ y : ι with ρ y = -r, μ y) := by
          symm
          calc
            (∑ r : κ, ∑ x : ι with ρ x = r,
                μ x * star (∑ y : ι with ρ y = -r, μ y)) =
              ∑ r : κ, ∑ x : ι with ρ x = r,
                μ x * star (∑ y : ι with ρ y = -(ρ x), μ y) := by
                  apply Finset.sum_congr rfl
                  intro r _
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [(Finset.mem_filter.mp hx).2]
            _ = _ := Finset.sum_fiberwise Finset.univ ρ
              (fun x => μ x * star (∑ y : ι with ρ y = -(ρ x), μ y))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]

omit [NeZero m] in
theorem pushdownUnit_neg {d : ℕ} (hd : d ∣ m)
    (x : UnitClass m) :
  pushdownUnit hd (-x) = -pushdownUnit hd x := by
  apply Units.ext
  unfold pushdownUnit
  simp only [ZMod.unitsMap_val, Units.val_neg]
  exact ZMod.cast_neg hd x.val

noncomputable def conductorLedgerTerm
    (d : ℕ) (μ : UnitClass m → ℂ) : ℂ := by
  classical
  by_cases hd : d ∣ m
  · letI : NeZero d := ⟨by
      intro hzero
      subst d
      exact NeZero.ne m (Nat.eq_zero_of_zero_dvd hd)⟩
    exact (d.totient : ℂ) *
      ((∑ r : UnitClass d,
          unitPushdown hd μ r * star (unitPushdown hd μ r)) -
       (∑ r : UnitClass d,
          unitPushdown hd μ r * star (unitPushdown hd μ (-r))))
  · exact 0

theorem conductorLedgerTerm_eq_boundaryPairing
    {d : ℕ} (hd : d ∣ m) (hdpos : 0 < d)
    (μ : UnitClass m → ℂ) :
    conductorLedgerTerm d μ =
      ∑ x : UnitClass m, ∑ y : UnitClass m,
        μ x * star (μ y) *
          ((d.totient : ℂ) *
            ((if residueCongruent d x y then 1 else 0) -
             (if residueCongruent d (-x) y then 1 else 0))) := by
  classical
  letI : NeZero d := ⟨hdpos.ne'⟩
  simp only [← pushdownUnit_eq_iff_residueCongruent hd,
    pushdownUnit_neg hd]
  have hdistribute := doublePairing_distribute
    (fun x y : UnitClass m => μ x * star (μ y))
    (fun x y => if pushdownUnit hd x = pushdownUnit hd y then 1 else 0)
    (fun x y => if -pushdownUnit hd x = pushdownUnit hd y then 1 else 0)
    (fun _ _ => 0) (fun _ _ => 0) (d.totient : ℂ) 0
  have hpair :
      (∑ x : UnitClass m, ∑ y : UnitClass m,
        μ x * star (μ y) *
          ((d.totient : ℂ) *
            ((if pushdownUnit hd x = pushdownUnit hd y then 1 else 0) -
             (if -pushdownUnit hd x = pushdownUnit hd y then 1 else 0)))) =
      (d.totient : ℂ) *
        ((∑ x : UnitClass m, ∑ y : UnitClass m,
          μ x * star (μ y) *
            (if pushdownUnit hd x = pushdownUnit hd y then 1 else 0)) -
         (∑ x : UnitClass m, ∑ y : UnitClass m,
          μ x * star (μ y) *
            (if -pushdownUnit hd x = pushdownUnit hd y then 1 else 0))) := by
    simpa using hdistribute
  rw [hpair]
  rw [fiberPairing_eq_pushdown (pushdownUnit hd) μ,
    antipodalFiberPairing_eq_pushdown (pushdownUnit hd) μ]
  simp [conductorLedgerTerm, hd, unitPushdown]

theorem doublePairing_finset_sum_swap
    {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (c : ι → ι → ℂ)
    (A : κ → ι → ι → ℂ) (K : ℂ) :
    (∑ x : ι, ∑ y : ι, c x y * (K * ∑ d ∈ s, A d x y)) =
      K * ∑ d ∈ s, ∑ x : ι, ∑ y : ι, c x y * A d x y := by
  classical
  calc
    (∑ x : ι, ∑ y : ι, c x y * (K * ∑ d ∈ s, A d x y)) =
      ∑ x : ι, ∑ y : ι, ∑ d ∈ s, K * (c x y * A d x y) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ = ∑ x : ι, ∑ d ∈ s, ∑ y : ι,
        K * (c x y * A d x y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ d ∈ s, ∑ x : ι, ∑ y : ι,
        K * (c x y * A d x y) := by
          rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]

/-- Title: `Conductor decomposition of the primitive odd boundary moment`. -/
theorem primitiveOddBoundaryMoment_conductorLedger
    (μ : UnitClass m → ℂ) :
    primitiveOddBoundaryMoment μ =
      (1 / 2 : ℂ) * ∑ d ∈ m.divisors,
        (ArithmeticFunction.moebius (m / d) : ℂ) *
          conductorLedgerTerm d μ := by
  classical
  rw [primitiveOddBoundaryMoment_expand]
  simp_rw [primitiveOddKernel_congruenceFormula]
  rw [doublePairing_finset_sum_swap m.divisors
    (fun x y : UnitClass m => μ x * star (μ y))
    (fun d x y =>
      (ArithmeticFunction.moebius (m / d) : ℂ) * (d.totient : ℂ) *
        ((if residueCongruent d x y then 1 else 0) -
         (if residueCongruent d (-x) y then 1 else 0)))
    (1 / 2 : ℂ)]
  congr 1
  apply Finset.sum_congr rfl
  intro d hdmem
  have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hdmem
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
  rw [conductorLedgerTerm_eq_boundaryPairing hdvd hdpos μ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end NField.Alignment.ConductorBoundaryLedger
