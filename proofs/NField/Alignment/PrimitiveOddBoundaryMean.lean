/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

namespace NField.Alignment.PrimitiveOddBoundaryMean

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure

variable {m : ℕ} [NeZero m]

noncomputable def oddCharacterKernel
    (x y : UnitClass m) : ℂ :=
  by
    classical
    exact ∑ χ : Character m with χ.Odd, χ x.val * star (χ y.val)

theorem allCharacterKernel (x y : UnitClass m) :
    (∑ χ : Character m, χ x.val * star (χ y.val)) =
      if x = y then (m.totient : ℂ) else 0 := by
  calc
    (∑ χ : Character m, χ x.val * star (χ y.val)) =
        ∑ χ : Character m, star (χ y.val) * χ x.val := by
          apply Finset.sum_congr rfl
          intro χ _
          ring
    _ = if y = x then (m.totient : ℂ) else 0 :=
      unit_character_orthogonality y x
    _ = if x = y then (m.totient : ℂ) else 0 := by
      by_cases h : x = y
      · subst y
        simp
      · have hyx : y ≠ x := fun heq => h heq.symm
        simp [h, hyx]

theorem oddCharacterKernel_eq (x y : UnitClass m) :
    oddCharacterKernel x y =
      (1 / 2 : ℂ) * (m.totient : ℂ) *
        ((if x = y then 1 else 0) - (if -x = y then 1 else 0)) := by
  classical
  unfold oddCharacterKernel
  rw [Finset.sum_filter]
  have hproject (χ : Character m) :
      (if χ.Odd then χ x.val * star (χ y.val) else 0) =
        (1 / 2 : ℂ) *
          (χ x.val * star (χ y.val) -
            χ (-1 : ZMod m) * (χ x.val * star (χ y.val))) := by
    rcases χ.even_or_odd with heven | hodd
    · rw [if_neg heven.not_odd, heven]
      ring
    · rw [if_pos hodd, hodd]
      ring
  simp_rw [hproject]
  rw [← Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  have htwist :
      (∑ χ : Character m,
        χ (-1 : ZMod m) * (χ x.val * star (χ y.val))) =
        ∑ χ : Character m, χ (-x).val * star (χ y.val) := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [Units.val_neg]
    rw [show -x.val = (-1 : ZMod m) * x.val by ring]
    rw [map_mul]
    ring
  rw [allCharacterKernel x y, htwist, allCharacterKernel (-x) y]
  split_ifs <;> ring

theorem changeLevel_odd_iff
    {d M : ℕ} [NeZero M] (hd : d ∣ M) (χ : Character d) :
    (DirichletCharacter.changeLevel hd χ).Odd ↔ χ.Odd := by
  unfold DirichletCharacter.Odd
  have hmap : ZMod.unitsMap hd (-1 : (ZMod M)ˣ) =
      (-1 : (ZMod d)ˣ) := by
    apply Units.ext
    change ZMod.cast (-1 : ZMod M) = (-1 : ZMod d)
    rw [ZMod.cast_neg hd, ZMod.cast_one hd]
  have heval :
      (DirichletCharacter.changeLevel hd χ) (-1 : ZMod M) =
        χ (-1 : ZMod d) := by
    calc
      (DirichletCharacter.changeLevel hd χ) (-1 : ZMod M) =
          (((DirichletCharacter.changeLevel hd χ).toUnitHom
            (-1 : (ZMod M)ˣ) : (ℂ)ˣ) : ℂ) := by
              rw [MulChar.coe_toUnitHom]
              simp
      _ = ((χ.toUnitHom (-1 : (ZMod d)ˣ) : (ℂ)ˣ) : ℂ) := by
            rw [DirichletCharacter.changeLevel_toUnitHom]
            simp [hmap]
      _ = χ (-1 : ZMod d) := by
            rw [MulChar.coe_toUnitHom]
            simp
  rw [heval]

theorem primePower_previous_dvd
    {p N : ℕ} (hN : 1 ≤ N) : p ^ (N - 1) ∣ p ^ N :=
  pow_dvd_pow p (by omega)

theorem nonprimitive_iff_factorsThrough_previous
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (χ : Character (p ^ N)) :
    ¬χ.IsPrimitive ↔ χ.FactorsThrough (p ^ (N - 1)) := by
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  constructor
  · intro hnot
    obtain ⟨k, hk, hcond⟩ :=
      (Nat.dvd_prime_pow hp).mp χ.conductor_dvd_level
    have hkne : k ≠ N := by
      intro heq
      apply hnot
      unfold DirichletCharacter.IsPrimitive
      simpa [heq] using hcond
    have hkprev : k ≤ N - 1 := by omega
    have hdiv : χ.conductor ∣ p ^ (N - 1) := by
      rw [hcond]
      exact pow_dvd_pow p hkprev
    exact DirichletCharacter.FactorsThrough.mono χ
      χ.factorsThrough_conductor hdiv
      (primePower_previous_dvd (p := p) (N := N) (by omega))
  · intro hfactor hprimitive
    have hcdvd : χ.conductor ∣ p ^ (N - 1) :=
      DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hfactor
    have hlowerpos : 0 < p ^ (N - 1) := pow_pos hp.pos _
    have hle : χ.conductor ≤ p ^ (N - 1) :=
      Nat.le_of_dvd hlowerpos hcdvd
    unfold DirichletCharacter.IsPrimitive at hprimitive
    rw [hprimitive] at hle
    have hstrict : p ^ (N - 1) < p ^ N := by
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega

noncomputable def previousLevelCharacterEquiv
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N) :
    Character (p ^ (N - 1)) ≃
      {χ : Character (p ^ N) // ¬χ.IsPrimitive} := by
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let hd : p ^ (N - 1) ∣ p ^ N := primePower_previous_dvd (by omega)
  let liftCharacter : Character (p ^ (N - 1)) →
      {χ : Character (p ^ N) // ¬χ.IsPrimitive} := fun ψ =>
    ⟨DirichletCharacter.changeLevel hd ψ,
      (nonprimitive_iff_factorsThrough_previous hp hN _).2
        (DirichletCharacter.changeLevel_factorsThrough ψ hd)⟩
  exact Equiv.ofBijective liftCharacter ⟨by
    intro ψ₁ ψ₂ heq
    apply DirichletCharacter.changeLevel_injective hd
    exact congrArg Subtype.val heq, by
    intro χ
    have hfactor :=
      (nonprimitive_iff_factorsThrough_previous hp hN χ.val).1 χ.property
    obtain ⟨hd', ψ, hψ⟩ := hfactor
    refine ⟨ψ, ?_⟩
    apply Subtype.ext
    exact hψ.symm⟩

noncomputable def primitiveOddKernel
    (x y : UnitClass m) : ℂ := by
  classical
  exact ∑ χ : Character m with χ.IsPrimitive ∧ χ.Odd,
    χ x.val * star (χ y.val)

noncomputable def previousUnit
    {p N : ℕ} (hN : 1 ≤ N) (x : UnitClass (p ^ N)) :
    UnitClass (p ^ (N - 1)) :=
  ZMod.unitsMap (primePower_previous_dvd hN) x

noncomputable def nonprimitiveOddKernel
    (x y : UnitClass m) : ℂ := by
  classical
  exact ∑ χ : Character m with ¬χ.IsPrimitive ∧ χ.Odd,
    χ x.val * star (χ y.val)

theorem liftedCharacter_apply_unit
    {d M : ℕ} [NeZero M] (hd : d ∣ M)
    (ψ : Character d) (x : UnitClass M) :
    DirichletCharacter.changeLevel hd ψ x.val =
      ψ (ZMod.unitsMap hd x).val := by
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd x]
  rfl

omit [NeZero m] in
theorem oddKernel_split_primitive
    (x y : UnitClass m) :
    oddCharacterKernel x y = primitiveOddKernel x y +
      nonprimitiveOddKernel x y := by
  classical
  unfold oddCharacterKernel primitiveOddKernel nonprimitiveOddKernel
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hprim : χ.IsPrimitive <;> by_cases hodd : χ.Odd <;>
    simp [hprim, hodd]

theorem nonprimitiveOddKernel_eq_previous
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (x y : UnitClass (p ^ N)) :
    nonprimitiveOddKernel x y =
      oddCharacterKernel (previousUnit (by omega) x)
        (previousUnit (by omega) y) := by
  classical
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ (N - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let hd : p ^ (N - 1) ∣ p ^ N := primePower_previous_dvd (by omega)
  let e := previousLevelCharacterEquiv hp hN
  unfold nonprimitiveOddKernel
  calc
    (∑ χ : Character (p ^ N) with ¬χ.IsPrimitive ∧ χ.Odd,
        χ x.val * star (χ y.val)) =
      ∑ χ : {χ : Character (p ^ N) // ¬χ.IsPrimitive},
        if χ.val.Odd then χ.val x.val * star (χ.val y.val) else 0 := by
          rw [← Finset.sum_subtype
            ((Finset.univ : Finset (Character (p ^ N))).filter
              (fun χ => ¬χ.IsPrimitive)) (by intro χ; simp)
            (fun χ => if χ.Odd then χ x.val * star (χ y.val) else 0)]
          rw [Finset.sum_filter, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro χ _
          by_cases hnon : ¬χ.IsPrimitive <;> by_cases hodd : χ.Odd <;>
            simp [hnon, hodd]
    _ = ∑ ψ : Character (p ^ (N - 1)),
        if ψ.Odd then
          ψ (previousUnit (by omega) x).val *
            star (ψ (previousUnit (by omega) y).val)
        else 0 := by
          symm
          apply Fintype.sum_equiv e
          intro ψ
          have hodd : (e ψ).val.Odd ↔ ψ.Odd := by
            change (DirichletCharacter.changeLevel hd ψ).Odd ↔ ψ.Odd
            exact changeLevel_odd_iff hd ψ
          by_cases hψ : ψ.Odd
          · rw [if_pos hψ, if_pos (hodd.mpr hψ)]
            change _ =
              DirichletCharacter.changeLevel hd ψ x.val *
                star (DirichletCharacter.changeLevel hd ψ y.val)
            rw [liftedCharacter_apply_unit hd ψ x,
              liftedCharacter_apply_unit hd ψ y]
            simp only [previousUnit]
          · rw [if_neg hψ, if_neg (fun h => hψ (hodd.mp h))]
    _ = oddCharacterKernel (previousUnit (by omega) x)
        (previousUnit (by omega) y) := by
          unfold oddCharacterKernel
          rw [Finset.sum_filter]

theorem primitiveOddKernel_eq_difference
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (x y : UnitClass (p ^ N)) :
    primitiveOddKernel x y = oddCharacterKernel x y -
      oddCharacterKernel (previousUnit (by omega) x)
        (previousUnit (by omega) y) := by
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [oddKernel_split_primitive x y,
    nonprimitiveOddKernel_eq_previous hp hN x y]
  ring

/-- Title: `Primitive odd character kernel at a prime power`. -/
theorem primitiveOddKernel_eq_primePowerKernel
    {p N : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (x y : UnitClass (p ^ N)) :
    primitiveOddKernel x y =
      (1 / 2 : ℂ) * ((p ^ N).totient : ℂ) *
        ((if x = y then 1 else 0) - (if -x = y then 1 else 0)) -
      (1 / 2 : ℂ) * ((p ^ (N - 1)).totient : ℂ) *
        ((if previousUnit (by omega) x = previousUnit (by omega) y then 1 else 0) -
          (if -(previousUnit (by omega) x) = previousUnit (by omega) y then 1 else 0)) := by
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ (N - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [primitiveOddKernel_eq_difference hp hN x y,
    oddCharacterKernel_eq, oddCharacterKernel_eq]

noncomputable def boundaryFlux
    (μ : UnitClass m → ℂ) (χ : Character m) : ℂ :=
  ∑ x : UnitClass m, μ x * χ x.val

noncomputable def primitiveOddBoundaryMoment
    (μ : UnitClass m → ℂ) : ℂ := by
  classical
  exact ∑ χ : Character m with χ.IsPrimitive ∧ χ.Odd,
    star (boundaryFlux μ χ) * boundaryFlux μ χ

theorem primitiveOddBoundaryMoment_expand
    (μ : UnitClass m → ℂ) :
    primitiveOddBoundaryMoment μ =
      ∑ x : UnitClass m, ∑ y : UnitClass m,
        μ x * star (μ y) * primitiveOddKernel x y := by
  classical
  unfold primitiveOddBoundaryMoment boundaryFlux primitiveOddKernel
  rw [Finset.sum_filter]
  calc
    (∑ χ : Character m,
      if χ.IsPrimitive ∧ χ.Odd then
        star (∑ x : UnitClass m, μ x * χ x.val) *
          ∑ x : UnitClass m, μ x * χ x.val
      else 0) =
      ∑ χ : Character m, ∑ x : UnitClass m, ∑ y : UnitClass m,
        if χ.IsPrimitive ∧ χ.Odd then
          μ x * star (μ y) * (χ x.val * star (χ y.val))
        else 0 := by
          apply Finset.sum_congr rfl
          intro χ _
          by_cases hχ : χ.IsPrimitive ∧ χ.Odd
          · simp_rw [if_pos hχ]
            have hstar :
                star (∑ x : UnitClass m, μ x * χ x.val) =
                  ∑ x : UnitClass m, star (μ x * χ x.val) := by
              change (starRingEnd ℂ) (∑ x : UnitClass m, μ x * χ x.val) = _
              rw [map_sum]
              simp only [starRingEnd_apply]
            rw [hstar, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            simp_rw [star_mul]
            apply Finset.sum_congr rfl
            intro y _
            ring
          · simp [hχ]
    _ = ∑ x : UnitClass m, ∑ y : UnitClass m,
        ∑ χ : Character m,
          if χ.IsPrimitive ∧ χ.Odd then
            μ x * star (μ y) * (χ x.val * star (χ y.val))
          else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_comm]
    _ = ∑ x : UnitClass m, ∑ y : UnitClass m,
        μ x * star (μ y) *
          ∑ χ : Character m with χ.IsPrimitive ∧ χ.Odd,
            χ x.val * star (χ y.val) := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.mul_sum, Finset.sum_filter]

theorem diagonalBoundaryPairing
    (μ : UnitClass m → ℂ) :
    (∑ x : UnitClass m, ∑ y : UnitClass m,
      μ x * star (μ y) * (if x = y then 1 else 0)) =
      ∑ x : UnitClass m, μ x * star (μ x) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem antipodalBoundaryPairing
    (μ : UnitClass m → ℂ) :
    (∑ x : UnitClass m, ∑ y : UnitClass m,
      μ x * star (μ y) * (if -x = y then 1 else 0)) =
      ∑ x : UnitClass m, μ x * star (μ (-x)) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem fiberPairing_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ρ : ι → κ) (μ : ι → ℂ)
    (hbalance : ∀ r : κ, ∑ x : ι with ρ x = r, μ x = 0) :
    (∑ x : ι, ∑ y : ι,
      μ x * star (μ y) * (if ρ x = ρ y then 1 else 0)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  have hstar :
      star (∑ y : ι with ρ y = ρ x, μ y) =
        ∑ y : ι with ρ y = ρ x, star (μ y) := by
    change (starRingEnd ℂ) (∑ y : ι with ρ y = ρ x, μ y) = _
    rw [map_sum]
    rfl
  calc
    (∑ y : ι, μ x * star (μ y) * (if ρ x = ρ y then 1 else 0)) =
        μ x * star (∑ y : ι with ρ y = ρ x, μ y) := by
          rw [hstar]
          rw [Finset.mul_sum]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hxy : ρ x = ρ y
          · have hyx : ρ y = ρ x := hxy.symm
            rw [if_pos hxy, if_pos hyx]
            ring
          · have hyx : ¬ρ y = ρ x := fun h => hxy h.symm
            rw [if_neg hxy, if_neg hyx]
            ring
    _ = 0 := by rw [hbalance]; simp

theorem antipodalFiberPairing_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Neg κ]
    (ρ : ι → κ) (μ : ι → ℂ)
    (hbalance : ∀ r : κ, ∑ x : ι with ρ x = r, μ x = 0) :
    (∑ x : ι, ∑ y : ι,
      μ x * star (μ y) * (if -(ρ x) = ρ y then 1 else 0)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  have hstar :
      star (∑ y : ι with ρ y = -(ρ x), μ y) =
        ∑ y : ι with ρ y = -(ρ x), star (μ y) := by
    change (starRingEnd ℂ) (∑ y : ι with ρ y = -(ρ x), μ y) = _
    rw [map_sum]
    rfl
  calc
    (∑ y : ι, μ x * star (μ y) * (if -(ρ x) = ρ y then 1 else 0)) =
        μ x * star (∑ y : ι with ρ y = -(ρ x), μ y) := by
          rw [hstar]
          rw [Finset.mul_sum]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hxy : -(ρ x) = ρ y
          · have hyx : ρ y = -(ρ x) := hxy.symm
            rw [if_pos hxy, if_pos hyx]
            ring
          · have hyx : ¬ρ y = -(ρ x) := fun h => hxy h.symm
            rw [if_neg hxy, if_neg hyx]
            ring
    _ = 0 := by rw [hbalance]; simp

theorem doublePairing_distribute
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ℂ) (P Q R S : ι → ι → ℂ) (A B : ℂ) :
    (∑ x : ι, ∑ y : ι,
      c x y * (A * (P x y - Q x y) - B * (R x y - S x y))) =
      A * ((∑ x : ι, ∑ y : ι, c x y * P x y) -
        (∑ x : ι, ∑ y : ι, c x y * Q x y)) -
      B * ((∑ x : ι, ∑ y : ι, c x y * R x y) -
        (∑ x : ι, ∑ y : ι, c x y * S x y)) := by
  classical
  have hpull (K : ℂ) (T : ι → ι → ℂ) :
      (∑ x : ι, ∑ y : ι, K * (c x y * T x y)) =
        K * ∑ x : ι, ∑ y : ι, c x y * T x y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  calc
    (∑ x : ι, ∑ y : ι,
      c x y * (A * (P x y - Q x y) - B * (R x y - S x y))) =
      ∑ x : ι, ∑ y : ι,
        ((A * (c x y * P x y) - A * (c x y * Q x y)) -
          (B * (c x y * R x y) - B * (c x y * S x y))) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            ring
    _ = (∑ x : ι, ∑ y : ι, A * (c x y * P x y)) -
        (∑ x : ι, ∑ y : ι, A * (c x y * Q x y)) -
        ((∑ x : ι, ∑ y : ι, B * (c x y * R x y)) -
          (∑ x : ι, ∑ y : ι, B * (c x y * S x y))) := by
            simp_rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [hpull, hpull, hpull, hpull]
      ring

theorem boundaryMeanCriterion_complex
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hN : 2 ≤ N)
    (μ : UnitClass (p ^ N) → ℂ)
    (hbalance : ∀ r : UnitClass (p ^ (N - 1)),
      ∑ x : UnitClass (p ^ N) with previousUnit (by omega) x = r, μ x = 0)
    (hodd : ∀ x : UnitClass (p ^ N), μ (-x) = -μ x) :
    primitiveOddBoundaryMoment μ =
      ((p ^ N).totient : ℂ) *
        ∑ x : UnitClass (p ^ N), μ x * star (μ x) := by
  classical
  rw [primitiveOddBoundaryMoment_expand]
  simp_rw [primitiveOddKernel_eq_primePowerKernel hp hN]
  rw [doublePairing_distribute]
  rw [diagonalBoundaryPairing]
  rw [antipodalBoundaryPairing]
  have hanti :
      (∑ x : UnitClass (p ^ N), μ x * star (μ (-x))) =
        -∑ x : UnitClass (p ^ N), μ x * star (μ x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [hodd]
    rw [star_neg]
    ring
  rw [hanti]
  have hlowerDiagonal := fiberPairing_zero
    (previousUnit (p := p) (N := N) (by omega)) μ hbalance
  have hlowerAntipodal := antipodalFiberPairing_zero
    (previousUnit (p := p) (N := N) (by omega)) μ hbalance
  rw [hlowerDiagonal, hlowerAntipodal]
  ring

noncomputable def primitiveOddCharacterCount (m : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Character m)).filter
    (fun χ => χ.IsPrimitive ∧ χ.Odd)).card

omit [NeZero m] in
theorem character_mul_star_at_unit
    (χ : Character m) (x : UnitClass m) :
    χ x.val * star (χ x.val) = 1 := by
  have hstar : star (χ x.val) = χ (x⁻¹ : UnitClass m).val := by
    calc
      star (χ x.val) = ((χ : MulChar (ZMod m) ℂ)⁻¹) x.val :=
        MulChar.star_apply' (χ : MulChar (ZMod m) ℂ) x.val
      _ = χ (x⁻¹ : UnitClass m).val := by
        rw [MulChar.inv_apply, Ring.inverse_unit]
  rw [hstar]
  rw [← map_mul]
  have hprod : x.val * (x⁻¹ : UnitClass m).val = (1 : ZMod m) := by
    rw [← Units.val_mul]
    simp
  rw [hprod, map_one]

omit [NeZero m] in
theorem primitiveOddKernel_one_eq_count :
    primitiveOddKernel (1 : UnitClass m) (1 : UnitClass m) =
      (primitiveOddCharacterCount m : ℂ) := by
  classical
  unfold primitiveOddKernel primitiveOddCharacterCount
  rw [Finset.sum_filter]
  calc
    (∑ χ : Character m,
      if χ.IsPrimitive ∧ χ.Odd then
        χ (1 : UnitClass m).val * star (χ (1 : UnitClass m).val)
      else 0) =
      ∑ χ : Character m, if χ.IsPrimitive ∧ χ.Odd then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro χ _
        by_cases hχ : χ.IsPrimitive ∧ χ.Odd
        · rw [if_pos hχ, if_pos hχ, character_mul_star_at_unit]
        · simp [hχ]
    _ = (((Finset.univ : Finset (Character m)).filter
        (fun χ => χ.IsPrimitive ∧ χ.Odd)).card : ℂ) := by
          rw [Finset.cast_card]
          simp

theorem primitiveOddCharacterCount_primePower
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hpodd : p ≠ 2) (hN : 2 ≤ N) :
    (primitiveOddCharacterCount (p ^ N) : ℂ) =
      (1 / 2 : ℂ) *
        (((p ^ N).totient : ℂ) - ((p ^ (N - 1)).totient : ℂ)) := by
  have htop : 2 < p ^ N := by
    have hp2 := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hpow : p ≤ p ^ N := by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ N := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hlower : 2 < p ^ (N - 1) := by
    have hp2 := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hpow : p ≤ p ^ (N - 1) := by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ (N - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  letI : Fact (2 < p ^ N) := ⟨htop⟩
  letI : Fact (2 < p ^ (N - 1)) := ⟨hlower⟩
  have hnegTop : -(1 : UnitClass (p ^ N)) ≠ 1 := by
    intro h
    have hv := congrArg Units.val h
    exact ZMod.neg_one_ne_one (by simpa using hv)
  have hnegLower :
      -(previousUnit (p := p) (N := N) (by omega)
        (1 : UnitClass (p ^ N))) ≠
      previousUnit (p := p) (N := N) (by omega)
        (1 : UnitClass (p ^ N)) := by
    have hone : previousUnit (p := p) (N := N) (by omega)
        (1 : UnitClass (p ^ N)) = 1 := by
      apply Units.ext
      change ZMod.cast (1 : ZMod (p ^ N)) = (1 : ZMod (p ^ (N - 1)))
      rw [ZMod.cast_one (primePower_previous_dvd (p := p) (N := N) (by omega))]
    rw [hone]
    intro h
    have hv := congrArg Units.val h
    exact ZMod.neg_one_ne_one (by simpa using hv)
  rw [← primitiveOddKernel_one_eq_count]
  rw [primitiveOddKernel_eq_primePowerKernel hp hN]
  simp [hnegTop, hnegLower]
  ring

noncomputable def primitiveOddBoundaryMomentReal
    (μ : UnitClass m → ℂ) : ℝ := by
  classical
  exact ∑ χ : Character m with χ.IsPrimitive ∧ χ.Odd,
    ‖boundaryFlux μ χ‖ ^ 2

theorem boundaryMeanCriterion_real
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hN : 2 ≤ N)
    (μ : UnitClass (p ^ N) → ℂ)
    (hbalance : ∀ r : UnitClass (p ^ (N - 1)),
      ∑ x : UnitClass (p ^ N) with previousUnit (by omega) x = r, μ x = 0)
    (hodd : ∀ x : UnitClass (p ^ N), μ (-x) = -μ x) :
    primitiveOddBoundaryMomentReal μ =
      ((p ^ N).totient : ℝ) *
        ∑ x : UnitClass (p ^ N), ‖μ x‖ ^ 2 := by
  unfold primitiveOddBoundaryMomentReal
  simp_rw [Complex.sq_norm]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  have hmain := boundaryMeanCriterion_complex hp hN μ hbalance hodd
  simpa [primitiveOddBoundaryMoment,
    mul_comm] using hmain

theorem primitiveOddCharacterCount_primePower_real
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hpodd : p ≠ 2) (hN : 2 ≤ N) :
    (primitiveOddCharacterCount (p ^ N) : ℝ) =
      (1 / 2 : ℝ) *
        (((p ^ N).totient : ℝ) - ((p ^ (N - 1)).totient : ℝ)) := by
  apply Complex.ofReal_injective
  push_cast
  exact primitiveOddCharacterCount_primePower hp hpodd hN

theorem primitiveOdd_population_ratio
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hpodd : p ≠ 2) (hN : 2 ≤ N) :
    ((p ^ N).totient : ℝ) /
        (primitiveOddCharacterCount (p ^ N) : ℝ) =
      2 * (p : ℝ) / (p - 1) := by
  have hcount := primitiveOddCharacterCount_primePower_real hp hpodd hN
  have hNpos : 0 < N := by omega
  have hNprev : 0 < N - 1 := by omega
  rw [Nat.totient_prime_pow hp hNpos] at hcount ⊢
  rw [Nat.totient_prime_pow hp hNprev] at hcount
  have hsub : N - 1 - 1 = N - 2 := by omega
  rw [hsub] at hcount
  have hpow : p ^ (N - 1) = p ^ (N - 2) * p := by
    have heq : N - 1 = (N - 2) + 1 := by omega
    rw [heq, pow_succ]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  have hbase : (p ^ (N - 2) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero (N - 2) hp.ne_zero)
  rw [hpow] at hcount ⊢
  push_cast at hcount ⊢
  rw [Nat.cast_sub hp.one_le] at hcount ⊢
  rw [hcount]
  field_simp [hp1, hbase]

/-- Title: `Mean law under the boundary criterion`. -/
theorem boundaryMeanCriterion_average
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hpodd : p ≠ 2) (hN : 2 ≤ N)
    (μ : UnitClass (p ^ N) → ℂ)
    (hbalance : ∀ r : UnitClass (p ^ (N - 1)),
      ∑ x : UnitClass (p ^ N) with previousUnit (by omega) x = r, μ x = 0)
    (hodd : ∀ x : UnitClass (p ^ N), μ (-x) = -μ x) :
    primitiveOddBoundaryMomentReal μ /
        (primitiveOddCharacterCount (p ^ N) : ℝ) =
      (2 * (p : ℝ) / (p - 1)) *
        ∑ x : UnitClass (p ^ N), ‖μ x‖ ^ 2 := by
  rw [boundaryMeanCriterion_real hp hN μ hbalance hodd]
  rw [div_eq_mul_inv, mul_assoc]
  have hratio := primitiveOdd_population_ratio hp hpodd hN
  rw [div_eq_mul_inv] at hratio
  calc
    ((p ^ N).totient : ℝ) *
        ((∑ x : UnitClass (p ^ N), ‖μ x‖ ^ 2) *
          (primitiveOddCharacterCount (p ^ N) : ℝ)⁻¹) =
      (((p ^ N).totient : ℝ) *
        (primitiveOddCharacterCount (p ^ N) : ℝ)⁻¹) *
          ∑ x : UnitClass (p ^ N), ‖μ x‖ ^ 2 := by ring
    _ = _ := by rw [hratio]

end NField.Alignment.PrimitiveOddBoundaryMean
