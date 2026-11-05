/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthFactorization
import NField.Alignment.PrimitiveOddBoundaryMean

/-!
# Primitive sources of prime-power characters

Every odd character at a positive prime-power level has one positive
prime-power conductor and is the lift of a primitive odd character there.
The level-cast equivalence keeps this classification independent of dependent
type transports.
-/

namespace NField.Alignment.PrimePowerCharacterSources

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean

/-- Transport a character along equality of its levels. -/
noncomputable def characterLevelCast
    {m n : ℕ} (h : m = n) : Character m ≃ Character n :=
  Equiv.cast (congrArg Character h)

theorem characterLevelCast_isPrimitive
    {m n : ℕ} (h : m = n) (ψ : Character m) :
    (characterLevelCast h ψ).IsPrimitive ↔ ψ.IsPrimitive := by
  subst n
  rfl

theorem characterLevelCast_odd
    {m n : ℕ} (h : m = n) (ψ : Character m) :
    (characterLevelCast h ψ).Odd ↔ ψ.Odd := by
  subst n
  rfl

theorem changeLevel_characterLevelCast
    {d e M : ℕ} [NeZero M] (h : d = e)
    (hd : d ∣ M) (he : e ∣ M) (ψ : Character d) :
    DirichletCharacter.changeLevel he (characterLevelCast h ψ) =
      DirichletCharacter.changeLevel hd ψ := by
  subst e
  rfl

/-- An odd character at level p^N has a positive conductor p^t with t at most N. -/
theorem odd_conductor_prime_power
    {p N : ℕ} [NeZero (p ^ N)] (hp : p.Prime) (hN : 1 ≤ N)
    {χ : Character (p ^ N)} (hχ : χ.Odd) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ N ∧ χ.conductor = p ^ t := by
  obtain ⟨t, htN, hcond⟩ :=
    (Nat.dvd_prime_pow hp).mp χ.conductor_dvd_level
  have ht : 1 ≤ t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    have hc1 : χ.conductor = 1 := by simpa [ht0] using hcond
    have hone : χ = 1 :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hc1
    subst χ
    apply hχ.not_even
    have htop : 2 ≤ p ^ N := hp.two_le.trans (Nat.le_pow hN)
    letI : Fact (1 < p ^ N) := ⟨by omega⟩
    unfold DirichletCharacter.Even
    exact MulChar.one_apply isUnit_neg_one
  exact ⟨t, ht, htN, hcond⟩

/-- Title: `Primitive source of an odd character`.

Every odd prime-power character is induced from a primitive odd character at
one unique positive conductor level. This theorem supplies existence; source
uniqueness follows from invariance of the conductor under change of level. -/
theorem odd_character_has_primitive_source
    {p N : ℕ} [NeZero (p ^ N)] (hp : p.Prime) (hN : 1 ≤ N)
    {χ : Character (p ^ N)} (hχ : χ.Odd) :
    ∃ (t : ℕ) (ht : t ≤ N) (ψ : Character (p ^ t)),
      1 ≤ t ∧ ψ.IsPrimitive ∧ ψ.Odd ∧
        DirichletCharacter.changeLevel (pow_dvd_pow p ht) ψ = χ := by
  obtain ⟨t, ht1, htN, hcond⟩ :=
    odd_conductor_prime_power hp hN hχ
  let ψ : Character (p ^ t) :=
    characterLevelCast hcond χ.primitiveCharacter
  have hprim : ψ.IsPrimitive :=
    (characterLevelCast_isPrimitive hcond χ.primitiveCharacter).2
      χ.primitiveCharacter_isPrimitive
  have hlift :
      DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ = χ := by
    rw [changeLevel_characterLevelCast hcond
      χ.conductor_dvd_level (pow_dvd_pow p htN)]
    exact χ.changeLevel_primitiveCharacter
  have hodd : ψ.Odd :=
    (changeLevel_odd_iff (pow_dvd_pow p htN) ψ).mp (hlift ▸ hχ)
  exact ⟨t, htN, ψ, ht1, hprim, hodd, hlift⟩

/-- Two primitive source exponents inducing the same character are equal. -/
theorem primitive_source_exponent_unique
    {p N t u : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (ht : t ≤ N) (hu : u ≤ N)
    {ψ : Character (p ^ t)} {ξ : Character (p ^ u)}
    (hψ : ψ.IsPrimitive) (hξ : ξ.IsPrimitive)
    (heq :
      DirichletCharacter.changeLevel (pow_dvd_pow p ht) ψ =
        DirichletCharacter.changeLevel (pow_dvd_pow p hu) ξ) :
    t = u := by
  have hc :
      p ^ t = p ^ u := by
    calc
      p ^ t = ψ.conductor := hψ.symm
      _ = (DirichletCharacter.changeLevel (pow_dvd_pow p ht) ψ).conductor := by
        rw [DirichletCharacter.conductor_changeLevel]
      _ = (DirichletCharacter.changeLevel (pow_dvd_pow p hu) ξ).conductor := by
        rw [heq]
      _ = ξ.conductor := by
        rw [DirichletCharacter.conductor_changeLevel]
      _ = p ^ u := hξ
  exact (Nat.pow_right_injective hp.one_lt) hc

/-- A primitive odd source character together with its positive conductor exponent. -/
structure PrimitiveOddSource (p N : ℕ) where
  exponent : Fin (N + 1)
  positive : 1 ≤ exponent.val
  character : Character (p ^ exponent.val)
  primitive : character.IsPrimitive
  odd : character.Odd

noncomputable instance primitiveOddSourceFintype
    (p N : ℕ) : Fintype (PrimitiveOddSource p N) := by
  classical
  let f : PrimitiveOddSource p N →
      Σ t : Fin (N + 1), Character (p ^ t.val) :=
    fun source => ⟨source.exponent, source.character⟩
  apply Fintype.ofInjective f
  intro a b hab
  rcases a with ⟨ta, hta, ψ, hψp, hψo⟩
  rcases b with ⟨tb, htb, ξ, hξp, hξo⟩
  cases hab
  rfl

/-- Lift a primitive source character to the ambient prime-power level. -/
noncomputable def PrimitiveOddSource.lift
    {p N : ℕ} [NeZero (p ^ N)]
    (source : PrimitiveOddSource p N) : {χ : Character (p ^ N) // χ.Odd} :=
  ⟨DirichletCharacter.changeLevel
      (pow_dvd_pow p (by omega : source.exponent.val ≤ N)) source.character,
    (changeLevel_odd_iff
      (pow_dvd_pow p (by omega : source.exponent.val ≤ N))
      source.character).2 source.odd⟩

theorem primitiveOddSource_lift_injective
    {p N : ℕ} [NeZero (p ^ N)] (hp : p.Prime) :
    Function.Injective
      (PrimitiveOddSource.lift :
        PrimitiveOddSource p N → {χ : Character (p ^ N) // χ.Odd}) := by
  intro a b hab
  rcases a with ⟨ta, hta, ψ, hψp, hψo⟩
  rcases b with ⟨tb, htb, ξ, hξp, hξo⟩
  have heq :
      DirichletCharacter.changeLevel
          (pow_dvd_pow p (by omega : ta.val ≤ N)) ψ =
        DirichletCharacter.changeLevel
          (pow_dvd_pow p (by omega : tb.val ≤ N)) ξ := by
    exact congrArg Subtype.val hab
  have htu : ta.val = tb.val :=
    primitive_source_exponent_unique hp
      (by omega : ta.val ≤ N) (by omega : tb.val ≤ N) hψp hξp heq
  have ht : ta = tb := Fin.ext htu
  subst tb
  have hchar : ψ = ξ := by
    exact DirichletCharacter.changeLevel_injective
      (pow_dvd_pow p (by omega : ta.val ≤ N)) heq
  subst ξ
  rfl

theorem primitiveOddSource_lift_surjective
    {p N : ℕ} [NeZero (p ^ N)] (hp : p.Prime) (hN : 1 ≤ N) :
    Function.Surjective
      (PrimitiveOddSource.lift :
        PrimitiveOddSource p N → {χ : Character (p ^ N) // χ.Odd}) := by
  intro χ
  obtain ⟨t, htN, ψ, ht1, hprim, hodd, hlift⟩ :=
    odd_character_has_primitive_source hp hN χ.property
  let tf : Fin (N + 1) := ⟨t, by omega⟩
  let source : PrimitiveOddSource p N :=
    ⟨tf, ht1, ψ, hprim, hodd⟩
  refine ⟨source, ?_⟩
  apply Subtype.ext
  simpa [PrimitiveOddSource.lift, source, tf] using hlift

/-- Exact finite equivalence between positive primitive odd sources and ambient odd characters. -/
noncomputable def primitiveOddSourceEquiv
    {p N : ℕ} [NeZero (p ^ N)] (hp : p.Prime) (hN : 1 ≤ N) :
    PrimitiveOddSource p N ≃ {χ : Character (p ^ N) // χ.Odd} :=
  Equiv.ofBijective PrimitiveOddSource.lift
    ⟨primitiveOddSource_lift_injective hp,
      primitiveOddSource_lift_surjective hp hN⟩

end NField.Alignment.PrimePowerCharacterSources
