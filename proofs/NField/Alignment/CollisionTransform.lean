/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionInvariant

/-!
# The collision transform

Natural coarse-fiber centering, exact active-channel gates, Euler-product
bookkeeping, and zero-ledger algebra for the Lean companion to
"The Collision Transform".
-/

namespace NField.Alignment.CollisionTransform

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem

/-! ## The natural centered finite transform -/

/-- The manuscript's centered finite collision signal on the unit group
modulo `b^(ell+1)`. -/
noncomputable def centeredCollisionTransform (b ell : ℕ)
    [NeZero b] [NeZero (allLagModulus b ell)] :
    UnitClass (allLagModulus b ell) → ℂ :=
  centeredSignal (coarseUnitReduction b ell) (allLagUnitTable b ell)

/-- Natural reduction from the fine unit group to the base unit group
commutes with reflection. -/
theorem coarseUnitReduction_neg
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (a : UnitClass (allLagModulus b ell)) :
    coarseUnitReduction b ell (-a) = -coarseUnitReduction b ell a := by
  unfold coarseUnitReduction
  apply Units.ext
  rw [ZMod.unitsMap_val]
  change ((-(a : ZMod (allLagModulus b ell))).cast : ZMod b) =
    -((a : ZMod (allLagModulus b ell)).cast : ZMod b)
  exact ZMod.cast_neg
    (show b ∣ allLagModulus b ell by
      unfold allLagModulus
      exact dvd_pow_self b (by omega))
    (a : ZMod (allLagModulus b ell))

/-- Fiber centering gives exactly zero total mass. -/
theorem centeredCollisionTransform_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a, centeredCollisionTransform b ell a = 0 :=
  centeredSignal_sum_zero (coarseUnitReduction b ell)
    (allLagUnitTable b ell) (coarseUnitReduction_surjective b ell)

/-- Reflection makes the naturally centered table exactly odd. -/
theorem centeredCollisionTransform_odd
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTransform b ell (-a) =
      -centeredCollisionTransform b ell a := by
  exact centered_allLagUnitTable_odd hb2 hell
    (coarseUnitReduction b ell) (fun u : UnitClass b => -u)
    (fun _ => neg_neg _) coarseUnitReduction_neg
    (coarseUnitReduction_surjective b ell) a

/-- A character factors through the exact coarse reduction when its values
are pulled back from a character on the base unit group. -/
def BaseFactored {b ell : ℕ} [NeZero b]
    [NeZero (allLagModulus b ell)]
    (χ : Character (allLagModulus b ell)) : Prop :=
  ∃ ψ : Character b, ∀ a : UnitClass (allLagModulus b ell),
    χ a.val = ψ (coarseUnitReduction b ell a).val

/-- Mathlib's conductor-level factorization supplies the manuscript's
pointwise coarse factorization. -/
theorem baseFactored_of_factorsThrough
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {χ : Character (allLagModulus b ell)}
    (hχ : χ.FactorsThrough b) : BaseFactored χ := by
  let hd : b ∣ allLagModulus b ell := hχ.dvd
  let ψ : Character b := hχ.χ₀
  refine ⟨ψ, fun a => ?_⟩
  have heq : χ = DirichletCharacter.changeLevel hd ψ := by
    dsimp [hd, ψ]
    exact hχ.eq_changeLevel
  calc
    χ a.val = (DirichletCharacter.changeLevel hd ψ) a.val := by
      exact DFunLike.congr_fun heq a.val
    _ = ψ (coarseUnitReduction b ell a).val := by
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd a]
      unfold coarseUnitReduction
      rw [ZMod.unitsMap_val]

/-- Every even channel is absent from the naturally centered transform. -/
theorem centeredCollisionTransform_even_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (heven : χ.Even) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  centered_allLag_even_character_zero hb2 hell
    (coarseUnitReduction b ell) (fun u : UnitClass b => -u)
    (fun _ => neg_neg _) coarseUnitReduction_neg
    (coarseUnitReduction_surjective b ell) χ heven

/-- Every channel descending to the base is absent. -/
theorem centeredCollisionTransform_baseFactored_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (χ : Character (allLagModulus b ell)) (hfactor : BaseFactored χ) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 := by
  obtain ⟨ψ, hψ⟩ := hfactor
  exact centered_allLag_factored_character_zero
    (coarseUnitReduction b ell) (coarseUnitReduction_surjective b ell)
    (fun u => ψ u.val) χ hψ

/-- The exact active character set of the centered transform. -/
noncomputable def transformActiveCharacters
    (b ell : ℕ) [NeZero b] [NeZero (allLagModulus b ell)] :
    Finset (Character (allLagModulus b ell)) :=
  activeCharacters (centeredCollisionTransform b ell)

theorem mem_transformActiveCharacters_iff
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {χ : Character (allLagModulus b ell)} :
    χ ∈ transformActiveCharacters b ell ↔
      collisionCoefficient (centeredCollisionTransform b ell) χ ≠ 0 := by
  simp [transformActiveCharacters, activeCharacters]

/-- Every active channel is odd. -/
theorem activeCharacter_odd
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    {χ : Character (allLagModulus b ell)}
    (hactive : χ ∈ transformActiveCharacters b ell) : χ.Odd := by
  have hne := mem_transformActiveCharacters_iff.mp hactive
  rcases χ.even_or_odd with heven | hodd
  · exact (hne (centeredCollisionTransform_even_zero hb2 hell χ heven)).elim
  · exact hodd

/-- No active channel descends to the base. -/
theorem activeCharacter_not_baseFactored
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {χ : Character (allLagModulus b ell)}
    (hactive : χ ∈ transformActiveCharacters b ell) :
    ¬BaseFactored χ := by
  intro hfactor
  exact (mem_transformActiveCharacters_iff.mp hactive)
    (centeredCollisionTransform_baseFactored_zero χ hfactor)

/-- In particular, every active channel is nonprincipal. -/
theorem activeCharacter_ne_one
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    {χ : Character (allLagModulus b ell)}
    (hactive : χ ∈ transformActiveCharacters b ell) : χ ≠ 1 := by
  have hodd := activeCharacter_odd hb2 hell hactive
  intro h
  subst χ
  have heven : (1 : Character (allLagModulus b ell)).Even := by
    unfold DirichletCharacter.Even
    exact MulChar.one_apply isUnit_neg_one
  exact (1 : Character (allLagModulus b ell)).not_even_and_odd ⟨heven, hodd⟩

/-! ## The prime-base gate -/

/-- At prime base and lag one, an imprimitive character modulo `b^2`
factors through the base. -/
theorem baseFactored_of_prime_lag_one_imprimitive
    {b : ℕ} (hb : Nat.Prime b)
    [NeZero b] [NeZero (allLagModulus b 1)]
    {χ : Character (allLagModulus b 1)} (himp : ¬χ.IsPrimitive) :
    BaseFactored χ := by
  have hlevel : allLagModulus b 1 = b ^ 2 := by
    simp [allLagModulus, pow_two]
  have hcond : χ.conductor ∣ b ^ 2 := by
    simpa [hlevel] using χ.conductor_dvd_level
  obtain ⟨k, hk, hkcond⟩ := (Nat.dvd_prime_pow hb).mp hcond
  have hkne : k ≠ 2 := by
    intro hkeq
    subst k
    apply himp
    exact hkcond.trans hlevel.symm
  have hklt : k < 2 := by
    omega
  have hcondb : χ.conductor ∣ b := by
    rw [hkcond]
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · simp
    · simp
  apply baseFactored_of_factorsThrough
  exact DirichletCharacter.FactorsThrough.mono (χ := χ)
    χ.factorsThrough_conductor hcondb
    (show b ∣ allLagModulus b 1 by
      unfold allLagModulus
      exact dvd_pow_self b (by omega))

/-- Therefore every active lag-one channel at a prime base is primitive and
odd. -/
theorem primeBase_active_primitive_and_odd
    {b : ℕ} (hb : Nat.Prime b)
    [NeZero b] [NeZero (allLagModulus b 1)]
    {χ : Character (allLagModulus b 1)}
    (hactive : χ ∈ transformActiveCharacters b 1) :
    χ.IsPrimitive ∧ χ.Odd := by
  constructor
  · by_contra himp
    exact activeCharacter_not_baseFactored hactive
      (baseFactored_of_prime_lag_one_imprimitive hb himp)
  · exact activeCharacter_odd hb.two_le (by omega) hactive

/-! ## Finite Fourier and Euler-product bookkeeping -/

/-- Exact character decomposition of every finite weighted packet. -/
theorem transform_finite_packet_decomposition
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass (allLagModulus b ell))
    (weight : ι → ℂ) :
    ∑ i, centeredCollisionTransform b ell (residue i) * weight i =
      ∑ χ : Character (allLagModulus b ell),
        collisionCoefficient (centeredCollisionTransform b ell) χ *
          ∑ i, χ (residue i).val * weight i :=
  finite_prime_packet_decomposition
    (centeredCollisionTransform b ell) residue weight

/-- The common divergent class term cancels whenever the finite collision
signal has zero total.  This is the exact finite algebra used at `s=1`. -/
theorem commonClassTerm_cancels
    {α : Type*} [Fintype α]
    (f remainder : α → ℂ) (common : ℂ) (hsum : ∑ a, f a = 0) :
    ∑ a, f a * (common + remainder a) =
      ∑ a, f a * remainder a := by
  calc
    (∑ a, f a * (common + remainder a)) =
        (∑ a, f a) * common + ∑ a, f a * remainder a := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [hsum]; simp

/-- The exact structural signs in the Euler-product decomposition. -/
theorem collisionEulerProduct_decomposition
    {ι : Type*} [Fintype ι]
    (C P logL H : ι → ℂ) (F E : ℂ)
    (hprime : F + E = ∑ i, C i * P i)
    (hEuler : ∀ i, P i = logL i - H i) :
    F = (∑ i, C i * logL i) - (∑ i, C i * H i) - E := by
  rw [Finset.sum_congr rfl (fun i _ => by rw [hEuler i])] at hprime
  simp_rw [mul_sub] at hprime
  rw [Finset.sum_sub_distrib] at hprime
  linear_combination hprime

/-! ## The exact zero ledger -/

/-- Residues of the weighted logarithmic derivatives give the collision zero
ledger exactly once each channel residue is identified with its zero
multiplicity. -/
theorem collisionZeroLedger_eq_residue_sum
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (multiplicity : Character q → ℕ) (residue : Character q → ℂ)
    (hresidue : ∀ χ ∈ activeCharacters F,
      residue χ = (multiplicity χ : ℂ)) :
    collisionZeroLedger F multiplicity =
      ∑ χ ∈ activeCharacters F,
        collisionCoefficient F χ * residue χ := by
  unfold collisionZeroLedger
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hresidue χ hχ]

/-- A holomorphic weighted logarithmic-derivative balance has zero collision
ledger. -/
theorem collisionZeroLedger_eq_zero_of_residue_balance
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (multiplicity : Character q → ℕ) (residue : Character q → ℂ)
    (hresidue : ∀ χ ∈ activeCharacters F,
      residue χ = (multiplicity χ : ℂ))
    (hbalance : ∑ χ ∈ activeCharacters F,
      collisionCoefficient F χ * residue χ = 0) :
    collisionZeroLedger F multiplicity = 0 := by
  rw [collisionZeroLedger_eq_residue_sum F multiplicity residue hresidue]
  exact hbalance

/-- One isolated active channel with positive zero multiplicity gives a
nonzero ledger and therefore cannot satisfy the holomorphic balance. -/
theorem isolatedTransformChannel_nonzero_ledger
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (multiplicity : Character (allLagModulus b ell) → ℕ)
    (χ₀ : Character (allLagModulus b ell))
    (hactive : χ₀ ∈ transformActiveCharacters b ell)
    (hmult : 0 < multiplicity χ₀)
    (hisolated : ∀ χ ∈ transformActiveCharacters b ell,
      χ ≠ χ₀ → multiplicity χ = 0) :
    collisionZeroLedger (centeredCollisionTransform b ell) multiplicity ≠ 0 := by
  exact isolated_active_channel_has_nonzero_ledger
    (centeredCollisionTransform b ell) multiplicity χ₀
    (mem_transformActiveCharacters_iff.mp hactive) hmult hisolated

end NField.Alignment.CollisionTransform
