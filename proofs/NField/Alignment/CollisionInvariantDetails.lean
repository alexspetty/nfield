/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CompositeCollisionConjugation
import NField.Alignment.CenteredCollisionClosure

/-! # Literal finite objects in the collision invariant -/

noncomputable section
namespace NField.Alignment.CollisionInvariantDetails
open scoped BigOperators
open NField.CollisionDefinition SpectralPower PhaseFilteredRamanujan
  CenteredCollisionSum CenteredCollisionClosure CollisionInvariant CollisionTransformStrip

/-- Natural representatives of the manuscript's collision set. -/
def naturalCollisionSet (b N a : ℕ) : Finset ℕ :=
  (Finset.Ico 1 N).filter fun r => digitBin b N r = digitBin b N (a * r % N)

/-- The generic digit-word count is literally the count on `1,...,N-1`,
including composite moduli. -/
theorem collisionCount_eq_natural_card {b N : ℕ} (hb : 0 < b) [NeZero N]
    (g : (ZMod N)ˣ) :
    collisionCount (primeDigitWord b N hb (NeZero.pos N)) g.val =
      (naturalCollisionSet b N g.val.val).card := by
  classical
  have hword : collisionCount (primeDigitWord b N hb (NeZero.pos N)) g.val =
      (Finset.univ.filter fun r : ZMod N => r ≠ 0 ∧
        digitBin b N r.val = digitBin b N (g.val * r).val).card := by
    unfold collisionCount
    have heq (r : ZMod N) :
        (primeDigitWord b N hb (NeZero.pos N) r =
          primeDigitWord b N hb (NeZero.pos N) (g.val * r) ∧
          primeDigitWord b N hb (NeZero.pos N) r ≠ none) ↔
        (r ≠ 0 ∧ digitBin b N r.val = digitBin b N (g.val * r).val) := by
      by_cases hr : r = 0
      · simp [hr, primeDigitWord_zero]
      · have hgr : g.val * r ≠ 0 := by simpa using hr
        simp [primeDigitWord, hr, hgr, Fin.ext_iff]
    simp_rw [heq]
    exact Finset.sum_boole _ _
  rw [hword]
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    have hrpos : 0 < r.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr hr.1)
    simp only [naturalCollisionSet, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hrpos, r.val_lt⟩, by simpa [ZMod.val_mul] using hr.2⟩
  · intro r hr s hs heq
    exact ZMod.val_injective N heq
  · intro r hr
    simp only [naturalCollisionSet, Finset.mem_filter, Finset.mem_Ico] at hr
    have hrval : (r : ZMod N).val = r := ZMod.val_natCast_of_lt hr.1.2
    refine ⟨(r : ZMod N), ?_, hrval⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · apply (ZMod.val_ne_zero _).mp
      rw [hrval]
      omega
    · simpa [ZMod.val_mul, hrval] using hr.2

theorem directAllLagCollisionCount_eq_natural_card (b ell N : ℕ) :
    directAllLagCollisionCount b ell N =
      (naturalCollisionSet b N (b ^ ell)).card := by
  unfold directAllLagCollisionCount naturalCollisionSet
  exact Finset.sum_boole _ _

theorem identity_collision_count {b N : ℕ} (hb : 0 < b) [NeZero N] :
    collisionCount (primeDigitWord b N hb (NeZero.pos N)) 1 = N - 1 := by
  rw [collisionCount_one, prime_assignedMass hb (NeZero.pos N)]

/-- The half-group theorem applies to every nonendpoint actual diagonal cell. -/
theorem diagonal_wrapping_card {b ell n : ℕ}
    [NeZero (allLagModulus b ell)] (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hn : n ∈ allLagDiagonal b ell) (hn0 : n ≠ 0)
    (hnlast : n ≠ allLagModulus b ell - 1) :
    Fintype.card (WrappingClass (allLagModulus b ell) (n + 1)) =
      (allLagModulus b ell).totient / 2 := by
  have hnlt := allLagDiagonal_index_lt hb2 hell hn
  apply interiorWrappingClass_card <;> omega

end NField.Alignment.CollisionInvariantDetails
