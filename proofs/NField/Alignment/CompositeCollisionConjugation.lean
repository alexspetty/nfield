/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BinDerangements

/-! # Conjugating digit bins at every coprime modulus -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CompositeCollisionConjugation
open scoped BigOperators
open NField.CollisionDefinition SpectralPower PhaseFilteredRamanujan BinDerangements

theorem digit_eq_iff_transformed_mod_coprime {b p : ℕ}
    (hb : 0 < b) (hcop : Nat.Coprime b p) (hbp : b < p) [NeZero p]
    (r s : ZMod p) :
    digitBin b p r.val = digitBin b p s.val ↔
      ((b : ZMod p) * r).val % b =
        ((b : ZMod p) * s).val % b := by
  let dr := digitBin b p r.val
  let ds := digitBin b p s.val
  let xr := ((b : ZMod p) * r).val
  let xs := ((b : ZMod p) * s).val
  have hdr : b * r.val = p * dr + xr := digit_decomposition hbp r
  have hds : b * s.val = p * ds + xs := digit_decomposition hbp s
  have hrmod : p * dr + xr ≡ 0 [MOD b] := by
    rw [← hdr]
    simp [Nat.ModEq]
  have hsmod : p * ds + xs ≡ 0 [MOD b] := by
    rw [← hds]
    simp [Nat.ModEq]
  constructor
  · intro hd
    change dr = ds at hd
    have hsum : p * dr + xr ≡ p * ds + xs [MOD b] :=
      hrmod.trans hsmod.symm
    rw [hd] at hsum
    have := hsum.add_left_cancel' (p * ds)
    simpa [Nat.ModEq] using this
  · intro hx
    have hxmod : xr ≡ xs [MOD b] := by
      simpa [Nat.ModEq] using hx
    have hsum : p * dr + xr ≡ p * ds + xs [MOD b] :=
      hrmod.trans hsmod.symm
    have hprod : p * dr ≡ p * ds [MOD b] :=
      hxmod.add_right_cancel hsum
    have hdmod : dr ≡ ds [MOD b] :=
      Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hprod
    have hdrlt : dr < b := digitBin_lt_base hb (NeZero.pos p) r.val_lt
    have hdslt : ds < b := digitBin_lt_base hb (NeZero.pos p) s.val_lt
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hdrlt,
      Nat.mod_eq_of_lt hdslt] using hdmod


/-- The digit word is defined at composite moduli too; unit multiplication
preserves precisely the nonzero residues counted by the manuscript. -/
theorem collisionCount_eq_congruence_coprime {b N : ℕ}
    (hb : 0 < b) (hcop : Nat.Coprime b N) (hbN : b < N) [NeZero N]
    (g : (ZMod N)ˣ) :
    collisionCount (primeDigitWord b N hb (NeZero.pos N)) g.val =
      transformedCollisionCount b N g.val := by
  classical
  let base := ZMod.unitOfCoprime b hcop
  let e : ZMod N ≃ ZMod N := base.mulLeft
  let term : ZMod N → ℕ := fun x =>
    if x ≠ 0 ∧ x.val % b = (g.val * x).val % b then 1 else 0
  calc
    collisionCount (primeDigitWord b N hb (NeZero.pos N)) g.val =
        ∑ r : ZMod N,
          if r ≠ 0 ∧ ((b : ZMod N) * r).val % b =
            ((b : ZMod N) * (g.val * r)).val % b then 1 else 0 := by
      unfold collisionCount
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : r = 0
      · simp [hr, primeDigitWord_zero]
      · have hgr : g.val * r ≠ 0 := by simpa using hr
        simp [primeDigitWord, hr, hgr, Fin.ext_iff,
          digit_eq_iff_transformed_mod_coprime hb hcop hbN]
    _ = ∑ x : ZMod N, term x := by
      apply Fintype.sum_equiv e
      intro r
      simp only [term, e, Units.mulLeft_apply, base, ZMod.coe_unitOfCoprime]
      rw [show g.val * ((b : ZMod N) * r) = (b : ZMod N) * (g.val * r) by ring]
      have hzero : (b : ZMod N) * r = 0 ↔ r = 0 := by
        change base.val * r = 0 ↔ r = 0
        exact Units.mul_right_eq_zero base
      simp only [ne_eq, hzero]
    _ = transformedCollisionCount b N g.val := rfl

end NField.Alignment.CompositeCollisionConjugation
