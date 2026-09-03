/-
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

/-!
# Odd-character expansion of the centered sawtooth

This file states the finite Fourier reconstruction in the exact character
labeling used by the cubic-energy manuscript.
-/

namespace NField.Alignment.SawtoothCharacterExpansion

open scoped BigOperators ComplexConjugate
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CollisionCharacterStructure

/-- The odd-character sum in the sawtooth Fourier expansion. -/
noncomputable def oddSawtoothCharacterSum
    {m : ℕ} [NeZero m] (a : UnitClass m) : ℂ := by
  classical
  exact ∑ χ : Character m,
    if χ.Odd then bernoulliOne χ⁻¹ * χ a.val else 0

private theorem characterTransform_odd_even_zero
    {m : ℕ} [NeZero m] (F : UnitClass m → ℂ)
    (hF : ∀ u, F (-u) = -F u)
    (χ : Character m) (heven : χ.Even) :
    characterTransform F χ = 0 := by
  classical
  unfold characterTransform
  have hreindex :
      (∑ u : UnitClass m, χ u.val * F u) =
        ∑ u : UnitClass m, χ (-u).val * F (-u) := by
    simpa using (Equiv.sum_comp (Equiv.neg (UnitClass m))
      (fun u : UnitClass m => χ u.val * F u)).symm
  have hneg :
      (∑ u : UnitClass m, χ (-u).val * F (-u)) =
        -∑ u : UnitClass m, χ u.val * F u := by
    calc
      _ = ∑ u : UnitClass m, χ u.val * (-F u) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Units.val_neg, heven.eval_neg, hF]
      _ = -∑ u : UnitClass m, χ u.val * F u := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring
  have hself :
      (∑ u : UnitClass m, χ u.val * F u) =
        -∑ u : UnitClass m, χ u.val * F u := hreindex.trans hneg
  linear_combination (1 / 2 : ℂ) * hself

/-- The centered sawtooth on the unit group is reconstructed exactly from
its odd Dirichlet-character coordinates. -/
theorem centeredSawtooth_eq_oddCharacterExpansion
    {m : ℕ} [NeZero m] (hm : 2 ≤ m) (a : UnitClass m) :
    centeredSawtooth a.val =
      (m.totient : ℂ)⁻¹ * oddSawtoothCharacterSum a := by
  classical
  let F : UnitClass m → ℂ := fun u => centeredSawtooth u.val
  have hFodd : ∀ u : UnitClass m, F (-u) = -F u := by
    intro u
    unfold F
    rw [Units.val_neg, centeredSawtooth_neg hm]
  have hcoefficient (ψ : Character m) :
      characterTransform F ψ =
        if ψ.Odd then bernoulliOne ψ else 0 := by
    rcases ψ.even_or_odd with heven | hodd
    · have hnotodd : ¬ψ.Odd := fun h =>
        ψ.not_even_and_odd ⟨heven, h⟩
      rw [characterTransform_odd_even_zero F hFodd ψ heven,
        if_neg hnotodd]
    · rw [if_pos hodd]
      have hne : ψ ≠ 1 := by
        intro h
        subst ψ
        have honeEven : (1 : Character m).Even := by
          unfold DirichletCharacter.Even
          exact MulChar.one_apply isUnit_neg_one
        exact (1 : Character m).not_even_and_odd ⟨honeEven, hodd⟩
      have hfull := centeredSawtooth_transform_eq_bernoulliOne
        (by omega : m ≠ 1) hne
      unfold twistedTransform at hfull
      simp only [one_mul] at hfull
      rw [sum_character_pairing_eq_units] at hfull
      unfold characterTransform F
      calc
        (∑ r : UnitClass m, ψ r.val * centeredSawtooth r.val) =
            ∑ r : UnitClass m, centeredSawtooth r.val * ψ r.val := by
              apply Finset.sum_congr rfl
              intro r _
              ring
        _ = bernoulliOne ψ := hfull
  have hoddStar (ψ : Character m) : (star ψ).Odd ↔ ψ.Odd := by
    constructor
    · intro h
      change ψ (-1) = -1
      change (star ψ) (-1) = -1 at h
      rw [MulChar.star_apply] at h
      have hs : star (ψ (-1)) = -1 := h
      simpa using congrArg star hs
    · intro h
      change star (ψ (-1)) = -1
      rw [h]
      simp
  let T : Character m → ℂ := fun χ =>
    if χ.Odd then bernoulliOne χ⁻¹ * χ a.val else 0
  have hterm (ψ : Character m) :
      T (star ψ) = star (ψ a.val) * characterTransform F ψ := by
    unfold T
    rw [hcoefficient]
    by_cases hodd : ψ.Odd
    · rw [if_pos hodd, if_pos ((hoddStar ψ).2 hodd)]
      have happ : ψ⁻¹ a.val = star (ψ a.val) :=
        (MulChar.star_apply' ψ a.val).symm
      simp only [MulChar.star_eq_inv, inv_inv]
      rw [happ]
      ring
    · rw [if_neg hodd, if_neg (fun hs => hodd ((hoddStar ψ).1 hs))]
      ring
  have hreindex :
      (∑ ψ : Character m, T (star ψ)) = ∑ χ : Character m, T χ := by
    simpa using (Equiv.sum_comp
      (Equiv.Perm.star : Equiv.Perm (Character m)) T)
  have hinversion := inverse_characterTransform F a
  unfold inverseCharacterTransform at hinversion
  change F a = _
  rw [← hinversion]
  congr 1
  unfold oddSawtoothCharacterSum
  symm
  calc
    (∑ χ : Character m,
        if χ.Odd then bernoulliOne χ⁻¹ * χ a.val else 0) =
        ∑ χ : Character m, T χ := by rfl
    _ = ∑ ψ : Character m, T (star ψ) := hreindex.symm
    _ = ∑ ψ : Character m,
        star (ψ a.val) * characterTransform F ψ := by
          apply Finset.sum_congr rfl
          intro ψ _
          exact hterm ψ

end NField.Alignment.SawtoothCharacterExpansion
