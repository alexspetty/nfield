/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra
import NField.Alignment.SubgroupOrbitJacobiExpansion
import NField.Alignment.IndexTwoOrbitEnergy

/-! # Parity, Fourier expansion and the resonant part of the orbit energy -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.OrbitPaperDetails
open CollisionCharacterStructure CarryBoundarySpectra SubgroupOrbitJacobiExpansion
open IndexTwoOrbitEnergy
open scoped BigOperators Classical

theorem twistedSawtooth_even_zero {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (χ : Character m) (hχ : χ.Even) (k : ZMod m) :
    twistedTransform centeredSawtooth χ⁻¹ k = 0 := by
  have hself : twistedTransform centeredSawtooth χ⁻¹ k =
      -twistedTransform centeredSawtooth χ⁻¹ k := by
    unfold twistedTransform
    calc
      _ = ∑ a : ZMod m, centeredSawtooth (k * -a) * χ⁻¹ (-a) :=
        (Equiv.sum_comp (Equiv.neg (ZMod m))
          (fun a => centeredSawtooth (k * a) * χ⁻¹ a)).symm
      _ = _ := by
        simp only [mul_neg, centeredSawtooth_neg hm, (inverse_even hχ).eval_neg,
          neg_mul, Finset.sum_neg_distrib]
  linear_combination (1 / 2 : ℂ) * hself

theorem finite_fourier_expansion {m : ℕ} [NeZero m] (f : ZMod m → ℂ) (x : ZMod m) :
    f x = ∑ j : ZMod m, ((m : ℂ)⁻¹ * ZMod.dft f j) * ZMod.stdAddChar (j * x) := by
  have h := congr_fun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at h
  simpa [smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h.symm

theorem twistedSawtooth_difference {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (χ : Character m) (hχ : χ.IsPrimitive) (n : ZMod m) :
    (∑ a : ZMod m, (centeredSawtooth ((n + 1) * a) - centeredSawtooth (n * a)) * χ⁻¹ a) =
      (χ (n + 1) - χ n) * bernoulliOne χ⁻¹ := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  change twistedTransform centeredSawtooth χ⁻¹ (n + 1) -
    twistedTransform centeredSawtooth χ⁻¹ n = _
  rw [twistedSawtooth_evaluation hm hχ, twistedSawtooth_evaluation hm hχ]

theorem off_resonance_character_sum {q : ℕ} [NeZero q] [Fact q.Prime]
    (hq : q.Prime) (hqodd : q ≠ 2) (z : ZMod q) :
    (∑ χ ∈ offResonanceOddCharacters q, χ z) =
      ((q - 1 : ℕ) : ℂ) / 2 *
        ((if z = 1 then 1 else 0) - (if z = -1 then 1 else 0)) -
        if q % 4 = 3 then complexQuadraticCharacter q z else 0 := by
  classical
  have herase : offResonanceOddCharacters q =
      (oddCharacters q).erase (complexQuadraticCharacter q) := by
    ext χ
    simp [offResonanceOddCharacters, oddCharacters, quadratic_mul_ne_one_iff hq, and_comm]
  rw [herase]
  have hall : (∑ χ ∈ oddCharacters q, χ z) =
      ((q - 1 : ℕ) : ℂ) / 2 *
        ((if z = 1 then 1 else 0) - (if z = -1 then 1 else 0)) :=
    oddCharacterSum_eq hq hqodd z
  by_cases hodd : (complexQuadraticCharacter q).Odd
  · have hmem : complexQuadraticCharacter q ∈ oddCharacters q := by simp [oddCharacters, hodd]
    rw [if_pos ((complexQuadraticCharacter_odd_iff hq hqodd).mp hodd)]
    exact eq_sub_of_add_eq ((Finset.sum_erase_add _ (fun χ : Character q => χ z) hmem).trans hall)
  · have hnot : complexQuadraticCharacter q ∉ oddCharacters q := by simp [oddCharacters, hodd]
    rw [Finset.erase_eq_self.mpr hnot, hall,
      if_neg (fun h => hodd ((complexQuadraticCharacter_odd_iff hq hqodd).mpr h)), sub_zero]

theorem fourier_twisted_expansion {m : ℕ} [NeZero m]
    (f : ZMod m → ℂ) (χ : Character m) (k : ZMod m) :
    twistedTransform f χ k =
      ∑ j : ZMod m, ((m : ℂ)⁻¹ * ZMod.dft f j) *
        gaussSum χ (ZMod.stdAddChar.mulShift (j * k)) := by
  unfold twistedTransform
  simp_rw [finite_fourier_expansion f]
  simp only [Finset.sum_mul, gaussSum, AddChar.mulShift_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_assoc]
  ring

theorem trivial_on_subgroup_iff_factors {q : ℕ}
    (H : Subgroup (UnitClass q)) (χ : UnitClass q →* ℂ) :
    (∀ u ∈ H, χ u = 1) ↔
      ∃ ρ : (UnitClass q ⧸ H) →* ℂ, χ = ρ.comp (QuotientGroup.mk' H) := by
  constructor
  · intro h
    refine ⟨QuotientGroup.lift H χ h, ?_⟩
    ext u
    rfl
  · rintro ⟨ρ, rfl⟩ u hu
    change ρ (u : UnitClass q ⧸ H) = 1
    rw [(QuotientGroup.eq_one_iff u).mpr hu, map_one]

theorem no_odd_resonance_of_neg_one_mem {q : ℕ}
    (H : Subgroup (UnitClass q)) (hH : (-1 : UnitClass q) ∈ H)
    (χ : Character q) (hχ : χ.Odd) : ¬∀ u ∈ H, χ u.val = 1 := by
  intro h
  have h1 := h (-1) hH
  change χ (-1) = 1 at h1
  rw [hχ] at h1
  norm_num at h1

theorem odd_energy_resonance_split {q : ℕ} [NeZero q]
    (H : Subgroup (UnitClass q)) :
    (∑ χ : Character q with χ.Odd, ‖subgroupOrbitFlux H χ‖ ^ 2) =
      (∑ χ : Character q with χ.Odd ∧ (∀ u ∈ H, χ u.val = 1),
        ‖subgroupOrbitFlux H χ‖ ^ 2) +
      ∑ χ : Character q with χ.Odd ∧ ¬(∀ u ∈ H, χ u.val = 1),
        ‖subgroupOrbitFlux H χ‖ ^ 2 := by
  classical
  simpa only [Finset.filter_filter] using
    (Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Character q)).filter fun χ => χ.Odd)
      (fun χ => ∀ u ∈ H, χ u.val = 1)
      (fun χ => ‖subgroupOrbitFlux H χ‖ ^ 2)).symm

end NField.Alignment.OrbitPaperDetails
