/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectrumLandscape
import Mathlib.Analysis.Fourier.ZMod

/-!
# Carry boundaries and Bernoulli spectra

Reusable finite proofs for the carry-boundary factorization.  The central
result is proved from discrete Fourier inversion and Mathlib's primitive
Gauss-sum separation.  In particular, the proof treats unit and nonunit
boundary indices uniformly and uses no unchecked analytic assumption.

The module also proves exact recovery of the unit boundary from all ordinary
Dirichlet fluxes, interval telescoping, the eight terminal-boundary
certificates stated in the manuscript, and the complete base-fifteen leakage
ledger.
-/

namespace NField.Alignment.CarryBoundarySpectra

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure

variable {m : ℕ} [NeZero m]

/-- Multiplicatively twisted finite transform of a function on `ZMod m`. -/
noncomputable def twistedTransform
    (f : ZMod m → ℂ) (ψ : Character m) (k : ZMod m) : ℂ :=
  ∑ a : ZMod m, f (k * a) * ψ a

/-- The centered sawtooth on the canonical residues modulo `m`. -/
noncomputable def centeredSawtooth (x : ZMod m) : ℂ :=
  if x = 0 then 0 else (x.val : ℂ) / (m : ℂ) - 1 / 2

/-- The first generalized Bernoulli sum in the manuscript's normalization. -/
noncomputable def bernoulliOne (ψ : Character m) : ℂ :=
  (m : ℂ)⁻¹ * ∑ x : ZMod m, (x.val : ℂ) * ψ x

/-- The centered sawtooth is odd. -/
theorem centeredSawtooth_neg (hm : 2 ≤ m) (x : ZMod m) :
    centeredSawtooth (-x) = -centeredSawtooth x := by
  unfold centeredSawtooth
  by_cases hx : x = 0
  · subst x
    simp
  · have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
    simp only [hneg, hx, if_false]
    rw [ZMod.neg_val, if_neg hx]
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hxle : x.val ≤ m := Nat.le_of_lt x.val_lt
    push_cast [Nat.cast_sub hxle]
    field_simp [hm0]
    ring

/-- A nonprincipal character evaluates the basic sawtooth transform as its
first generalized Bernoulli sum. -/
theorem centeredSawtooth_transform_eq_bernoulliOne
    (hm : m ≠ 1) {ψ : Character m} (hψ : ψ ≠ 1) :
    twistedTransform centeredSawtooth ψ 1 = bernoulliOne ψ := by
  classical
  unfold twistedTransform centeredSawtooth bernoulliOne
  simp only [one_mul]
  have hzero : ψ (0 : ZMod m) = 0 := ψ.map_zero' hm
  have hsum : ∑ x : ZMod m, ψ x = 0 := ψ.sum_eq_zero_of_ne_one hψ
  calc
    (∑ x : ZMod m,
        (if x = 0 then 0 else (x.val : ℂ) / (m : ℂ) - 1 / 2) * ψ x) =
        ∑ x : ZMod m,
          ((x.val : ℂ) / (m : ℂ) - 1 / 2) * ψ x := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = 0
            · subst x
              simp [hzero]
            · simp [hx]
    _ = (m : ℂ)⁻¹ * ∑ x : ZMod m, (x.val : ℂ) * ψ x -
        (1 / 2 : ℂ) * ∑ x : ZMod m, ψ x := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          rw [div_eq_inv_mul]
          ring
    _ = (m : ℂ)⁻¹ * ∑ x : ZMod m, (x.val : ℂ) * ψ x := by
          rw [hsum, mul_zero, sub_zero]

/-- Primitive Gauss separation makes every twisted transform a character
multiple of the untwisted transform, including at nonunit multipliers. -/
theorem twistedTransform_eq_inv_mul
    (f : ZMod m → ℂ) {ψ : Character m} (hψ : ψ.IsPrimitive)
    (k : ZMod m) :
    twistedTransform f ψ k = ψ⁻¹ k * twistedTransform f ψ 1 := by
  classical
  unfold twistedTransform
  have hinv (x : ZMod m) :
      f x = (m : ℂ)⁻¹ * ∑ j : ZMod m, ZMod.stdAddChar (j * x) * ZMod.dft f j := by
    have h := congr_fun (ZMod.dft.symm_apply_apply f) x
    rw [ZMod.invDFT_apply] at h
    simpa [smul_eq_mul] using h.symm
  have hformula (t : ZMod m) :
      (∑ a : ZMod m, f (t * a) * ψ a) =
        (m : ℂ)⁻¹ * ∑ j : ZMod m,
          ZMod.dft f j * (ψ⁻¹ (j * t) * gaussSum ψ ZMod.stdAddChar) := by
    simp_rw [hinv]
    calc
      (∑ a : ZMod m,
          ((m : ℂ)⁻¹ * ∑ j : ZMod m,
            ZMod.stdAddChar (j * (t * a)) * ZMod.dft f j) * ψ a) =
          (m : ℂ)⁻¹ * ∑ a : ZMod m, ∑ j : ZMod m,
            ZMod.dft f j *
              (ψ a * ZMod.stdAddChar ((j * t) * a)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            calc
              ((m : ℂ)⁻¹ * ∑ j : ZMod m,
                  ZMod.stdAddChar (j * (t * a)) * ZMod.dft f j) * ψ a =
                  (m : ℂ)⁻¹ * ((∑ j : ZMod m,
                    ZMod.stdAddChar (j * (t * a)) * ZMod.dft f j) * ψ a) := by
                    ring
              _ = (m : ℂ)⁻¹ * ∑ j : ZMod m,
                    (ZMod.stdAddChar (j * (t * a)) * ZMod.dft f j) * ψ a := by
                    rw [Finset.sum_mul]
              _ = _ := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro j _
                    ring_nf
      _ = (m : ℂ)⁻¹ * ∑ j : ZMod m,
          ZMod.dft f j *
            (∑ a : ZMod m, ψ a * ZMod.stdAddChar ((j * t) * a)) := by
              congr 1
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
      _ = (m : ℂ)⁻¹ * ∑ j : ZMod m,
          ZMod.dft f j *
            (ψ⁻¹ (j * t) * gaussSum ψ ZMod.stdAddChar) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [show (∑ a : ZMod m,
                    ψ a * ZMod.stdAddChar ((j * t) * a)) =
                  ψ⁻¹ (j * t) * gaussSum ψ ZMod.stdAddChar by
                    change gaussSum ψ
                      (ZMod.stdAddChar.mulShift (j * t)) = _
                    exact gaussSum_mulShift_of_isPrimitive
                      ZMod.stdAddChar hψ (j * t)]
  rw [hformula k, hformula 1]
  simp_rw [map_mul]
  simp only [map_one, mul_one]
  rw [Finset.mul_sum]
  calc
    (∑ i : ZMod m, (m : ℂ)⁻¹ *
        (ZMod.dft f i *
          (ψ⁻¹ i * ψ⁻¹ k * gaussSum ψ ZMod.stdAddChar))) =
        ∑ i : ZMod m, ψ⁻¹ k *
          ((m : ℂ)⁻¹ *
            (ZMod.dft f i * (ψ⁻¹ i * gaussSum ψ ZMod.stdAddChar))) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
    _ = ψ⁻¹ k * ∑ i : ZMod m, (m : ℂ)⁻¹ *
          (ZMod.dft f i * (ψ⁻¹ i * gaussSum ψ ZMod.stdAddChar)) := by
      exact (Finset.mul_sum (s := Finset.univ)
        (f := fun i : ZMod m => (m : ℂ)⁻¹ *
          (ZMod.dft f i * (ψ⁻¹ i * gaussSum ψ ZMod.stdAddChar)))
        (ψ⁻¹ k)).symm
    _ = _ := by
      congr 1
      exact (Finset.mul_sum (s := Finset.univ)
        (f := fun i : ZMod m =>
          ZMod.dft f i * (ψ⁻¹ i * gaussSum ψ ZMod.stdAddChar))
        ((m : ℂ)⁻¹)).symm

/-- A primitive character at a nontrivial level is nonprincipal. -/
theorem primitive_ne_one (hm : 2 ≤ m) {χ : Character m}
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  intro heq
  have hcond : χ.conductor = 1 := by
    rw [heq]
    exact DirichletCharacter.conductor_one
  unfold DirichletCharacter.IsPrimitive at hχ
  omega

omit [NeZero m] in
/-- Inversion preserves the conductor and hence primitivity. -/
theorem inverse_isPrimitive {χ : Character m} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive at hχ ⊢
  rw [DirichletCharacter.conductor_inv]
  exact hχ

/-- Exact twisted-sawtooth evaluation for every residue multiplier. -/
theorem twistedSawtooth_evaluation (hm : 2 ≤ m)
    {χ : Character m} (hχ : χ.IsPrimitive) (k : ZMod m) :
    twistedTransform centeredSawtooth χ⁻¹ k =
      χ k * bernoulliOne χ⁻¹ := by
  rw [twistedTransform_eq_inv_mul centeredSawtooth
    (inverse_isPrimitive hχ) k]
  rw [centeredSawtooth_transform_eq_bernoulliOne (by omega)
    (inv_ne_one.mpr (primitive_ne_one hm hχ))]
  simp

/-- Sawtooth-normalized carry observable attached to a cell weight. -/
noncomputable def carryObservable
    (w : ZMod m → ℂ) (a : ZMod m) : ℂ :=
  -∑ n : ZMod m, w n *
    (centeredSawtooth ((n + 1) * a) - centeredSawtooth (n * a))

/-- Dirichlet transform of the carry observable. -/
noncomputable def carryTransform
    (w : ZMod m → ℂ) (χ : Character m) : ℂ :=
  ∑ a : ZMod m, carryObservable w a * χ⁻¹ a

/-- The carry observable restricted to the unit group. -/
noncomputable def unitCarrySignal
    (w : ZMod m → ℂ) (u : UnitClass m) : ℂ :=
  carryObservable w u.val

/-- Boundary flux in the cell-difference form used by the factorization. -/
noncomputable def cellBoundaryFlux
    (w : ZMod m → ℂ) (χ : Character m) : ℂ :=
  ∑ n : ZMod m, w n * (χ (n + 1) - χ n)

/-- The exact primitive carry-boundary factorization. -/
theorem carryBoundary_factorization (hm : 2 ≤ m)
    (w : ZMod m → ℂ) {χ : Character m} (hχ : χ.IsPrimitive) :
    carryTransform w χ =
      -(bernoulliOne χ⁻¹ * cellBoundaryFlux w χ) := by
  classical
  unfold carryTransform carryObservable cellBoundaryFlux
  calc
    (∑ a : ZMod m,
        (-∑ n : ZMod m, w n *
          (centeredSawtooth ((n + 1) * a) -
            centeredSawtooth (n * a))) * χ⁻¹ a) =
      ∑ a : ZMod m, ∑ n : ZMod m,
        -(w n *
            (centeredSawtooth ((n + 1) * a) -
              centeredSawtooth (n * a))) * χ⁻¹ a := by
          apply Finset.sum_congr rfl
          intro a _
          rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro n _
          ring
    _ = ∑ n : ZMod m, ∑ a : ZMod m,
        -(w n *
            (centeredSawtooth ((n + 1) * a) -
              centeredSawtooth (n * a))) * χ⁻¹ a := by
          rw [Finset.sum_comm]
    _ =
      ∑ n : ZMod m, -w n *
        (twistedTransform centeredSawtooth χ⁻¹ (n + 1) -
          twistedTransform centeredSawtooth χ⁻¹ n) := by
            apply Finset.sum_congr rfl
            intro n _
            unfold twistedTransform
            calc
              (∑ a : ZMod m,
                  -(w n *
                    (centeredSawtooth ((n + 1) * a) -
                      centeredSawtooth (n * a))) * χ⁻¹ a) =
                ∑ a : ZMod m, -w n *
                  (centeredSawtooth ((n + 1) * a) * χ⁻¹ a -
                    centeredSawtooth (n * a) * χ⁻¹ a) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      ring
              _ = -w n * ∑ a : ZMod m,
                  (centeredSawtooth ((n + 1) * a) * χ⁻¹ a -
                    centeredSawtooth (n * a) * χ⁻¹ a) := by
                      rw [Finset.mul_sum]
              _ = -w n *
                  ((∑ a : ZMod m,
                    centeredSawtooth ((n + 1) * a) * χ⁻¹ a) -
                   ∑ a : ZMod m,
                    centeredSawtooth (n * a) * χ⁻¹ a) := by
                      rw [Finset.sum_sub_distrib]
    _ = ∑ n : ZMod m, -w n *
        (χ (n + 1) * bernoulliOne χ⁻¹ -
          χ n * bernoulliOne χ⁻¹) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [twistedSawtooth_evaluation hm hχ,
              twistedSawtooth_evaluation hm hχ]
    _ = -(bernoulliOne χ⁻¹ *
        ∑ n : ZMod m, w n * (χ (n + 1) - χ n)) := by
          calc
            (∑ n : ZMod m, -w n *
                (χ (n + 1) * bernoulliOne χ⁻¹ -
                  χ n * bernoulliOne χ⁻¹)) =
              ∑ n : ZMod m,
                -(bernoulliOne χ⁻¹ *
                  (w n * (χ (n + 1) - χ n))) := by
                    apply Finset.sum_congr rfl
                    intro n _
                    ring
            _ = _ := by
              rw [Finset.sum_neg_distrib, Finset.mul_sum]

/-- Cyclic signed boundary derivative of a cell weight. -/
def signedBoundary (w : ZMod m → ℂ) (x : ZMod m) : ℂ :=
  w (x - 1) - w x

/-- Cell differences and signed-boundary pairing give the same flux. -/
theorem cellBoundaryFlux_eq_boundary_pairing
    (w : ZMod m → ℂ) (χ : Character m) :
    cellBoundaryFlux w χ = ∑ x : ZMod m, signedBoundary w x * χ x := by
  classical
  unfold cellBoundaryFlux signedBoundary
  have hshift :
      (∑ n : ZMod m, w n * χ (n + 1)) =
        ∑ x : ZMod m, w (x - 1) * χ x := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : ZMod m))
      (fun x : ZMod m => w (x - 1) * χ x))
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hshift]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A constant weight has no carry observable. -/
theorem constant_carryObservable_zero (c : ℂ) (a : ZMod m) :
    carryObservable (fun _ => c) a = 0 := by
  classical
  unfold carryObservable
  rw [← Finset.mul_sum]
  have hshift :
      (∑ n : ZMod m, centeredSawtooth ((n + 1) * a)) =
        ∑ n : ZMod m, centeredSawtooth (n * a) := by
    simpa [add_mul] using (Equiv.sum_comp (Equiv.addRight (1 : ZMod m))
      (fun n : ZMod m => centeredSawtooth (n * a)))
  rw [Finset.sum_sub_distrib, hshift, sub_self, mul_zero, neg_zero]

/-- A constant cell weight has zero transform in every character channel. -/
theorem constant_carryTransform_zero (c : ℂ) (χ : Character m) :
    carryTransform (fun _ => c) χ = 0 := by
  unfold carryTransform
  apply Finset.sum_eq_zero
  intro a _
  rw [constant_carryObservable_zero]
  ring

/-- Reflection makes every carry observable odd. -/
theorem carryObservable_neg (hm : 2 ≤ m)
    (w : ZMod m → ℂ) (a : ZMod m) :
    carryObservable w (-a) = -carryObservable w a := by
  classical
  unfold carryObservable
  simp_rw [mul_neg, centeredSawtooth_neg hm]
  calc
    (-∑ n : ZMod m, w n *
        (-centeredSawtooth ((n + 1) * a) -
          -centeredSawtooth (n * a))) =
      -∑ n : ZMod m, -(w n *
        (centeredSawtooth ((n + 1) * a) -
          centeredSawtooth (n * a))) := by
            congr 1
            apply Finset.sum_congr rfl
            intro n _
            ring
    _ = -(-∑ n : ZMod m, w n *
        (centeredSawtooth ((n + 1) * a) -
          centeredSawtooth (n * a))) := by
            rw [Finset.sum_neg_distrib]

omit [NeZero m] in
/-- Inversion preserves even character parity. -/
theorem inverse_even {χ : Character m} (hχ : χ.Even) : (χ⁻¹).Even := by
  unfold DirichletCharacter.Even at hχ ⊢
  rw [MulChar.inv_apply]
  have hinv : Ring.inverse (-1 : ZMod m) = -1 := by
    change Ring.inverse ((-1 : (ZMod m)ˣ).val) = -1
    rw [Ring.inverse_unit]
    rfl
  rw [hinv, hχ]

/-- Every even character channel of the carry observable vanishes. -/
theorem carryTransform_even_zero (hm : 2 ≤ m)
    (w : ZMod m → ℂ) (χ : Character m) (hχ : χ.Even) :
    carryTransform w χ = 0 := by
  classical
  unfold carryTransform
  have hreindex :
      (∑ a : ZMod m, carryObservable w a * χ⁻¹ a) =
        ∑ a : ZMod m, carryObservable w (-a) * χ⁻¹ (-a) := by
    simpa using (Equiv.sum_comp (Equiv.neg (ZMod m))
      (fun a : ZMod m => carryObservable w a * χ⁻¹ a)).symm
  have hneg :
      (∑ a : ZMod m, -carryObservable w a * χ⁻¹ a) =
        -∑ a : ZMod m, carryObservable w a * χ⁻¹ a := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hself :
      (∑ a : ZMod m, carryObservable w a * χ⁻¹ a) =
        -∑ a : ZMod m, carryObservable w a * χ⁻¹ a := by
    calc
      (∑ a : ZMod m, carryObservable w a * χ⁻¹ a) =
          ∑ a : ZMod m, carryObservable w (-a) * χ⁻¹ (-a) := hreindex
      _ = ∑ a : ZMod m, -carryObservable w a * χ⁻¹ a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [carryObservable_neg hm, (inverse_even hχ).eval_neg]
      _ = _ := hneg
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hz : (2 : ℂ) *
      (∑ a : ZMod m, carryObservable w a * χ⁻¹ a) = 0 := by
    calc
      (2 : ℂ) * (∑ a : ZMod m, carryObservable w a * χ⁻¹ a) =
          (∑ a : ZMod m, carryObservable w a * χ⁻¹ a) +
            ∑ a : ZMod m, carryObservable w a * χ⁻¹ a := by ring
      _ = 0 := eq_neg_iff_add_eq_zero.mp hself
  exact (mul_eq_zero.mp hz).resolve_left htwo

/-- Canonical equivalence between units and residues carrying an `IsUnit`
certificate. -/
noncomputable def unitsEquivIsUnit : (ZMod m)ˣ ≃ {x : ZMod m // IsUnit x} where
  toFun u := ⟨u.val, u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := by
    apply Units.ext
    exact u.isUnit.unit_spec
  right_inv x := by
    apply Subtype.ext
    exact x.property.unit_spec

/-- A Dirichlet character pairing over all residues is exactly its unit-group
pairing because the character vanishes on nonunits. -/
theorem sum_character_pairing_eq_units
    (f : ZMod m → ℂ) (χ : Character m) :
    (∑ x : ZMod m, f x * χ x) =
      ∑ u : UnitClass m, f u.val * χ u.val := by
  classical
  let g : ZMod m → ℂ := fun x => f x * χ x
  have hnonunit :
      ∑ x ∈ (Finset.univ : Finset (ZMod m)) with ¬IsUnit x, g x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    unfold g
    rw [χ.map_nonunit hx]
    ring
  have hfilter :
      (∑ x : ZMod m, g x) =
        ∑ x ∈ (Finset.univ : Finset (ZMod m)) with IsUnit x, g x := by
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (ZMod m)) IsUnit g
    rw [hnonunit, add_zero] at h
    exact h.symm
  calc
    (∑ x : ZMod m, f x * χ x) = ∑ x : ZMod m, g x := rfl
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod m)) with IsUnit x, g x := hfilter
    _ = ∑ x : {x : ZMod m // IsUnit x}, g x.val := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset (ZMod m)).filter IsUnit)
        (by intro x; simp) g
    _ = ∑ u : UnitClass m, f u.val * χ u.val := by
      symm
      apply Fintype.sum_equiv unitsEquivIsUnit
      intro u
      rfl

/-- Signed boundary restricted to unit residues. -/
noncomputable def unitBoundarySignal
    (w : ZMod m → ℂ) (u : UnitClass m) : ℂ :=
  signedBoundary w u.val

/-- Complete ordinary Dirichlet flux family of a signed boundary. -/
noncomputable def ordinaryBoundaryFlux
    (w : ZMod m → ℂ) (χ : Character m) : ℂ :=
  characterTransform (unitBoundarySignal w) χ

/-- The cell flux equals the unit-group character transform. -/
theorem cellBoundaryFlux_eq_ordinaryBoundaryFlux
    (w : ZMod m → ℂ) (χ : Character m) :
    cellBoundaryFlux w χ = ordinaryBoundaryFlux w χ := by
  rw [cellBoundaryFlux_eq_boundary_pairing]
  rw [sum_character_pairing_eq_units]
  unfold ordinaryBoundaryFlux characterTransform unitBoundarySignal
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The full carry transform is the ordinary character transform of the unit
carry signal, evaluated at the inverse character. -/
theorem carryTransform_eq_characterTransform
    (w : ZMod m → ℂ) (χ : Character m) :
    carryTransform w χ = characterTransform (unitCarrySignal w) χ⁻¹ := by
  unfold carryTransform
  rw [sum_character_pairing_eq_units]
  unfold characterTransform unitCarrySignal
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Parseval for the complete finite carry spectrum. -/
theorem carryTransform_parseval (w : ZMod m → ℂ) :
    ∑ χ : Character m, ‖carryTransform w χ‖ ^ 2 =
      m.totient * ∑ u : UnitClass m, ‖unitCarrySignal w u‖ ^ 2 := by
  classical
  simp_rw [carryTransform_eq_characterTransform]
  have hreindex :
      (∑ χ : Character m,
          ‖characterTransform (unitCarrySignal w) χ⁻¹‖ ^ 2) =
        ∑ ψ : Character m,
          ‖characterTransform (unitCarrySignal w) ψ‖ ^ 2 := by
    simpa [MulChar.star_eq_inv] using
      (Equiv.sum_comp (Equiv.Perm.star : Equiv.Perm (Character m))
        (fun ψ : Character m =>
          ‖characterTransform (unitCarrySignal w) ψ‖ ^ 2))
  rw [hreindex]
  exact character_parseval (unitCarrySignal w)

/-- Fourier inversion reconstructs the signed boundary at every unit. -/
theorem unitBoundary_reconstruction
    (w : ZMod m → ℂ) (u : UnitClass m) :
    inverseCharacterTransform (ordinaryBoundaryFlux w) u =
      unitBoundarySignal w u := by
  exact inverse_characterTransform (unitBoundarySignal w) u

/-- Two weights have all the same ordinary fluxes exactly when their unit
boundary derivatives agree. -/
theorem ordinaryBoundaryFlux_injective_on_unit_boundary
    (w₁ w₂ : ZMod m → ℂ) :
    (∀ χ : Character m,
      ordinaryBoundaryFlux w₁ χ = ordinaryBoundaryFlux w₂ χ) ↔
    unitBoundarySignal w₁ = unitBoundarySignal w₂ := by
  constructor
  · intro h
    apply characterTransform_injective
    funext χ
    exact h χ
  · intro h χ
    unfold ordinaryBoundaryFlux
    rw [h]

/-- A signed boundary vanishing on units has zero ordinary flux. -/
theorem no_unit_boundary_flux
    (w : ZMod m → ℂ)
    (hunit : ∀ u : UnitClass m, signedBoundary w u.val = 0)
    (χ : Character m) :
    ordinaryBoundaryFlux w χ = 0 := by
  unfold ordinaryBoundaryFlux characterTransform unitBoundarySignal
  apply Finset.sum_eq_zero
  intro u _
  rw [hunit]
  ring

/-- A boundary supported only on nonunits is invisible to every primitive
carry transform. -/
theorem no_unit_boundary_primitive_transform
    (hm : 2 ≤ m) (w : ZMod m → ℂ)
    (hunit : ∀ u : UnitClass m, signedBoundary w u.val = 0)
    {χ : Character m} (hχ : χ.IsPrimitive) :
    carryTransform w χ = 0 := by
  rw [carryBoundary_factorization hm w hχ]
  rw [cellBoundaryFlux_eq_ordinaryBoundaryFlux,
    no_unit_boundary_flux w hunit χ]
  ring

/-- Finite interval Stokes formula. -/
theorem intervalStokes (f : ℕ → ℂ) (start length : ℕ) :
    (∑ i ∈ Finset.range length,
      (f (start + i + 1) - f (start + i))) =
        f (start + length) - f start := by
  simpa [Nat.add_assoc] using
    (Finset.sum_range_sub (fun i => f (start + i)) length)

/-! Exact terminal-boundary ledgers used by the paper's finite checks. -/

/-- Modulus of a padded base-`base` word of the given depth. -/
def terminalModulus (base depth : ℕ) : ℕ := base ^ depth

/-- Boolean membership in the first-digit-equals-last-digit support. -/
def terminalCollisionMember (base depth n : ℕ) : Bool :=
  let modulus := terminalModulus base depth
  let residue := n % modulus
  residue / (base ^ (depth - 1)) == residue % base

/-- Number of marked cells in the terminal collision support. -/
def terminalCollisionPointCount (base depth : ℕ) : ℕ :=
  ((Finset.range (terminalModulus base depth)).filter
    (fun n => terminalCollisionMember base depth n)).card

/-- Formal endpoint count when the terminal support consists of singleton
linear intervals. -/
def terminalFormalBoundaryCount (base depth : ℕ) : ℕ :=
  2 * terminalCollisionPointCount base depth

/-- Whether every marked terminal-collision cell is an isolated cell in the
linear interval from zero through `base ^ depth - 1`. -/
def terminalSupportIsSingleton (base depth : ℕ) : Bool :=
  let modulus := terminalModulus base depth
  (List.range modulus).all fun x =>
    decide (terminalCollisionMember base depth x = true →
      (x = 0 ∨ terminalCollisionMember base depth (x - 1) = false) ∧
      (x + 1 = modulus ∨ terminalCollisionMember base depth (x + 1) = false))

/-- Integer indicator of a Boolean condition. -/
def boolWeight (condition : Bool) : ℤ :=
  if condition then 1 else 0

/-- Cyclic signed boundary weight of the terminal collision support. -/
def terminalBoundaryWeight (base depth x : ℕ) : ℤ :=
  let modulus := terminalModulus base depth
  boolWeight (terminalCollisionMember base depth ((x + modulus - 1) % modulus)) -
    boolWeight (terminalCollisionMember base depth (x % modulus))

/-- Squared norm of the terminal boundary after restriction to units. -/
def terminalUnitBoundaryNorm (base depth : ℕ) : ℤ :=
  let modulus := terminalModulus base depth
  ∑ x ∈ Finset.range modulus,
    if x.Coprime modulus then
      terminalBoundaryWeight base depth x ^ 2
    else 0

/-- Executable conductor-balance test at the immediately lower prime-power
level. -/
def terminalConductorBalance (prime depth : ℕ) : Bool :=
  let coarse := prime ^ (depth - 1)
  (List.range coarse).all fun r =>
    decide (r.Coprime prime →
      (∑ j ∈ Finset.range prime,
        terminalBoundaryWeight prime depth (r + j * coarse)) = 0)

/-- Executable antipodal-oddness test for the unit boundary. -/
def terminalAntipodalOdd (base depth : ℕ) : Bool :=
  let modulus := terminalModulus base depth
  (List.range modulus).all fun x =>
    decide (x.Coprime modulus →
      terminalBoundaryWeight base depth ((modulus - x) % modulus) =
        -terminalBoundaryWeight base depth x)

/-- Complete finite certificate for the terminal-boundary claims used in the
manuscript's exact checks. -/
def terminalBoundaryCertificate (p depth : ℕ) : Bool :=
  decide (terminalCollisionPointCount p depth = p ^ (depth - 1)) &&
  decide (terminalFormalBoundaryCount p depth = 2 * p ^ (depth - 1)) &&
  terminalSupportIsSingleton p depth &&
  decide (terminalUnitBoundaryNorm p depth =
    2 * (p : ℤ) ^ (depth - 2) * (p - 1)) &&
  terminalConductorBalance p depth &&
  terminalAntipodalOdd p depth

set_option maxRecDepth 100000 in
/-- All eight declared prime/depth terminal-boundary certificates pass. -/
theorem terminal_boundary_certificates :
    terminalBoundaryCertificate 3 2 = true ∧
    terminalBoundaryCertificate 3 3 = true ∧
    terminalBoundaryCertificate 5 2 = true ∧
    terminalBoundaryCertificate 5 3 = true ∧
    terminalBoundaryCertificate 7 2 = true ∧
    terminalBoundaryCertificate 7 3 = true ∧
    terminalBoundaryCertificate 11 2 = true ∧
    terminalBoundaryCertificate 11 3 = true := by
  decide

/-! Exact composite-conductor obstruction at base fifteen. -/

/-- Signed contribution of one base-fifteen singleton's two formal endpoints. -/
def baseFifteenEndpointContribution (x a : ℕ) : ℤ :=
  (if x = (16 * a) % 225 then -1 else 0) +
    (if x = (16 * a + 1) % 225 then 1 else 0)

/-- Complete signed boundary weight modulo 225. -/
def baseFifteenBoundaryWeight (x : ℕ) : ℤ :=
  ∑ a ∈ Finset.range 15, baseFifteenEndpointContribution x a

/-- Unit-restricted pushdown of the base-fifteen boundary modulo `d`. -/
def baseFifteenPushdown (d r : ℕ) : ℤ :=
  ∑ x ∈ Finset.range 225,
    if x.Coprime 225 ∧ x % d = r % d then
      baseFifteenBoundaryWeight x
    else 0

/-- Diagonal square ledger at a divisor of 225. -/
def baseFifteenDiagonalLedger (d : ℕ) : ℤ :=
  ∑ r ∈ Finset.range d,
    if r.Coprime d then baseFifteenPushdown d r ^ 2 else 0

/-- Antipodal cross ledger at a divisor of 225. -/
def baseFifteenAntipodalLedger (d : ℕ) : ℤ :=
  ∑ r ∈ Finset.range d,
    if r.Coprime d then
      baseFifteenPushdown d r *
        baseFifteenPushdown d ((d - r) % d)
    else 0

/-- Difference between the diagonal and antipodal ledgers. -/
def baseFifteenLedgerDifference (d : ℕ) : ℤ :=
  baseFifteenDiagonalLedger d - baseFifteenAntipodalLedger d

set_option maxRecDepth 100000 in
/-- Proper-conductor leakage is already nonzero at residue one modulo 45 and
75. -/
theorem base_fifteen_proper_pushdowns_nonzero :
    baseFifteenPushdown 45 1 = 1 ∧
      baseFifteenPushdown 75 1 = 1 := by
  decide

set_option maxRecDepth 100000 in
/-- Complete exact base-fifteen obstruction ledger, including the total moment,
mean, support size, singleton property, and formal boundary count. -/
theorem base_fifteen_conductor_ledger :
    baseFifteenLedgerDifference 15 = 0 ∧
    baseFifteenLedgerDifference 45 = 32 ∧
    baseFifteenLedgerDifference 75 = 32 ∧
    baseFifteenLedgerDifference 225 = 32 ∧
    ((120 : ℤ) * 32 - 40 * 32 - 24 * 32 + 8 * 0) / 2 = 896 ∧
    (896 : ℤ) / 32 = 28 ∧
    terminalCollisionPointCount 15 2 = 15 ∧
    terminalSupportIsSingleton 15 2 = true ∧
    terminalFormalBoundaryCount 15 2 = 30 := by
  decide

end NField.Alignment.CarryBoundarySpectra
