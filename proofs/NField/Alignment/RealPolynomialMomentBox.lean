/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealBilinearMoment
import NField.Alignment.ReciprocalFirstDerivativeBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-! # Literal integer power vectors and real polynomial frequency boxes -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealPolynomialMomentBox
open scoped BigOperators Classical ComplexConjugate
open RealBilinearMoment VinogradovDiagonal VinogradovMomentFibers KaratsubaFiberEnergy

def realCharacter : AddChar ℝ ℂ where
  toFun t := fourier 1 (t : AddCircle (1 : ℝ))
  map_zero_eq_one' := by simp
  map_add_eq_mul' := ReciprocalFirstDerivativeBound.character_add

theorem realCharacter_norm (t : ℝ) : ‖realCharacter t‖ = 1 := Circle.norm_coe _

def bilinearCharacter {n : ℕ} (β : Fin n → ℝ) (u : Fin n → ℤ) :
    AddChar (Fin n → ℤ) ℂ :=
  realCharacter.compAddMonoidHom {
    toFun v := ∑ j, β j*(u j : ℝ)*(v j : ℝ)
    map_zero' := by simp
    map_add' v w := by simp [mul_add, Finset.sum_add_distrib] }

theorem bilinearCharacter_apply {n : ℕ} (β : Fin n → ℝ) (u v : Fin n → ℤ) :
    bilinearCharacter β u v = realCharacter (∑ j, β j*(u j : ℝ)*(v j : ℝ)) := rfl

theorem bilinearCharacter_norm {n : ℕ} (β : Fin n → ℝ) (u v : Fin n → ℤ) :
    ‖bilinearCharacter β u v‖ = 1 := realCharacter_norm _

theorem bilinearCharacter_symm {n : ℕ} (β : Fin n → ℝ) (u v : Fin n → ℤ) :
    bilinearCharacter β u v = bilinearCharacter β v u := by
  simp only [bilinearCharacter_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

def powerVector (n : ℕ) (x : ℤ) : Fin n → ℤ := fun j => x^(j.val+1)

def momentBox (H s n : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc (-(s*(H:ℤ)^(j.val+1))) (s*(H:ℤ)^(j.val+1))

theorem tuple_power_sum_bounds (H s n : ℕ)
    (u : IntegerTuple (Finset.Icc 1 (H:ℤ)) s) (j : Fin n) :
    0 ≤ (∑ i, (u i).val^(j.val+1)) ∧
      (∑ i, (u i).val^(j.val+1)) ≤ s*(H:ℤ)^(j.val+1) := by
  have hlo (i : Fin s) : 0 ≤ (u i).val :=
    le_trans (by norm_num) (Finset.mem_Icc.mp (u i).property).1
  refine ⟨Finset.sum_nonneg (fun i _ => pow_nonneg (hlo i) _), ?_⟩
  calc
    _ ≤ ∑ _i : Fin s, (H:ℤ)^(j.val+1) := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (hlo i) (Finset.mem_Icc.mp (u i).property).2 _
    _ = _ := by simp

theorem tupleDifference_mem_box (H s n : ℕ)
    (uv : IntegerTuple (Finset.Icc 1 (H:ℤ)) s ×
      IntegerTuple (Finset.Icc 1 (H:ℤ)) s) :
    tupleDifference (fun x : {x // x ∈ Finset.Icc 1 (H:ℤ)} => powerVector n x.val)
      s uv ∈ momentBox H s n := by
  apply Fintype.mem_piFinset.mpr
  intro j
  obtain ⟨hu0,hu⟩ := tuple_power_sum_bounds H s n uv.1 j
  obtain ⟨hv0,hv⟩ := tuple_power_sum_bounds H s n uv.2 j
  simp only [tupleDifference, Pi.sub_apply, Finset.sum_apply, powerVector, Finset.mem_Icc]
  constructor <;> omega

theorem tupleDifference_fiber_bound (S : Finset ℤ) (s n : ℕ) (t : Fin n → ℤ) :
    fiberCount (tupleDifference (fun x : {x // x ∈ S} => powerVector n x.val) s) t ≤
      momentCount S s n := by
  have he : fiberCount (tupleDifference (fun x : {x // x ∈ S} => powerVector n x.val) s) t =
      shiftedMomentCount S s n (-t) := by
    unfold fiberCount shiftedMomentCount
    congr 1
    ext uv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, tupleDifference,
      momentVector, powerVector, funext_iff, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      Finset.sum_apply]
    constructor <;> intro h j <;> have := h j <;> omega
  rw [he]
  exact shiftedMomentCount_le_momentCount S s n (-t)

def polynomialBilinear {n : ℕ} (β : Fin n → ℝ) (H : ℕ) : ℂ :=
  ∑ x : {x // x ∈ Finset.Icc 1 (H:ℤ)},
    ∑ y : {y // y ∈ Finset.Icc 1 (H:ℤ)},
      realCharacter (∑ j, β j*((x.val*y.val : ℤ):ℝ)^(j.val+1))

theorem polynomialBilinear_eq {n : ℕ} (β : Fin n → ℝ) (H : ℕ) :
    polynomialBilinear β H =
      ∑ x : {x // x ∈ Finset.Icc 1 (H:ℤ)},
        ∑ y : {y // y ∈ Finset.Icc 1 (H:ℤ)},
          bilinearCharacter β (powerVector n x.val) (powerVector n y.val) := by
  unfold polynomialBilinear
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [bilinearCharacter_apply, powerVector, Int.cast_pow, Int.cast_mul, mul_pow,
    mul_assoc]

theorem polynomial_bilinear_moment_bound {n : ℕ} (β : Fin n → ℝ)
    (H s : ℕ) (hs : 1 ≤ s) :
    ‖polynomialBilinear β H‖^(4*s^2) ≤
      (H:ℝ)^(4*s*(2*s-1))*(momentCount (Finset.Icc 1 (H:ℤ)) s n : ℝ)^2*
        ∑ v ∈ momentBox H s n, ‖∑ u ∈ momentBox H s n, bilinearCharacter β u v‖ := by
  rw [polynomialBilinear_eq]
  have h := bilinear_moment_bound (bilinearCharacter β)
    (bilinearCharacter_norm β) (bilinearCharacter_symm β)
    (fun x : {x // x ∈ Finset.Icc 1 (H:ℤ)} => powerVector n x.val) s hs
    (momentBox H s n) (momentCount (Finset.Icc 1 (H:ℤ)) s n)
    (Nat.cast_nonneg _) (tupleDifference_mem_box H s n)
    (fun t _ => by exact_mod_cast tupleDifference_fiber_bound (Finset.Icc 1 (H:ℤ)) s n t)
  simpa only [Fintype.card_coe, Int.card_Icc, add_sub_cancel_right, Int.toNat_natCast] using h

end NField.Alignment.RealPolynomialMomentBox
