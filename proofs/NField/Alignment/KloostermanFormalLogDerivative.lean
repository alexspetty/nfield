/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanFiniteEulerProduct
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal logarithmic derivatives and finite Euler products

All identities are coefficientwise formal power-series identities. No
analytic logarithm or convergence statement is used.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanFormalLogDerivative
open scoped BigOperators Classical
open PowerSeries

noncomputable def logarithmicDerivative (f : PowerSeries ℂ) : PowerSeries ℂ :=
  X * derivative ℂ f * f⁻¹

theorem constantCoeff_logarithmicDerivative (f : PowerSeries ℂ) :
    constantCoeff (logarithmicDerivative f) = 0 := by
  simp [logarithmicDerivative]

theorem logarithmicDerivative_mul (f g : PowerSeries ℂ)
    (hf : constantCoeff f ≠ 0) (hg : constantCoeff g ≠ 0) :
    logarithmicDerivative (f*g) = logarithmicDerivative f + logarithmicDerivative g := by
  unfold logarithmicDerivative
  rw [PowerSeries.mul_inv_rev,Derivation.leibniz]
  have hff := PowerSeries.mul_inv_cancel f hf
  have hgg := PowerSeries.mul_inv_cancel g hg
  simp only [smul_eq_mul]
  calc
    _ = X * derivative ℂ g * g⁻¹ * (f*f⁻¹) +
      X * derivative ℂ f * f⁻¹ * (g*g⁻¹) := by ring
    _ = _ := by rw [hff,hgg]; ring

@[simp] theorem logarithmicDerivative_one : logarithmicDerivative (1 : PowerSeries ℂ) = 0 := by
  simp [logarithmicDerivative]

theorem logarithmicDerivative_prod {ι : Type*} (s : Finset ι)
    (f : ι → PowerSeries ℂ) (hf : ∀ i ∈ s, constantCoeff (f i) ≠ 0) :
    logarithmicDerivative (∏ i ∈ s, f i) = ∑ i ∈ s, logarithmicDerivative (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, constantCoeff (f j) ≠ 0 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.sum_insert hi,logarithmicDerivative_mul
      _ _ (hf i (Finset.mem_insert_self _ _)) (by simpa using Finset.prod_ne_zero_iff.mpr hs),ih hs]

/-- Multiplication by X after differentiation weights the n-th coefficient by n. -/
theorem coeff_X_derivative (f : PowerSeries ℂ) (n : ℕ) :
    coeff n (X * derivative ℂ f) = (n:ℂ)*coeff n f := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul,coeff_derivative]; push_cast; ring

/-- If a series equals one through degree N, its formal logarithmic
derivative is zero through that degree. -/
theorem coeff_logarithmicDerivative_eq_zero (f : PowerSeries ℂ) (N n : ℕ)
    (hf : ∀ k≤N, coeff k f = if k=0 then 1 else 0) (hn : n≤N) :
    coeff n (logarithmicDerivative f) = 0 := by
  unfold logarithmicDerivative
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [coeff_X_derivative,hf ij.1 (by omega)]
  by_cases h0 : ij.1=0 <;> simp [h0]

/-- The geometric inverse, with exact coefficients in multiples of d. -/
noncomputable def geometricSeries (w : ℂ) (d : ℕ) : PowerSeries ℂ :=
  mk fun n => if d ∣ n then w^(n/d) else 0

theorem one_sub_mul_geometricSeries (w : ℂ) (d : ℕ) (hd : 0<d) :
    (1-C w*X^d)*geometricSeries w d = 1 := by
  ext n
  simp only [sub_mul,one_mul,mul_assoc,map_sub,coeff_C_mul,coeff_X_pow_mul',
    geometricSeries,coeff_mk,coeff_one]
  by_cases hn : d≤n
  · rw [if_pos hn]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left,Nat.dvd_add_self_left,Nat.add_div_left _ hd]
    by_cases hk : d ∣ k <;> simp [hk,ne_of_gt hd,pow_add,mul_comm]
  · rw [if_neg hn,mul_zero,sub_zero]
    by_cases h0 : n=0
    · subst n; simp
    · have hdn : ¬ d ∣ n := by
        intro h
        exact hn (Nat.le_of_dvd (by omega) h)
      simp [hdn,h0]

theorem geometricSeries_eq_inverse (w : ℂ) (d : ℕ) (hd : 0<d) :
    geometricSeries w d = (1-C w*X^d : PowerSeries ℂ)⁻¹ := by
  have hc : constantCoeff (1-C w*X^d : PowerSeries ℂ) ≠ 0 := by
    simp [ne_of_gt hd]
  have h := one_sub_mul_geometricSeries w d hd
  have hi := PowerSeries.inv_mul_cancel (1-C w*X^d : PowerSeries ℂ) hc
  calc
    geometricSeries w d = ((1-C w*X^d : PowerSeries ℂ)⁻¹ *
      (1-C w*X^d)) * geometricSeries w d := by rw [hi,one_mul]
    _ = _ := by rw [mul_assoc,h,mul_one]

theorem X_derivative_eulerFactor (w : ℂ) (d : ℕ) (hd : 0<d) :
    X * derivative ℂ (1-C w*X^d) = -C ((d:ℂ)*w)*X^d := by
  ext n
  rw [coeff_X_derivative]
  simp only [map_sub,coeff_one,coeff_C_mul,coeff_X_pow,neg_mul,map_neg]
  by_cases he : n=d
  · subst n
    simp [ne_of_gt hd]
  · by_cases h0 : n=0 <;> simp [he,h0,Ne.symm (ne_of_gt hd)]

/-- The contribution of one Euler factor, including zero weights. -/
theorem coeff_logarithmicDerivative_eulerFactor (w : ℂ) (d : ℕ) (hd : 0<d)
    (n : ℕ) (hn : 0<n) :
    coeff n (logarithmicDerivative (1-C w*X^d)) =
      if d ∣ n then -(d:ℂ)*w^(n/d) else 0 := by
  rw [logarithmicDerivative,X_derivative_eulerFactor w d hd,
    ← geometricSeries_eq_inverse w d hd]
  simp only [neg_mul,map_neg,mul_assoc,coeff_C_mul,coeff_X_pow_mul',
    geometricSeries,coeff_mk]
  by_cases hdn : d≤n
  · rw [if_pos hdn]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hdn
    simp only [Nat.add_sub_cancel_left,Nat.dvd_add_self_left,Nat.add_div_left _ hd]
    by_cases hk : d ∣ k
    · simp only [hk,if_true,pow_add,pow_one]; ring
    · simp [hk]
  · have hdiv : ¬ d ∣ n := fun h => hdn (Nat.le_of_dvd hn h)
    simp [hdn,hdiv]

end NField.Alignment.KloostermanFormalLogDerivative
