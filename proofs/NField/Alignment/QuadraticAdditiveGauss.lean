/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-!
# Norm of the actual additive quadratic Gauss sum

Multiply the literal sum by its conjugate and translate one variable.
Primitive character orthogonality kills every nonzero difference. The
linear coefficient is arbitrary and the quadratic coefficient is nonzero.
-/

set_option autoImplicit false
namespace NField.Alignment.QuadraticAdditiveGauss
open scoped BigOperators Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The actual finite additive quadratic exponential sum. -/
noncomputable def quadraticSum (ψ : AddChar F ℂ) (a b : F) : ℂ :=
  ∑ x : F, ψ (a*x^2+b*x)

/-- The squared modulus is computed by an exact double-sum identity and
primitive additive orthogonality, including arbitrary linear phase. -/
theorem quadratic_sum_mul_conj (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (ha : a≠0) (h2 : (2:F)≠0) :
    quadraticSum ψ a b*(starRingEnd ℂ) (quadraticSum ψ a b) = Fintype.card F := by
  have he : quadraticSum ψ a b*(starRingEnd ℂ) (quadraticSum ψ a b) =
      ∑ x : F, ∑ y : F, ψ ((a*x^2+b*x)-(a*y^2+b*y)) := by
    unfold quadraticSum
    rw [map_sum,Finset.sum_mul]
    simp_rw [Finset.mul_sum,← AddChar.map_neg_eq_conj,← AddChar.map_add_eq_mul]
    simp only [sub_eq_add_neg]
  rw [he,Finset.sum_comm]
  have ht (y : F) : (∑ x : F, ψ ((a*x^2+b*x)-(a*y^2+b*y))) =
      ∑ h : F, ψ (a*h^2+b*h)*ψ (y*(2*a*h)) := by
    rw [← Equiv.sum_comp (Equiv.addRight y) (fun x : F => ψ ((a*x^2+b*x)-(a*y^2+b*y)))]
    apply Finset.sum_congr rfl
    intro h _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    change (a*(h+y)^2+b*(h+y))-(a*y^2+b*y) = _
    ring
  simp_rw [ht]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,AddChar.sum_mulShift _ hψ]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro h _ hh
    rw [if_neg (mul_ne_zero (mul_ne_zero h2 ha) hh)]
    simp
  · simp

/-- The actual quadratic sum has norm exactly sqrt(card(F)) when the
quadratic coefficient and characteristic two obstruction are nonzero. -/
theorem norm_quadratic_sum (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (ha : a≠0) (h2 : (2:F)≠0) :
    ‖quadraticSum ψ a b‖ = Real.sqrt (Fintype.card F:ℝ) := by
  have h := congrArg norm (quadratic_sum_mul_conj ψ hψ a b ha h2)
  rw [norm_mul,Complex.norm_conj,Complex.norm_natCast] at h
  have hs : ‖quadraticSum ψ a b‖^2=(Fintype.card F:ℝ) := by nlinarith
  rw [← hs,Real.sqrt_sq (norm_nonneg _)]

/-- At an odd prime, the literal standard-character quadratic sum has
norm sqrt(p), for every linear coefficient and nonzero quadratic coefficient. -/
theorem norm_prime_quadratic_sum (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (a b : ZMod p) (ha : a≠0) :
    ‖quadraticSum ZMod.stdAddChar a b‖=Real.sqrt p := by
  have h2 : (2:ZMod p)≠0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
  simpa only [ZMod.card] using norm_quadratic_sum ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar p) a b ha h2

end NField.Alignment.QuadraticAdditiveGauss
