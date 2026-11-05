/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeFamily

/-!
# Literal odd and primitive odd pair projectors

Unit equality is equality modulo the indicated modulus. previousUnit at
N=2 is the canonical reduction from the prime-square unit group to the
prime unit group. The actual complete primitive odd family is retained.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MagnitudeKernelDisplays
open scoped BigOperators
open CollisionCharacterStructure PrimitiveOddBoundaryMean PrimeSquareMagnitudeFamily
attribute [local instance] Classical.propDecidable

theorem odd_projector {q : ℕ} [NeZero q] (u v : UnitClass q) :
    (∑ χ : Character q with χ.Odd, χ u.val*star (χ v.val)) =
      (q.totient : ℂ)/2*((if u=v then 1 else 0)-(if -u=v then 1 else 0)) := by
  have h := oddCharacterKernel_eq u v
  change (∑ χ : Character q with χ.Odd, χ u.val*star (χ v.val)) = _ at h
  convert h using 1
  ring

theorem primitive_odd_prime_square_projector {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (u v : UnitClass (p^2)) :
    (∑ χ : PrimitiveOddFamily p, χ.val u.val*star (χ.val v.val)) =
      (p : ℂ)*(p-1)/2*((if u=v then 1 else 0)-(if -u=v then 1 else 0)) -
      ((p : ℂ)-1)/2*
        ((if previousUnit (N := 2) (by norm_num) u = previousUnit (N := 2) (by norm_num) v then 1 else 0)-
         (if -(previousUnit (N := 2) (by norm_num) u) = previousUnit (N := 2) (by norm_num) v then 1 else 0)) := by
  have h := primitiveOddKernel_eq_primePowerKernel hp (by norm_num : 2 ≤ 2) u v
  unfold primitiveOddKernel at h
  rw [Finset.sum_subtype (p := fun χ : Character (p^2) => χ.IsPrimitive ∧ χ.Odd)
    (F := familyFintype p) _ (by simp) (fun χ => χ u.val*star (χ v.val))] at h
  rw [Nat.totient_prime_pow hp (by norm_num : 0 < 2)] at h
  norm_num only [Nat.reduceSub,pow_one] at h
  rw [Nat.totient_prime hp] at h
  push_cast [Nat.cast_sub hp.one_lt.le] at h
  convert h using 1
  ring

end NField.Alignment.MagnitudeKernelDisplays
