/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionReciprocalBudget
import NField.Alignment.CollisionBoundaryTesting

/-!
# The literal gcd reset observable

The existing reduced-address bijection is applied to reciprocal products.
Its finite primitive rows are exactly the divisor reset. The final term
at j=n contributes one, including the case n=1.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionGcdResetDisplay

open scoped BigOperators
open CollisionReciprocalBudget CollisionRemainderDynamics SecondaryCapacityLedger
open CollisionBoundaryTesting CollisionResetIntegrability ProfiniteRemainderMeasure

theorem divisor_reset_primitive_addresses (n : ℕ) :
    (∑ k ∈ n.divisors, (k : ℝ)*collisionWeight k)=
      ∑ p ∈ primitiveAddresses n, 1/((p.1 : ℝ)*(p.2 : ℝ)) := by
  rw [primitiveAddresses,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
  unfold collisionWeight reducedHarmonicStar
  simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  rw [← Finset.sum_mul]
  field_simp

theorem interior_gcd_sum_reset {n : ℕ} (hn : 0 < n) :
    (∑ a ∈ Finset.Ico 1 n, (a.gcd n : ℝ)^2/((a : ℝ)*(n : ℝ)))=
      ∑ k ∈ n.divisors, (k : ℝ)*collisionWeight k := by
  rw [divisor_reset_primitive_addresses]
  apply Finset.sum_bij (fun a _ => reducedAddress n a)
  · intro a ha
    exact reducedAddress_mem ha
  · intro a ha b hb he
    have hr := congrArg (fun p : Σ _ : ℕ, ℕ => (n/p.1)*p.2) he
    simpa only [reducedAddress_restore ha,reducedAddress_restore hb] using hr
  · intro p hp
    exact ⟨(n/p.1)*p.2,(primitiveAddress_restore p hp).1,(primitiveAddress_restore p hp).2⟩
  · intro a ha
    have hap := (Finset.mem_Ico.mp ha).1
    have hg : 0 < a.gcd n := Nat.gcd_pos_of_pos_left n hap
    have hgR : (a.gcd n : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [reducedAddress]
    rw [Nat.cast_div (Nat.gcd_dvd_right a n) hgR,Nat.cast_div (Nat.gcd_dvd_left a n) hgR]
    field_simp

theorem literal_gcd_reset_identity {n : ℕ} (hn : 0 < n) :
    1+resetFunction (integerPhase n)=
      ∑ j ∈ Finset.Icc 1 n, (j.gcd n : ℝ)^2/((j : ℝ)*(n : ℝ)) := by
  have hset : Finset.Icc 1 n=insert n (Finset.Ico 1 n) := by
    ext a
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ico]
    omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hset,Finset.sum_insert (by simp),Nat.gcd_self,
    pow_two,div_self (mul_ne_zero hnR hnR),interior_gcd_sum_reset hn,resetFunction_integer hn]

end NField.Alignment.CollisionGcdResetDisplay
