/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetDedekind

/-! # Bernoulli lifts with only the necessary removed-factor coprimality -/

noncomputable section

namespace NField.Alignment.CommonResetBernoulliLifts

open scoped BigOperators
open DedekindReciprocity DedekindInverseResidueTransform RademacherThreeTerm

theorem sum_residue_values {R : Type*} [AddCommMonoid R] {m : ℕ} [NeZero m] (f : ℕ → R) :
    (∑ a : ZMod m, f a.val) = ∑ a ∈ Finset.range m, f a := by
  rw [← (ZMod.finEquiv m).toEquiv.sum_comp (fun a : ZMod m => f a.val)]
  change (∑ i : Fin m, f (ZMod.finEquiv m i).val) = _
  simp only [ConductorDepthSawtooth.finEquiv_eq_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Fin.isLt _)]
  exact Fin.sum_univ_eq_sum_range f m

theorem sum_coprime_affine {R : Type*} [AddCommMonoid R] {d c : ℕ}
    (hd : 0 < d) (hc : c.Coprime d) (B : ℕ) (f : ℕ → R) :
    (∑ a ∈ Finset.range d, f ((B+c*a)%d)) = ∑ a ∈ Finset.range d, f a := by
  letI : NeZero d := ⟨hd.ne'⟩
  let e : ZMod d ≃ ZMod d := (ZMod.unitOfCoprime c hc).mulLeft.trans (Equiv.addLeft (B : ZMod d))
  have he := Equiv.sum_comp e (fun a : ZMod d => f a.val)
  have hp (a : ZMod d) : (e a).val = (B+c*a.val)%d := by
    dsimp [e]
    simp only [Units.mulLeft_apply]
    rw [ZMod.coe_unitOfCoprime]
    nth_rw 1 [← ZMod.natCast_zmod_val a]
    rw [← Nat.cast_mul, ← Nat.cast_add, ZMod.val_natCast]
  simp only [hp] at he
  rw [sum_residue_values (fun a => f ((B+c*a)%d)), sum_residue_values f] at he
  exact he

/-- Title: `Bernoulli multiplication requires coprimality only with the removed lift factor`. -/
theorem sawtooth_coprime_lifts {d k c : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hc : c.Coprime d) (y : ℕ) :
    (∑ a ∈ Finset.range d, rationalSawtooth (c*(y+a*k)) (d*k)) = rationalSawtooth (c*y) k := by
  let r := (c*y)%k
  let B := (c*y)/k
  have hcy : r+B*k = c*y := by dsimp [r, B]; simpa only [Nat.mul_comm] using Nat.mod_add_div (c*y) k
  have hpoint (a : ℕ) : rationalSawtooth (c*(y+a*k)) (d*k) =
      rationalSawtooth (r+((B+c*a)%d)*k) (d*k) := by
    apply rationalSawtooth_eq_of_mod_eq
    have hfirst : c*(y+a*k) = r+(B+c*a)*k := by nlinarith [hcy]
    rw [hfirst]
    have he : r+(B+c*a)*k = (r+((B+c*a)%d)*k)+(d*k)*((B+c*a)/d) := by
      calc
        _ = r+((B+c*a)%d+d*((B+c*a)/d))*k := by rw [Nat.mod_add_div]
        _ = _ := by ring
    rw [he, Nat.add_mul_mod_self_left]
  simp only [hpoint]
  rw [sum_coprime_affine hd hc B (fun a => rationalSawtooth (r+a*k) (d*k)),
    sum_rationalSawtooth_lifts hd hk (Nat.mod_lt (c*y) hk)]
  simp only [r, rationalSawtooth, Nat.mod_mod]

theorem coefficient_swap (x y m : ℕ) :
    arithmeticCoefficientDedekindTerm x y m = arithmeticCoefficientDedekindTerm y x m := by
  unfold arithmeticCoefficientDedekindTerm
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

theorem coefficient_unit_scale {c m : ℕ} (hm : 0 < m) (hc : c.Coprime m) (x y : ℕ) :
    arithmeticCoefficientDedekindTerm (c*x) (c*y) m = arithmeticCoefficientDedekindTerm x y m := by
  unfold arithmeticCoefficientDedekindTerm
  have he := sum_coprime_affine hm hc 0 (fun a => rationalSawtooth (x*a) m*rationalSawtooth (y*a) m)
  simp only [zero_add] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro a _
  have hmod (z : ℕ) : ((c*z)*a)%m = (z*((c*a)%m))%m := by
    rw [show (c*z)*a = z*(c*a) by ring]
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod]
    simp only [Nat.mod_mod]
  congr 1 <;> exact rationalSawtooth_eq_of_mod_eq (hmod _)

/-- Title: `Removing a common numerator and modulus factor preserves the exact coefficient sum`. -/
theorem coefficient_strip {c d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hc : c.Coprime d) (x : ℕ) :
    arithmeticCoefficientDedekindTerm c (d*x) (d*k) = arithmeticCoefficientDedekindTerm c x k := by
  unfold arithmeticCoefficientDedekindTerm
  rw [sum_range_mul_blocks hk]
  apply Finset.sum_congr rfl
  intro y hy
  have hpoint (a : ℕ) : rationalSawtooth ((d*x)*(y+a*k)) (d*k) = rationalSawtooth (x*y) k := by
    rw [show (d*x)*(y+a*k) = d*(x*(y+a*k)) by ring, rationalSawtooth_scale hd hk]
    apply rationalSawtooth_eq_of_mod_eq
    rw [show x*(y+a*k) = x*y+k*(x*a) by ring, Nat.add_mul_mod_self_left]
  simp only [hpoint, ← Finset.sum_mul, sawtooth_coprime_lifts hd hk hc]

theorem coefficient_common_scale {d k : ℕ} (hd : 0 < d) (hk : 0 < k) (x y : ℕ) :
    arithmeticCoefficientDedekindTerm (d*x) (d*y) (d*k) =
      (d : ℚ)*arithmeticCoefficientDedekindTerm x y k := by
  unfold arithmeticCoefficientDedekindTerm
  rw [sum_range_mul_blocks hk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hs (x b : ℕ) : rationalSawtooth ((d*x)*(a+b*k)) (d*k) = rationalSawtooth (x*a) k := by
    rw [show (d*x)*(a+b*k) = d*(x*(a+b*k)) by ring, rationalSawtooth_scale hd hk]
    apply rationalSawtooth_eq_of_mod_eq
    rw [show x*(a+b*k) = x*a+k*(x*b) by ring, Nat.add_mul_mod_self_left]
  simp only [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end NField.Alignment.CommonResetBernoulliLifts
