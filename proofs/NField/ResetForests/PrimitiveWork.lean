/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrimitiveArithmetic
/-! # Actual continuous work of the primitive midpoint fields

The level-one field is retained. Every finite mixed term is integrated
before the two divisor inversions impose orthogonality.
-/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators
open MeasureTheory NField.Alignment CollisionRampEnergy CommonResetGram

theorem scaled_saw_product_integrable {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (a b : ℝ) :
    IntervalIntegrable (fun x => scaledSaw k x*scaledSaw m x) volume a b := by
  have he : (fun x => scaledSaw k x*scaledSaw m x)=
      fun x => (4*(k : ℝ)*(m : ℝ))*(midpointRow k x*midpointRow m x) := by
    funext x
    unfold scaledSaw
    ring
  rw [he]
  exact (midpointProduct_intervalIntegrable hk hm a b).const_mul _

theorem scaled_saw_work {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    (∫ x in (0 : ℝ)..1, scaledSaw k x*scaledSaw m x)=(k.gcd m : ℝ)^2/3 := by
  have he : (fun x => scaledSaw k x*scaledSaw m x)=
      fun x => (4*(k : ℝ)*(m : ℝ))*(midpointRow k x*midpointRow m x) := by
    funext x
    unfold scaledSaw
    ring
  rw [he, intervalIntegral.integral_const_mul, midpoint_ramp_gram hk hm]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  norm_num

theorem primitive_right_product (k n : ℕ) (x : ℝ) :
    scaledSaw k x*primitiveField n x=
      ∑ d ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius d.1 : ℝ)*
        (scaledSaw k x*scaledSaw d.2 x) := by
  simp only [primitiveField, ← Int.cast_smul_eq_zsmul ℝ, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem scaled_primitive_integrable {k : ℕ} (hk : 0 < k) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => scaledSaw k x*primitiveField n x) volume a b := by
  simp_rw [primitive_right_product]
  have hint (d : ℕ × ℕ) (hd : d ∈ n.divisorsAntidiagonal) :
      IntervalIntegrable (fun x => (ArithmeticFunction.moebius d.1 : ℝ)*
        (scaledSaw k x*scaledSaw d.2 x)) volume a b :=
    (scaled_saw_product_integrable hk
      (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hd)) a b).const_mul _
  exact ⟨integrable_finsetSum _ (fun d hd => (hint d hd).1),
    integrable_finsetSum _ (fun d hd => (hint d hd).2)⟩

theorem scaled_primitive_work {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..1, scaledSaw k x*primitiveField n x)=
      if n ∣ k then jordanMass n/3 else 0 := by
  let f : ℕ → ℝ := fun d => if d ∣ k then jordanMass d/3 else 0
  have hf : ∀ m > 0, (∑ d ∈ m.divisors, f d)=
      ∫ x in (0 : ℝ)..1, scaledSaw k x*scaledSaw m x := by
    intro m hm
    rw [scaled_saw_work hk hm]
    have h := congrArg (fun r : ℝ => r/3) (gcd_jordan_divisor_sum hk hm)
    simpa only [f, Finset.sum_div, ite_div, zero_div] using h
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := f) (g := fun m => ∫ x in (0 : ℝ)..1, scaledSaw k x*scaledSaw m x)).mp hf n hn
  simp_rw [primitive_right_product]
  rw [intervalIntegral.integral_finsetSum (fun d hd =>
    (scaled_saw_product_integrable hk
      (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hd)) 0 1).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  exact hi

theorem primitive_left_product (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    primitiveField n x*f x=
      ∑ d ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius d.1 : ℝ)*
        (scaledSaw d.2 x*f x) := by
  simp only [primitiveField, ← Int.cast_smul_eq_zsmul ℝ, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem primitive_product_integrable (n m : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => primitiveField n x*primitiveField m x) volume a b := by
  simp_rw [primitive_left_product n (primitiveField m)]
  have hint (d : ℕ × ℕ) (hd : d ∈ n.divisorsAntidiagonal) :
      IntervalIntegrable (fun x => (ArithmeticFunction.moebius d.1 : ℝ)*
        (scaledSaw d.2 x*primitiveField m x)) volume a b :=
    (scaled_primitive_integrable
      (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hd)) m a b).const_mul _
  exact ⟨integrable_finsetSum _ (fun d hd => (hint d hd).1),
    integrable_finsetSum _ (fun d hd => (hint d hd).2)⟩

theorem primitive_field_gram {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∫ x in (0 : ℝ)..1, primitiveField n x*primitiveField m x)=
      if n=m then jordanMass n/3 else 0 := by
  let f : ℕ → ℝ := fun d => if d=m then jordanMass m/3 else 0
  have hf : ∀ k > 0, (∑ d ∈ k.divisors, f d)=
      ∫ x in (0 : ℝ)..1, scaledSaw k x*primitiveField m x := by
    intro k hk
    rw [scaled_primitive_work hk hm]
    simp only [f, Finset.sum_ite_eq']
    by_cases hd : m ∣ k
    · rw [if_pos (Nat.mem_divisors.mpr ⟨hd,hk.ne'⟩), if_pos hd]
    · rw [if_neg (fun h => hd (Nat.mem_divisors.mp h).1), if_neg hd]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := f) (g := fun k => ∫ x in (0 : ℝ)..1, scaledSaw k x*primitiveField m x)).mp hf n hn
  have he : (∫ x in (0 : ℝ)..1, primitiveField n x*primitiveField m x)=f n := by
    simp_rw [primitive_left_product n (primitiveField m)]
    rw [intervalIntegral.integral_finsetSum (fun d hd =>
      (scaled_primitive_integrable
        (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hd)) m 0 1).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
    exact hi
  by_cases heq : n=m <;> simpa only [f,heq,if_true,if_false] using he

end NField.ResetForests.PrimitiveCoordinates
