/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimePowerMajorant
import NField.Alignment.CollisionCylinderMeans
import NField.Alignment.CollisionAmplitudeTail
import NField.Alignment.CollisionBoundaryTesting

/-!
# The uniform prime-power reset and alignment bound

The exact divisor reset and conductor formula reduce both observables to
positive prime-power rows. Their logarithmic bounds have the same
summable majorant, with one constant for every prime and every exponent.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimePowerBoundDisplay

open scoped BigOperators
open CollisionPrimePowerMajorant CollisionCylinderMeans CollisionAmplitudeTail
open CollisionBoundaryTesting CollisionResetIntegrability ProfiniteRemainderMeasure
open CollisionRemainderDynamics CollisionMassReadout CollisionJordanVariance CollisionPositiveLogTail

theorem prime_power_reset_sum {p : ℕ} (hp : p.Prime) (v : ℕ) :
    resetFunction (integerPhase (p^v : ℕ))=
      ∑ j ∈ Finset.range v, (p^(j+1) : ℝ)*collisionWeight (p^(j+1)) := by
  rw [resetFunction_integer (pow_pos hp.pos _),Nat.sum_divisors_prime_pow hp,Finset.sum_range_succ']
  simp only [Nat.pow_zero,Nat.cast_one,collisionWeight_one,mul_zero,add_zero,Nat.cast_pow]

theorem prime_power_alignment_sum {p : ℕ} (hp : p.Prime) (v : ℕ) :
    alignmentConstant (p^v)=(1/3 : ℝ)*
      ∑ j ∈ Finset.range v, (Nat.totient (p^(j+1)) : ℝ)*amplitude (p^(j+1)) := by
  rw [alignmentConstant_conductors (pow_pos hp.pos _),Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ']
  simp only [Nat.pow_zero,show ¬2 ≤ (1 : ℕ) by omega,if_false,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_pos (hp.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero j) p))]

theorem reset_coefficient_log_bound {q : ℕ} (hq : 2 ≤ q) :
    (q : ℝ)*collisionWeight q ≤ (1+Real.log q)/(q : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  calc
    _ ≤ (q : ℝ)*((1+Real.log q)/(q : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (collisionWeight_log_bound (by omega)) (Nat.cast_nonneg q)
    _ = _ := by field_simp

theorem conductor_coefficient_log_bound {q : ℕ} (hq : 2 ≤ q) :
    (Nat.totient q : ℝ)*amplitude q ≤ amplitudeLogConstant*(1+Real.log q)/(q : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have ht : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  calc
    _ ≤ (q : ℝ)*amplitude q := mul_le_mul_of_nonneg_right ht (amplitude_nonneg q)
    _ ≤ (q : ℝ)*(amplitudeLogConstant*positiveLogKernel q) :=
      mul_le_mul_of_nonneg_left (amplitude_log_bound hq) (Nat.cast_nonneg q)
    _ = _ := by unfold positiveLogKernel; field_simp

theorem prime_power_reset_bound {p : ℕ} (hp : p.Prime) (v : ℕ) :
    resetFunction (integerPhase (p^v : ℕ)) ≤ 4*(1+Real.log p)/(p : ℝ) := by
  rw [prime_power_reset_sum hp]
  apply le_trans _ (prime_power_majorant_sum (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p) v)
  apply Finset.sum_le_sum
  intro j hj
  have hq : 2 ≤ p^(j+1) := hp.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero j) p)
  simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one] using reset_coefficient_log_bound hq

theorem prime_power_alignment_bound {p : ℕ} (hp : p.Prime) (v : ℕ) :
    alignmentConstant (p^v) ≤ (amplitudeLogConstant/3)*(4*(1+Real.log p)/(p : ℝ)) := by
  have hs : (∑ j ∈ Finset.range v, (Nat.totient (p^(j+1)) : ℝ)*amplitude (p^(j+1))) ≤
      amplitudeLogConstant*(∑ j ∈ Finset.range v,
        (1+((j : ℝ)+1)*Real.log p)/(p : ℝ)^(j+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hq : 2 ≤ p^(j+1) := hp.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero j) p)
    simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one,mul_div_assoc]
      using conductor_coefficient_log_bound hq
  have hb := mul_le_mul_of_nonneg_left
    (prime_power_majorant_sum (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p) v)
    amplitudeLogConstant_pos.le
  rw [prime_power_alignment_sum hp]
  have h := mul_le_mul_of_nonneg_left (hs.trans hb) (by norm_num : (0 : ℝ) ≤ 1/3)
  convert! h using 1
  ring

theorem literal_prime_power_bound : ∃ C : ℝ, 0 < C ∧ ∀ p v : ℕ, p.Prime → 1 ≤ v →
    resetFunction (integerPhase (p^v : ℕ))+alignmentConstant (p^v) ≤ C*(1+Real.log p)/(p : ℝ) := by
  refine ⟨4*(1+amplitudeLogConstant/3),by positivity [amplitudeLogConstant_pos],?_⟩
  intro p v hp _hv
  have hf := prime_power_reset_bound hp v
  have hC := prime_power_alignment_bound hp v
  calc
    _ ≤ 4*(1+Real.log p)/(p : ℝ) +
        (amplitudeLogConstant/3)*(4*(1+Real.log p)/(p : ℝ)) := add_le_add hf hC
    _ = _ := by ring

end NField.Alignment.CollisionPrimePowerBoundDisplay
