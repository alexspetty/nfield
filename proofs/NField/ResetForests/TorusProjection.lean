/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.TorusCounting
/-! # The literal primitive torus projects to the same midpoint field -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators
open NField.Alignment CollisionDedekindPairing CollisionRampEnergy RealSawtoothDistribution FibreReconstruction

theorem sawtooth_negative_grid_distribution {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (∑ a ∈ Finset.range n, periodicSawtooth (x-(a : ℝ)/(n : ℝ)))=
      periodicSawtooth ((n : ℝ)*x) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ = ∑ a ∈ Finset.range n,
        periodicSawtooth (x-((n-1-a : ℕ) : ℝ)/(n : ℝ)) :=
      (Finset.sum_range_reflect (fun a => periodicSawtooth (x-(a : ℝ)/(n : ℝ))) n).symm
    _ = ∑ a ∈ Finset.range n,
        periodicSawtooth (x-((n-1 : ℕ) : ℝ)/(n : ℝ)+(a : ℝ)/(n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      rw [Nat.cast_sub (by have := Finset.mem_range.mp ha; omega : a ≤ n-1)]
      ring
    _ = periodicSawtooth ((n : ℝ)*(x-((n-1 : ℕ) : ℝ)/(n : ℝ))) := sawtooth_distribution hn _
    _ = periodicSawtooth ((n : ℝ)*x-((n-1 : ℕ) : ℝ)) := by
      congr 1
      field_simp
    _ = periodicSawtooth ((n : ℝ)*x) := by
      simpa only [mul_one] using sawtooth_periodic.sub_nat_mul_eq (x := (n : ℝ)*x) (n-1)

theorem primitive_point_count {n : ℕ} (hn : 0 < n) :
    ((primitivePoints n).card : ℝ)=jordanMass n := by
  rw [← primitive_sum_one_eq_card, primitive_sum_exclusion hn]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have he : (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ)*((n/d : ℕ) : ℝ)*((n/d : ℕ) : ℝ))=
        ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)*((n/d : ℕ) : ℝ)^2 := by
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he, ← Nat.sum_divisorsAntidiagonal
    (fun a b : ℕ => (ArithmeticFunction.moebius a : ℝ)*(b : ℝ)^2),
    Nat.sum_divisorsAntidiagonal'
      (fun a b : ℕ => (ArithmeticFunction.moebius a : ℝ)*(b : ℝ)^2)]
  rfl

def torusProjection (n : ℕ) (x : ℝ) : ℝ :=
  2*primitiveSum n (fun a => periodicSawtooth (x-(a : ℝ)/(n : ℝ)))

theorem primitive_torus_projection {n : ℕ} (hn : 0 < n) (x : ℝ) :
    torusProjection n x=primitiveField n x := by
  rw [torusProjection, primitive_sum_exclusion hn]
  have hrow (d : ℕ) (hd : d ∈ n.divisors) :
      (∑ a ∈ Finset.range (n/d), periodicSawtooth (x-((d*a : ℕ) : ℝ)/(n : ℝ)))=
        periodicSawtooth (((n/d : ℕ) : ℝ)*x) := by
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hdp := Nat.pos_of_mem_divisors hd
    have hnd : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdiv) hdp
    have harg (a : ℕ) : ((d*a : ℕ) : ℝ)/(n : ℝ)=(a : ℝ)/((n/d : ℕ) : ℝ) := by
      have hndR : (n : ℝ)=(d : ℝ)*((n/d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdp.ne'
      have hnR : ((n/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnd.ne'
      rw [hndR, Nat.cast_mul]
      field_simp
    simp_rw [harg]
    exact sawtooth_negative_grid_distribution hnd x
  have hsum : (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ)*((n/d : ℕ) : ℝ)*
        ∑ a ∈ Finset.range (n/d), periodicSawtooth (x-((d*a : ℕ) : ℝ)/(n : ℝ)))=
      ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℝ)*((n/d : ℕ) : ℝ)*
          periodicSawtooth (((n/d : ℕ) : ℝ)*x) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [hrow d hd]
  rw [hsum, ← Nat.sum_divisorsAntidiagonal
    (fun d a : ℕ => (ArithmeticFunction.moebius d : ℝ)*(a : ℝ)*periodicSawtooth ((a : ℝ)*x)),
    Nat.sum_divisorsAntidiagonal'
      (fun d a : ℕ => (ArithmeticFunction.moebius d : ℝ)*(a : ℝ)*periodicSawtooth ((a : ℝ)*x)),
    primitive_field_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [midpoint_row_periodic_saw]
  ring

theorem primitive_two_points : primitivePoints 2={(0,1),(1,0),(1,1)} := by decide

theorem primitive_two_field (x : ℝ) :
    primitiveField 2 x=4*periodicSawtooth (2*x)-2*periodicSawtooth x := by
  rw [primitive_field_formula]
  norm_num [show Nat.divisors 2={1,2} by decide, midpoint_row_periodic_saw,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

theorem primitive_two_projection (x : ℝ) :
    torusProjection 2 x=2*periodicSawtooth x+4*periodicSawtooth (x-1/2) := by
  norm_num [torusProjection, primitiveSum, Finset.sum_range_succ, primitiveAt, Nat.Coprime]
  ring

theorem primitive_two_example (x : ℝ) :
    2*periodicSawtooth x+4*periodicSawtooth (x-1/2)=
      4*periodicSawtooth (2*x)-2*periodicSawtooth x := by
  rw [← primitive_two_projection, primitive_torus_projection (by decide : 0 < 2),
    primitive_two_field]

end NField.ResetForests.PrimitiveCoordinates
