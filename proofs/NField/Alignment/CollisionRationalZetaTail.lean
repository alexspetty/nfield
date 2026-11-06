/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicSeed

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionRationalZetaTail
open scoped BigOperators
open CollisionHarmonicSeed

theorem cube_step_bound {x : ℝ} (hx : 1 ≤ x) :
    1/(x+1)^3 ≤ 1/(2*x^2)-1/(2*(x+1)^2) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  apply (mul_le_mul_iff_right₀ (show 0 < 2*x^2*(x+1)^3 by positivity)).mp
  field_simp [hx0.ne',hx1.ne']
  nlinarith [sq_nonneg x]

theorem finite_cube_tail_bound {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    (∑ n ∈ Finset.range K, 1/((N+n+1 : ℕ) : ℝ)^3) ≤
      1/(2*(N : ℝ)^2)-1/(2*((N+K : ℕ) : ℝ)^2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h := cube_step_bound (x := ((N+K : ℕ) : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N+K))
    push_cast at ih h ⊢
    simp only [← add_assoc] at *
    linarith

theorem cube_tail_bound {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, 1/((N+n+1 : ℕ) : ℝ)^3) ≤ 1/(2*(N : ℝ)^2) := by
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro K
  exact (finite_cube_tail_bound hN K).trans (sub_le_self _ (by positivity))

theorem zetaThree_rational_enclosure {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range (N+1), cubeKernel n) ≤ zetaThree ∧
    zetaThree ≤ (∑ n ∈ Finset.range (N+1), cubeKernel n)+1/(2*(N : ℝ)^2) := by
  have hs := cubeKernel_summable.sum_add_tsum_nat_add (N+1)
  have hn : 0 ≤ ∑' n : ℕ, cubeKernel (n+(N+1)) := tsum_nonneg (fun _ => cubeKernel_nonneg _)
  have hb : (∑' n : ℕ, cubeKernel (n+(N+1))) ≤ 1/(2*(N : ℝ)^2) := by
    simpa only [cubeKernel, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using cube_tail_bound hN
  change _ = zetaThree at hs
  constructor <;> linarith

end NField.Alignment.CollisionRationalZetaTail
