/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPartitionDerivative
import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor polynomials of the actual Harper partition

The polynomial coefficients come from the constructed label weights. The
scalar Lagrange remainder keeps the exact factorial of the next order.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace NField.Alignment.HarperPartitionTaylor

open HarperPartition HarperPartitionDerivative

def polynomial (delta : ℝ) (J : ℕ) (i : Fin (2*J+2)) (N : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range N,
    Polynomial.monomial k (iteratedDeriv k (labelWeight delta J i) 0 / (k.factorial : ℝ))

theorem polynomial_coeff (delta : ℝ) (J : ℕ) (i : Fin (2*J+2)) (N k : ℕ) :
    (polynomial delta J i N).coeff k =
      if k < N then iteratedDeriv k (labelWeight delta J i) 0 / (k.factorial : ℝ) else 0 := by
  classical
  simp [polynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, eq_comm]

theorem polynomial_eval (delta : ℝ) (J : ℕ) (i : Fin (2*J+2)) (N : ℕ) (x : ℝ) :
    (polynomial delta J i N).eval x =
      ∑ k ∈ Finset.range N,
        (iteratedDeriv k (labelWeight delta J i) 0 / (k.factorial : ℝ))*x^k := by
  simp [polynomial, Polynomial.eval_finsetSum]

theorem polynomial_support (delta : ℝ) (J : ℕ) (i : Fin (2*J+2)) (N : ℕ) :
    (polynomial delta J i N).support ⊆ Finset.range N := by
  intro k hk
  rw [Polynomial.mem_support_iff, polynomial_coeff] at hk
  by_contra h
  have hn : ¬ k < N := by simpa using h
  simp [hn] at hk

theorem polynomial_natDegree (delta : ℝ) (J : ℕ) (i : Fin (2*J+2)) (N : ℕ) :
    (polynomial delta J i N).natDegree ≤ N-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [polynomial_coeff, if_neg (by omega)]

theorem polynomial_eval_zero (delta : ℝ) (J : ℕ) (i : Fin (2*J+2))
    {N : ℕ} (hN : 0 < N) : (polynomial delta J i N).eval 0 = labelWeight delta J i 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, polynomial_coeff]
  simp [hN]

theorem polynomial_eq_taylorWithin {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (polynomial delta J i (n+1)).eval x =
      taylorWithinEval (labelWeight delta J i) n (uIcc 0 x) 0 x := by
  rw [polynomial_eval, taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) x) :=
    uniqueDiffOn_Icc (by
      rcases lt_or_gt_of_ne (Ne.symm hx) with h | h
      · simpa only [min_eq_left h.le, max_eq_right h.le] using h
      · simpa only [min_eq_right h.le, max_eq_left h.le] using h)
  rw [iteratedDerivWithin_eq_iteratedDeriv hu
    (((contDiff_labelWeight hd J i).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt) (left_mem_uIcc)]
  simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

theorem polynomial_remainder {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) {N : ℕ} (hN : 0 < N) (x : ℝ) :
    |labelWeight delta J i x - (polynomial delta J i N).eval x| ≤
      (2*J+1 : ℝ)*derivativeBound delta N * |x|^N / (N.factorial : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  by_cases hx : x = 0
  · subst x
    rw [polynomial_eval_zero _ _ _ (Nat.succ_pos n)]
    simp
  · have hf : ContDiffOn ℝ (n+1) (labelWeight delta J i) (uIcc 0 x) :=
      ((contDiff_labelWeight hd J i).of_le
        (by exact_mod_cast (le_top : (n+1 : ℕ∞) ≤ ⊤))).contDiffOn
    obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hx) hf
    rw [polynomial_eq_taylorWithin hd J i n hx, hy]
    simp only [abs_div, abs_mul, abs_pow, sub_zero, Nat.abs_cast]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (labelWeight_derivative_bound hd J i (by omega) y)
        (by positivity)) (by positivity)

theorem polynomial_abs_le {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) {N : ℕ} (hN : 0 < N) (x : ℝ) :
    |(polynomial delta J i N).eval x| ≤
      1 + (2*J+1 : ℝ)*derivativeBound delta N * |x|^N / (N.factorial : ℝ) := by
  have ht := polynomial_remainder hd J i hN x
  have hl : |labelWeight delta J i x| ≤ 1 := by
    rw [abs_of_nonneg (labelWeight_nonneg hd J i x)]
    exact labelWeight_le_one hd J i x
  calc
    _ ≤ |labelWeight delta J i x| +
        |labelWeight delta J i x - (polynomial delta J i N).eval x| := by
      simpa [abs_sub_comm] using
        (abs_add_le (labelWeight delta J i x)
          ((polynomial delta J i N).eval x - labelWeight delta J i x))
    _ ≤ _ := add_le_add hl ht

/-- The manuscript's degree-(2S-1) remainder, with an explicit uniform
constant and the full factorial. The outside label is included. -/
theorem polynomial_even_remainder {delta : ℝ} (hd : 0 < delta) {J S : ℕ}
    (hJ : 0 < J) (hS : 0 < S) (i : Fin (2*J+2)) (x : ℝ) :
    |labelWeight delta J i x - (polynomial delta J i (2*S)).eval x| ≤
      3*(J : ℝ)*|2*Real.pi*x/delta|^(2*S) /
        (delta*(S : ℝ)*((2*S).factorial : ℝ)) := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hfac : (0 : ℝ) < (2*S).factorial := by positivity
  have hpow : (2*Real.pi/delta)^(2*S)*|x|^(2*S) =
      |2*Real.pi*x/delta|^(2*S) := by
    rw [← mul_pow, abs_div, abs_mul, abs_mul, abs_of_pos hd,
      abs_of_pos Real.pi_pos]
    norm_num
    ring
  calc
    _ ≤ (2*J+1 : ℝ)*derivativeBound delta (2*S)*|x|^(2*S) /
        ((2*S).factorial : ℝ) := polynomial_remainder hd J i (by omega) x
    _ = (2*J+1 : ℝ)*2*|2*Real.pi*x/delta|^(2*S) /
        (delta*(2*(S : ℝ)+1)*((2*S).factorial : ℝ)) := by
      unfold derivativeBound
      rw [pow_succ]
      push_cast
      rw [← hpow]
      field_simp [hd.ne', Real.pi_ne_zero]
    _ ≤ (2*J+1 : ℝ)*|2*Real.pi*x/delta|^(2*S) /
        (delta*(S : ℝ)*((2*S).factorial : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (by positivity : 0 ≤ (2*J+1 : ℝ)*
        |2*Real.pi*x/delta|^(2*S)) (mul_pos hd hfac).le]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end NField.Alignment.HarperPartitionTaylor
