/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovIteration

/-!
# A degree-uniform loss budget

The explicit step constants grow by at most an exponential of the degree
times the moment order. This is what permits a uniform quadratic total
loss after iteration.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovLossBudget
open scoped BigOperators Classical
open VinogradovNormalizedRecurrence VinogradovIteration

theorem self_le_exp (x : ℝ) : x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

theorem nat_pow_le_exp (a k : ℕ) : (a : ℝ) ^ k ≤ Real.exp ((k : ℝ) * a) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (self_le_exp _) _

theorem primeFamilySize_le_exp {n : ℕ} (hn : 1 ≤ n) :
    ((2 * n ^ 3 + 1 : ℕ) : ℝ) ≤ Real.exp (6 * n) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow := nat_pow_le_exp n 3
  have he : (1 : ℝ) ≤ Real.exp (3 * n) := Real.one_le_exp_iff.mpr (by positivity)
  push_cast at hpow ⊢
  calc
    _ ≤ 3 * Real.exp (3 * n) := by linarith
    _ ≤ Real.exp 3 * Real.exp (3 * n) := by gcongr; exact self_le_exp 3
    _ = Real.exp (3 + 3 * n) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem primeFactor_le_exp {C n : ℕ} (hn : 1 ≤ n) :
    (primeFactor C n : ℝ) ≤ Real.exp (((C : ℝ) + 15) * n) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM := primeFamilySize_le_exp hn
  calc
    _ = (2 : ℝ) * C * ((2 * n ^ 3 + 1 : ℕ) : ℝ) ^ 2 * n := by
      simp only [primeFactor, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ Real.exp 2 * Real.exp C * (Real.exp (6 * n)) ^ 2 * Real.exp n := by
      gcongr
      · exact self_le_exp 2
      · exact self_le_exp _
      · exact self_le_exp _
    _ = Real.exp (2 + C + 12 * n + n) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C])

theorem selectionCost_le_exp {n s : ℕ} (hn : 1 ≤ n) :
    ((selectionCost n s * 2 ^ (2 * s) : ℕ) : ℝ) ≤ Real.exp (13 * n * (n + s)) := by
  have hL : 1 ≤ n + s := by omega
  have hnL : n ≤ n + s := by omega
  have hsL : s ≤ n + s := by omega
  have hTn : n ≤ n * (n + s) := le_mul_of_one_le_right (Nat.zero_le _) hL
  have hTn2 : n ^ 2 ≤ n * (n + s) := by nlinarith
  have hTs : s ≤ n * (n + s) :=
    hsL.trans (le_mul_of_one_le_left (Nat.zero_le _) hn)
  have hhead := nat_pow_le_exp (n + s) (2 * n)
  have hM := primeFamilySize_le_exp hn
  have hfact : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * n) :=
    (show (n.factorial : ℝ) ≤ (n : ℝ) ^ n by exact_mod_cast Nat.factorial_le_pow n).trans
      (nat_pow_le_exp n n)
  have htwo := nat_pow_le_exp 2 (2 * s)
  calc
    _ = ((n + s : ℕ) : ℝ) ^ (2 * n) * ((2 * n ^ 3 + 1 : ℕ) : ℝ) *
        (n.factorial : ℝ) * (2 : ℝ) ^ (2 * s) := by
      simp only [selectionCost, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ Real.exp (((2 * n : ℕ) : ℝ) * (n + s)) * Real.exp (6 * n) *
        Real.exp ((n : ℝ) * n) * Real.exp (((2 * s : ℕ) : ℝ) * 2) := by
      gcongr
      · simpa only [Nat.cast_add] using hhead
      · simpa only [Nat.cast_ofNat] using htwo
    _ = Real.exp (((2 * n * (n + s) + 6 * n + n ^ 2 + 4 * s : ℕ) : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact_mod_cast (show 2 * n * (n + s) + 6 * n + n ^ 2 + 4 * s ≤ 13 * n * (n + s) by
        nlinarith)

theorem stepConstant_le_exp {C n s : ℕ} (hn : 1 ≤ n) (hs : n ^ 2 ≤ s) :
    (stepConstant C n s : ℝ) ≤ Real.exp ((2 * (C : ℝ) + 50) * n * (n + s)) := by
  have hL : 1 ≤ n + s := by omega
  have hT : (1 : ℝ) ≤ (n : ℝ) * (n + s) := by
    exact_mod_cast (show 1 ≤ n * (n + s) from hn.trans (le_mul_of_one_le_right (Nat.zero_le _) hL))
  have hrep : (((n - 1) ^ (n + s) : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * (n + s)) := by
    calc
      _ ≤ (n : ℝ) ^ (n + s) := by exact_mod_cast Nat.pow_le_pow_left (Nat.sub_le n 1) (n + s)
      _ ≤ Real.exp (((n + s : ℕ) : ℝ) * n) := nat_pow_le_exp n (n + s)
      _ = _ := by push_cast; congr 1; ring
  have hsel := selectionCost_le_exp (s := s) hn
  have he1 : Real.exp ((n : ℝ) * (n + s)) ≤ Real.exp (13 * n * (n + s)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2 : (1 : ℝ) ≤ Real.exp (13 * n * (n + s)) := Real.one_le_exp_iff.mpr (by positivity)
  have hsum : ((2 * (n - 1) ^ (n + s) + 2 + selectionCost n s * 2 ^ (2 * s) : ℕ) : ℝ) ≤
      Real.exp (18 * n * (n + s)) := by
    calc
      _ ≤ 5 * Real.exp (13 * n * (n + s)) := by push_cast at hrep hsel ⊢; linarith
      _ ≤ Real.exp 5 * Real.exp (13 * n * (n + s)) := by gcongr; exact self_le_exp 5
      _ = Real.exp (5 + 13 * n * (n + s)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hB := primeFactor_le_exp (C := C) hn
  have hdegree : n * (n + 1) * n ≤ 2 * n * (n + s) := by
    have := Nat.mul_le_mul_left n hs
    nlinarith
  have hBpow : (primeFactor C n : ℝ) ^ (n * (n + 1)) ≤
      Real.exp (2 * ((C : ℝ) + 15) * n * (n + s)) := by
    calc
      _ ≤ Real.exp (((C : ℝ) + 15) * n) ^ (n * (n + 1)) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
      _ = Real.exp (((C : ℝ) + 15) * ((n * (n + 1) * n : ℕ) : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh : ((n * (n + 1) * n : ℕ) : ℝ) ≤ 2 * n * (n + s) := by exact_mod_cast hdegree
        nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ (C : ℝ) + 15 by positivity)]
  calc
    _ ≤ Real.exp (18 * n * (n + s)) * Real.exp (2 * ((C : ℝ) + 15) * n * (n + s)) := by
      rw [stepConstant, Nat.cast_mul, Nat.cast_pow]
      exact mul_le_mul hsum hBpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((2 * (C : ℝ) + 48) * n * (n + s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The product of every iteration loss is bounded by one absolute quadratic exponential. -/
theorem iterationCost_le_exp {C n s₀ t : ℕ} (hn : 1 ≤ n) (hs₀ : n ^ 2 ≤ s₀) :
    (iterationCost C n s₀ t : ℝ) ≤
      Real.exp ((2 * (C : ℝ) + 52) * ((s₀ + n * t : ℕ) : ℝ) ^ 2) := by
  let L : ℕ := s₀ + n * t
  let a : ℝ := 2 * (C : ℝ) + 50
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hL : 1 ≤ L := by dsimp [L]; nlinarith
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hprod : (∏ i ∈ Finset.range t, (stepConstant C n (s₀ + n * i) : ℝ)) ≤
      Real.exp (a * n * L) ^ t := by
    calc
      _ ≤ ∏ _i ∈ Finset.range t, Real.exp (a * n * L) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        intro i hi
        have hi' : i + 1 ≤ t := Finset.mem_range.mp hi
        have hindex : n + (s₀ + n * i) ≤ L := by
          have := Nat.mul_le_mul_left n hi'
          dsimp [L]
          nlinarith
        calc
          _ ≤ Real.exp (a * n * (n + (s₀ + n * i))) := by
            simpa only [Nat.cast_add, Nat.cast_mul, a] using
              (stepConstant_le_exp (C := C) hn (show n ^ 2 ≤ s₀ + n * i by omega))
          _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
            (by exact_mod_cast hindex) (by positivity : 0 ≤ a * n))
      _ = _ := by simp
  have hnt : (n : ℝ) * t ≤ L := by
    exact_mod_cast (show n * t ≤ L by dsimp [L]; omega)
  have hmain : (t : ℝ) * (a * n * L) ≤ a * (L : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hnt (show 0 ≤ a * L by positivity)
    nlinarith
  calc
    _ = 2 * ∏ i ∈ Finset.range t, (stepConstant C n (s₀ + n * i) : ℝ) := by
      simp only [iterationCost, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_prod]
    _ ≤ Real.exp 2 * Real.exp (a * n * L) ^ t :=
      mul_le_mul (self_le_exp 2) hprod (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (2 + (t : ℝ) * (a * n * L)) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have haeq : 2 * (C : ℝ) + 52 = a + 2 := by dsimp [a]; ring
      rw [haeq]
      change 2 + (t : ℝ) * (a * n * L) ≤ (a + 2) * (L : ℝ) ^ 2
      nlinarith

end NField.Alignment.VinogradovLossBudget
