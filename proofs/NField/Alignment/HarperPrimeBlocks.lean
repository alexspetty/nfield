/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperCharacteristicTail

/-!
# Exact prime blocks for the critical weighted Euler product

The source blocks have endpoints x^(exp(-(l+2))) and x^(exp(-(l+1))).
Their half-open endpoint convention makes them pairwise disjoint, and
every block lies within the actual tilted cutoff x^(1/e). These are the
literal source ranges, including empty blocks at large natural indices.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlocks
open scoped BigOperators
open CollisionMertensInput

def blockUpper (x : ℝ) (l : ℕ) : ℝ := x^(Real.exp (-((l : ℝ)+1)))
def blockLower (x : ℝ) (l : ℕ) : ℝ := x^(Real.exp (-((l : ℝ)+2)))
def sourceCutoff (x : ℝ) : ℝ := x^(1/Real.exp 1)
def primeBlock (x : ℝ) (l : ℕ) : Finset ℕ := by
  classical
  exact (primesUpTo (blockUpper x l)).filter (fun q => blockLower x l < (q : ℝ))

theorem primeBlock_mem {x : ℝ} {l q : ℕ} :
    q ∈ primeBlock x l ↔ q.Prime ∧ blockLower x l < (q : ℝ) ∧
      (q : ℝ) ≤ blockUpper x l := by
  classical
  simp only [primeBlock, Finset.mem_filter, primesUpTo_mem]
  tauto

theorem blockLower_eq_next (x : ℝ) (l : ℕ) :
    blockLower x l = blockUpper x (l+1) := by
  unfold blockLower blockUpper
  congr 2
  push_cast
  ring

theorem blockUpper_zero (x : ℝ) : blockUpper x 0 = sourceCutoff x := by
  simp [blockUpper, sourceCutoff, Real.exp_neg, one_div]

theorem blockUpper_gt_one {x : ℝ} (hx : 1 < x) (l : ℕ) : 1 < blockUpper x l :=
  Real.one_lt_rpow hx (Real.exp_pos _)

theorem blockLower_gt_one {x : ℝ} (hx : 1 < x) (l : ℕ) : 1 < blockLower x l :=
  Real.one_lt_rpow hx (Real.exp_pos _)

theorem blockUpper_antitone {x : ℝ} (hx : 1 ≤ x) : Antitone (blockUpper x) := by
  intro l m hlm
  apply Real.rpow_le_rpow_of_exponent_le hx
  apply Real.exp_le_exp.mpr
  have h : (l : ℝ) ≤ m := by exact_mod_cast hlm
  linarith

theorem blockLower_le_upper {x : ℝ} (hx : 1 ≤ x) (l : ℕ) :
    blockLower x l ≤ blockUpper x l := by
  rw [blockLower_eq_next]
  exact blockUpper_antitone hx (Nat.le_succ l)

theorem blockUpper_le_cutoff {x : ℝ} (hx : 1 ≤ x) (l : ℕ) :
    blockUpper x l ≤ sourceCutoff x := by
  rw [← blockUpper_zero]
  exact blockUpper_antitone hx (Nat.zero_le l)

theorem later_upper_le_lower {x : ℝ} (hx : 1 ≤ x) {l m : ℕ} (hlm : l < m) :
    blockUpper x m ≤ blockLower x l := by
  rw [blockLower_eq_next]
  exact blockUpper_antitone hx (Nat.succ_le_of_lt hlm)

theorem blockLower_power {x : ℝ} (hx : 0 ≤ x) (l : ℕ) :
    blockLower x l = (blockUpper x l)^(1/Real.exp 1) := by
  unfold blockLower blockUpper
  rw [← Real.rpow_mul hx]
  congr 1
  rw [one_div, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem primeBlock_subset {x : ℝ} (hx : 1 ≤ x) (l : ℕ) :
    primeBlock x l ⊆ primesUpTo (sourceCutoff x) := by
  intro q hq
  rcases primeBlock_mem.mp hq with ⟨hp, _, hu⟩
  exact primesUpTo_mem.mpr ⟨hp, hu.trans (blockUpper_le_cutoff hx l)⟩

theorem primeBlock_disjoint_of_lt {x : ℝ} (hx : 1 ≤ x) {l m : ℕ} (hlm : l < m) :
    Disjoint (primeBlock x l) (primeBlock x m) := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  have hl := (primeBlock_mem.mp hq).2.1
  have hu := (primeBlock_mem.mp hq').2.2
  exact (not_lt_of_ge (hu.trans (later_upper_le_lower hx hlm))) hl

theorem primeBlock_pairwise_disjoint {x : ℝ} (hx : 1 ≤ x) :
    Pairwise (fun l m => Disjoint (primeBlock x l) (primeBlock x m)) := by
  intro l m hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact primeBlock_disjoint_of_lt hx h
  · exact (primeBlock_disjoint_of_lt hx h).symm

end NField.Alignment.HarperPrimeBlocks
