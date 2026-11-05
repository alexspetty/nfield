/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFrequencyMesh

/-!
# Finite values of the actual recursive frequency approximations

At a fixed scale, the attainable codes form an exact finite subset of a
single integer interval. Their representative frequencies retain the
same full suffix of recursive approximations. The cardinal bound is
linear in the reciprocal mesh width, not a product over all scales.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperFrequencyCodes
open MeasureTheory Set HarperFrequencyRounding HarperFrequencyMesh

def codeBound (d : ℝ) : ℕ := ⌈1/d⌉₊
def codeBox (d : ℝ) : Finset ℤ := Finset.Icc (-(codeBound d : ℤ)) (codeBound d : ℤ)
def attainableCodes (d : ℕ → ℝ) (j : ℕ) : Set ℤ :=
  {k | ∃ t : ℝ, |t| ≤ 1/2 ∧ roundCode d t j = k}

def representative (d : ℕ → ℝ) (j : ℕ) (k : ℤ) : ℝ := by
  classical
  exact if h : k ∈ attainableCodes d j then Classical.choose h else 0

theorem representative_spec {d : ℕ → ℝ} {j : ℕ} {k : ℤ} (hk : k ∈ attainableCodes d j) :
    |representative d j k| ≤ 1/2 ∧ roundCode d (representative d j k) j = k := by
  simpa only [representative,dif_pos hk] using Classical.choose_spec hk

theorem representative_suffix {d : ℕ → ℝ} {j k : ℕ} (hjk : j ≤ k) {t : ℝ} (ht : |t| ≤ 1/2) :
    rounded d (representative d j (roundCode d t j)) (k+1) = rounded d t (k+1) := by
  exact rounded_tail_from_code hjk (representative_spec ⟨t,ht,rfl⟩).2

theorem mem_codeBox_of_abs {d : ℝ} (hd : 0 < d) {k : ℤ} (hk : |(k : ℝ)*d| ≤ 1) :
    k ∈ codeBox d := by
  have ha : |(k : ℝ)| ≤ 1/d := (le_div_iff₀ hd).mpr (by simpa only [abs_mul,abs_of_pos hd] using hk)
  have hb := abs_le.mp (ha.trans (Nat.le_ceil (1/d)))
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

theorem codeBox_card (d : ℝ) : (codeBox d).card = 2*codeBound d+1 := by
  simp only [codeBox,Int.card_Icc]
  have he : (codeBound d : ℤ)+1-(-(codeBound d : ℤ)) = ((2*codeBound d+1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [he,Int.toNat_natCast]

theorem codeBox_card_bound {d : ℝ} (hd : 0 < d) : ((codeBox d).card : ℝ) ≤ 2/d+3 := by
  rw [codeBox_card]
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 1/d by positivity)).le
  unfold codeBound
  push_cast
  rw [show 2/d = 2*(1/d) by ring]
  linarith

theorem source_roundCode_mem {x t : ℝ} (hx : 1 < x) (j : ℕ)
    (hj : Real.exp 2 ≤ logScale x j) (ht : |t| ≤ 1/2) :
    roundCode (mesh x) t j ∈ codeBox (mesh x j) := by
  have he : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  apply mem_codeBox_of_abs (mesh_pos (by linarith : 1 < logScale x j))
  exact approximation_abs_le_one hx j hj ht

theorem attainableCodes_subset_box {x : ℝ} (hx : 1 < x) (j : ℕ)
    (hj : Real.exp 2 ≤ logScale x j) :
    attainableCodes (mesh x) j ⊆ (codeBox (mesh x j) : Set ℤ) := by
  rintro k ⟨t,ht,rfl⟩
  exact source_roundCode_mem hx j hj ht

theorem attainableCodes_finite {x : ℝ} (hx : 1 < x) (j : ℕ)
    (hj : Real.exp 2 ≤ logScale x j) : (attainableCodes (mesh x) j).Finite :=
  (codeBox (mesh x j)).finite_toSet.subset (attainableCodes_subset_box hx j hj)

theorem attainableCodes_card {x : ℝ} (hx : 1 < x) (j : ℕ)
    (hj : Real.exp 2 ≤ logScale x j) :
    (((attainableCodes_finite hx j hj).toFinset.card : ℕ) : ℝ) ≤ 2/(mesh x j)+3 := by
  have he : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  apply le_trans _ (codeBox_card_bound (mesh_pos (by linarith : 1 < logScale x j)))
  exact_mod_cast Finset.card_le_card (show (attainableCodes_finite hx j hj).toFinset ⊆ codeBox (mesh x j) by
    intro k hk
    exact attainableCodes_subset_box hx j hj ((Set.Finite.mem_toFinset _).mp hk))

end NField.Alignment.HarperFrequencyCodes
