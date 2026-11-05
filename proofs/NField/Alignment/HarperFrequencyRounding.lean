/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSourceBarrierBound

/-!
# Recursive downward rounding on a changing frequency grid

Time zero is the original frequency. The value at time j+1 is the source
approximation t(j), obtained by rounding the preceding value down to the
grid of width d(j). Subsequent values depend only on the current value.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperFrequencyRounding
open scoped BigOperators
open MeasureTheory Set

def roundDown (d t : ℝ) : ℝ := (⌊t/d⌋ : ℝ)*d

def rounded (d : ℕ → ℝ) (t : ℝ) : ℕ → ℝ
  | 0 => t
  | j+1 => roundDown (d j) (rounded d t j)

def roundCode (d : ℕ → ℝ) (t : ℝ) (j : ℕ) : ℤ := ⌊rounded d t j/d j⌋

theorem roundDown_le {d : ℝ} (hd : 0 < d) (t : ℝ) : roundDown d t ≤ t := by
  exact (le_div_iff₀ hd).mp (Int.floor_le (t/d))

theorem sub_roundDown_lt {d : ℝ} (hd : 0 < d) (t : ℝ) : t-roundDown d t < d := by
  have h := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (t/d))
  dsimp [roundDown]
  nlinarith

theorem rounded_succ_code (d : ℕ → ℝ) (t : ℝ) (j : ℕ) :
    rounded d t (j+1) = (roundCode d t j : ℝ)*d j := rfl

theorem rounded_step {d : ℕ → ℝ} {j : ℕ} (hd : 0 < d j) (t : ℝ) :
    0 ≤ rounded d t j-rounded d t (j+1) ∧ rounded d t j-rounded d t (j+1) < d j :=
  ⟨sub_nonneg.mpr (roundDown_le hd _),sub_roundDown_lt hd _⟩

theorem rounded_error {d : ℕ → ℝ} (n : ℕ) (hd : ∀ j < n, 0 < d j) (t : ℝ) :
    0 ≤ t-rounded d t n ∧ t-rounded d t n ≤ ∑ j ∈ Finset.range n, d j := by
  induction n with
  | zero => simp [rounded]
  | succ n ih =>
    have hi := ih (fun j hj => hd j (Nat.lt_trans hj (Nat.lt_succ_self n)))
    have hs := rounded_step (hd n (Nat.lt_succ_self n)) t
    rw [Finset.sum_range_succ]
    exact ⟨by linarith [hi.1,hs.1],by linarith [hi.2,hs.2]⟩

theorem sum_doubling_width {d : ℕ → ℝ} (j : ℕ) (hpos : ∀ i ≤ j, 0 ≤ d i)
    (hd : ∀ i < j, 2*d i ≤ d (i+1)) :
    (∑ i ∈ Finset.range (j+1), d i) ≤ 2*d j := by
  induction j with
  | zero => simpa using (show d 0 ≤ 2*d 0 by linarith [hpos 0 le_rfl])
  | succ j ih =>
    have hi := ih (fun i hi => hpos i (hi.trans (Nat.le_succ j)))
      (fun i hi => hd i (hi.trans (Nat.lt_succ_self j)))
    rw [Finset.sum_range_succ]
    linarith [hd j (Nat.lt_succ_self j)]

theorem rounded_error_le_two {d : ℕ → ℝ} (j : ℕ) (hpos : ∀ i ≤ j, 0 < d i)
    (hd : ∀ i < j, 2*d i ≤ d (i+1)) (t : ℝ) :
    |t-rounded d t (j+1)| ≤ 2*d j := by
  have h := rounded_error (j+1) (fun i hi => hpos i (by omega)) t
  rw [abs_of_nonneg h.1]
  exact h.2.trans (sum_doubling_width j (fun i hi => (hpos i hi).le) hd)

theorem rounded_tail_congr {d : ℕ → ℝ} {s t : ℝ} {j k : ℕ} (hjk : j ≤ k)
    (h : rounded d s j = rounded d t j) : rounded d s k = rounded d t k := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => simp only [rounded,ih]

theorem rounded_tail_from_code {d : ℕ → ℝ} {s t : ℝ} {j k : ℕ} (hjk : j ≤ k)
    (h : roundCode d s j = roundCode d t j) :
    rounded d s (k+1) = rounded d t (k+1) := by
  apply rounded_tail_congr (Nat.succ_le_succ hjk)
  simp only [rounded_succ_code,h]

theorem roundDown_measurable (d : ℝ) : Measurable (roundDown d) := by
  unfold roundDown
  fun_prop

theorem rounded_measurable (d : ℕ → ℝ) (j : ℕ) : Measurable (fun t => rounded d t j) := by
  induction j with
  | zero => exact measurable_id
  | succ j ih => exact (roundDown_measurable (d j)).comp ih

theorem roundCode_measurable (d : ℕ → ℝ) (j : ℕ) : Measurable (fun t => roundCode d t j) := by
  unfold roundCode
  have hm := rounded_measurable d j
  fun_prop

end NField.Alignment.HarperFrequencyRounding
