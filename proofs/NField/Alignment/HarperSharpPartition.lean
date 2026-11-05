/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperPartition

/-!
# Sharp localization of the constructed smooth partition

The regular label center is J-i; the final label is the outside cell.
Within the declared range, the weight rejected by a sharp unit window is
at most delta for every label, including the outside cell. An exact product
marginal identity sums out all other coordinates. The rejected mass is
therefore bounded by (2J+2) delta, independent of the number of coordinates.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSharpPartition
open scoped BigOperators Classical
open HarperPartition

def labelCenter (J : ℕ) (i : Fin (2*J+2)) : ℝ := (J : ℝ)-(i.val : ℝ)
def sharpLabel (J : ℕ) (i : Fin (2*J+2)) (x : ℝ) : Prop :=
  i.val < 2*J+1 ∧ |x-labelCenter J i| ≤ 1

def rejectedLabelWeight (delta : ℝ) (J : ℕ) (i : Fin (2*J+2)) (x : ℝ) : ℝ := by
  classical
  exact if sharpLabel J i x then 0 else labelWeight delta J i x

theorem labelWeight_regular (delta : ℝ) (J : ℕ) (i : Fin (2*J+2))
    (hi : i.val < 2*J+1) (x : ℝ) : labelWeight delta J i x = cell delta (x-labelCenter J i) := by
  rw [labelWeight, if_pos hi]
  congr 1
  unfold labelCenter
  ring

theorem rejectedLabelWeight_nonneg {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) (x : ℝ) : 0 ≤ rejectedLabelWeight delta J i x := by
  classical
  unfold rejectedLabelWeight
  split_ifs
  · exact le_rfl
  · exact labelWeight_nonneg hd J i x

theorem rejectedLabelWeight_le {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    (i : Fin (2*J+2)) {x : ℝ} (hx : |x| ≤ J) : rejectedLabelWeight delta J i x ≤ delta := by
  classical
  unfold rejectedLabelWeight
  split_ifs with hs
  · exact hd.le
  · by_cases hi : i.val < 2*J+1
    · rw [labelWeight_regular delta J i hi]
      apply cell_localization hd
      exact lt_of_not_ge (fun hh => hs ⟨hi,hh⟩)
    · rw [labelWeight, if_neg hi]
      exact outside_localization hd J hx

theorem rejectedLabelWeight_sum_bound {delta : ℝ} (hd : 0 < delta) (J : ℕ)
    {x : ℝ} (hx : |x| ≤ J) :
    (∑ i : Fin (2*J+2), rejectedLabelWeight delta J i x) ≤ (2*(J : ℝ)+2)*delta := by
  calc
    _ ≤ ∑ _i : Fin (2*J+2), delta := Finset.sum_le_sum (fun i _ => rejectedLabelWeight_le hd J i hx)
    _ = _ := by simp

theorem boxWeight_marginal {A : ℕ} (delta : ℝ) (J : ℕ) (values : Fin A → ℝ)
    (k : Fin A) (g : Fin (2*J+2) → ℝ) :
    (∑ labels : Fin A → Fin (2*J+2), boxWeight delta J values labels*g (labels k)) =
      ∑ j : Fin (2*J+2), labelWeight delta J j (values k)*g j := by
  classical
  have he (labels : Fin A → Fin (2*J+2)) : boxWeight delta J values labels*g (labels k) =
      ∏ i : Fin A, labelWeight delta J (labels i) (values i)*(if i=k then g (labels i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [boxWeight]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (i : Fin A) (j : Fin (2*J+2)) =>
    labelWeight delta J j (values i)*(if i=k then g j else 1))]
  have hp (i : Fin A) : (∑ j : Fin (2*J+2), labelWeight delta J j (values i)*(if i=k then g j else 1)) =
      if i=k then (∑ j : Fin (2*J+2), labelWeight delta J j (values k)*g j) else 1 := by
    by_cases hi : i=k
    · subst i
      simp
    · simp [hi, labelWeight_sum]
  simp_rw [hp]
  simp

theorem boxWeight_rejected_sum_bound {A : ℕ} {delta : ℝ} (hd : 0 < delta)
    (J : ℕ) (values : Fin A → ℝ) (k : Fin A) (hx : |values k| ≤ J) :
    (∑ labels : Fin A → Fin (2*J+2),
      if sharpLabel J (labels k) (values k) then 0 else boxWeight delta J values labels) ≤
        (2*(J : ℝ)+2)*delta := by
  classical
  have he : (∑ labels : Fin A → Fin (2*J+2),
      if sharpLabel J (labels k) (values k) then 0 else boxWeight delta J values labels) =
      ∑ j : Fin (2*J+2), rejectedLabelWeight delta J j (values k) := by
    convert boxWeight_marginal delta J values k (fun j => if sharpLabel J j (values k) then 0 else 1) using 1
    · apply Finset.sum_congr rfl
      intro labels _
      split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro j _
      unfold rejectedLabelWeight
      split_ifs <;> simp
  rw [he]
  exact rejectedLabelWeight_sum_bound hd J hx

end NField.Alignment.HarperSharpPartition
