/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaWeightedMoment
import Mathlib.Order.Interval.Finset.Nat

/-! # Actual ordinary sums of ordered prime tuples -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaTupleSumRange
open scoped BigOperators
open KaratsubaPrimeMoment KaratsubaWeightedMoment

def ordinaryTupleSums (Q : Finset ℕ) (s : ℕ) : Finset ℕ :=
  Finset.univ.image fun u : PrimeTuple Q s => ∑ i, (u i).val

theorem ordinaryTupleSums_subset {Q : Finset ℕ} {s L U : ℕ} (hs : 0 < s)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U) :
    ordinaryTupleSums Q s ⊆ Finset.Ioc (s*L) (s*U) := by
  intro n hn
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hn
  have hlo : s*(L+1) ≤ ∑ i, (u i).val := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin s => L+1) (g := fun i => (u i).val)
      (fun i _ => hL _ (u i).property)
  have hhi : (∑ i, (u i).val) ≤ s*U := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (f := fun i => (u i).val) (g := fun _ : Fin s => U)
      (fun i _ => hU _ (u i).property)
  apply Finset.mem_Ioc.mpr
  constructor
  · nlinarith
  · exact hhi

/-- The actual sum set is bounded by its interval, without counting tuples as distinct sums. -/
theorem ordinaryTupleSums_card_le {Q : Finset ℕ} {s L U : ℕ} (hs : 0 < s)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U) :
    (ordinaryTupleSums Q s).card ≤ s*(U-L) := by
  calc
    _ ≤ (Finset.Ioc (s*L) (s*U)).card :=
      Finset.card_le_card (ordinaryTupleSums_subset hs hL hU)
    _ = _ := by rw [Nat.card_Ioc, Nat.mul_sub_left_distrib]

/-- The mixed moment is summed over the actual ordinary-coordinate support. -/
theorem actual_tuple_parameter_moment_le {P Q : Finset ℕ} {m k s L U : ℕ}
    [NeZero m] {X : ℝ} (hs : 0 < s)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2*k-1) < m) (a : ZMod m) (b : ℕ → ZMod m) :
    (∑ j ∈ ordinaryTupleSums Q s, ∑ t : ZMod m,
      ‖mixedPrimeSum P (t*a) (b j)‖ ^ (2*k)) ≤
      (s*(U-L) : ℕ) * ((m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k))) := by
  apply (mixed_parameter_moment_le _ hX hprime hcop hlower hupper hsize a b).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast ordinaryTupleSums_card_le hs hL hU

end NField.Alignment.KaratsubaTupleSumRange
