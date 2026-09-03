/-
Author: Alexander S. Petty
-/

import NField.Alignment.SubgroupOrbitJacobiExpansion

/-!
# Finite-state orbit boundaries

Long division coupled to a deterministic finite automaton is still a map on a
finite state space.  Every trajectory therefore enters a cycle.  On a cycle,
predecessor minus current value is the intrinsic dynamical boundary.
-/

namespace NField.Alignment.FiniteStateOrbitBoundary

open scoped BigOperators ZMod

/-- A finite trajectory repeats before `card alpha + 1` states have been
visited. -/
theorem finiteTrajectory_repeats
    {alpha : Type*} [Fintype alpha] (T : alpha → alpha) (x : alpha) :
    ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card alpha ∧
      T^[i] x = T^[j] x := by
  let orbitPrefix : Fin (Fintype.card alpha + 1) → alpha :=
    fun n => T^[n.val] x
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    orbitPrefix (by simp)
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact ⟨i, j, hijlt, by omega, heq⟩
  · exact ⟨j, i, hjilt, by omega, heq.symm⟩

/-- A repeated finite trajectory is periodic from the first repeated state
onward. -/
theorem finiteTrajectory_eventuallyPeriodic
    {alpha : Type*} [Fintype alpha] (T : alpha → alpha) (x : alpha) :
    ∃ start period : ℕ, 0 < period ∧
      ∀ n : ℕ, T^[start + n + period] x = T^[start + n] x := by
  obtain ⟨i, j, hij, _, heq⟩ := finiteTrajectory_repeats T x
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, fun n => ?_⟩
  have hindex : i + n + (j - i) = n + j := by
    calc
      i + n + (j - i) = n + (i + (j - i)) := by omega
      _ = n + j := by rw [Nat.add_sub_of_le hij.le]
  calc
    T^[i + n + (j - i)] x = T^[n + j] x := by rw [hindex]
    _ = T^[n] (T^[j] x) := Function.iterate_add_apply T n j x
    _ = T^[n] (T^[i] x) := by rw [heq]
    _ = T^[i + n] x := by
      simpa [Nat.add_comm] using (Function.iterate_add_apply T n i x).symm

/-- The emitted base-`b` digit from the least nonnegative representative of a
unit remainder. -/
def emittedDigit (b q : ℕ) (R : (ZMod q)ˣ) : ℕ :=
  b * R.val.val / q

/-- Remainder multiplication coupled to a deterministic automaton update. -/
def liftedTransition
    {Q : Type*} (b q : ℕ) (hbq : b.Coprime q)
    (delta : Q → ℕ → Q) : (ZMod q)ˣ × Q → (ZMod q)ˣ × Q :=
  fun state =>
    (ZMod.unitOfCoprime b hbq * state.1,
      delta state.2 (emittedDigit b q state.1))

/-- The finite-state lift of long division is eventually periodic. -/
theorem liftedTransition_eventuallyPeriodic
    {Q : Type*} [Fintype Q] (b q : ℕ) [NeZero q]
    (hbq : b.Coprime q) (delta : Q → ℕ → Q)
    (initial : (ZMod q)ˣ × Q) :
    ∃ start period : ℕ, 0 < period ∧
      ∀ n : ℕ,
        (liftedTransition b q hbq delta)^[start + n + period] initial =
          (liftedTransition b q hbq delta)^[start + n] initial :=
  finiteTrajectory_eventuallyPeriodic (liftedTransition b q hbq delta) initial

/-- Predecessor minus current value on a finite cycle. -/
def dynamicalBoundary
    {C A : Type*} [AddGroup A] (cycle : C ≃ C) (weight : C → A)
    (z : C) : A :=
  weight (cycle.symm z) - weight z

/-- A Boolean predicate is a cycle weight and has the stated dynamical
boundary. -/
noncomputable def booleanDynamicalBoundary
    {C A : Type*} [AddGroup A] [One A]
    (cycle : C ≃ C) (good : Set C) (z : C) : A := by
  classical
  exact dynamicalBoundary cycle (fun x => if x ∈ good then 1 else 0) z

/-- Every dynamical boundary has total mass zero on its finite cycle. -/
theorem dynamicalBoundary_sum_zero
    {C A : Type*} [Fintype C] [AddCommGroup A]
    (cycle : C ≃ C) (weight : C → A) :
    ∑ z : C, dynamicalBoundary cycle weight z = 0 := by
  unfold dynamicalBoundary
  rw [Finset.sum_sub_distrib, Equiv.sum_comp cycle.symm]
  simp

/-- The Boolean boundary is exactly predecessor-indicator minus
current-indicator. -/
theorem booleanDynamicalBoundary_eq
    {C A : Type*} [AddGroup A] [One A]
    (cycle : C ≃ C) (good : Set C)
    [DecidablePred fun z => z ∈ good] (z : C) :
    booleanDynamicalBoundary (A := A) cycle good z =
      (if cycle.symm z ∈ good then 1 else 0) -
        (if z ∈ good then 1 else 0) := by
  classical
  unfold booleanDynamicalBoundary dynamicalBoundary
  by_cases hpre : cycle.symm z ∈ good <;>
    by_cases hcur : z ∈ good <;> simp [hpre, hcur]

end NField.Alignment.FiniteStateOrbitBoundary
