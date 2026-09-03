/-
Author: Alexander S. Petty
-/

import Mathlib

/-!
# Eventually periodic digit blocks

Long division is a finite-state orbit.  This module proves that the remainder
orbit, and therefore the digit stream of a rational number, is eventually
periodic.  It then proves the exact block-count obstruction used to distinguish
such a stream from a normal expansion: a tail of period `L` realizes at most
`L` different blocks of any fixed length.
-/

namespace NField.Alignment.EventuallyPeriodicDigitBlocks

open Function

/-- A finite deterministic orbit repeats with a positive period no later than
the number of states. -/
theorem finite_orbit_eventually_periodic {α : Type*} [Fintype α]
    (f : α → α) (x : α) :
    ∃ μ L : ℕ, 0 < L ∧ μ + L ≤ Fintype.card α ∧
      ∀ t : ℕ, (f^[μ + t + L]) x = (f^[μ + t]) x := by
  let orbit : Fin (Fintype.card α + 1) → α := fun i => (f^[i.1]) x
  obtain ⟨i, j, hij, horbit⟩ := Fintype.exists_ne_map_eq_of_card_lt orbit (by simp)
  have hlt : i.1 < j.1 ∨ j.1 < i.1 := by
    rcases Nat.lt_trichotomy i.1 j.1 with h | h | h
    · exact Or.inl h
    · exact False.elim (hij (Fin.ext h))
    · exact Or.inr h
  rcases hlt with hlt | hlt
  · refine ⟨i.1, j.1 - i.1, Nat.sub_pos_of_lt hlt, ?_, ?_⟩
    · have hj : j.1 ≤ Fintype.card α := Nat.le_of_lt_succ j.2
      omega
    · intro t
      have happly := congrArg (fun y => (f^[t]) y) horbit
      simp only [orbit] at happly
      simpa [Function.iterate_add_apply, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_sub_of_le (Nat.le_of_lt hlt)] using happly.symm
  · refine ⟨j.1, i.1 - j.1, Nat.sub_pos_of_lt hlt, ?_, ?_⟩
    · have hi : i.1 ≤ Fintype.card α := Nat.le_of_lt_succ i.2
      omega
    · intro t
      have happly := congrArg (fun y => (f^[t]) y) horbit
      simp only [orbit] at happly
      simpa [Function.iterate_add_apply, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_sub_of_le (Nat.le_of_lt hlt)] using happly

/-- One long-division remainder step. -/
def remainderStep (b n r : ℕ) : ℕ :=
  (b * r) % n

/-- The remainder before digit position `j` in the fractional expansion of
`a/n`. -/
def remainderState (b n a j : ℕ) : ℕ :=
  (b ^ j * a) % n

/-- The base-`b` digit at position `j` in the fractional expansion of `a/n`. -/
def rationalDigit (b n a j : ℕ) : ℕ :=
  (b * remainderState b n a j) / n

theorem remainderState_zero (b n a : ℕ) :
    remainderState b n a 0 = a % n := by
  simp [remainderState]

theorem remainderState_succ (b n a j : ℕ) :
    remainderState b n a (j + 1) =
      remainderStep b n (remainderState b n a j) := by
  unfold remainderState remainderStep
  calc
    (b ^ (j + 1) * a) % n = (b * (b ^ j * a)) % n := by
      congr 1
      rw [pow_succ]
      ring
    _ = (b * ((b ^ j * a) % n)) % n := by
      rw [Nat.mul_mod b (b ^ j * a) n,
        Nat.mul_mod b ((b ^ j * a) % n) n, Nat.mod_mod]

/-- The long-division remainder is exactly an iterate of the finite remainder
transition. -/
theorem remainderState_eq_iterate (b n a j : ℕ) :
    remainderState b n a j = (remainderStep b n)^[j] (a % n) := by
  induction j with
  | zero => simp [remainderState_zero]
  | succ j ih =>
      rw [remainderState_succ, ih]
      simpa [Nat.succ_eq_add_one] using
        (Function.iterate_succ_apply' (remainderStep b n) j (a % n)).symm

/-- Every rational remainder orbit, hence every canonical fractional digit
stream, is eventually periodic. -/
theorem rational_digits_eventually_periodic {b n a : ℕ} (hn : 0 < n) :
    ∃ μ L : ℕ, 0 < L ∧ μ + L ≤ n ∧
      ∀ t : ℕ, rationalDigit b n a (μ + t + L) =
        rationalDigit b n a (μ + t) := by
  let step : Fin n → Fin n := fun r =>
    ⟨remainderStep b n r.1, Nat.mod_lt _ hn⟩
  let initial : Fin n := ⟨a % n, Nat.mod_lt _ hn⟩
  obtain ⟨μ, L, hL, hbound, hperiod⟩ :=
    finite_orbit_eventually_periodic step initial
  refine ⟨μ, L, hL, by simpa using hbound, ?_⟩
  intro t
  have hiterate : ∀ j : ℕ,
      ((step^[j]) initial).1 = (remainderStep b n)^[j] (a % n) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact congrArg (remainderStep b n) ih
  have hrem : remainderState b n a (μ + t + L) =
      remainderState b n a (μ + t) := by
    rw [remainderState_eq_iterate, remainderState_eq_iterate]
    calc
      (remainderStep b n)^[μ + t + L] (a % n) =
          ((step^[μ + t + L]) initial).1 := (hiterate _).symm
      _ = ((step^[μ + t]) initial).1 := congrArg Fin.val (hperiod t)
      _ = (remainderStep b n)^[μ + t] (a % n) := hiterate _
  simp [rationalDigit, hrem]

/-- Every rational digit lies in the base alphabet. -/
theorem rationalDigit_lt_base {b n a j : ℕ} (hb : 0 < b) (hn : 0 < n) :
    rationalDigit b n a j < b := by
  unfold rationalDigit
  rw [Nat.div_lt_iff_lt_mul hn]
  exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hn) hb

/-- The canonical digit stream, with its alphabet bound carried in the type. -/
def rationalDigitFin (b n a : ℕ) (hb : 0 < b) (hn : 0 < n) :
    ℕ → Fin b := fun j =>
  ⟨rationalDigit b n a j, rationalDigit_lt_base hb hn⟩

/-- A length-`k` digit block beginning at `start`. -/
def digitBlock {b : ℕ} (d : ℕ → Fin b) (start k : ℕ) : Fin k → Fin b :=
  fun i => d (start + i.1)

/-- Iterating a one-period identity removes any whole number of periods. -/
theorem periodic_tail_add_mul {β : Type*} {d : ℕ → β} {μ L : ℕ}
    (hperiod : ∀ t : ℕ, d (μ + t + L) = d (μ + t))
    (r q : ℕ) : d (μ + (r + q * L)) = d (μ + r) := by
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        d (μ + (r + (q + 1) * L)) = d (μ + (r + q * L) + L) := by
          congr 1
          simp [Nat.succ_mul, Nat.add_assoc]
        _ = d (μ + (r + q * L)) := hperiod (r + q * L)
        _ = d (μ + r) := ih

/-- Every block in a periodic tail is determined by one of its `L` starting
phases. -/
theorem periodic_tail_block_eq_phase {b μ L k t : ℕ} {d : ℕ → Fin b}
    (hperiod : ∀ s : ℕ, d (μ + s + L) = d (μ + s)) :
    digitBlock d (μ + t) k =
      digitBlock d (μ + t % L) k := by
  funext i
  have ht : t % L + (t / L) * L = t := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div t L)
  unfold digitBlock
  have hreduce := periodic_tail_add_mul hperiod (t % L + i.1) (t / L)
  rw [show μ + t + i.1 = μ + (t % L + i.1 + (t / L) * L) by omega]
  simpa [Nat.add_assoc] using hreduce

/-- At most `L` different length-`k` blocks occur in a tail of period `L`. -/
theorem periodic_tail_blocks_at_most_period {b μ L k : ℕ} {d : ℕ → Fin b}
    (hL : 0 < L) (hperiod : ∀ s : ℕ, d (μ + s + L) = d (μ + s)) :
    ∃ phaseBlock : Fin L → (Fin k → Fin b),
      (∀ t : ℕ, digitBlock d (μ + t) k =
        phaseBlock ⟨t % L, Nat.mod_lt _ hL⟩) ∧
      Fintype.card (Set.range phaseBlock) ≤ L := by
  let phaseBlock : Fin L → (Fin k → Fin b) := fun r =>
    digitBlock d (μ + r.1) k
  refine ⟨phaseBlock, ?_, ?_⟩
  · intro t
    exact periodic_tail_block_eq_phase hperiod
  · simpa [Fintype.card_fin] using Fintype.card_range_le phaseBlock

/-- If the alphabet has more length-`k` words than the tail has phases, one
word is absent from every block beginning in the tail. -/
theorem periodic_tail_omits_block {b μ L k : ℕ} {d : ℕ → Fin b}
    (hL : 0 < L) (hperiod : ∀ s : ℕ, d (μ + s + L) = d (μ + s))
    (hcard : L < b ^ k) :
    ∃ word : Fin k → Fin b,
      ∀ t : ℕ, digitBlock d (μ + t) k ≠ word := by
  let phaseBlock : Fin L → (Fin k → Fin b) := fun r =>
    digitBlock d (μ + r.1) k
  have hnot : ¬Function.Surjective phaseBlock := by
    intro hsurj
    have hle := Fintype.card_le_of_surjective phaseBlock hsurj
    simp only [Fintype.card_fun, Fintype.card_fin] at hle
    omega
  simp only [Function.Surjective, not_forall] at hnot
  obtain ⟨word, hword⟩ := hnot
  push Not at hword
  refine ⟨word, ?_⟩
  intro t heq
  have hphase := periodic_tail_block_eq_phase (k := k) hperiod (t := t)
  exact hword ⟨t % L, Nat.mod_lt _ hL⟩ (hphase.symm.trans heq)

/-- A rational base-`b` expansion omits a length-`k` word from its eventual
tail once `b^k` exceeds the denominator, and therefore cannot be normal. -/
theorem rational_digit_tail_omits_block {b n a k : ℕ}
    (hb : 0 < b) (hn : 0 < n) (hcard : n < b ^ k) :
    ∃ μ L : ℕ, 0 < L ∧ μ + L ≤ n ∧
      ∃ word : Fin k → Fin b,
        ∀ t : ℕ,
          digitBlock (rationalDigitFin b n a hb hn) (μ + t) k ≠ word := by
  obtain ⟨μ, L, hL, hbound, hperiod⟩ :=
    rational_digits_eventually_periodic (b := b) (n := n) (a := a) hn
  have hperiodFin : ∀ t : ℕ,
      rationalDigitFin b n a hb hn (μ + t + L) =
        rationalDigitFin b n a hb hn (μ + t) := by
    intro t
    apply Fin.ext
    exact hperiod t
  have hLcard : L < b ^ k := lt_of_le_of_lt (by omega) hcard
  exact ⟨μ, L, hL, hbound,
    periodic_tail_omits_block hL hperiodFin hLcard⟩

/-- In every genuine base, each rational digit stream has some finite word
that never occurs after the periodic tail begins. -/
theorem rational_digit_tail_omits_some_block {b n a : ℕ}
    (hb : 2 ≤ b) (hn : 0 < n) :
    ∃ k μ L : ℕ, 0 < L ∧ μ + L ≤ n ∧
      ∃ word : Fin k → Fin b,
        ∀ t : ℕ,
          digitBlock (rationalDigitFin b n a (by omega) hn) (μ + t) k ≠ word := by
  have hcard : n < b ^ n := Nat.lt_pow_self (by omega)
  obtain ⟨μ, L, hL, hbound, word, hword⟩ :=
    rational_digit_tail_omits_block (b := b) (n := n) (a := a) (k := n)
      (by omega) hn hcard
  exact ⟨n, μ, L, hL, hbound, word, hword⟩

end NField.Alignment.EventuallyPeriodicDigitBlocks
