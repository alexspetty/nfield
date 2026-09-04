/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

/-!
Finite diagonal-slice definitions for the Bernoulli factorization paper.

This module follows the paper's forced digit diagonal
`G_{ell,b} = {n : floor(n / b^ell) = n mod b}` and its
parametrization `n = b^ell*q + q + b*t`.
-/

namespace NField.DiagonalSlice

/-- Boolean membership in the digit diagonal `G_{ell,b}`. -/
def diagonalMember (b ell n : Nat) : Bool :=
  n / (b ^ ell) == n % b

/-- The paper's parametrization of the diagonal slices. -/
def diagonalParam (b ell q t : Nat) : Nat :=
  (b ^ ell) * q + q + b * t

/-- The slice increment `floor((n+1)a/m) - floor(na/m)`. -/
def sliceIncrement (m n a : Nat) : Int :=
  Int.ofNat (((n + 1) * a) / m) - Int.ofNat ((n * a) / m)

/-- If `ell >= 1`, then `b` divides `b^ell`. -/
theorem dvd_pow_of_one_le (b ell : Nat) (hell : 1 ≤ ell) : b ∣ b ^ ell := by
  cases ell with
  | zero => omega
  | succ k =>
      rw [Nat.pow_succ']
      exact Nat.dvd_mul_right b (b ^ k)

/-- Rewrite `b^ell` by peeling off one power of `b`. -/
theorem pow_eq_mul_pred (b ell : Nat) (hell : 1 ≤ ell) :
    b ^ ell = b * b ^ (ell - 1) := by
  cases ell with
  | zero => omega
  | succ k =>
      simp [Nat.pow_succ']

/-- Rewrite the next power in the direction useful for division bounds. -/
theorem pow_succ_eq_mul (b ell : Nat) :
    b ^ (ell + 1) = b ^ ell * b := by
  rw [Nat.pow_succ]

/-- The parametrized tail `q + b*t` is smaller than `b^ell` in the paper's range. -/
theorem diagonalParam_tail_lt_pow (b ell q t : Nat)
    (hell : 1 ≤ ell) (hq : q < b) (ht : t < b ^ (ell - 1)) :
    q + b * t < b ^ ell := by
  cases ell with
  | zero => omega
  | succ k =>
      have ht' : t + 1 ≤ b ^ k := by
        simpa using Nat.succ_le_of_lt ht
      have hq' : q + b * t < b + b * t := by omega
      have hbt : b + b * t = b * (t + 1) := by
        rw [Nat.mul_succ]
        omega
      have hle : b * (t + 1) ≤ b * b ^ k := Nat.mul_le_mul_left b ht'
      calc
        q + b * t < b + b * t := hq'
        _ = b * (t + 1) := hbt
        _ ≤ b * b ^ k := hle
        _ = b ^ (Nat.succ k) := by rw [Nat.pow_succ']

/-- A parametrized diagonal slice satisfies the defining diagonal condition. -/
theorem diagonalParam_member_of_tail_lt (b ell q t : Nat)
    (hb : 0 < b) (hell : 1 ≤ ell)
    (hsmall : q + b * t < b ^ ell) (hq : q < b) :
    diagonalMember b ell (diagonalParam b ell q t) = true := by
  unfold diagonalMember diagonalParam
  have hp : 0 < b ^ ell := Nat.pow_pos hb
  have hdiv : ((b ^ ell) * q + (q + b * t)) / (b ^ ell) = q := by
    rw [Nat.mul_add_div hp q (q + b * t)]
    rw [Nat.div_eq_of_lt hsmall]
    simp
  have hpowmod : b ^ ell % b = 0 := by
    cases ell with
    | zero => omega
    | succ k =>
        rw [Nat.pow_succ]
        exact Nat.mul_mod_left (b ^ k) b
  have hmod : ((b ^ ell) * q + (q + b * t)) % b = q := by
    rw [Nat.add_mod, Nat.add_mod]
    simp [Nat.mul_mod, hpowmod, Nat.mod_eq_of_lt hq]
  have hassoc :
      (b ^ ell) * q + q + b * t = (b ^ ell) * q + (q + b * t) := by
    omega
  rw [hassoc, hdiv, hmod]
  simp

/-- The paper's diagonal parametrization lands in `G_{ell,b}`. -/
theorem diagonalParam_member (b ell q t : Nat)
    (hb : 0 < b) (hell : 1 ≤ ell)
    (hq : q < b) (ht : t < b ^ (ell - 1)) :
    diagonalMember b ell (diagonalParam b ell q t) = true := by
  exact diagonalParam_member_of_tail_lt b ell q t hb hell
    (diagonalParam_tail_lt_pow b ell q t hell hq ht) hq

/-- Every diagonal member below `b^(ell+1)` has the paper's `q,t` parametrization. -/
theorem diagonalMember_param_exists (b ell n : Nat)
    (hb : 0 < b) (hell : 1 ≤ ell)
    (hn : n < b ^ (ell + 1))
    (hdiag : diagonalMember b ell n = true) :
    ∃ q t, q < b ∧ t < b ^ (ell - 1) ∧ n = diagonalParam b ell q t := by
  let q := n / (b ^ ell)
  let s := n % (b ^ ell)
  let t := s / b
  have hq_eq_nb : q = n % b := by
    unfold q
    unfold diagonalMember at hdiag
    simpa using hdiag
  have hs_mod : s % b = q := by
    unfold s
    rw [Nat.mod_mod_of_dvd n (dvd_pow_of_one_le b ell hell)]
    exact hq_eq_nb.symm
  have hs_eq : s = q + b * t := by
    unfold t
    have h := Nat.mod_add_div s b
    rw [hs_mod] at h
    exact h.symm
  have hq : q < b := by
    unfold q
    rw [pow_succ_eq_mul] at hn
    exact Nat.div_lt_of_lt_mul hn
  have hs_lt : s < b ^ ell := by
    unfold s
    exact Nat.mod_lt n (Nat.pow_pos hb)
  have ht : t < b ^ (ell - 1) := by
    unfold t
    rw [pow_eq_mul_pred b ell hell] at hs_lt
    exact Nat.div_lt_of_lt_mul hs_lt
  refine ⟨q, t, hq, ht, ?_⟩
  unfold diagonalParam q s at *
  have hdecomp := Nat.div_add_mod n (b ^ ell)
  rw [hs_eq] at hdecomp
  omega

end NField.DiagonalSlice
