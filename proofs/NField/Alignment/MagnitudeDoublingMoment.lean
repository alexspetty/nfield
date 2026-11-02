/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeMomentArithmetic

/-!
# Exact centered digit pairing under doubling

Both carry cases are evaluated by splitting their finite ranges at the
actual wrap point. Each yields half the centered square mass. These are
identities for every odd modulus, not estimates from numerical samples.
-/

set_option autoImplicit false
open scoped BigOperators

namespace NField.Alignment.PrimeSquareMagnitudeFamily

private theorem sum_quadratic (n : ℕ) (A B C : ℝ) :
    (∑ k ∈ Finset.range n, (A*(k:ℝ)^2+B*k+C)) =
      A*n*(n-1)*(2*n-1)/6 + B*n*(n-1)/2 + C*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem centered_double_zero (h : ℕ) :
    (∑ k ∈ Finset.range (2*h+1),
      ((k:ℝ)-h)*(((2*k) % (2*h+1):ℕ)-h:ℝ)) =
      (2*(h:ℝ)+1)*h*(h+1)/6 := by
  have hs : 2*h+1 = (h+1)+h := by omega
  have heq :
      (∑ k ∈ Finset.range (2*h+1),
        ((k:ℝ)-h)*(((2*k) % (2*h+1):ℕ)-h:ℝ)) =
      (∑ k ∈ Finset.range (h+1),
        (2*(k:ℝ)^2+(-3*(h:ℝ))*k+(h:ℝ)^2)) +
      ∑ k ∈ Finset.range h,
        (2*(k:ℝ)^2+(3-h)*k+(1-h)) := by
    rw [hs, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [Nat.mod_eq_of_lt (by omega : 2*k < (h+1)+h)]
      push_cast
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hm : 2*(h+1+k) % ((h+1)+h) = 2*k+1 := by
        have hv : 2*(h+1+k) = ((h+1)+h)+(2*k+1) := by omega
        rw [hv, Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : 2*k+1 < (h+1)+h)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hm]
      push_cast
      ring
  rw [heq, sum_quadratic, sum_quadratic]
  push_cast
  ring

theorem centered_double_one (h : ℕ) :
    (∑ k ∈ Finset.range (2*h+1),
      ((k:ℝ)-h)*(((2*k+1) % (2*h+1):ℕ)-h:ℝ)) =
      (2*(h:ℝ)+1)*h*(h+1)/6 := by
  have hs : 2*h+1 = h+(h+1) := by omega
  have heq :
      (∑ k ∈ Finset.range (2*h+1),
        ((k:ℝ)-h)*(((2*k+1) % (2*h+1):ℕ)-h:ℝ)) =
      (∑ k ∈ Finset.range h,
        (2*(k:ℝ)^2+(1-3*h)*k+((h:ℝ)^2-h))) +
      ∑ k ∈ Finset.range (h+1),
        (2*(k:ℝ)^2+(-h)*k+0) := by
    rw [hs, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [Nat.mod_eq_of_lt (by omega : 2*k+1 < h+(h+1))]
      push_cast
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hm : (2*(h+k)+1) % (h+(h+1)) = 2*k := by
        have hv : 2*(h+k)+1 = (h+(h+1))+2*k := by omega
        rw [hv, Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : 2*k < h+(h+1))]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hm]
      push_cast
      ring
  rw [heq, sum_quadratic, sum_quadratic]
  push_cast
  ring

theorem centered_double_moment {p : ℕ} (hpodd : Odd p)
    (ε : ℕ) (hε : ε ≤ 1) :
    (∑ k ∈ Finset.range p,
      (((k:ℝ)-((p:ℝ)-1)/2)/p) *
        ((((2*k+ε)%p:ℕ)-((p:ℝ)-1)/2)/p)) =
      ((p:ℝ)^2-1)/(24*p) := by
  obtain ⟨h, hh⟩ := hpodd
  have hp : p = 2*h+1 := by omega
  subst p
  have hsum : (∑ k ∈ Finset.range (2*h+1),
      ((k:ℝ)-h)*(((2*k+ε)%(2*h+1):ℕ)-h:ℝ)) =
      (2*(h:ℝ)+1)*h*(h+1)/6 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · simpa using centered_double_zero h
    · exact centered_double_one h
  have heq (k : ℕ) :
      (((k:ℝ)-((2*h+1:ℕ)-1:ℝ)/2)/(2*h+1:ℕ)) *
        ((((2*k+ε)%(2*h+1):ℕ)-((2*h+1:ℕ)-1:ℝ)/2)/(2*h+1:ℕ)) =
      (((k:ℝ)-h)*(((2*k+ε)%(2*h+1):ℕ)-h:ℝ))/(2*(h:ℝ)+1)^2 := by
    have hp0 : (2*(h:ℝ)+1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  simp_rw [heq]
  rw [← Finset.sum_div, hsum]
  have hp0 : (2*(h:ℝ)+1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring


/-- Doubling preserves nonzero representatives at every odd modulus. -/
theorem odd_double_residue_pos {q c : ℕ} (hq : Odd q) (hc0 : 0 < c) (hcq : c < q) :
    0 < (2*c)%q := by
  by_contra h
  have hz : (2*c)%q = 0 := by omega
  have hdiv : q ∣ c := hq.coprime_two_right.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hz)
  exact (Nat.le_of_dvd hc0 hdiv).not_gt hcq

/-- Both halves of the literal J(q) split, including the odd wrap point. -/
theorem odd_doubling_split {q : ℕ} (hq : Odd q) :
    (∑ c ∈ Finset.Ico 1 q, (c : ℝ) * (2 * (((2*c)%q : ℕ) : ℝ) - q)) =
      4 * (∑ c ∈ Finset.Ico 1 q, (c : ℝ)^2) -
        q * (∑ c ∈ Finset.Ico 1 q, (c : ℝ)) -
        2*q * (∑ c ∈ Finset.Ico ((q+1)/2) q, (c : ℝ)) := by
  classical
  obtain ⟨h, hh⟩ := hq
  have hq : q = 2*h+1 := by omega
  have hfilter : (Finset.Ico 1 q).filter (fun c => (q+1)/2 ≤ c) =
      Finset.Ico ((q+1)/2) q := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [← hfilter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := Finset.mem_Ico.mp hc
  by_cases hwrap : (q+1)/2 ≤ c
  · have hlow : q ≤ 2*c := by omega
    have hhigh : 2*c-q < q := by omega
    rw [if_pos hwrap, Nat.mod_eq_sub_mod hlow, Nat.mod_eq_of_lt hhigh,
      Nat.cast_sub hlow]
    push_cast
    ring
  · have hlow : 2*c < q := by omega
    rw [if_neg hwrap, Nat.mod_eq_of_lt hlow]
    push_cast
    ring

/-- The literal odd-modulus doubling sum J(q) in Proposition 8's written proof.
The zero index contributes zero; no primality hypothesis is needed. -/
theorem odd_doubling_sum_range {q : ℕ} (hq : Odd q) :
    (∑ c ∈ Finset.range q, (c : ℝ) * (2 * (((2*c)%q : ℕ) : ℝ) - q)) =
      (q : ℝ) * (q-1) * (q-5) / 12 := by
  obtain ⟨h, hh⟩ := hq
  have hq : q = 2*h+1 := by omega
  subst q
  have hs : 2*h+1 = (h+1)+h := by omega
  have heq :
      (∑ c ∈ Finset.range (2*h+1),
        (c : ℝ) * (2 * (((2*c)%(2*h+1) : ℕ) : ℝ) - (2*h+1:ℕ))) =
      (∑ k ∈ Finset.range (h+1),
        (4*(k:ℝ)^2 + (-(2*(h:ℝ)+1))*k + 0)) +
      ∑ k ∈ Finset.range h,
        (4*(k:ℝ)^2 + (2*(h:ℝ)+5)*k + ((h:ℝ)+1)*(1-2*h)) := by
    rw [hs, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [Nat.mod_eq_of_lt (by omega : 2*k < (h+1)+h)]
      push_cast
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hm : 2*(h+1+k) % ((h+1)+h) = 2*k+1 := by
        have hv : 2*(h+1+k) = ((h+1)+h)+(2*k+1) := by omega
        rw [hv, Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : 2*k+1 < (h+1)+h)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hm]
      push_cast
      ring
  rw [heq]
  rw [sum_quadratic, sum_quadratic]
  push_cast
  ring


/-- J(q) on the literal indices 1 <= c < q, with ordinary modular representatives. -/
theorem odd_doubling_sum {q : ℕ} (hq : Odd q) :
    (∑ c ∈ Finset.Ico 1 q, (c : ℝ) * (2 * (((2*c)%q : ℕ) : ℝ) - q)) =
      (q : ℝ) * (q-1) * (q-5) / 12 := by
  rw [← odd_doubling_sum_range hq]
  apply Finset.sum_subset
  · intro c hc
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hc).2
  · intro c hc hnot
    have hcr := Finset.mem_range.mp hc
    have hc0 : c = 0 := by
      simp only [Finset.mem_Ico, not_and] at hnot
      omega
    simp [hc0]

/-- Exact full-minus-lifted polynomial arithmetic for the proof's J table.
This arithmetic identity in fact holds for every odd b. The character-table
orthogonality and lifted-character identities are separate obligations. -/
theorem odd_doubling_square_subtraction {b : ℕ} (hb : Odd b) :
    (∑ c ∈ Finset.Ico 1 (b^2),
      (c : ℝ) * (2 * (((2*c)%(b^2) : ℕ) : ℝ) - (b^2:ℕ))) -
      (b : ℝ)^2 * (∑ c ∈ Finset.Ico 1 b,
        (c : ℝ) * (2 * (((2*c)%b : ℕ) : ℝ) - b)) =
      (b : ℝ)^2 * (b-1) * ((b:ℝ)^3-5) / 12 := by
  rw [odd_doubling_sum (q := b^2) hb.pow, odd_doubling_sum hb]
  push_cast
  ring

end NField.Alignment.PrimeSquareMagnitudeFamily
