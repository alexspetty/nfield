/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FinitePrefixCarryReduction

namespace NField.Alignment.FiniteCarrierArithmeticCollapse

open scoped BigOperators
open NField.Alignment.FinitePrefixCarryReduction

/-- The ceiling-boundary increment at phase `a`. -/
def ceilingBoundaryIncrement (m a n : ℕ) : ℕ :=
  ((n + 1) * a) ⌈/⌉ m - (n * a) ⌈/⌉ m

/-- The all-denominator ceiling-boundary response. -/
def ceilingBoundaryCount (m a : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range m,
    ((ceilingBoundaryIncrement m a n : ℕ) : ℂ) * w n

lemma ceilDiv_pos_of_pos
    {x m : ℕ} (hm : 0 < m) (hx : 0 < x) :
    0 < x ⌈/⌉ m := by
  by_contra h
  have hz : x ⌈/⌉ m = 0 := Nat.eq_zero_of_not_pos h
  have hle : x ≤ m * 0 := by
    rw [← ceilDiv_le_iff_le_mul hm, hz]
  omega

lemma ceilDiv_mono
    {x y m : ℕ} (hm : 0 < m) (hxy : x ≤ y) :
    x ⌈/⌉ m ≤ y ⌈/⌉ m :=
  (gc_mul_ceilDiv hm).monotone_l hxy

/-- Exact cell multiplicity for every denominator phase, including zero and
nonunit phases.  The endpoint correction is placed on the initial cell. -/
theorem prefixFiber_card_all_denominators
    {m q h a n : ℕ} (hm : 0 < m) (hq : q = h * m + a)
    (hqpos : 0 < q) (ham : a < m) (hn : n < m) :
    (prefixFiber m q n).card + (if n = 0 then 1 else 0) =
      h + ceilingBoundaryIncrement m a n := by
  rw [prefixFiber_card hm hqpos hn]
  have hlower : (n * q) ⌈/⌉ m = n * h + ((n * a) ⌈/⌉ m) := by
    rw [hq]
    have heq : n * (h * m + a) = m * (n * h) + n * a := by ring
    rw [heq, ceilDiv_add_multiple hm]
  have hupper : ((n + 1) * q) ⌈/⌉ m =
      (n + 1) * h + (((n + 1) * a) ⌈/⌉ m) := by
    rw [hq]
    have heq : (n + 1) * (h * m + a) =
        m * ((n + 1) * h) + (n + 1) * a := by ring
    rw [heq, ceilDiv_add_multiple hm]
  rw [hlower, hupper]
  unfold ceilingBoundaryIncrement
  have hceilmono : (n * a) ⌈/⌉ m ≤ ((n + 1) * a) ⌈/⌉ m :=
    ceilDiv_mono hm (Nat.mul_le_mul_right a (Nat.le_succ n))
  by_cases hn0 : n = 0
  · subst n
    simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, zero_ceilDiv,
      if_pos]
    have hceil : a ⌈/⌉ m ≤ 1 := by
      rw [ceilDiv_le_iff_le_mul hm]
      omega
    have hpositive : 1 ≤ h + a ⌈/⌉ m := by
      by_cases hh : h = 0
      · subst h
        have hqa : q = a := by simpa using hq
        have ha : 0 < a := by omega
        have hcpos := ceilDiv_pos_of_pos hm ha
        omega
      · omega
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hqmul : 0 < n * q := Nat.mul_pos hnpos hqpos
    have hceilpos : 0 < (n * q) ⌈/⌉ m := ceilDiv_pos_of_pos hm hqmul
    have hmax : max 1 (n * h + (n * a) ⌈/⌉ m) =
        n * h + (n * a) ⌈/⌉ m := by
      have hlower : (n * q) ⌈/⌉ m =
          n * h + (n * a) ⌈/⌉ m := hlower
      rw [← hlower]
      exact max_eq_right hceilpos
    rw [if_neg hn0, Nat.add_zero, hmax]
    have hhstep : (n + 1) * h = n * h + h := by ring
    omega

def prefixFiberContribution (m q : ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((prefixFiber m q n).card : ℂ) * w n

/-- Pointwise complex form used by the weighted all-denominator identity. -/
theorem prefixFiber_contribution_all_denominators
    {m q h a n : ℕ} (hm : 0 < m) (hq : q = h * m + a)
    (hqpos : 0 < q) (ham : a < m) (hn : n < m) (w : ℕ → ℂ) :
    prefixFiberContribution m q w n =
      ((h : ℂ) + (ceilingBoundaryIncrement m a n : ℕ) -
        ((if n = 0 then 1 else 0 : ℕ) : ℂ)) * w n := by
  unfold prefixFiberContribution
  have hcard := prefixFiber_card_all_denominators hm hq hqpos ham hn
  have hcorrection :
      (if n = 0 then 1 else 0) ≤ h + ceilingBoundaryIncrement m a n := by
    omega
  have heq :
      (prefixFiber m q n).card =
        h + ceilingBoundaryIncrement m a n -
          (if n = 0 then 1 else 0) := by
    omega
  rw [heq, Nat.cast_sub hcorrection]
  by_cases hn0 : n = 0 <;> simp [hn0]

/-- Every weighted finite-prefix source transposes to the denominator phase,
without a coprimality assumption. -/
theorem finitePrefixSliceIdentityAllDenominators
    {m q h a : ℕ} (hm : 0 < m) (hq : q = h * m + a)
    (hqpos : 0 < q) (ham : a < m) (w : ℕ → ℂ) :
    prefixWeightedCount m q w =
      (h : ℂ) * (∑ n ∈ Finset.range m, w n) +
        ceilingBoundaryCount m a w - w 0 := by
  classical
  rw [prefixWeightedCount_grouped hm hqpos]
  unfold ceilingBoundaryCount
  have hendpoint :
      (∑ n ∈ Finset.range m,
        (((if n = 0 then 1 else 0 : ℕ) : ℂ) * w n)) = w 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro n hn hne
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hm)).elim
  calc
    (∑ n ∈ Finset.range m, ((prefixFiber m q n).card : ℂ) * w n) =
        ∑ n ∈ Finset.range m,
          (((h : ℂ) + (ceilingBoundaryIncrement m a n : ℕ) -
            ((if n = 0 then 1 else 0 : ℕ) : ℂ)) * w n) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact prefixFiber_contribution_all_denominators
                hm hq hqpos ham (Finset.mem_range.mp hn) w
    _ = (h : ℂ) * (∑ n ∈ Finset.range m, w n) +
        (∑ n ∈ Finset.range m,
          ((ceilingBoundaryIncrement m a n : ℕ) : ℂ) * w n) -
        (∑ n ∈ Finset.range m,
          (((if n = 0 then 1 else 0 : ℕ) : ℂ) * w n)) := by
            rw [Finset.mul_sum]
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro n _
            ring
    _ = _ := by rw [hendpoint]

/-- Centered all-denominator transposition. -/
theorem finitePrefixCenteredIdentityAllDenominators
    {m q h a : ℕ} (hm : 0 < m) (hq : q = h * m + a)
    (hqpos : 0 < q) (ham : a < m) (w : ℕ → ℂ) :
    prefixWeightedCount m q w -
        (q : ℂ) / (m : ℂ) * (∑ n ∈ Finset.range m, w n) + w 0 =
      ceilingBoundaryCount m a w -
        (a : ℂ) / (m : ℂ) * (∑ n ∈ Finset.range m, w n) := by
  rw [finitePrefixSliceIdentityAllDenominators hm hq hqpos ham w]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqcast : (q : ℂ) = (h : ℂ) * (m : ℂ) + (a : ℂ) := by
    exact_mod_cast hq
  rw [hqcast]
  field_simp [hm0]
  ring

/-- Positional refinement removes the last digit by division. -/
theorem encodedPrefix_dropLast
    {b _N n : ℕ} (hb : 0 < b) :
    (b * n) / b = n := by
  simpa [Nat.mul_comm] using Nat.mul_div_left n hb

/-- The shifted length-`N` face is reduction modulo `b^N`. -/
theorem encodedPrefix_dropFirst
    {b _N d n : ℕ} (hn : n < b ^ _N) :
    (d * b ^ _N + n) % b ^ _N = n := by
  have hpow : 0 < b ^ _N := by
    by_cases hb : b = 0
    · subst b
      cases _N <;> simp_all
    · positivity
  rw [Nat.add_mod]
  have hmul : d * b ^ _N % b ^ _N = 0 := Nat.mul_mod_left _ _
  rw [hmul, Nat.mod_eq_of_lt hn]
  simpa using Nat.mod_eq_of_lt hn

/-- Once the base-supported part of a modulus divides the accumulated
transport multiplier, two differences merge precisely when their surviving
coprime coordinate agrees.  This is the divisibility core of arithmetic
collapse. -/
theorem transportedDifference_merges_iff_survivor_dvd
    {qparallel qperp bpow d : ℕ}
    (hparallel : qparallel ∣ bpow)
    (hcoprime : qperp.Coprime bpow) :
    qparallel * qperp ∣ bpow * d ↔ qperp ∣ d := by
  constructor
  · intro hmerge
    have hqperp_modulus : qperp ∣ qparallel * qperp := by
      exact dvd_mul_left qperp qparallel
    have hqperp_product : qperp ∣ bpow * d :=
      dvd_trans hqperp_modulus hmerge
    exact hcoprime.dvd_of_dvd_mul_left hqperp_product
  · intro hsurvivor
    rcases hparallel with ⟨u, rfl⟩
    rcases hsurvivor with ⟨v, rfl⟩
    use u * v
    ring

/-- A strict state-depletion budget cannot exist on a finite permutation. -/
theorem finitePermutation_no_strict_depletion
    {X : Type} [Fintype X] [Nonempty X]
    (T : Equiv.Perm X) (B : X → ℤ) (ε : ℕ) (hε : 0 < ε)
    (hdec : ∀ x, B (T x) ≤ B x - (ε : ℤ)) : False := by
  classical
  have hsum := Finset.sum_le_sum fun x (_hx : x ∈ Finset.univ) => hdec x
  have hperm : (∑ x : X, B (T x)) = ∑ x : X, B x :=
    Equiv.sum_comp T B
  rw [hperm] at hsum
  have hright :
      (∑ x : X, (B x - (ε : ℤ))) =
        (∑ x : X, B x) - (Fintype.card X : ℤ) * ε := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hright] at hsum
  have hcard : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
  have hprod : 0 < (Fintype.card X : ℤ) * (ε : ℤ) := by positivity
  omega

end NField.Alignment.FiniteCarrierArithmeticCollapse
