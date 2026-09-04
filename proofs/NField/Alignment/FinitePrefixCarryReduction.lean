/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

namespace NField.Alignment.FinitePrefixCarryReduction

def remainderAfter (b q r ell : ℕ) : ℕ := (b ^ ell * r) % q

def digitReadout (b q r ell : ℕ) : ℕ :=
  b * remainderAfter b q r ell / q

def greedyDigitDifference (b q r ell : ℕ) : ℕ :=
  b ^ (ell + 1) * r / q - b * (b ^ ell * r / q)

theorem digitReadout_eq_quotient_mod
    (b q r ell : ℕ) (hb : 0 < b) (hq : 0 < q) :
    digitReadout b q r ell = (b ^ (ell + 1) * r / q) % b := by
  let X := b ^ ell * r
  have hdecomp : b * X = q * (b * (X / q)) + b * (X % q) := by
    calc
      b * X = b * (q * (X / q) + X % q) := by rw [Nat.div_add_mod X q]
      _ = q * (b * (X / q)) + b * (X % q) := by ring
  have hquot : b * X / q = b * (X / q) + b * (X % q) / q := by
    rw [hdecomp]
    exact Nat.mul_add_div hq (b * (X / q)) (b * (X % q))
  have hlt : b * (X % q) / q < b := by
    rw [Nat.div_lt_iff_lt_mul hq]
    have hr := Nat.mod_lt X hq
    exact (Nat.mul_lt_mul_left hb).2 hr
  unfold digitReadout remainderAfter
  change b * (X % q) / q = _
  rw [show b ^ (ell + 1) * r = b * X by simp [X, pow_succ', mul_assoc]]
  rw [hquot]
  rw [Nat.mul_add_mod_self_left]
  exact (Nat.mod_eq_of_lt hlt).symm

theorem greedyDigitDifference_eq_readout
    (b q r ell : ℕ) (hq : 0 < q) :
    greedyDigitDifference b q r ell = digitReadout b q r ell := by
  let X := b ^ ell * r
  have hdecomp : b * X = q * (b * (X / q)) + b * (X % q) := by
    calc
      b * X = b * (q * (X / q) + X % q) := by rw [Nat.div_add_mod X q]
      _ = q * (b * (X / q)) + b * (X % q) := by ring
  have hquot : b * X / q = b * (X / q) + b * (X % q) / q := by
    rw [hdecomp]
    exact Nat.mul_add_div hq (b * (X / q)) (b * (X % q))
  unfold greedyDigitDifference digitReadout remainderAfter
  change b ^ (ell + 1) * r / q - b * (X / q) = b * (X % q) / q
  rw [show b ^ (ell + 1) * r = b * X by simp [X, pow_succ', mul_assoc]]
  rw [hquot]
  exact Nat.add_sub_cancel_left _ _

/-- The digit in a padded prefix code, indexed from the most significant
position. -/
def encodedPrefixDigit (b N n ell : ℕ) : ℕ :=
  (n / b ^ (N - 1 - ell)) % b

/-- The cell index `floor (b^N r / q)` contains exactly the first `N`
long-division digits of `r / q`. -/
theorem prefixIndex_digit
    {b q r N ell : ℕ} (hb : 0 < b) (hq : 0 < q)
    (hell : ell < N) :
    encodedPrefixDigit b N (b ^ N * r / q) ell =
      digitReadout b q r ell := by
  unfold encodedPrefixDigit
  have hN : N = (ell + 1) + (N - 1 - ell) := by omega
  let c := b ^ (N - 1 - ell)
  have hc : 0 < c := pow_pos hb _
  rw [hN, pow_add]
  have hexp : ell + 1 + (N - 1 - ell) - 1 - ell = N - 1 - ell := by
    omega
  rw [hexp]
  change (b ^ (ell + 1) * c * r / q / c) % b = _
  have hmul : b ^ (ell + 1) * c * r = (b ^ (ell + 1) * r) * c := by
    ring
  rw [show b ^ (ell + 1) * c * r / q / c =
      b ^ (ell + 1) * c * r / (q * c) by
        rw [Nat.div_div_eq_div_mul]]
  rw [hmul, Nat.mul_div_mul_right _ _ hc]
  rw [← digitReadout_eq_quotient_mod b q r ell hb hq]

/-- Intrinsic weighted count of length-`N` digit prefixes. -/
def intrinsicPrefixCount (b N q : ℕ)
    (Φ : (Fin N → ℕ) → ℂ) : ℂ :=
  ∑ r ∈ Finset.Ico 1 q, Φ (fun ell => digitReadout b q r ell)

/-- A digit-prefix observable transported to the integer cell code. -/
def encodedPrefixWeight (b N : ℕ)
    (Φ : (Fin N → ℕ) → ℂ) (n : ℕ) : ℂ :=
  Φ (fun ell => encodedPrefixDigit b N n ell)


open scoped BigOperators

def prefixFiber (m q n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 q).filter fun r => m * r / q = n

theorem div_eq_iff_bounds {x q n : ℕ} (hq : 0 < q) :
    x / q = n ↔ n * q ≤ x ∧ x < (n + 1) * q := by
  constructor
  · intro h
    constructor
    · rw [← h]
      exact Nat.div_mul_le_self x q
    · rw [← h]
      exact (Nat.div_lt_iff_lt_mul hq).1 (Nat.lt_succ_self _)
  · rintro ⟨hl, hu⟩
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq).2 hu)
    · exact (Nat.le_div_iff_mul_le hq).2 hl

theorem lt_ceilDiv_iff {x y m : ℕ} (hm : 0 < m) :
    x < y ⌈/⌉ m ↔ m * x < y := by
  rw [← not_le, ← not_le]
  exact not_congr (ceilDiv_le_iff_le_mul hm)

theorem prefixFiber_eq_Ico
    {m q n : ℕ} (hm : 0 < m) (hq : 0 < q) (hn : n < m) :
    prefixFiber m q n =
      Finset.Ico (max 1 (n * q ⌈/⌉ m)) ((n + 1) * q ⌈/⌉ m) := by
  ext r
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_Ico]
  rw [div_eq_iff_bounds hq]
  rw [← (ceilDiv_le_iff_le_mul hm)]
  rw [← lt_ceilDiv_iff hm]
  have huq : (n + 1) * q ⌈/⌉ m ≤ q := by
    rw [ceilDiv_le_iff_le_mul hm]
    nlinarith
  constructor
  · rintro ⟨⟨hr1, hrq⟩, hlow, hupp⟩
    exact ⟨max_le_iff.mpr ⟨hr1, hlow⟩, hupp⟩
  · rintro ⟨hlow, hupp⟩
    have hr1 := (max_le_iff.mp hlow).1
    have hrlo := (max_le_iff.mp hlow).2
    exact ⟨⟨hr1, lt_of_lt_of_le hupp huq⟩, hrlo, hupp⟩

theorem prefixFiber_card
    {m q n : ℕ} (hm : 0 < m) (hq : 0 < q) (hn : n < m) :
    (prefixFiber m q n).card =
      ((n + 1) * q ⌈/⌉ m) - max 1 (n * q ⌈/⌉ m) := by
  rw [prefixFiber_eq_Ico hm hq hn, Nat.card_Ico]

theorem ceilDiv_eq_div_add_one_of_mod_ne_zero
    {x m : ℕ} (hm : 0 < m) (hmod : x % m ≠ 0) :
    x ⌈/⌉ m = x / m + 1 := by
  apply Nat.le_antisymm
  · rw [ceilDiv_le_iff_le_mul hm]
    have hrem : x % m ≤ m := (Nat.mod_lt x hm).le
    calc
      x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
      _ ≤ m * (x / m) + m := Nat.add_le_add_left hrem _
      _ = m * (x / m + 1) := by ring
  · apply Nat.succ_le_of_lt
    rw [lt_ceilDiv_iff hm]
    have hrem : 0 < x % m := Nat.pos_of_ne_zero hmod
    calc
      m * (x / m) < m * (x / m) + x % m := Nat.lt_add_of_pos_right hrem
      _ = x := Nat.div_add_mod x m

theorem ceilDiv_add_multiple
    {x m z : ℕ} (hm : 0 < m) :
    (m * z + x) ⌈/⌉ m = z + (x ⌈/⌉ m) := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
  have heq : m * z + x + m - 1 = (x + m - 1) + m * z := by omega
  rw [heq, Nat.add_mul_div_left _ z hm]
  omega

theorem coprime_mul_mod_ne_zero
    {a m n : ℕ} (ha : a.Coprime m) (hn0 : n ≠ 0) (hnm : n < m) :
    (n * a) % m ≠ 0 := by
  intro hzero
  have hdvd : m ∣ n * a := Nat.dvd_of_mod_eq_zero hzero
  have hmn : m ∣ n := (ha.symm.dvd_of_dvd_mul_right hdvd)
  have hnle : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hmn
  omega

theorem prefixFiber_card_slice
    {m q h a n : ℕ} (hm : 0 < m) (hq : q = h * m + a)
    (ha1 : 1 ≤ a) (ham : a < m) (hcop : a.Coprime m)
    (hn : n < m) :
    (prefixFiber m q n).card =
      h + ((n + 1) * a / m - n * a / m) -
        (if n = m - 1 then 1 else 0) := by
  have hqpos : 0 < q := by omega
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
  by_cases hn0 : n = 0
  · subst n
    simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul]
    have hamod : a % m ≠ 0 := by
      rw [Nat.mod_eq_of_lt ham]
      omega

    rw [ceilDiv_eq_div_add_one_of_mod_ne_zero hm hamod]
    have hnotlast : (0 : ℕ) ≠ m - 1 := by omega
    simp [Nat.div_eq_of_lt ham, hnotlast]
  · have hnmod : (n * a) % m ≠ 0 :=
      coprime_mul_mod_ne_zero hcop hn0 hn
    rw [ceilDiv_eq_div_add_one_of_mod_ne_zero hm hnmod]
    by_cases hlast : n = m - 1
    · have hn1 : n + 1 = m := by omega
      rw [hlast, if_pos rfl]
      have hpredsucc : m - 1 + 1 = m := by omega
      rw [hpredsucc]
      have hceil : (m * a) ⌈/⌉ m = a := by
        simpa using (ceilDiv_add_multiple (x := 0) (z := a) hm)
      rw [hceil]
      rw [Nat.mul_div_right _ hm]
      have hmax : max 1 ((m - 1) * h + ((m - 1) * a / m + 1)) =
          (m - 1) * h + ((m - 1) * a / m + 1) := by
        exact max_eq_right (Nat.succ_le_succ (Nat.zero_le _))
      rw [hmax]
      have hdivle : (m - 1) * a / m ≤ a := by
        have hd := Nat.div_le_div_right (c := m)
          (Nat.mul_le_mul_right a (show m - 1 ≤ m by omega))
        simpa [Nat.mul_div_right a hm] using hd
      have hstep : m * h = (m - 1) * h + h := by
        calc
          m * h = (m - 1 + 1) * h := by rw [hpredsucc]
          _ = (m - 1) * h + h := by ring
      omega
    · have hn1lt : n + 1 < m := by omega
      have hn1ne : n + 1 ≠ 0 := by omega
      have hn1mod : ((n + 1) * a) % m ≠ 0 :=
        coprime_mul_mod_ne_zero hcop hn1ne hn1lt
      rw [ceilDiv_eq_div_add_one_of_mod_ne_zero hm hn1mod]
      rw [if_neg hlast]
      have hmax : max 1 (n * h + (n * a / m + 1)) =
          n * h + (n * a / m + 1) := by
        exact max_eq_right (Nat.succ_le_succ (Nat.zero_le _))
      rw [hmax]
      have hdivle : n * a / m ≤ (n + 1) * a / m :=
        Nat.div_le_div_right (Nat.mul_le_mul_right a (Nat.le_succ n))
      have hsumle : n * h + (n * a / m + 1) ≤
          (n + 1) * h + ((n + 1) * a / m + 1) := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_right h (Nat.le_succ n))
          (Nat.add_le_add_right hdivle 1)
      have hstep : (n + 1) * h = n * h + h := by ring
      have hdivstep :
          ((n + 1) * a / m + 1) - (n * a / m + 1) =
            (n + 1) * a / m - n * a / m := by omega
      omega

def prefixWeightedCount (m q : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ r ∈ Finset.Ico 1 q, w (m * r / q)

def weightedCarryCount (m a : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range m,
    (((n + 1) * a / m - n * a / m : ℕ) : ℂ) * w n

/-- Every weighted finite-prefix observable is exactly its weighted cell
count.  Arbitrary word sets are recovered by taking `Φ` to be their indicator. -/
theorem cylinderToCarryCount
    {b N q : ℕ} (hb : 0 < b) (hq : 0 < q)
    (Φ : (Fin N → ℕ) → ℂ) :
    intrinsicPrefixCount b N q Φ =
      prefixWeightedCount (b ^ N) q (encodedPrefixWeight b N Φ) := by
  classical
  unfold intrinsicPrefixCount prefixWeightedCount encodedPrefixWeight
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  funext ell
  exact (prefixIndex_digit hb hq ell.isLt).symm

theorem prefixCell_lt
    {m q r : ℕ} (hm : 0 < m) (hq : 0 < q) (hr : r < q) :
    m * r / q < m := by
  rw [Nat.div_lt_iff_lt_mul hq]
  exact (Nat.mul_lt_mul_left hm).2 hr

theorem prefixWeightedCount_grouped
    {m q : ℕ} (hm : 0 < m) (hq : 0 < q) (w : ℕ → ℂ) :
    prefixWeightedCount m q w =
      ∑ n ∈ Finset.range m, ((prefixFiber m q n).card : ℂ) * w n := by
  classical
  let cell : ℕ → Fin m := fun r =>
    ⟨(m * r / q) % m, Nat.mod_lt _ hm⟩
  unfold prefixWeightedCount
  calc
    (∑ r ∈ Finset.Ico 1 q, w (m * r / q)) =
        ∑ n : Fin m, ∑ r ∈ Finset.Ico 1 q with cell r = n,
          w (m * r / q) := by
            symm
            exact Finset.sum_fiberwise (Finset.Ico 1 q) cell
              (fun r => w (m * r / q))
    _ = ∑ n : Fin m, ((prefixFiber m q n.val).card : ℂ) * w n.val := by
      apply Finset.sum_congr rfl
      intro n _
      have hfilter :
          (Finset.Ico 1 q).filter (fun r => cell r = n) =
            prefixFiber m q n.val := by
        ext r
        simp only [prefixFiber, Finset.mem_filter, Finset.mem_Ico]
        constructor
        · rintro ⟨hrange, hcell⟩
          have hlt := prefixCell_lt hm hq hrange.2
          have hval : (cell r).val = m * r / q := by
            simp [cell, Nat.mod_eq_of_lt hlt]
          exact ⟨hrange, by
            have heq := congrArg Fin.val hcell
            simpa [hval] using heq⟩
        · rintro ⟨hrange, hquot⟩
          refine ⟨hrange, Fin.ext ?_⟩
          simp [cell, hquot, Nat.mod_eq_of_lt n.isLt]
      rw [hfilter]
      calc
        (∑ r ∈ prefixFiber m q n.val, w (m * r / q)) =
            ∑ _r ∈ prefixFiber m q n.val, w n.val := by
              apply Finset.sum_congr rfl
              intro r hr
              have hquot := (Finset.mem_filter.mp hr).2
              rw [hquot]
        _ = ((prefixFiber m q n.val).card : ℂ) * w n.val := by simp
    _ = ∑ n ∈ Finset.range m,
        ((prefixFiber m q n).card : ℂ) * w n := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n hn
      have hnlt := Finset.mem_range.mp hn
      simp [hnlt]

theorem terminalCorrection_le_sliceMultiplicity
    {m a h n : ℕ} (hm : 0 < m) (ha1 : 1 ≤ a)
    (hn : n < m) :
    (if n = m - 1 then 1 else 0) ≤
      h + ((n + 1) * a / m - n * a / m) := by
  by_cases hlast : n = m - 1
  · rw [if_pos hlast]
    have hn1 : n + 1 = m := by omega
    rw [hn1, Nat.mul_div_right a hm]
    have hlt : (m - 1) * a / m < a := by
      rw [Nat.div_lt_iff_lt_mul hm]
      have ha0 : 0 < a := ha1
      nlinarith
    rw [hlast]
    omega
  · simp [hlast]

theorem finitePrefixSliceIdentity
    {m q h a : ℕ} (hm : 0 < m) (hq : q = h * m + a)
    (ha1 : 1 ≤ a) (ham : a < m) (hcop : a.Coprime m)
    (w : ℕ → ℂ) :
    prefixWeightedCount m q w =
      (h : ℂ) * (∑ n ∈ Finset.range m, w n) +
        weightedCarryCount m a w - w (m - 1) := by
  classical
  have hqpos : 0 < q := by omega
  rw [prefixWeightedCount_grouped hm hqpos]
  unfold weightedCarryCount
  have hpoint (n : ℕ) (hn : n < m) :
      ((prefixFiber m q n).card : ℂ) =
        (h : ℂ) + (((n + 1) * a / m - n * a / m : ℕ) : ℂ) -
          ((if n = m - 1 then 1 else 0 : ℕ) : ℂ) := by
    rw [prefixFiber_card_slice hm hq ha1 ham hcop hn]
    rw [Nat.cast_sub (terminalCorrection_le_sliceMultiplicity hm ha1 hn)]
    by_cases hlast : n = m - 1 <;> simp [hlast]
  have hendpoint :
      (∑ n ∈ Finset.range m,
        (((if n = m - 1 then 1 else 0 : ℕ) : ℂ) * w n)) =
        w (m - 1) := by
    rw [Finset.sum_eq_single (m - 1)]
    · simp
    · intro n hn hne
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  calc
    (∑ n ∈ Finset.range m, ((prefixFiber m q n).card : ℂ) * w n) =
        ∑ n ∈ Finset.range m,
          (((h : ℂ) + (((n + 1) * a / m - n * a / m : ℕ) : ℂ) -
            ((if n = m - 1 then 1 else 0 : ℕ) : ℂ)) * w n) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [hpoint n (Finset.mem_range.mp hn)]
    _ = (h : ℂ) * (∑ n ∈ Finset.range m, w n) +
        (∑ n ∈ Finset.range m,
          (((n + 1) * a / m - n * a / m : ℕ) : ℂ) * w n) -
        (∑ n ∈ Finset.range m,
          (((if n = m - 1 then 1 else 0 : ℕ) : ℂ) * w n)) := by
            rw [Finset.mul_sum]
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro n _
            ring
    _ = _ := by rw [hendpoint]

/-- Centered form of the finite-prefix slice identity. -/
theorem finitePrefixCenteredIdentity
    {m q h a : ℕ} (hm : 0 < m) (hq : q = h * m + a)
    (ha1 : 1 ≤ a) (ham : a < m) (hcop : a.Coprime m)
    (w : ℕ → ℂ) :
    prefixWeightedCount m q w -
        (q : ℂ) / (m : ℂ) * (∑ n ∈ Finset.range m, w n) + w (m - 1) =
      weightedCarryCount m a w -
        (a : ℂ) / (m : ℂ) * (∑ n ∈ Finset.range m, w n) := by
  rw [finitePrefixSliceIdentity hm hq ha1 ham hcop w]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqcast : (q : ℂ) = (h : ℂ) * (m : ℂ) + (a : ℂ) := by
    exact_mod_cast hq
  rw [hqcast]
  field_simp [hm0]
  ring

end NField.Alignment.FinitePrefixCarryReduction
