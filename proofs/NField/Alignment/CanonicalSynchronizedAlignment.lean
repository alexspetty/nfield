/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SynchronizedPeriodAlignment
import NField.Alignment.SynchronizedOneDigitAlignment
import NField.Alignment.SupportedRoughDecomposition

/-!
# Canonical synchronized alignment

This module connects literal denominator numerators to the canonical supported
and rough decomposition.  The common clearing depth remains explicit, while
the comparison length is the multiplicative period of the base modulo the
canonical rough part.
-/

namespace NField.Alignment

open NField.Alignment.ThreeTier

/-- The full comparison period attached to the canonical rough part. -/
noncomputable def canonicalAlignmentPeriod (b n : ℕ) (hn : 0 < n) : ℕ :=
  coprimeBasePeriod b (roughPart b n) (roughPart_coprime_base hn)

theorem canonicalAlignmentPeriod_pos {b n : ℕ} (hn : 0 < n) :
    0 < canonicalAlignmentPeriod b n hn :=
  coprimeBasePeriod_pos (roughPart_coprime_base hn)

theorem pow_canonicalAlignmentPeriod_mod_eq_one {b n : ℕ} (hn : 0 < n) :
    b ^ canonicalAlignmentPeriod b n hn % roughPart b n =
      1 % roughPart b n :=
  pow_coprimeBasePeriod_mod_eq_one (roughPart_coprime_base hn)

/-- The manuscript's alignment at a chosen valid common clearing depth. -/
noncomputable def canonicalSynchronizedAlignmentReal
    (b n D : ℕ) (hn : 0 < n) : ℝ :=
  clearedAlignmentReal b (roughPart b n) (supportedPart b n) D
    (canonicalAlignmentPeriod b n hn)

/-- Any two valid common clearing depths give the same canonical alignment. -/
theorem canonicalSynchronizedAlignmentReal_independent_of_clearing_depth
    {b n D E : ℕ} (hn : 0 < n)
    (hD : supportedPart b n ∣ b ^ D)
    (hE : supportedPart b n ∣ b ^ E) :
    canonicalSynchronizedAlignmentReal b n D hn =
      canonicalSynchronizedAlignmentReal b n E hn := by
  unfold canonicalSynchronizedAlignmentReal
  exact clearedAlignmentReal_independent_of_clearing_depth_of_period
    (roughPart_pos hn) (supportedPart_pos hn) hD hE
      (pow_canonicalAlignmentPeriod_mod_eq_one hn)

/-- With a supported factor and a coprime rough factor, a numerator terminates
exactly when it is divisible by the rough factor. -/
theorem terminatesInBase_mul_supported_iff {b t m k : ℕ}
    (hmSupported : Supported b m) (hcop : Nat.Coprime t b) :
    TerminatesInBase b k (t * m) ↔ t ∣ k := by
  constructor
  · rintro ⟨D, hterm⟩
    have htProduct : t ∣ k * b ^ D :=
      (dvd_mul_right t m).trans hterm
    exact (hcop.pow_right D).dvd_mul_right.mp htProduct
  · rintro ⟨q, rfl⟩
    rcases hmSupported with ⟨D, hD⟩
    refine ⟨D, ?_⟩
    unfold TerminatesAtDepth
    obtain ⟨c, hc⟩ := hD
    refine ⟨q * c, ?_⟩
    rw [hc]
    ring

/-- The termination criterion on the original positive denominator. -/
theorem canonicalNumerator_terminates_iff {b n k : ℕ} (hn : 0 < n) :
    TerminatesInBase b k n ↔ roughPart b n ∣ k := by
  simpa only [roughPart_mul_supportedPart (b := b) hn] using
    (terminatesInBase_mul_supported_iff (k := k)
      (supportedPart_supported (b := b) hn) (roughPart_coprime_base (b := b) hn))

/-- Literal set of positive proper numerators whose fractions terminate. -/
noncomputable def canonicalTerminatingNumerators (b n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (n - 1)).filter (fun k => TerminatesInBase b k n)

/-- Literal set of positive proper numerators whose fractions do not
terminate. -/
noncomputable def canonicalNonterminatingNumerators (b n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (n - 1)).filter (fun k => ¬TerminatesInBase b k n)

theorem pred_mul_div_eq_pred {t m : ℕ} (ht : 0 < t) (hm : 0 < m) :
    (t * m - 1) / t = m - 1 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hshape : t * (q + 1) - 1 = q * t + (t - 1) := by
    calc
      t * (q + 1) - 1 = t * q + t - 1 := by rw [Nat.mul_add, Nat.mul_one]
      _ = t * q + (t - 1) := Nat.add_sub_assoc ht (t * q)
      _ = q * t + (t - 1) := by rw [Nat.mul_comm t q]
  rw [hshape]
  apply Nat.div_eq_of_lt_le
  · exact Nat.le_add_right (q * t) (t - 1)
  · rw [Nat.add_mul, one_mul]
    exact Nat.add_lt_add_left (Nat.sub_lt ht (by norm_num)) (q * t)

/-- Exactly `supportedPart b n - 1` positive proper fractions terminate. -/
theorem canonicalTerminatingNumerators_card {b n : ℕ} (hn : 0 < n) :
    (canonicalTerminatingNumerators b n).card = supportedPart b n - 1 := by
  classical
  let t := roughPart b n
  let m := supportedPart b n
  have ht : 0 < t := roughPart_pos hn
  have hm : 0 < m := supportedPart_pos hn
  have hdecomp : t * m = n := by
    simpa [t, m] using roughPart_mul_supportedPart (b := b) hn
  have hset : canonicalTerminatingNumerators b n =
      (Finset.Ioc 0 (n - 1)).filter (fun k => t ∣ k) := by
    ext k
    simp only [canonicalTerminatingNumerators, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Ioc]
    rw [canonicalNumerator_terminates_iff hn]
    simp only [t]
    constructor <;> rintro ⟨hkpos, hkle, hdiv⟩
    · exact ⟨by omega, hkle, hdiv⟩
    · exact ⟨by omega, hkle, hdiv⟩
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  calc
    (n - 1) / t = (t * m - 1) / t := by rw [hdecomp]
    _ = m - 1 := pred_mul_div_eq_pred ht hm
    _ = supportedPart b n - 1 := by rfl

/-- The remaining `(roughPart-1)*supportedPart` positive proper fractions are
nonterminating. -/
theorem canonicalNonterminatingNumerators_card {b n : ℕ} (hn : 0 < n) :
    (canonicalNonterminatingNumerators b n).card =
      (roughPart b n - 1) * supportedPart b n := by
  classical
  let s := Finset.Icc 1 (n - 1)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s) (fun k => TerminatesInBase b k n)
  have hterm : (s.filter (fun k => TerminatesInBase b k n)).card =
      supportedPart b n - 1 := by
    simpa [s, canonicalTerminatingNumerators] using
      canonicalTerminatingNumerators_card (b := b) hn
  have hnonterm : (s.filter (fun k => ¬TerminatesInBase b k n)).card =
      (canonicalNonterminatingNumerators b n).card := by
    rfl
  have hsCard : s.card = n - 1 := by
    simp [s, Nat.card_Icc]
  rw [hterm, hnonterm, hsCard] at hsplit
  have hmLe : supportedPart b n ≤ n :=
    Nat.le_of_dvd hn (supportedPart_dvd hn)
  have hcard : (canonicalNonterminatingNumerators b n).card =
      n - supportedPart b n := by
    apply Eq.symm
    apply (Nat.sub_eq_iff_eq_add hmLe).2
    have hmPos := supportedPart_pos (b := b) hn
    omega
  calc
    (canonicalNonterminatingNumerators b n).card =
        n - supportedPart b n := hcard
    _ = roughPart b n * supportedPart b n - supportedPart b n := by
      rw [roughPart_mul_supportedPart (b := b) hn]
    _ =
        roughPart b n * supportedPart b n - 1 * supportedPart b n := by simp
    _ = (roughPart b n - 1) * supportedPart b n :=
      (Nat.sub_mul (roughPart b n) 1 (supportedPart b n)).symm

/-- In the even-base setting, a nonterminating numerator cannot be fixed by
the complementary-numerator involution. -/
theorem complementNumerator_fixed_implies_terminating {b t m k : ℕ}
    (hbeven : Even b) (hcop : Nat.Coprime t b)
    (hfix : t * m - k = k) : t ∣ k := by
  have htOdd : Odd t := roughPart_odd_of_even_base hcop hbeven
  have hcopTwo : Nat.Coprime t 2 := Nat.coprime_two_right.mpr htOdd
  have hkLe : k ≤ t * m := by
    have hsub : t * m - k ≤ t * m := Nat.sub_le _ _
    rwa [hfix] at hsub
  have hdouble : t * m = 2 * k := by omega
  have htDouble : t ∣ 2 * k := ⟨m, hdouble.symm⟩
  exact hcopTwo.dvd_mul_left.mp htDouble

/-- Consequently the number of nonterminating complement pairs is the exact
half-count displayed in the manuscript. -/
theorem canonicalNonterminatingComplementPairCount {b n : ℕ}
    (hn : 0 < n) (hbeven : Even b) :
    Even ((canonicalNonterminatingNumerators b n).card) ∧
      (canonicalNonterminatingNumerators b n).card / 2 =
        ((roughPart b n - 1) * supportedPart b n) / 2 := by
  rw [canonicalNonterminatingNumerators_card hn]
  have htOdd := roughPart_odd_of_even_base
    (roughPart_coprime_base (b := b) hn) hbeven
  rcases htOdd with ⟨q, hq⟩
  constructor
  · refine ⟨q * supportedPart b n, ?_⟩
    rw [hq]
    simp only [Nat.add_sub_cancel]
    ring
  · rfl

/-- The residue of the complementary numerator is the complementary nonzero
rough residue. -/
theorem complementNumerator_mod {t m k : ℕ} (ht : 0 < t)
    (hk : k < t * m) (hnonterm : ¬t ∣ k) :
    (t * m - k) % t = t - k % t := by
  have hrPos : 0 < k % t := by
    rw [Nat.pos_iff_ne_zero]
    exact mt Nat.dvd_of_mod_eq_zero hnonterm
  have hrLt : k % t < t := Nat.mod_lt k ht
  have htm : t * m ≡ t [MOD t] := by
    rw [Nat.ModEq]
    simp
  have hkr : k ≡ k % t [MOD t] := by
    rw [Nat.ModEq]
    simp [Nat.mod_eq_of_lt hrLt]
  have hmod : t * m - k ≡ t - k % t [MOD t] :=
    Nat.ModEq.sub hk.le hrLt.le htm hkr
  simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : t - k % t < t)] using hmod

theorem complementNumerator_nonterminating {t m k : ℕ} (ht : 0 < t)
    (hk : k < t * m) (hnonterm : ¬t ∣ k) :
    ¬t ∣ t * m - k := by
  intro hdiv
  have hzero := (Nat.dvd_iff_mod_eq_zero).mp hdiv
  rw [complementNumerator_mod ht hk hnonterm] at hzero
  have hrPos : 0 < k % t := by
    rw [Nat.pos_iff_ne_zero]
    exact mt Nat.dvd_of_mod_eq_zero hnonterm
  have hrLt : k % t < t := Nat.mod_lt k ht
  omega

/-- Literal common-depth digits of complementary nonterminating numerators sum
to `b-1` at every synchronized position. -/
theorem clearedDigit_complementary_numerators {b t m k D j : ℕ}
    (hb : 0 < b) (ht : 0 < t) (hm : 0 < m)
    (hD : m ∣ b ^ D) (hcop : Nat.Coprime t b)
    (hk : k < t * m) (hnonterm : ¬t ∣ k) :
    clearedDigit b (t * m) (t * m - k) D j =
      b - 1 - clearedDigit b (t * m) k D j := by
  let u := clearingCofactor b m D
  let r := k % t
  have hrPos : 0 < r := by
    rw [Nat.pos_iff_ne_zero]
    exact mt Nat.dvd_of_mod_eq_zero hnonterm
  have hrLt : r < t := Nat.mod_lt k ht
  have hu : Nat.Coprime t u :=
    (hcop.pow_right D).of_dvd_right (Nat.div_dvd_of_dvd hD)
  have hres : (t * m - k) % t = t - r := by
    simpa [r] using complementNumerator_mod ht hk hnonterm
  rw [clearedDigit_eq_periodicDigit hm hD,
    clearedDigit_eq_periodicDigit hm hD, hres]
  exact periodicDigit_complement hb ht hrPos hrLt hcop hu

/-- In an even base, complementary nonterminating numerators cannot both match
the reference at one synchronized position. -/
theorem clearedMatches_complementary_exclusive {b t m k D j : ℕ}
    (hb : 0 < b) (ht : 0 < t) (hm : 0 < m)
    (hD : m ∣ b ^ D) (hcop : Nat.Coprime t b) (hbeven : Even b)
    (hk : k < t * m) (hnonterm : ¬t ∣ k) :
    ¬(clearedMatchAt b t m k D j ∧
      clearedMatchAt b t m (t * m - k) D j) := by
  let u := clearingCofactor b m D
  let r := k % t
  have hrPos : 0 < r := by
    rw [Nat.pos_iff_ne_zero]
    exact mt Nat.dvd_of_mod_eq_zero hnonterm
  have hrLt : r < t := Nat.mod_lt k ht
  have hu : Nat.Coprime t u :=
    (hcop.pow_right D).of_dvd_right (Nat.div_dvd_of_dvd hD)
  have hres : (t * m - k) % t = t - r := by
    simpa [r] using complementNumerator_mod ht hk hnonterm
  rw [clearedMatchAt_iff_periodicMatchAt hm hD,
    clearedMatchAt_iff_periodicMatchAt hm hD, hres]
  exact complementary_matches_exclusive hb ht hrPos hrLt hcop hu hbeven

/-- The two literal synchronized match counts of a complementary pair have
total at most one full period. -/
theorem clearedNumeratorMatchCount_pair_le {b t m k D L : ℕ}
    (hb : 0 < b) (ht : 0 < t) (hm : 0 < m)
    (hD : m ∣ b ^ D) (hcop : Nat.Coprime t b) (hbeven : Even b)
    (hk : k < t * m) (hnonterm : ¬t ∣ k) :
    clearedNumeratorMatchCount b t m k D L +
      clearedNumeratorMatchCount b t m (t * m - k) D L ≤ L := by
  let u := clearingCofactor b m D
  let r := k % t
  have hrPos : 0 < r := by
    rw [Nat.pos_iff_ne_zero]
    exact mt Nat.dvd_of_mod_eq_zero hnonterm
  have hrLt : r < t := Nat.mod_lt k ht
  have hu : Nat.Coprime t u :=
    (hcop.pow_right D).of_dvd_right (Nat.div_dvd_of_dvd hD)
  have hres : (t * m - k) % t = t - r := by
    simpa [r] using complementNumerator_mod ht hk hnonterm
  have hmateNonterm := complementNumerator_nonterminating ht hk hnonterm
  have hrNe : k % t ≠ 0 := mt Nat.dvd_of_mod_eq_zero hnonterm
  have hmateModNe : (t * m - k) % t ≠ 0 :=
    mt Nat.dvd_of_mod_eq_zero hmateNonterm
  rw [clearedNumeratorMatchCount_eq_periodic hm hD,
    clearedNumeratorMatchCount_eq_periodic hm hD]
  unfold numeratorPeriodicMatchCount
  rw [if_neg hrNe, if_neg hmateModNe, hres]
  exact periodicMatchCount_pair_le hb ht hrPos hrLt hcop hu hbeven

end NField.Alignment
