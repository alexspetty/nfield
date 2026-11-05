/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CyclicShiftCounts

/-!
# Cumulative closure of actual repeating digits

A closure is a return of the literal long-division digit stream with cumulative
digit sum zero modulo b-1. Its length is the least positive such return. The
order and gcd formulas are proved from this definition, not used to define it.

The proof retains leading zeros, complete primitive blocks, arbitrary unit
numerators, phases and valid supported-factor clearing depths. Base two is
included. Reusable results close Proposition 13 of "Repetend Rigidity at the
Golden Scale" and supply the actual-tail bridge for its endpoint corollary.
-/

namespace NField.Alignment

/-- Sum of the actual first N long-division digits, including leading zeros. -/
def repetendDigitSum (b q a N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N, digitAt b q a j

/-- A complete number of primitive blocks whose combined digit sum is zero
modulo b-1, stated directly on the digit stream. Zero is allowed as a return;
the closure length below selects the least positive return. -/
def CumulativeClosesAt (b q a N : ℕ) : Prop :=
  (∀ j, digitAt b q a (j + N) = digitAt b q a j) ∧
    b - 1 ∣ repetendDigitSum b q a N

/-- The least positive cumulative digit closure; no order formula is built in. -/
noncomputable def cumulativeClosureLength (b q a : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ CumulativeClosesAt b q a N}

/-- The finite base-b repunit as the sum of its place values. -/
def baseRepunit (b N : ℕ) : ℕ := ∑ i ∈ Finset.range N, b ^ i

theorem baseRepunit_mul {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    (b - 1) * baseRepunit b N = b ^ N - 1 := by
  simpa [baseRepunit, Nat.mul_comm] using
    geom_sum_mul_of_one_le (show 1 ≤ b by omega) N

theorem coprime_closure_modulus {b q : ℕ} (hb : 2 ≤ b)
    (hcop : Nat.Coprime q b) : Nat.Coprime (q * (b - 1)) b := by
  exact hcop.mul_left ((Nat.coprime_self_sub_left (show 1 ≤ b by omega)).mpr
    (Nat.coprime_one_left b))

theorem coprimeBasePeriod_dvd_iff_modEq {b q N : ℕ}
    (hcop : Nat.Coprime q b) :
    coprimeBasePeriod b q hcop ∣ N ↔ b ^ N ≡ 1 [MOD q] := by
  rw [coprimeBasePeriod, orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    have hc := congrArg (fun z : (ZMod q)ˣ => (z : ZMod q)) h
    apply (ZMod.natCast_eq_natCast_iff' (b ^ N) 1 q).mp
    simpa [ZMod.coe_unitOfCoprime] using hc
  · intro h
    apply Units.ext
    have hc := (ZMod.natCast_eq_natCast_iff' (b ^ N) 1 q).mpr h
    simpa [ZMod.coe_unitOfCoprime] using hc

theorem repetendDigitSum_modEq_prefix {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 0 < q) (ha : a < q) (N : ℕ) :
    (b ^ N * a) / q ≡ repetendDigitSum b q a N [MOD (b - 1)] := by
  have hbmod : b ≡ 1 [MOD (b - 1)] := Nat.modEq_sub (by omega)
  induction N with
  | zero => simp [repetendDigitSum, Nat.div_eq_of_lt ha, Nat.ModEq]
  | succ N ih =>
    rw [digitPrefix_succ b q a N hq, repetendDigitSum,
      Finset.sum_range_succ]
    simpa only [one_mul, repetendDigitSum] using (hbmod.mul ih).add_right (digitAt b q a N)

theorem digitPrefix_complete_block {b q a N : ℕ}
    (hb : 2 ≤ b) (_hq : 0 < q) (ha : a < q)
    (hret : b ^ N ≡ 1 [MOD q]) :
    q * ((b ^ N * a) / q) = a * (b ^ N - 1) := by
  have hrem := hret.mul_right a
  have hrem' : (b ^ N * a) % q = a := by
    simpa only [Nat.ModEq, one_mul, Nat.mod_eq_of_lt ha] using hrem
  have hid := Nat.mod_add_div (b ^ N * a) q
  rw [hrem'] at hid
  have hp := Nat.one_le_pow N b (by omega)
  have hs := Nat.sub_add_cancel hp
  nlinarith

theorem completeBlock_sum_dvd_iff_repunit {b q a N : ℕ}
    (hb : 2 ≤ b) (hq : 0 < q) (ha : a < q)
    (haq : Nat.Coprime q a) (hret : b ^ N ≡ 1 [MOD q]) :
    b - 1 ∣ repetendDigitSum b q a N ↔ q ∣ baseRepunit b N := by
  have hsum := repetendDigitSum_modEq_prefix hb hq ha N
  have hprefix := digitPrefix_complete_block hb hq ha hret
  have hd : 0 < b - 1 := by omega
  have hdiv : b - 1 ∣ repetendDigitSum b q a N ↔
      b - 1 ∣ (b ^ N * a) / q := by
    exact hsum.symm.dvd_iff dvd_rfl
  rw [hdiv]
  calc
    b - 1 ∣ (b ^ N * a) / q ↔
        q * (b - 1) ∣ q * ((b ^ N * a) / q) := by
      exact (Nat.mul_dvd_mul_iff_left hq).symm
    _ ↔ (b - 1) * q ∣ (b - 1) * (a * baseRepunit b N) := by
      rw [hprefix, ← baseRepunit_mul hb N]
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ↔ q ∣ a * baseRepunit b N := Nat.mul_dvd_mul_iff_left hd
    _ ↔ q ∣ baseRepunit b N := haq.dvd_mul_left

theorem repunit_dvd_iff_enlarged_return {b q N : ℕ} (hb : 2 ≤ b) :
    q ∣ baseRepunit b N ↔ b ^ N ≡ 1 [MOD (q * (b - 1))] := by
  have hp := Nat.one_le_pow N b (by omega)
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hp, ← baseRepunit_mul hb N]
  rw [Nat.mul_comm q (b-1)]
  exact (Nat.mul_dvd_mul_iff_left (show 0 < b-1 by omega)).symm

/-- Literal cumulative closure occurs exactly at multiples of the enlarged
modular order, for every reduced numerator. -/
theorem cumulativeClosesAt_iff_order_dvd {b q a N : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (ha : a < q)
    (hcop : Nat.Coprime q b) (haq : Nat.Coprime q a) :
    CumulativeClosesAt b q a N ↔
      coprimeBasePeriod b (q * (b - 1)) (coprime_closure_modulus hb hcop) ∣ N := by
  rw [CumulativeClosesAt, reference_digit_period_iff hb hq hcop haq,
    coprimeBasePeriod_dvd_iff_modEq (coprime_closure_modulus hb hcop)]
  constructor
  · rintro ⟨hper, hsum⟩
    exact (repunit_dvd_iff_enlarged_return hb).mp
      ((completeBlock_sum_dvd_iff_repunit hb (by omega) ha haq
        ((coprimeBasePeriod_dvd_iff_modEq hcop).mp hper)).mp hsum)
  · intro hret
    have hsmall : b ^ N ≡ 1 [MOD q] := hret.of_dvd (Nat.dvd_mul_right q (b-1))
    refine ⟨(coprimeBasePeriod_dvd_iff_modEq hcop).mpr hsmall, ?_⟩
    exact (completeBlock_sum_dvd_iff_repunit hb (by omega) ha haq hsmall).mpr
      ((repunit_dvd_iff_enlarged_return hb).mpr hret)

theorem cumulativeClosureLength_eq_order {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (ha : a < q)
    (hcop : Nat.Coprime q b) (haq : Nat.Coprime q a) :
    cumulativeClosureLength b q a =
      coprimeBasePeriod b (q * (b - 1)) (coprime_closure_modulus hb hcop) := by
  unfold cumulativeClosureLength
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨coprimeBasePeriod_pos _,
      (cumulativeClosesAt_iff_order_dvd hb hq ha hcop haq).mpr dvd_rfl⟩
  · intro N hN
    exact Nat.le_of_dvd hN.1
      ((cumulativeClosesAt_iff_order_dvd hb hq ha hcop haq).mp hN.2)


theorem repetendDigitSum_completeBlocks {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hcop : Nat.Coprime q b)
    (haq : Nat.Coprime q a) (t : ℕ) :
    repetendDigitSum b q a (coprimeBasePeriod b q hcop * t) =
      t * repetendDigitSum b q a (coprimeBasePeriod b q hcop) := by
  induction t with
  | zero => simp [repetendDigitSum]
  | succ t ih =>
    have hper := (reference_digit_period_iff hb hq hcop haq
      (s := coprimeBasePeriod b q hcop * t)).mpr (Nat.dvd_mul_right _ _)
    rw [Nat.mul_succ, repetendDigitSum, Finset.sum_range_add]
    have htail : (∑ j ∈ Finset.range (coprimeBasePeriod b q hcop),
        digitAt b q a (coprimeBasePeriod b q hcop * t + j)) =
        repetendDigitSum b q a (coprimeBasePeriod b q hcop) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Nat.add_comm] using hper j
    rw [htail]
    change repetendDigitSum b q a (coprimeBasePeriod b q hcop * t) + _ = _
    rw [ih, Nat.succ_mul]

theorem multiple_digitSum_dvd_iff_addOrder (sigma d t : ℕ) :
    d ∣ t * sigma ↔ addOrderOf (sigma : ZMod d) ∣ t := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff]

theorem cumulativeClosureLength_eq_period_mul_addOrder {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hcop : Nat.Coprime q b)
    (haq : Nat.Coprime q a) :
    cumulativeClosureLength b q a = coprimeBasePeriod b q hcop *
      addOrderOf (repetendDigitSum b q a (coprimeBasePeriod b q hcop) : ZMod (b-1)) := by
  let h := coprimeBasePeriod b q hcop
  let sigma := repetendDigitSum b q a h
  let A := addOrderOf (sigma : ZMod (b-1))
  letI : NeZero (b-1) := ⟨by omega⟩
  have hh : 0 < h := coprimeBasePeriod_pos hcop
  have hA : 0 < A := addOrderOf_pos _
  unfold cumulativeClosureLength
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨Nat.mul_pos hh hA, ?_⟩
    refine ⟨(reference_digit_period_iff hb hq hcop haq).mpr (Nat.dvd_mul_right _ _), ?_⟩
    rw [repetendDigitSum_completeBlocks hb hq hcop haq]
    exact (multiple_digitSum_dvd_iff_addOrder sigma (b-1) A).mpr dvd_rfl
  · intro N hN
    have hdiv := (reference_digit_period_iff hb hq hcop haq).mp hN.2.1
    obtain ⟨t, rfl⟩ := hdiv
    have ht : 0 < t := by
      by_contra hbad
      have ht0 : t = 0 := by omega
      simp [ht0] at hN
    have hsum := hN.2.2
    rw [repetendDigitSum_completeBlocks hb hq hcop haq] at hsum
    have hAdvd : A ∣ t := (multiple_digitSum_dvd_iff_addOrder sigma (b-1) t).mp hsum
    exact Nat.mul_le_mul_left h (Nat.le_of_dvd ht hAdvd)

/-- The primitive block digit-sum formula uses the least actual cumulative
return. Repeating blocks introduces no artificial primitive period. -/
theorem cumulativeClosureLength_eq_gcd {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hcop : Nat.Coprime q b)
    (haq : Nat.Coprime q a) :
    cumulativeClosureLength b q a =
      coprimeBasePeriod b q hcop * (b-1) /
        Nat.gcd (repetendDigitSum b q a (coprimeBasePeriod b q hcop)) (b-1) := by
  rw [cumulativeClosureLength_eq_period_mul_addOrder hb hq hcop haq,
    ZMod.addOrderOf_coe _ (by omega), Nat.gcd_comm (b-1),
    ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

/-- Both formulas for the least cumulative digit closure, with the actual
primitive digit block, arbitrary coprime base, and reduced numerator. -/
theorem cumulative_closure_length {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (_ha0 : 0 < a) (ha : a < q)
    (hcop : Nat.Coprime q b) (haq : Nat.Coprime q a) :
    cumulativeClosureLength b q a =
      coprimeBasePeriod b q hcop * (b-1) /
        Nat.gcd (repetendDigitSum b q a (coprimeBasePeriod b q hcop)) (b-1) ∧
    cumulativeClosureLength b q a =
      coprimeBasePeriod b (q * (b-1)) (coprime_closure_modulus hb hcop) := by
  exact ⟨cumulativeClosureLength_eq_gcd hb hq hcop haq,
    cumulativeClosureLength_eq_order hb hq ha hcop haq⟩


theorem cumulativeClosureLength_mod_start (b q a : ℕ) :
    cumulativeClosureLength b q (a % q) = cumulativeClosureLength b q a := by
  unfold cumulativeClosureLength CumulativeClosesAt repetendDigitSum
  simp only [digitAt_mod_start]

theorem cumulativeClosureLength_eq_order_of_coprime {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q)
    (hcop : Nat.Coprime q b) (haq : Nat.Coprime q a) :
    cumulativeClosureLength b q a =
      coprimeBasePeriod b (q * (b-1)) (coprime_closure_modulus hb hcop) := by
  rw [← cumulativeClosureLength_mod_start b q a]
  exact cumulativeClosureLength_eq_order hb hq (Nat.mod_lt _ (by omega)) hcop
    (by
      change Nat.gcd q (a % q) = 1
      rw [Nat.gcd_comm, ← Nat.gcd_rec]
      exact haq.gcd_eq_one)

/-- Changing the reduced numerator or rotating the starting phase leaves the
cumulative closure length unchanged. The phase shift is the actual long-division
shift `digitAt_shift`, represented by multiplication by a power of the base. -/
theorem cumulative_closure_numerator_and_phase {b q a a' : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hcop : Nat.Coprime q b)
    (haq : Nat.Coprime q a) (haq' : Nat.Coprime q a') (s : ℕ) :
    cumulativeClosureLength b q a' = cumulativeClosureLength b q a ∧
    cumulativeClosureLength b q (b ^ s * a) = cumulativeClosureLength b q a := by
  have hs : Nat.Coprime q (b ^ s * a) := (hcop.pow_right s).mul_right haq
  rw [cumulativeClosureLength_eq_order_of_coprime hb hq hcop haq,
    cumulativeClosureLength_eq_order_of_coprime hb hq hcop haq',
    cumulativeClosureLength_eq_order_of_coprime hb hq hcop hs]
  exact ⟨rfl, rfl⟩

theorem baseRepunit_modEq_length {b q : ℕ} (hbase : b ≡ 1 [MOD q]) (N : ℕ) :
    baseRepunit b N ≡ N [MOD q] := by
  have hc : (b : ZMod q) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff' b 1 q).mpr hbase
  have hsum : (baseRepunit b N : ZMod q) = (N : ZMod q) := by
    simp [baseRepunit, hc]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hsum

/-- When the primitive period is one, the least cumulative closure is exactly
the reduced denominator, for every unit numerator and every starting phase. -/
theorem cumulative_closure_period_one {b q a : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hcop : Nat.Coprime q b)
    (haq : Nat.Coprime q a) (hperiod : coprimeBasePeriod b q hcop = 1) :
    cumulativeClosureLength b q a = q := by
  have hbase : b ≡ 1 [MOD q] := by
    have h := (coprimeBasePeriod_dvd_iff_modEq (N:=1) hcop).mp (by simp [hperiod])
    simpa only [pow_one] using h
  have hrep : ∀ N, q ∣ baseRepunit b N ↔ q ∣ N := fun N =>
    (baseRepunit_modEq_length hbase N).dvd_iff dvd_rfl
  rw [cumulativeClosureLength_eq_order_of_coprime hb hq hcop haq]
  apply Nat.dvd_antisymm
  · apply (coprimeBasePeriod_dvd_iff_modEq (coprime_closure_modulus hb hcop)).mpr
    exact (repunit_dvd_iff_enlarged_return hb).mp ((hrep q).mpr dvd_rfl)
  · apply (hrep _).mp
    exact (repunit_dvd_iff_enlarged_return hb).mpr
      ((coprimeBasePeriod_dvd_iff_modEq (coprime_closure_modulus hb hcop)).mp dvd_rfl)

/-- Base two is included: the digit-sum congruence is modulo one, so cumulative
closure is exactly the ordinary primitive period. -/
theorem cumulative_closure_base_two {q a : ℕ}
    (hq : 1 < q) (hcop : Nat.Coprime q 2) (haq : Nat.Coprime q a) :
    cumulativeClosureLength 2 q a = coprimeBasePeriod 2 q hcop := by
  simpa using cumulativeClosureLength_eq_order_of_coprime (by omega) hq hcop haq


/-- Cumulative closure of the actual tail after D long-division places.
Multiplication by b^D represents the existing literal digit-stream shift. -/
noncomputable def cumulativeClosureLengthAtDepth (b d k D : ℕ) : ℕ :=
  cumulativeClosureLength b d (b ^ D * k)

theorem cumulativeClosureLengthAtDepth_literal (b d k D : ℕ) :
    cumulativeClosureLengthAtDepth b d k D =
      sInf {N : ℕ | 0 < N ∧
        (∀ j, digitAt b d k (D + (j + N)) = digitAt b d k (D + j)) ∧
        b - 1 ∣ ∑ j ∈ Finset.range N, digitAt b d k (D + j)} := by
  unfold cumulativeClosureLengthAtDepth cumulativeClosureLength CumulativeClosesAt
    repetendDigitSum
  simp only [← digitAt_shift, Nat.add_comm D]

/-- Clearing the supported factor preserves the literal cumulative closure
problem, including the chosen starting phase and every leading zero. -/
theorem cumulativeClosureLengthAtDepth_eq_cleared {b q m D k : ℕ}
    (hm : 0 < m) (hD : m ∣ b ^ D) :
    cumulativeClosureLengthAtDepth b (q * m) k D =
      cumulativeClosureLength b q (k * clearingCofactor b m D) := by
  rw [cumulativeClosureLengthAtDepth_literal]
  unfold cumulativeClosureLength CumulativeClosesAt repetendDigitSum
  simp only [clearedDigit_eq_digitAt hm hD]

/-- For a coprime residual denominator and a period-one base, the reference
tail and every accepted cyclic shift have cumulative closure q at any valid
clearing depth on the original denominator q*m. -/
theorem cyclic_shift_closure_period_one {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) (hperiod : coprimeBasePeriod b q hcop = 1) :
    cumulativeClosureLengthAtDepth b (q*m) 1 D = q ∧
    ∀ k, CyclicShiftAtDepth b q m D k →
      cumulativeClosureLengthAtDepth b (q*m) k D = q := by
  have hu := modulus_coprime_clearingCofactor hcop hD
  have href := cumulative_closure_period_one hb hq hcop hu hperiod
  constructor
  · simpa only [cumulativeClosureLengthAtDepth_eq_cleared hm hD, one_mul] using href
  · intro k hk
    obtain ⟨s, hs⟩ := hk
    rw [cumulativeClosureLengthAtDepth_literal]
    have hshift : ∀ j, digitAt b (q*m) k (D+j) =
        digitAt b q (b^s * clearingCofactor b m D) j := by
      intro j
      rw [hs j, clearedDigit_eq_digitAt hm hD, one_mul, digitAt_shift]
    have heq : sInf {N : ℕ | 0 < N ∧
        (∀ j, digitAt b (q*m) k (D+(j+N)) = digitAt b (q*m) k (D+j)) ∧
        b-1 ∣ ∑ j ∈ Finset.range N, digitAt b (q*m) k (D+j)} =
        cumulativeClosureLength b q (b^s * clearingCofactor b m D) := by
      unfold cumulativeClosureLength CumulativeClosesAt repetendDigitSum
      simp only [hshift]
    rw [heq]
    exact cumulative_closure_period_one hb hq hcop
      ((hcop.pow_right s).mul_right hu) hperiod

end NField.Alignment

