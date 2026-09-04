/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FloorDigitBinDistribution
import NField.Alignment.SynchronizedCosetAlignment

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Uniform alignment limits and finite decimal certificates

This module combines the exact floor-bin ceiling with the synchronized coset
formula.  It proves the unconditional sharp three-fifths bound, its limiting
sharpness, and kernel-checked finite certificates for the decimal table and
the exceptional primes below one hundred.
-/

namespace NField.Alignment

open scoped BigOperators
open NField.CollisionDefinition

/-- A directly executable closed formula for one digit-bin population. -/
def computableDigitBinPopulation (b p d : ℕ) : ℕ :=
  digitBinBoundary b p (d + 1) - max 1 (digitBinBoundary b p d)

/-- The closed executable population agrees with the defining finite count. -/
theorem computableDigitBinPopulation_eq {b p d : ℕ}
    (hb : 0 < b) (hp : 0 < p) (hd : d < b) :
    computableDigitBinPopulation b p d = digitBinPopulation b p d := by
  exact (digitBinPopulation_eq_boundary_sub hb hp hd).symm

/-- A directly executable version of the power-orbit bin sum. -/
def computablePowerOrbitBinSum (b p u L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L,
    computableDigitBinPopulation b p (digitBin b p ((b ^ j * u) % p))

/-- The executable sum is definitionally the theorem-level power-orbit sum. -/
theorem computablePowerOrbitBinSum_eq {b p u L : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hu : Nat.Coprime p u) :
    computablePowerOrbitBinSum b p u L = powerOrbitBinSum (L := L) hp hpb hu := by
  have hb : 0 < b := Nat.pos_of_ne_zero fun hb0 => hpb (by simp [hb0])
  unfold computablePowerOrbitBinSum powerOrbitBinSum orbitBinSum powerReferenceOrbit
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [computableDigitBinPopulation_eq hb hp.pos
    (digitBin_lt_base hb hp.pos (Nat.mod_lt _ hp.pos))]

/-- A directly executable closed formula for the global square sum. -/
def computableDigitBinSquareSum (b p : ℕ) : ℕ :=
  b * ((p - 1) / b) ^ 2 +
    ((p - 1) % b) * (2 * ((p - 1) / b) + 1)

/-- The closed square-sum formula agrees with the defining sum of squares. -/
theorem computableDigitBinSquareSum_eq {b p : ℕ} (hb : 0 < b) (hp : 0 < p) :
    computableDigitBinSquareSum b p = digitBinSquareSum b p := by
  exact (digitBinSquareSum_eq_quotient_remainder hb hp).symm

/-- The exact mathematical predicate that `L` is the least positive modular
return time of the base. -/
def IsLeastPositiveModularPeriod (b p L : ℕ) : Prop :=
  0 < L ∧ b ^ L % p = 1 % p ∧
    ∀ q, 0 < q → q < L → b ^ q % p ≠ 1 % p

/-- A finite Boolean checker for the least-period predicate. -/
def leastPositiveModularPeriodCheck (b p L : ℕ) : Bool :=
  decide (0 < L) && decide (b ^ L % p = 1 % p) &&
    (List.range L).all fun q =>
      decide (q = 0 ∨ b ^ q % p ≠ 1 % p)

/-- The finite checker has exactly the intended least-period semantics. -/
theorem leastPositiveModularPeriodCheck_eq_true_iff {b p L : ℕ} :
    leastPositiveModularPeriodCheck b p L = true ↔
      IsLeastPositiveModularPeriod b p L := by
  classical
  simp only [leastPositiveModularPeriodCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range,
    IsLeastPositiveModularPeriod]
  constructor
  · rintro ⟨⟨hL, hreturn⟩, hsmall⟩
    refine ⟨hL, hreturn, ?_⟩
    intro q hq hqL
    exact (hsmall q hqL).resolve_left (by omega)
  · rintro ⟨hL, hreturn, hsmall⟩
    refine ⟨⟨hL, hreturn⟩, ?_⟩
    intro q hqL
    by_cases hq : q = 0
    · exact Or.inl hq
    · exact Or.inr (hsmall q (Nat.pos_of_ne_zero hq) hqL)

/-- The least modular return agrees with the group-theoretic multiplicative
period used by the synchronized alignment definitions. -/
theorem primeBasePeriod_eq_of_isLeastPositiveModularPeriod {b p L : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hL : IsLeastPositiveModularPeriod b p L) :
    primeBasePeriod b p hp hpb = L := by
  let u := primeBaseUnit b p hp hpb
  have hpowL : u ^ L = 1 := by
    have hcast : ((b ^ L : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' (b ^ L) 1 p).2 hL.2.1
    apply Units.ext
    simpa [u, primeBaseUnit, ZMod.coe_unitOfCoprime] using hcast
  have hdiv : primeBasePeriod b p hp hpb ∣ L := by
    simpa [u, primeBaseUnit, primeBasePeriod] using
      (orderOf_dvd_iff_pow_eq_one.mpr hpowL)
  have hperiodLe : primeBasePeriod b p hp hpb ≤ L := Nat.le_of_dvd hL.1 hdiv
  have hnotLt : ¬primeBasePeriod b p hp hpb < L := by
    intro hlt
    exact hL.2.2 (primeBasePeriod b p hp hpb)
      (primeBasePeriod_pos hp hpb) hlt
      (pow_primeBasePeriod_mod_eq_one hp hpb)
  omega

/-- Nonzero canonical residue representatives at a prime modulus. -/
def PrimeNonzeroResidue (p : ℕ) := {r : ℕ // r ∈ nonzeroResidues p}

/-- At a prime modulus, units are exactly the nonzero canonical residue
representatives. -/
noncomputable def primeUnitResidueEquiv (p : ℕ) (hp : Nat.Prime p) :
    (ZMod p)ˣ ≃ PrimeNonzeroResidue p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let coprimeToResidue : {x : ZMod p // Nat.Coprime x.val p} ≃
      PrimeNonzeroResidue p :=
    { toFun := fun x => ⟨x.1.val, by
          apply Finset.mem_erase.mpr
          refine ⟨?_, Finset.mem_range.mpr x.1.val_lt⟩
          intro hx0
          have hcop : Nat.Coprime 0 p := by simpa [hx0] using x.2
          have hp1 : p = 1 := by simpa using hcop
          exact hp.ne_one hp1⟩
      invFun := fun r => ⟨(r.1 : ZMod p), by
          have rr := Finset.mem_erase.mp r.2
          have hrlt : r.1 < p := Finset.mem_range.mp rr.2
          have hnotdvd : ¬p ∣ r.1 := by
            exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero rr.1) hrlt
          have hcop : Nat.Coprime p r.1 := hp.coprime_iff_not_dvd.mpr hnotdvd
          simpa [ZMod.val_natCast_of_lt hrlt] using hcop.symm⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact ZMod.natCast_zmod_val x.1
      right_inv := by
        intro r
        apply Subtype.ext
        simp [ZMod.val_natCast_of_lt
          (Finset.mem_range.mp (Finset.mem_erase.mp r.2).2)] }
  exact ZMod.unitsEquivCoprime.trans coprimeToResidue

/-- The power orbit represented inside the prime unit group. -/
noncomputable def primePowerOrbitUnit {b p u : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hu : Nat.Coprime p u)
    (i : Fin (primeBasePeriod b p hp hpb)) : (ZMod p)ˣ :=
  (primeBaseUnit b p hp hpb) ^ (i : ℕ) *
    ZMod.unitOfCoprime u hu.symm

/-- When the base has full order, its translated power orbit is a bijection
onto the prime unit group. -/
theorem primePowerOrbitUnit_bijective_of_full_order {b p u : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hu : Nat.Coprime p u)
    (hfull : primeBasePeriod b p hp hpb = p - 1) :
    Function.Bijective (primePowerOrbitUnit hp hpb hu) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    have hpows : (primeBaseUnit b p hp hpb) ^ (i : ℕ) =
        (primeBaseUnit b p hp hpb) ^ (j : ℕ) := by
      apply mul_right_cancel (b := ZMod.unitOfCoprime u hu.symm)
      simpa [primePowerOrbitUnit] using hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf i.isLt j.isLt hpows
  · simp only [Fintype.card_fin, ZMod.card_units, hfull]

/-- A primitive-root power orbit visits every nonzero residue exactly once,
so its orbit-bin sum is the global digit-bin square sum. -/
theorem powerOrbitBinSum_eq_digitBinSquareSum_of_full_order {b p u : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hu : Nat.Coprime p u)
    (hfull : primeBasePeriod b p hp hpb = p - 1) :
    powerOrbitBinSum (L := primeBasePeriod b p hp hpb) hp hpb hu =
      digitBinSquareSum b p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (PrimeNonzeroResidue p) :=
    (nonzeroResidues p).fintypeCoeSort
  let orbitEquiv : Fin (primeBasePeriod b p hp hpb) ≃ (ZMod p)ˣ :=
    Equiv.ofBijective (primePowerOrbitUnit hp hpb hu)
      (primePowerOrbitUnit_bijective_of_full_order hp hpb hu hfull)
  have horbit (i : Fin (primeBasePeriod b p hp hpb)) :
      (orbitEquiv i : ZMod p).val = (b ^ (i : ℕ) * u) % p := by
    change ((primePowerOrbitUnit hp hpb hu i : (ZMod p)ˣ) : ZMod p).val = _
    have hcoe : ((primePowerOrbitUnit hp hpb hu i : (ZMod p)ˣ) : ZMod p) =
        ((b ^ (i : ℕ) * u : ℕ) : ZMod p) := by
      simp [primePowerOrbitUnit, primeBaseUnit, ZMod.coe_unitOfCoprime]
    calc
      ((primePowerOrbitUnit hp hpb hu i : (ZMod p)ˣ) : ZMod p).val =
          (((b ^ (i : ℕ) * u : ℕ) : ZMod p)).val := congrArg ZMod.val hcoe
      _ = (b ^ (i : ℕ) * u) % p := ZMod.val_natCast p _
  have hb : 0 < b := Nat.pos_of_ne_zero fun hb0 => hpb (by simp [hb0])
  unfold powerOrbitBinSum orbitBinSum powerReferenceOrbit
  calc
    ∑ i : Fin (primeBasePeriod b p hp hpb),
        digitBinPopulation b p (digitBin b p ((b ^ (i : ℕ) * u) % p)) =
      ∑ x : (ZMod p)ˣ,
        digitBinPopulation b p (digitBin b p (x : ZMod p).val) := by
          exact Fintype.sum_equiv orbitEquiv
            (fun i => digitBinPopulation b p
              (digitBin b p ((b ^ (i : ℕ) * u) % p)))
            (fun x => digitBinPopulation b p
              (digitBin b p (x : ZMod p).val))
            (fun i => by rw [horbit i])
    _ = ∑ r : PrimeNonzeroResidue p,
        digitBinPopulation b p (digitBin b p r.1) := by
          exact Fintype.sum_equiv (primeUnitResidueEquiv p hp) _ _ (fun _ => rfl)
    _ = ∑ r ∈ nonzeroResidues p,
        digitBinPopulation b p (digitBin b p r) := by
          exact (Finset.sum_subtype (nonzeroResidues p) (fun _ => Iff.rfl)
            (fun r => digitBinPopulation b p (digitBin b p r))).symm
    _ = digitBinSquareSum b p :=
      (digitBinSquareSum_eq_sum_population_at_residue hb hp.pos).symm

/-- Even if the selected starting multiplier changes with `m`, a full-order
base gives one global alignment limit because every orbit-bin sum equals `S`. -/
theorem powerOrbitAlignmentReal_tendsto_of_full_order {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1)
    (u : ℕ → ℕ) (hu : ∀ m, Nat.Coprime p (u m)) :
    Filter.Tendsto
      (fun m => cosetAlignmentReal p m (primeBasePeriod b p hp hpb)
        (powerOrbitBinSum (L := primeBasePeriod b p hp hpb)
          hp hpb (hu m)))
      Filter.atTop
      (nhds ((((p - 1 : ℕ) : ℝ) + digitBinSquareSum b p) /
        ((p : ℝ) * (p - 1)))) := by
  have hfixed := cosetAlignmentReal_tendsto
    (p := p) (L := primeBasePeriod b p hp hpb)
    (T := digitBinSquareSum b p) hp.pos (primeBasePeriod_pos hp hpb)
  convert hfixed using 1
  · funext m
    rw [powerOrbitBinSum_eq_digitBinSquareSum_of_full_order hp hpb (hu m) hfull]
  · rw [hfull]
    push_cast [Nat.cast_sub hp.one_lt.le]
    rfl

/-- The floor-bin theorem supplies the concrete population hypothesis used
by the abstract orbit bound. -/
theorem powerOrbitBinSum_le_ceiling {b p u L : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hu : Nat.Coprime p u)
    (hb : 0 < b) :
    powerOrbitBinSum (L := L) hp hpb hu ≤ L * ((p - 1) ⌈/⌉ b) := by
  apply orbitBinSum_le_of_population_bound
  intro i
  apply digitBinPopulation_le_ceil hb hp.pos
  exact digitBin_lt_base hb hp.pos
    ((powerReferenceOrbit hp hpb hu).state_lt i)

/-- Every admissible finite alignment at a prime `p>=5` lies strictly below
three-fifths, with no equidistribution hypothesis. -/
theorem powerOrbitAlignmentReal_lt_three_fifths {b p m u L : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b)
    (hb : 2 ≤ b) (hu : Nat.Coprime p u) (hm : 1 ≤ m) (hL : 0 < L) :
    cosetAlignmentReal p m L (powerOrbitBinSum (L := L) hp hpb hu) <
      (3 : ℝ) / 5 := by
  exact cosetAlignmentReal_lt_three_fifths hp5 hm hL
    (powerOrbitBinSum_le_ceiling hp hpb hu (by omega))
    (twice_ceil_digitBinCapacity_le hb hp hp5)

/-- Literal common-depth long division satisfies the same unconditional
finite bound. -/
theorem clearedAlignmentReal_lt_three_fifths {b p m D L : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b)
    (hb : 2 ≤ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) (hL : 0 < L) :
    ThreeTier.clearedAlignmentReal b p m D L < (3 : ℝ) / 5 := by
  rw [clearedAlignmentReal_eq_cosetAlignmentReal hp hpb hm hD hL]
  exact powerOrbitAlignmentReal_lt_three_fifths hp hp5 hpb hb
    (prime_coprime_clearingCofactor hp hpb hD) hm hL

/-- Every fixed-coset limiting value is at most three-fifths. -/
theorem cosetLimitReal_le_three_fifths {p L T c : ℕ}
    (hp : 5 ≤ p) (hL : 0 < L) (hT : T ≤ L * c)
    (hc : 2 * c ≤ p - 1) :
    (((L + T : ℕ) : ℝ) / ((p * L : ℕ) : ℝ)) ≤ (3 : ℝ) / 5 := by
  have hLR : (0 : ℝ) < L := by positivity
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hTR : (T : ℝ) ≤ (L : ℝ) * c := by exact_mod_cast hT
  have hcR : (2 : ℝ) * c ≤ (p : ℝ) - 1 := by
    have := show ((2 * c : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) by exact_mod_cast hc
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at this
    simpa using this
  push_cast
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < p * L)]
  nlinarith

/-- The concrete power-orbit form of the subsequential limit bound. -/
theorem powerOrbitLimitReal_le_three_fifths {b p u L : ℕ}
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b)
    (hb : 2 ≤ b) (hu : Nat.Coprime p u) (hL : 0 < L) :
    (((L + powerOrbitBinSum (L := L) hp hpb hu : ℕ) : ℝ) /
        ((p * L : ℕ) : ℝ)) ≤ (3 : ℝ) / 5 := by
  exact cosetLimitReal_le_three_fifths hp5 hL
    (powerOrbitBinSum_le_ceiling hp hpb hu (by omega))
    (twice_ceil_digitBinCapacity_le hb hp hp5)

/-- The sharp base-two, prime-five power orbit has bin sum eight. -/
theorem baseTwoPrimeFive_powerOrbitBinSum :
    computablePowerOrbitBinSum 2 5 1 4 = 8 := by decide

/-- The actual base-two, prime-five synchronized family has the displayed
finite formula. -/
theorem baseTwoPrimeFive_clearedAlignmentReal (a : ℕ) :
    ThreeTier.clearedAlignmentReal 2 5 (2 ^ a) a 4 =
      ((3 : ℝ) * ((2 ^ a : ℕ) : ℝ) - 1) /
        ((5 : ℝ) * ((2 ^ a : ℕ) : ℝ) - 1) := by
  have hm : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
  have hD : 2 ^ a ∣ 2 ^ a := dvd_rfl
  rw [clearedAlignmentReal_eq_cosetAlignmentReal Nat.prime_five (by norm_num)
    hm hD (by norm_num)]
  have hcofactor : clearingCofactor 2 (2 ^ a) a = 1 := by
    unfold clearingCofactor
    exact Nat.div_self (pow_pos (by norm_num) a)
  have hT : powerOrbitBinSum (b := 2) (p := 5)
      (u := clearingCofactor 2 (2 ^ a) a) (L := 4)
      Nat.prime_five (by norm_num)
      (prime_coprime_clearingCofactor Nat.prime_five (by norm_num) hD) = 8 := by
    rw [← computablePowerOrbitBinSum_eq Nat.prime_five (by norm_num)
      (prime_coprime_clearingCofactor Nat.prime_five (by norm_num) hD)]
    rw [hcofactor]
    exact baseTwoPrimeFive_powerOrbitBinSum
  rw [hT]
  simpa only [Nat.reduceMul] using
    (sharpness_family_eq (L := 4) (m := 2 ^ a) (by norm_num))

/-- Hence the literal sharpness family converges to three-fifths. -/
theorem baseTwoPrimeFive_clearedAlignmentReal_tendsto :
    Filter.Tendsto
      (fun a => ThreeTier.clearedAlignmentReal 2 5 (2 ^ a) a 4)
      Filter.atTop (nhds ((3 : ℝ) / 5)) := by
  have hpow : Filter.Tendsto (fun a : ℕ => 2 ^ a) Filter.atTop Filter.atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hcoset := sharpness_family_tendsto (L := 4) (by norm_num)
  have hcomp := hcoset.comp hpow
  convert hcomp using 1
  funext a
  rw [baseTwoPrimeFive_clearedAlignmentReal]
  unfold Function.comp
  symm
  simpa only [Nat.reduceMul] using
    (sharpness_family_eq (L := 4) (m := 2 ^ a) (by norm_num))

/-- Exact finite data for one row of the displayed decimal table. -/
structure DecimalAlignmentLimitRow where
  prime : ℕ
  period : ℕ
  squareSum : ℕ
  subgroupBinSum : ℕ
  limitNumerator : ℕ
  limitDenominator : ℕ
  roundedFourDigits : ℕ
  equidistributed : Bool
deriving DecidableEq, Repr

/-- Exhaustive finite equality of all nonzero starting-orbit bin sums. -/
def allOrbitBinSumsEquidistributed (p L S : ℕ) : Bool :=
  (List.range (p - 1)).all fun v =>
    let u := v + 1
    decide (computablePowerOrbitBinSum 10 p u L * (p - 1) = L * S)

/-- Exact rational rounding to four digits after the decimal point. -/
def roundFourDecimalPlaces (numerator denominator : ℕ) : ℕ :=
  (20000 * numerator + denominator) / (2 * denominator)

/-- Every field of a decimal row is checked from the definitions. -/
def DecimalAlignmentLimitRow.validCheck (row : DecimalAlignmentLimitRow) : Bool :=
  decide (Nat.Prime row.prime) &&
  leastPositiveModularPeriodCheck 10 row.prime row.period &&
  decide (computableDigitBinSquareSum 10 row.prime = row.squareSum) &&
  decide (computablePowerOrbitBinSum 10 row.prime 1 row.period = row.subgroupBinSum) &&
  decide ((row.period + row.subgroupBinSum) * row.limitDenominator =
    row.limitNumerator * row.prime * row.period) &&
  decide (roundFourDecimalPlaces row.limitNumerator row.limitDenominator =
    row.roundedFourDigits) &&
  decide (allOrbitBinSumsEquidistributed row.prime row.period row.squareSum =
    row.equidistributed)

def DecimalAlignmentLimitRow.Valid (row : DecimalAlignmentLimitRow) : Prop :=
  row.validCheck = true

/-- The exact rows printed in the manuscript's decimal table. -/
def decimalAlignmentLimitRows : List DecimalAlignmentLimitRow :=
  [ ⟨3, 1, 2, 1, 2, 3, 6667, true⟩,
    ⟨7, 6, 6, 6, 2, 7, 2857, true⟩,
    ⟨11, 2, 10, 2, 2, 11, 1818, true⟩,
    ⟨13, 6, 16, 8, 7, 39, 1795, true⟩,
    ⟨17, 16, 28, 28, 11, 68, 1618, true⟩,
    ⟨19, 18, 34, 34, 26, 171, 1520, true⟩,
    ⟨23, 22, 50, 50, 36, 253, 1423, true⟩,
    ⟨29, 28, 80, 80, 27, 203, 1330, true⟩,
    ⟨31, 15, 90, 45, 4, 31, 1290, true⟩,
    ⟨37, 3, 132, 11, 14, 111, 1261, true⟩,
    ⟨41, 5, 160, 20, 5, 41, 1220, true⟩,
    ⟨43, 21, 178, 89, 110, 903, 1218, true⟩,
    ⟨47, 46, 214, 214, 130, 1081, 1203, true⟩,
    ⟨53, 13, 272, 67, 80, 689, 1161, false⟩,
    ⟨59, 58, 338, 338, 198, 1711, 1157, true⟩,
    ⟨61, 60, 360, 360, 7, 61, 1148, true⟩ ]

/-- Every printed decimal row passes its exact kernel checker. -/
theorem decimalAlignmentLimitRows_check :
    decimalAlignmentLimitRows.all DecimalAlignmentLimitRow.validCheck = true := by
  set_option maxHeartbeats 4000000 in
    set_option maxRecDepth 10000 in
      decide

/-- Proposition-level reading of the executable row certificate. -/
theorem decimalAlignmentLimitRows_valid :
    ∀ row ∈ decimalAlignmentLimitRows, row.Valid := by
  intro row hrow
  exact (List.all_eq_true.mp decimalAlignmentLimitRows_check row hrow)

/-- Prime-period pairs needed for the exhaustive decimal check below one
hundred. -/
def decimalPrimePeriodsBelowOneHundred : List (ℕ × ℕ) :=
  [(3,1), (7,6), (11,2), (13,6), (17,16), (19,18), (23,22),
   (29,28), (31,15), (37,3), (41,5), (43,21), (47,46), (53,13),
   (59,58), (61,60), (67,33), (71,35), (73,8), (79,13), (83,41),
   (89,44), (97,96)]

/-- The stored periods are themselves exhaustively checked as least positive
return times. -/
theorem decimalPrimePeriodsBelowOneHundred_valid :
    ∀ pair ∈ decimalPrimePeriodsBelowOneHundred,
      Nat.Prime pair.1 ∧ pair.1 < 100 ∧ ¬pair.1 ∣ 10 ∧
        leastPositiveModularPeriodCheck 10 pair.1 pair.2 = true := by
  set_option maxHeartbeats 2000000 in
    decide

/-- The stored list contains every prime below one hundred that is coprime to
base ten, and no others. -/
theorem decimalPrimePeriodsBelowOneHundred_complete :
    (List.range 100).filter (fun p => decide (Nat.Prime p ∧ ¬p ∣ 10)) =
      decimalPrimePeriodsBelowOneHundred.map Prod.fst := by
  decide

theorem decimalThree_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 3 1 (computableDigitBinSquareSum 10 3) = true := by decide
theorem decimalSeven_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 7 6 (computableDigitBinSquareSum 10 7) = true := by decide
theorem decimalEleven_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 11 2 (computableDigitBinSquareSum 10 11) = true := by decide
theorem decimalThirteen_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 13 6 (computableDigitBinSquareSum 10 13) = true := by decide
theorem decimalSeventeen_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 17 16 (computableDigitBinSquareSum 10 17) = true := by decide
theorem decimalNineteen_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 19 18 (computableDigitBinSquareSum 10 19) = true := by decide
theorem decimalTwentyThree_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 23 22 (computableDigitBinSquareSum 10 23) = true := by decide
theorem decimalTwentyNine_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 29 28 (computableDigitBinSquareSum 10 29) = true := by decide
theorem decimalThirtyOne_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 31 15 (computableDigitBinSquareSum 10 31) = true := by decide
theorem decimalThirtySeven_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 37 3 (computableDigitBinSquareSum 10 37) = true := by decide
theorem decimalFortyOne_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 41 5 (computableDigitBinSquareSum 10 41) = true := by decide
theorem decimalFortyThree_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 43 21 (computableDigitBinSquareSum 10 43) = true := by decide
theorem decimalFortySeven_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 47 46 (computableDigitBinSquareSum 10 47) = true := by decide
theorem decimalFiftyThree_orbitBinSumsNotEquidistributed :
    allOrbitBinSumsEquidistributed 53 13 (computableDigitBinSquareSum 10 53) = false := by decide
theorem decimalFiftyNine_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 59 58 (computableDigitBinSquareSum 10 59) = true := by decide
theorem decimalSixtyOne_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 61 60 (computableDigitBinSquareSum 10 61) = true := by
  set_option maxHeartbeats 1000000 in decide
theorem decimalSixtySeven_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 67 33 (computableDigitBinSquareSum 10 67) = true := by decide
theorem decimalSeventyOne_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 71 35 (computableDigitBinSquareSum 10 71) = true := by decide
theorem decimalSeventyThree_orbitBinSumsNotEquidistributed :
    allOrbitBinSumsEquidistributed 73 8 (computableDigitBinSquareSum 10 73) = false := by decide
theorem decimalSeventyNine_orbitBinSumsNotEquidistributed :
    allOrbitBinSumsEquidistributed 79 13 (computableDigitBinSquareSum 10 79) = false := by decide
theorem decimalEightyThree_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 83 41 (computableDigitBinSquareSum 10 83) = true := by
  set_option maxHeartbeats 1000000 in decide
theorem decimalEightyNine_orbitBinSumsNotEquidistributed :
    allOrbitBinSumsEquidistributed 89 44 (computableDigitBinSquareSum 10 89) = false := by decide
theorem decimalNinetySeven_orbitBinSumsEquidistributed :
    allOrbitBinSumsEquidistributed 97 96 (computableDigitBinSquareSum 10 97) = true := by
  set_option maxHeartbeats 2000000 in
    set_option maxRecDepth 10000 in
      decide

/-- The exact four failures of coset-bin-sum equidistribution below one
hundred in base ten. -/
theorem decimalEquidistributionExceptionsBelowOneHundred :
    (decimalPrimePeriodsBelowOneHundred.filter fun pair =>
      !allOrbitBinSumsEquidistributed pair.1 pair.2
        (computableDigitBinSquareSum 10 pair.1)).map Prod.fst = [53, 73, 79, 89] := by
  simp [decimalPrimePeriodsBelowOneHundred,
    decimalThree_orbitBinSumsEquidistributed,
    decimalSeven_orbitBinSumsEquidistributed,
    decimalEleven_orbitBinSumsEquidistributed,
    decimalThirteen_orbitBinSumsEquidistributed,
    decimalSeventeen_orbitBinSumsEquidistributed,
    decimalNineteen_orbitBinSumsEquidistributed,
    decimalTwentyThree_orbitBinSumsEquidistributed,
    decimalTwentyNine_orbitBinSumsEquidistributed,
    decimalThirtyOne_orbitBinSumsEquidistributed,
    decimalThirtySeven_orbitBinSumsEquidistributed,
    decimalFortyOne_orbitBinSumsEquidistributed,
    decimalFortyThree_orbitBinSumsEquidistributed,
    decimalFortySeven_orbitBinSumsEquidistributed,
    decimalFiftyThree_orbitBinSumsNotEquidistributed,
    decimalFiftyNine_orbitBinSumsEquidistributed,
    decimalSixtyOne_orbitBinSumsEquidistributed,
    decimalSixtySeven_orbitBinSumsEquidistributed,
    decimalSeventyOne_orbitBinSumsEquidistributed,
    decimalSeventyThree_orbitBinSumsNotEquidistributed,
    decimalSeventyNine_orbitBinSumsNotEquidistributed,
    decimalEightyThree_orbitBinSumsEquidistributed,
    decimalEightyNine_orbitBinSumsNotEquidistributed,
    decimalNinetySeven_orbitBinSumsEquidistributed]

/-- At decimal prime fifty-three the four quotient families have precisely
the two stated bin sums. -/
theorem decimalPrimeFiftyThree_orbitBinSumValues :
    ((ThreeTier.positiveResidues 53).image fun u =>
      computablePowerOrbitBinSum 10 53 u 13) = {67, 69} := by decide

/-- The four representatives selected by successive powers of five give the
four cosets and the paired bin sums printed in the manuscript. -/
theorem decimalPrimeFiftyThree_selectedRepresentatives :
    (List.range 4).map (fun a =>
      (5 ^ a % 53, computablePowerOrbitBinSum 10 53 (5 ^ a) 13)) =
        [(1, 67), (5, 69), (25, 67), (19, 69)] := by decide

/-- The named prime-fifty-three cosets in the manuscript have the asserted
bin sums. -/
theorem decimalPrimeFiftyThree_namedCosetBinSums :
    computablePowerOrbitBinSum 10 53 1 13 = 67 ∧
      computablePowerOrbitBinSum 10 53 25 13 = 67 ∧
      computablePowerOrbitBinSum 10 53 2 13 = 69 ∧
      computablePowerOrbitBinSum 10 53 5 13 = 69 := by
  decide

/-- Clearing `m=2^a` at decimal depth `a` leaves exactly the cofactor `5^a`. -/
theorem decimalTwoPower_clearingCofactor (a : ℕ) :
    clearingCofactor 10 (2 ^ a) a = 5 ^ a := by
  unfold clearingCofactor
  rw [show 10 ^ a = (2 * 5) ^ a by norm_num, Nat.mul_pow]
  exact Nat.mul_div_cancel_left (5 ^ a) (by positivity : 0 < 2 ^ a)

/-- The unit selected by the supported family `m=2^a`, whose clearing
cofactor is `5^a`. -/
noncomputable def decimalPrimeFiftyThreeSelectedUnit (a : ℕ) : (ZMod 53)ˣ :=
  ZMod.unitOfCoprime (5 ^ a)
    ((prime_coprime_base_pow (D := a) (by norm_num : Nat.Prime 53)
      (by norm_num : ¬53 ∣ 5)).symm)

/-- Advancing the exponent by four returns to the same decimal base-orbit
coset at prime fifty-three. -/
theorem decimalPrimeFiftyThree_selectedCoset_period_four (a : ℕ) :
    (decimalPrimeFiftyThreeSelectedUnit a :
        (ZMod 53)ˣ ⧸ primeBaseOrbitSubgroup 10 53
          (by norm_num) (by norm_num)) =
      decimalPrimeFiftyThreeSelectedUnit (a + 4) := by
  have hp53 : Nat.Prime 53 := by norm_num
  have hperiod : primeBasePeriod 10 53 hp53 (by norm_num) = 13 := by
    apply primeBasePeriod_eq_of_isLeastPositiveModularPeriod hp53 (by norm_num)
    exact leastPositiveModularPeriodCheck_eq_true_iff.mp (by decide)
  apply (same_primeBaseOrbit_iff hp53 (by norm_num)
    (decimalPrimeFiftyThreeSelectedUnit a)
    (decimalPrimeFiftyThreeSelectedUnit (a + 4))).2
  refine ⟨5, by omega, ?_⟩
  apply Units.ext
  change ((5 ^ a : ℕ) : ZMod 53) * (((10 : ℕ) : ZMod 53) ^ 5) =
    ((5 ^ (a + 4) : ℕ) : ZMod 53)
  have hbase : 5 ^ 4 ≡ 10 ^ 5 [MOD 53] := by decide
  have hcong := (Nat.ModEq.refl (5 ^ a)).mul hbase
  have hmod : (5 ^ a * 10 ^ 5) % 53 = 5 ^ (a + 4) % 53 := by
    change 5 ^ a * 10 ^ 5 ≡ 5 ^ (a + 4) [MOD 53]
    simpa [pow_add] using hcong.symm
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    (ZMod.natCast_eq_natCast_iff' (5 ^ a * 10 ^ 5) (5 ^ (a + 4)) 53).2 hmod

/-- The orbit-bin sum selected by `5^a` is periodic with period four. -/
theorem decimalPrimeFiftyThree_powerOrbitBinSum_period_four (a : ℕ) :
    computablePowerOrbitBinSum 10 53 (5 ^ (a + 4)) 13 =
      computablePowerOrbitBinSum 10 53 (5 ^ a) 13 := by
  have hp53 : Nat.Prime 53 := by norm_num
  have hpb : ¬53 ∣ 10 := by norm_num
  have hua : Nat.Coprime 53 (5 ^ a) := by
    exact (by norm_num : Nat.Coprime 53 5).pow_right a
  have hua4 : Nat.Coprime 53 (5 ^ (a + 4)) := by
    exact (by norm_num : Nat.Coprime 53 5).pow_right (a + 4)
  have hbaseu : Nat.Coprime 53 (10 ^ 5 * 5 ^ a) :=
    ((by norm_num : Nat.Coprime 53 10).pow_right 5).mul_right hua
  rw [computablePowerOrbitBinSum_eq hp53 hpb hua4,
    computablePowerOrbitBinSum_eq hp53 hpb hua]
  calc
    powerOrbitBinSum (b := 10) (p := 53) (u := 5 ^ (a + 4)) (L := 13)
        hp53 hpb hua4 =
      powerOrbitBinSum (b := 10) (p := 53) (u := 10 ^ 5 * 5 ^ a) (L := 13)
        hp53 hpb hbaseu := by
          apply powerOrbitBinSum_congr_multiplier hp53 hpb hua4 hbaseu
          have hbase : 5 ^ 4 ≡ 10 ^ 5 [MOD 53] := by decide
          have hcong := (Nat.ModEq.refl (5 ^ a)).mul hbase
          have : 5 ^ (a + 4) ≡ 10 ^ 5 * 5 ^ a [MOD 53] := by
            simpa [pow_add, Nat.mul_comm] using hcong
          exact this
    _ = powerOrbitBinSum (b := 10) (p := 53) (u := 5 ^ a) (L := 13)
        hp53 hpb hua := by
          apply powerOrbitBinSum_mul_base_pow hp53 hpb hua
          decide

/-- The even and odd representatives of the period-four family realize the
two prime-fifty-three orbit-bin sums on explicit infinite subsequences. -/
theorem decimalPrimeFiftyThree_powerOrbitBinSum_subsequences (k : ℕ) :
    computablePowerOrbitBinSum 10 53 (5 ^ (4 * k)) 13 = 67 ∧
      computablePowerOrbitBinSum 10 53 (5 ^ (4 * k + 1)) 13 = 69 := by
  induction k with
  | zero =>
      simpa using And.intro
        decimalPrimeFiftyThree_namedCosetBinSums.1
        decimalPrimeFiftyThree_namedCosetBinSums.2.2.2
  | succ k ih =>
      constructor
      · rw [show 4 * (k + 1) = 4 * k + 4 by omega,
          decimalPrimeFiftyThree_powerOrbitBinSum_period_four]
        exact ih.1
      · rw [show 4 * (k + 1) + 1 = (4 * k + 1) + 4 by omega,
          decimalPrimeFiftyThree_powerOrbitBinSum_period_four]
        exact ih.2

/-- The first four selected exponents represent four distinct quotient
families.  Together with the period-four recurrence, the selected coset is
therefore determined exactly by `a mod 4`. -/
theorem decimalPrimeFiftyThree_firstFourCosets_injective :
    Function.Injective (fun a : Fin 4 =>
      (decimalPrimeFiftyThreeSelectedUnit a.val :
        (ZMod 53)ˣ ⧸ primeBaseOrbitSubgroup 10 53
          (by norm_num) (by norm_num))) := by
  have hp53 : Nat.Prime 53 := by norm_num
  have hperiod : primeBasePeriod 10 53 hp53 (by norm_num) = 13 := by
    apply primeBasePeriod_eq_of_isLeastPositiveModularPeriod hp53 (by norm_num)
    exact leastPositiveModularPeriodCheck_eq_true_iff.mp (by decide)
  intro x y hxy
  apply Fin.ext
  by_contra hval
  rcases (same_primeBaseOrbit_iff hp53 (by norm_num)
    (decimalPrimeFiftyThreeSelectedUnit x.val)
    (decimalPrimeFiftyThreeSelectedUnit y.val)).1 hxy with ⟨j, hj, heq⟩
  rw [hperiod] at hj
  have heqZ := congrArg (fun z : (ZMod 53)ˣ => (z : ZMod 53)) heq
  have heqVal := congrArg ZMod.val heqZ
  have hvalOne : ZMod.val (1 : ZMod 53) = 1 :=
    ZMod.val_one'' (by norm_num)
  fin_cases x <;> fin_cases y
  all_goals try { norm_num at hval }
  all_goals interval_cases j <;>
    norm_num [decimalPrimeFiftyThreeSelectedUnit, primeBaseUnit,
      ZMod.coe_unitOfCoprime, ZMod.val_ofNat, hvalOne] at heqVal

/-- The two orbit-bin sums at decimal prime fifty-three give exactly the two
subsequential limits displayed in the manuscript. -/
theorem decimalPrimeFiftyThree_subsequentialLimits :
    ((((13 + 67 : ℕ) : ℚ) / (53 * 13 : ℕ)) = 80 / 689) ∧
      ((((13 + 69 : ℕ) : ℚ) / (53 * 13 : ℕ)) = 82 / 689) := by
  norm_num

/-- The quotient by the decimal base orbit has exactly four cosets at prime
fifty-three. -/
theorem decimalPrimeFiftyThree_orbitFamilyCount :
    Nat.card ((ZMod 53)ˣ ⧸ primeBaseOrbitSubgroup 10 53
      (by norm_num) (by norm_num)) = 4 := by
  have hp53 : Nat.Prime 53 := by norm_num
  rw [primeBaseOrbitFamily_count hp53 (by norm_num)]
  have hleast : IsLeastPositiveModularPeriod 10 53 13 := by
    exact (leastPositiveModularPeriodCheck_eq_true_iff.mp (by decide))
  rw [primeBasePeriod_eq_of_isLeastPositiveModularPeriod
    hp53 (by norm_num) hleast]

end NField.Alignment
