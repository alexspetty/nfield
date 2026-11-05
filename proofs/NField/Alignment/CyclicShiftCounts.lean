/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OneDigitModulus
import NField.Alignment.ThreeTier

/-!
# Cyclic shifts on supported-denominator rows

The canonical long-division digits identify their starting remainder. This
gives the literal digit-tail criterion for membership in the subgroup generated
by the base, for every coprime integer modulus, including composite ones.
Counting the positive numerators gives `h*m` cyclic shifts and `m-1` terminating
rows. The classes are independent of common clearing depth, and summing their
actual row weights gives the finite score in Proposition 10 of
"Repetend Rigidity at the Golden Scale."

The existing `coprimeBasePeriod`, `digitAt`, `ClearsAtDepth`, clearing identity
and complete-residue count are reused. Cyclic matching is defined by equality
of digit streams, not by the residue condition that the proof must establish.
This module does not prove the later order-gap, period-rigidity or cumulative
closure results.
-/

namespace NField.Alignment

/-- Appending one long-division digit reconstructs the next prefix quotient. -/
theorem digitPrefix_succ (b q r t : ℕ) (hq : 0 < q) :
    (b ^ (t + 1) * r) / q =
      b * ((b ^ t * r) / q) + digitAt b q r t := by
  unfold digitAt NField.CollisionDefinition.digitBin
  have heq := Nat.mod_add_div (b ^ t * r) q
  rw [pow_succ]
  have hex : b ^ t * b * r =
      b * ((b ^ t * r) % q) + q * (b * ((b ^ t * r) / q)) := by
    nlinarith [congrArg (fun x => b * x) heq]
  rw [hex]
  rw [Nat.add_mul_div_left _ _ hq]
  omega

theorem digitPrefix_eq_of_digits {b q r s t : ℕ} (hq : 0 < q)
    (hr : r < q) (hs : s < q)
    (hd : ∀ j < t, digitAt b q r j = digitAt b q s j) :
    (b ^ t * r) / q = (b ^ t * s) / q := by
  induction t with
  | zero => simp [Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hs]
  | succ t ih =>
    rw [digitPrefix_succ b q r t hq, digitPrefix_succ b q s t hq,
      ih (fun j hj => hd j (by omega)), hd t (by omega)]

theorem digitAt_mod_start (b q r j : ℕ) :
    digitAt b q (r % q) j = digitAt b q r j := by
  simp [digitAt, Nat.mul_mod]

/-- The first `q` digits distinguish every remainder modulo `q` in a base at least two. -/
theorem digitStream_injective {b q r s : ℕ} (hb : 2 ≤ b) (hq : 0 < q)
    (hd : ∀ j < q, digitAt b q r j = digitAt b q s j) :
    r % q = s % q := by
  have hpref : (b ^ q * (r % q)) / q = (b ^ q * (s % q)) / q :=
    digitPrefix_eq_of_digits hq (Nat.mod_lt _ hq) (Nat.mod_lt _ hq)
      (fun j hj => by simpa only [digitAt_mod_start] using hd j hj)
  have hpow : q < b ^ q := Nat.lt_pow_self (by omega)
  rcases lt_trichotomy (r % q) (s % q) with hlt | heq | hgt
  · have h := above_digit_strict hq hpow hlt
    unfold NField.CollisionDefinition.digitBin at h
    omega
  · exact heq
  · have h := above_digit_strict hq hpow hgt
    unfold NField.CollisionDefinition.digitBin at h
    omega

theorem digitAt_shift (b q r j s : ℕ) :
    digitAt b q r (j + s) = digitAt b q (b ^ s * r) j := by
  simp [digitAt, pow_add, Nat.mul_assoc]

theorem digitStream_eq_iff_mod_eq {b q r s : ℕ} (hb : 2 ≤ b) (hq : 0 < q) :
    (∀ j, digitAt b q r j = digitAt b q s j) ↔ r % q = s % q := by
  constructor
  · intro hd
    exact digitStream_injective hb hq (fun j _ => hd j)
  · intro heq j
    rw [← digitAt_mod_start b q r, ← digitAt_mod_start b q s, heq]

/-- Canonical representatives of the powers of the base through its multiplicative period. -/
noncomputable def coprimeBaseOrbitResidues (b q : ℕ) (hcop : Nat.Coprime q b) :
    Finset ℕ :=
  (Finset.range (coprimeBasePeriod b q hcop)).image (fun j => b ^ j % q)

theorem coprimeBase_pow_mod_period (b q s : ℕ) (hcop : Nat.Coprime q b) :
    b ^ (s % coprimeBasePeriod b q hcop) % q = b ^ s % q := by
  have heq := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q))
    (pow_mod_orderOf (ZMod.unitOfCoprime b hcop.symm) s)
  have hc : ((b ^ (s % coprimeBasePeriod b q hcop) : ℕ) : ZMod q) =
      ((b ^ s : ℕ) : ZMod q) := by
    simpa only [coprimeBasePeriod, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Nat.cast_pow] using heq
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc

theorem coprimeBaseOrbitResidues_card (b q : ℕ) (hcop : Nat.Coprime q b) :
    (coprimeBaseOrbitResidues b q hcop).card = coprimeBasePeriod b q hcop := by
  rw [coprimeBaseOrbitResidues, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj heq
  have hcast : ((b ^ i : ℕ) : ZMod q) = ((b ^ j : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr heq
  have hunits : ZMod.unitOfCoprime b hcop.symm ^ i = ZMod.unitOfCoprime b hcop.symm ^ j := by
    apply Units.ext
    simpa [ZMod.coe_unitOfCoprime] using hcast
  exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hunits

theorem mem_coprimeBaseOrbitResidues_iff {b q r : ℕ} (_hq : 0 < q)
    (hcop : Nat.Coprime q b) :
    r ∈ coprimeBaseOrbitResidues b q hcop ↔ ∃ s, b ^ s % q = r := by
  constructor
  · intro hr
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hr
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    exact Finset.mem_image.mpr ⟨s % coprimeBasePeriod b q hcop,
      Finset.mem_range.mpr (Nat.mod_lt _ (coprimeBasePeriod_pos hcop)),
      coprimeBase_pow_mod_period b q s hcop⟩

theorem coprimeBaseOrbitResidues_nonzero {b q r : ℕ} (hq : 1 < q)
    (hcop : Nat.Coprime q b) (hr : r ∈ coprimeBaseOrbitResidues b q hcop) :
    r ≠ 0 ∧ r < q := by
  obtain ⟨s, rfl⟩ := (mem_coprimeBaseOrbitResidues_iff (by omega) hcop).mp hr
  refine ⟨?_, Nat.mod_lt _ (by omega)⟩
  intro heq
  have hd : q ∣ b ^ s := Nat.dvd_of_mod_eq_zero heq
  have hg : Nat.Coprime q (b ^ s) := hcop.pow_right s
  have hone := hg.eq_one_of_dvd hd
  omega

/-- The finite representatives are exactly the cyclic subgroup generated by
the base in the full unit group, including composite moduli. -/
theorem mem_coprimeBaseOrbitResidues_iff_subgroup {b q r : ℕ}
    (hcop : Nat.Coprime q b) (hr : r < q) :
    r ∈ coprimeBaseOrbitResidues b q hcop ↔
      ∃ v : (ZMod q)ˣ, v ∈ Subgroup.zpowers (ZMod.unitOfCoprime b hcop.symm) ∧
        (v : ZMod q) = (r : ZMod q) := by
  constructor
  · intro h
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp h
    refine ⟨ZMod.unitOfCoprime b hcop.symm ^ s,
      Subgroup.npow_mem_zpowers _ _, ?_⟩
    have hc := (ZMod.natCast_eq_natCast_iff' (b ^ s) r q).mpr
      (heq.trans (Nat.mod_eq_of_lt hr).symm)
    simpa [ZMod.coe_unitOfCoprime] using hc
  · rintro ⟨v, hv, heq⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv)
    have hc : ((b ^ s : ℕ) : ZMod q) = (r : ZMod q) := by
      simpa [ZMod.coe_unitOfCoprime] using heq
    exact Finset.mem_image.mpr ⟨s, hs,
      ((ZMod.natCast_eq_natCast_iff' (b ^ s) r q).mp hc).trans (Nat.mod_eq_of_lt hr)⟩

/-- Equality with a shift of the literal canonical reference digit stream. -/
def MatchesCyclicReference (b q u k : ℕ) : Prop :=
  ∃ s, ∀ j, digitAt b q (k * u) j = digitAt b q u (j + s)

theorem matchesCyclicReference_iff_orbit {b q u k : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hcop : Nat.Coprime q b)
    (hu : Nat.Coprime q u) :
    MatchesCyclicReference b q u k ↔ k % q ∈ coprimeBaseOrbitResidues b q hcop := by
  unfold MatchesCyclicReference
  simp only [digitAt_shift]
  constructor
  · rintro ⟨s, hs⟩
    have heq := (digitStream_eq_iff_mod_eq hb (by omega)).mp hs
    have hmul : k * u ≡ b ^ s * u [MOD q] := heq
    have hcancel := Nat.ModEq.cancel_right_of_coprime hu.gcd_eq_one hmul
    exact (mem_coprimeBaseOrbitResidues_iff (by omega) hcop).mpr ⟨s, hcancel.symm⟩
  · intro hk
    obtain ⟨s, hs⟩ := (mem_coprimeBaseOrbitResidues_iff (by omega) hcop).mp hk
    refine ⟨s, (digitStream_eq_iff_mod_eq hb (by omega)).mpr ?_⟩
    exact (show k ≡ b ^ s [MOD q] from hs.symm).mul_right u

theorem reference_digit_period_iff {b q u s : ℕ} (hb : 2 ≤ b) (hq : 1 < q)
    (hcop : Nat.Coprime q b) (hu : Nat.Coprime q u) :
    (∀ j, digitAt b q u (j + s) = digitAt b q u j) ↔
      coprimeBasePeriod b q hcop ∣ s := by
  rw [show (∀ j, digitAt b q u (j + s) = digitAt b q u j) ↔
      (b ^ s * u) % q = u % q by
    simp only [digitAt_shift]
    exact digitStream_eq_iff_mod_eq hb (by omega)]
  have hcancel : (b ^ s * u) % q = u % q ↔ b ^ s % q = 1 % q := by
    constructor
    · intro h
      have heq : b ^ s * u ≡ 1 * u [MOD q] := by simpa only [Nat.ModEq, one_mul] using h
      exact Nat.ModEq.cancel_right_of_coprime hu.gcd_eq_one heq
    · intro h
      have heq : b ^ s ≡ 1 [MOD q] := h
      simpa only [Nat.ModEq, one_mul] using heq.mul_right u
  rw [hcancel, coprimeBasePeriod, orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    apply Units.ext
    have hc := (ZMod.natCast_eq_natCast_iff' (b ^ s) 1 q).mpr h
    simpa [ZMod.coe_unitOfCoprime] using hc
  · intro h
    have hc := congrArg (fun z : (ZMod q)ˣ => (z : ZMod q)) h
    apply (ZMod.natCast_eq_natCast_iff' (b ^ s) 1 q).mp
    simpa [ZMod.coe_unitOfCoprime] using hc

/-- A cyclic shift after a common clearing depth, read on the original
denominator rather than defined by residue membership. -/
def CyclicShiftAtDepth (b q m D k : ℕ) : Prop :=
  ∃ s, ∀ j, digitAt b (q * m) k (D + j) =
    digitAt b (q * m) 1 (D + (j + s))

theorem clearedDigit_eq_digitAt {b q m D k j : ℕ}
    (hm : 0 < m) (hD : m ∣ b ^ D) :
    digitAt b (q * m) k (D + j) =
      digitAt b q (k * clearingCofactor b m D) j := by
  have h := ThreeTier.clearedDigit_eq_periodicDigit (t := q) (k := k) (j := j) hm hD
  simpa [ThreeTier.clearedDigit, ThreeTier.periodicDigit, ThreeTier.periodicResidue,
    digitAt, Nat.mul_mod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem cyclicShiftAtDepth_iff_orbit {b q m D k : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) :
    CyclicShiftAtDepth b q m D k ↔ k % q ∈ coprimeBaseOrbitResidues b q hcop := by
  have heq : CyclicShiftAtDepth b q m D k ↔
      MatchesCyclicReference b q (clearingCofactor b m D) k := by
    simp only [CyclicShiftAtDepth, MatchesCyclicReference, clearedDigit_eq_digitAt hm hD,
      one_mul]
  rw [heq]
  exact matchesCyclicReference_iff_orbit hb hq hcop
    (modulus_coprime_clearingCofactor hcop hD)

theorem cyclicShift_depth_independent {b q m D E k : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) (hE : m ∣ b ^ E) :
    CyclicShiftAtDepth b q m D k ↔ CyclicShiftAtDepth b q m E k := by
  rw [cyclicShiftAtDepth_iff_orbit hb hq hm hcop hD,
    cyclicShiftAtDepth_iff_orbit hb hq hm hcop hE]

theorem residueSet_positive_count {q m : ℕ} (_hq : 0 < q)
    (R : Finset ℕ) (hrange : ∀ r ∈ R, r < q) (hzero : 0 ∉ R) :
    ((Finset.Icc 1 (q * m - 1)).filter (fun k => k % q ∈ R)).card = R.card * m := by
  classical
  have hfilter : (Finset.range q).filter (fun r => r ∈ R) = R := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hrange r h, h⟩⟩
  have hpos : (Finset.Icc 1 (q * m - 1)).filter (fun k => k % q ∈ R) =
      (Finset.range (q * m)).filter (fun k => k % q ∈ R) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hk⟩
      exact ⟨by omega, hk⟩
    · rintro ⟨hklt, hk⟩
      have hk0 : k ≠ 0 := by
        intro heq
        subst k
        exact hzero (by simpa using hk)
      exact ⟨⟨by omega, by omega⟩, hk⟩
  have hblock := ThreeTier.sum_mod_blocks q m (fun r => if r ∈ R then 1 else 0)
  simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one] at hblock
  rw [hfilter] at hblock
  rw [hpos]
  simpa only [Nat.mul_comm] using hblock

/-- The actual positive numerator rows whose canonical tails match a cyclic shift. -/
noncomputable def cyclicShiftNumerators (b q m D : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (q * m - 1)).filter (CyclicShiftAtDepth b q m D)

theorem cyclicShiftNumerators_card {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) :
    (cyclicShiftNumerators b q m D).card = coprimeBasePeriod b q hcop * m := by
  classical
  have hset : cyclicShiftNumerators b q m D =
      (Finset.Icc 1 (q * m - 1)).filter
        (fun k => k % q ∈ coprimeBaseOrbitResidues b q hcop) := by
    ext k
    simp only [cyclicShiftNumerators, Finset.mem_filter,
      cyclicShiftAtDepth_iff_orbit hb hq hm hcop hD]
  rw [hset, residueSet_positive_count (by omega), coprimeBaseOrbitResidues_card]
  · intro r hr
    exact (coprimeBaseOrbitResidues_nonzero hq hcop hr).2
  · intro hzero
    exact (coprimeBaseOrbitResidues_nonzero hq hcop hzero).1 rfl

/-- The actual positive numerator rows cleared by the selected common depth. -/
noncomputable def terminatingAtDepthNumerators (b q m D : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (q * m - 1)).filter (ClearsAtDepth b q m D)

theorem terminatingAtDepthNumerators_card {b q m D : ℕ}
    (hq : 0 < q) (hm : 0 < m) (hcop : Nat.Coprime q b) (hD : m ∣ b ^ D) :
    (terminatingAtDepthNumerators b q m D).card = m - 1 := by
  classical
  have hfull : ((Finset.range (q * m)).filter (fun k => k % q = 0)).card = m := by
    rw [← Nat.count_eq_card_filter_range]
    exact residueCount_eq hq
  have hsplit : (Finset.range (q * m)).filter (fun k => k % q = 0) =
      insert 0 (terminatingAtDepthNumerators b q m D) := by
    rw [ThreeTier.range_product_eq_insert_positive hq (by omega), Finset.filter_insert]
    simp only [Nat.zero_mod, ↓reduceIte]
    congr 1
    ext k
    simp only [terminatingAtDepthNumerators, Finset.mem_filter,
      clearsAtDepth_iff_residue_zero hcop hD]
  rw [hsplit, Finset.card_insert_of_notMem] at hfull
  · omega
  · simp [terminatingAtDepthNumerators]

theorem cyclicShift_not_clearsAtDepth {b q m D k : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) (hk : CyclicShiftAtDepth b q m D k) :
    ¬ ClearsAtDepth b q m D k := by
  have horbit := (cyclicShiftAtDepth_iff_orbit hb hq hm hcop hD).mp hk
  have hnonzero := (coprimeBaseOrbitResidues_nonzero hq hcop horbit).1
  intro hc
  exact hnonzero ((clearsAtDepth_iff_residue_zero hcop hD).mp hc)

/-- The paper's actual row weighting: one for a cyclic shift, `lambda` for
termination, and zero otherwise. -/
noncomputable def cyclicShiftRowWeight (b q m D k : ℕ) (lambda : ℝ) : ℝ := by
  classical
  exact if CyclicShiftAtDepth b q m D k then 1 else
    if ClearsAtDepth b q m D k then lambda else 0

noncomputable def cyclicShiftScore (b q m D : ℕ) (lambda : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 (q * m - 1), cyclicShiftRowWeight b q m D k lambda) /
    (q * m - 1 : ℕ)

/-- The finite weighted average of the literal digit-tail classes has the
paper's closed formula. The equality is valid for every real weight. -/
theorem cyclicShiftScore_eq {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) (lambda : ℝ) :
    cyclicShiftScore b q m D lambda =
      ((coprimeBasePeriod b q hcop : ℝ) * m + lambda * (m - 1 : ℕ)) /
        (q * m - 1 : ℕ) := by
  classical
  have hrow (k : ℕ) : cyclicShiftRowWeight b q m D k lambda =
      (if CyclicShiftAtDepth b q m D k then (1 : ℝ) else 0) +
      (if ClearsAtDepth b q m D k then lambda else 0) := by
    by_cases hk : CyclicShiftAtDepth b q m D k
    · simp [cyclicShiftRowWeight, hk, cyclicShift_not_clearsAtDepth hb hq hm hcop hD hk]
    · simp [cyclicShiftRowWeight, hk]
  unfold cyclicShiftScore
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  change ((cyclicShiftNumerators b q m D).card * (1 : ℝ) +
    (terminatingAtDepthNumerators b q m D).card * lambda) / _ = _
  rw [cyclicShiftNumerators_card hb hq hm hcop hD,
    terminatingAtDepthNumerators_card (by omega) hm hcop hD]
  push_cast
  ring

/-- Returning to the reference digit tail after `s` positions is equivalent
to divisibility by the positive multiplicative order of the base. -/
theorem cyclic_reference_least_period {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) :
    0 < coprimeBasePeriod b q hcop ∧
    ∀ s, (∀ j, digitAt b (q * m) 1 (D + (j + s)) =
      digitAt b (q * m) 1 (D + j)) ↔ coprimeBasePeriod b q hcop ∣ s := by
  refine ⟨coprimeBasePeriod_pos hcop, fun s => ?_⟩
  simp only [clearedDigit_eq_digitAt hm hD, one_mul]
  exact reference_digit_period_iff hb hq hcop (modulus_coprime_clearingCofactor hcop hD)

/-- The exact cyclic-shift partition for arbitrary coprime bases: subgroup
membership, positive-row counts, and independence of the clearing depth. -/
theorem cyclic_shift_block_profile {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) :
    (∀ k, CyclicShiftAtDepth b q m D k ↔
      k % q ∈ coprimeBaseOrbitResidues b q hcop) ∧
    (cyclicShiftNumerators b q m D).card = coprimeBasePeriod b q hcop * m ∧
    (terminatingAtDepthNumerators b q m D).card = m - 1 ∧
    (∀ E, m ∣ b ^ E → ∀ k,
      (CyclicShiftAtDepth b q m D k ↔ CyclicShiftAtDepth b q m E k) ∧
      (ClearsAtDepth b q m D k ↔ ClearsAtDepth b q m E k)) := by
  refine ⟨fun k => cyclicShiftAtDepth_iff_orbit hb hq hm hcop hD,
    cyclicShiftNumerators_card hb hq hm hcop hD,
    terminatingAtDepthNumerators_card (by omega) hm hcop hD, ?_⟩
  intro E hE k
  exact ⟨cyclicShift_depth_independent hb hq hm hcop hD hE,
    (clearsAtDepth_iff_residue_zero hcop hD).trans
      (clearsAtDepth_iff_residue_zero hcop hE).symm⟩


end NField.Alignment
