/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliStraightening
import NField.Alignment.PrimeSquareCubicEnergy
import NField.Alignment.SecondaryCapacityLedger

/-!
# Exact sampling-reservoir bridge

This module identifies the continuous reduced-ratio capacity and the concrete
prime carry energy inside the same Rademacher decomposition.  The common
rational pole is cancelled here, rather than supplied as an assumed final
identity.
-/

namespace NField.Alignment.ExactSamplingReservoirBridge

open scoped BigOperators ZMod
open NField.Alignment.CollisionBernoulliStraightening
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarryTableColumnLaw
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.PrimeSquareReducedRatio
open NField.Alignment.PrimeSquareSawtoothEnergy
open NField.Alignment.SecondaryCapacityLedger

/-- The elementary reciprocal-ratio sum denoted `X_p` in the manuscript. -/
noncomputable def elementaryRatioReservoir (p : ℕ) : ℝ :=
  ∑ ak ∈ reducedRatioPairs p,
    (((p - 1) / ak.1 : ℕ) : ℝ) *
      ((ak.1 : ℝ) / (ak.2 : ℝ) + (ak.2 : ℝ) / (ak.1 : ℝ))

/-- The surviving lower-modulus Rademacher reservoir, as a real number. -/
noncomputable def lowerModulusReservoir (p : ℕ) : ℝ :=
  (offDiagonalModulusK p).re

/-- The finite sampling defect in the concrete carry-energy coordinates. -/
noncomputable def samplingDefect
    {p : ℕ} (hp : p.Prime) : ℝ :=
  continuousCapacity (p - 1) - collisionEnergy hp / (p : ℝ) ^ 2

/-- At a multiple of the prime, one carry-table entry is the corresponding
telescoping increment on the quotient clock. -/
theorem floorJump_primeMultiple
    {p c d : ℕ} (hp0 : 0 < p) :
    floorJump (p ^ 2) (p * c) ((p + 1) * d) =
      ((((d + 1) * c) / p : ℕ) : ℤ) -
        (((d * c) / p : ℕ) : ℤ) := by
  unfold floorJump
  have hnext :
      ((((p + 1) * d + 1) * (p * c)) / p ^ 2) =
        d * c + ((d + 1) * c) / p := by
    rw [show ((p + 1) * d + 1) * (p * c) =
        p * ((((p + 1) * d + 1) * c)) by ring,
      show p ^ 2 = p * p by ring,
      Nat.mul_div_mul_left _ _ hp0]
    rw [show ((p + 1) * d + 1) * c =
        (d + 1) * c + p * (d * c) by ring,
      Nat.add_mul_div_left _ _ hp0]
    omega
  have hcurrent :
      (((p + 1) * d) * (p * c) / p ^ 2) =
        d * c + (d * c) / p := by
    rw [show ((p + 1) * d) * (p * c) =
        p * (((p + 1) * d) * c) by ring,
      show p ^ 2 = p * p by ring,
      Nat.mul_div_mul_left _ _ hp0]
    rw [show ((p + 1) * d) * c = d * c + p * (d * c) by ring,
      Nat.add_mul_div_left _ _ hp0]
    omega
  rw [hnext, hcurrent]
  push_cast
  ring

/-- The raw threshold count at `p*c` telescopes to `c`. -/
theorem carryThresholdCount_primeMultiple
    {p c : ℕ} (hp0 : 0 < p) :
    carryThresholdCount p (p * c) = c := by
  unfold carryThresholdCount
  simp_rw [floorJump_primeMultiple hp0]
  let f : ℕ → ℤ := fun d => (((d * c) / p : ℕ) : ℤ)
  change (∑ d ∈ Finset.range p, (f (d + 1) - f d)) = c
  rw [Finset.sum_range_sub]
  simp only [f, zero_mul, Nat.zero_div, Nat.cast_zero, sub_zero]
  rw [Nat.mul_div_right c hp0]

/-- Every nonunit residue on the prime-square carrier has zero centered
collision response. -/
theorem collisionResponse_nonunit_eq_zero
    {p : ℕ} (hp : p.Prime) (a : ZMod (p ^ 2))
    (ha : ¬IsUnit a) : collisionResponse p a = 0 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hnotcop : ¬a.val.Coprime (p ^ 2) := by
    intro hcop
    have hunitCast : IsUnit (a.val : ZMod (p ^ 2)) :=
      (ZMod.isUnit_iff_coprime a.val (p ^ 2)).2 hcop
    apply ha
    simpa [ZMod.natCast_zmod_val] using hunitCast
  have hpdiv : p ∣ a.val := by
    by_contra hnotdiv
    apply hnotcop
    rw [Nat.coprime_pow_right_iff (by omega : 0 < 2)]
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact hnotdiv
  let c := a.val / p
  have hpc : p * c = a.val := Nat.mul_div_cancel' hpdiv
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2C : (((p ^ 2 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 hp.ne_zero)
  unfold collisionResponse
  rw [← hpc, carryThresholdCount_primeMultiple hp.pos]
  push_cast
  field_simp [hpC, hp2C]
  ring

/-- On a prime-square unit, the all-residue collision response is exactly the
class-centered carry statistic. -/
theorem collisionResponse_unit_eq_primeCarryCentered
    {p : ℕ} (hp : p.Prime) (a : (ZMod (p ^ 2))ˣ) :
    collisionResponse p a.val = primeCarryCentered hp a := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let q := a.val.val / p
  let s := a.val.val % p
  have hp0 : 0 < p := hp.pos
  have hA : a.val.val = p * q + s := by
    dsimp [q, s]
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.mod_add_div a.val.val p).symm
  have hcopA : a.val.val.Coprime (p ^ 2) := by
    have hu : IsUnit (a.val.val : ZMod (p ^ 2)) := by
      rw [ZMod.natCast_zmod_val]
      exact a.isUnit
    exact (ZMod.isUnit_iff_coprime a.val.val (p ^ 2)).mp hu
  have hspos : 0 < s := by
    dsimp [s]
    have hcopBase : a.val.val.Coprime p :=
      hcopA.of_dvd_right (dvd_pow_self p (by omega))
    exact Nat.pos_of_ne_zero (fun hs0 => by
      have hpdiv : p ∣ a.val.val := Nat.dvd_iff_mod_eq_zero.mpr hs0
      have hpone : p = 1 :=
        Nat.eq_one_of_dvd_coprimes hcopBase hpdiv dvd_rfl
      exact hp.ne_one hpone)
  have hslt : s < p := Nat.mod_lt _ hp0
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold collisionResponse primeCarryCentered
  rw [hA, fluctuationTable_eq_thresholdCount hp0 hslt]
  have hmod : (p * q + s) % p = s := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hslt]
  rw [hmod, Nat.cast_sub (Nat.le_of_lt hslt)]
  push_cast
  field_simp [hpC]
  ring

/-- The all-residue collision energy equals the concrete unit carry energy;
the omitted nonunits vanish pointwise. -/
theorem collisionEnergy_eq_primeCarryEnergy
    {p : ℕ} (hp : p.Prime) :
    collisionEnergy hp = primeCarryEnergy hp := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold collisionEnergy primeCarryEnergy
  calc
    (∑ a : ZMod (p ^ 2), ‖collisionResponse p a‖ ^ 2) =
        ∑ a ∈ (Finset.univ.filter fun a : ZMod (p ^ 2) => IsUnit a),
          ‖collisionResponse p a‖ ^ 2 := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro a _ha haFilter
            have hnonunit : ¬IsUnit a := by
              intro hunit
              exact haFilter (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hunit⟩)
            rw [collisionResponse_nonunit_eq_zero hp a hnonunit]
            simp
    _ = ∑ a : (ZMod (p ^ 2))ˣ, ‖collisionResponse p a.val‖ ^ 2 := by
          symm
          apply Finset.sum_bij (fun a _ => a.val)
          · intro a _ha
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩
          · intro a _ha b _hb hab
            exact Units.val_injective hab
          · intro x hx
            have hxunit : IsUnit x := (Finset.mem_filter.mp hx).2
            exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
          · intro a _ha
            rfl
    _ = ∑ a : (ZMod (p ^ 2))ˣ, ‖primeCarryCentered hp a‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [collisionResponse_unit_eq_primeCarryCentered hp]

/-- The reduced-ratio floor sum is precisely the off-diagonal part of the
continuous capacity. -/
theorem continuousCapacity_eq_floorEulerSum (p : ℕ) :
    continuousCapacity (p - 1) =
      ((p - 1 : ℕ) : ℝ) / 3 + (2 / 3 : ℝ) * floorEulerSum p := by
  classical
  unfold continuousCapacity floorEulerSum reducedHarmonicStar
  have hsum :
      (∑ ak ∈ reducedRatioPairs p,
          (((p - 1) / ak.1 : ℕ) : ℝ) /
            ((ak.2 : ℝ) * (ak.1 : ℝ))) =
        ∑ k ∈ Finset.Icc 2 (p - 1),
          (((p - 1) / k : ℕ) : ℝ) / (k : ℝ) *
            (∑ a ∈ (Finset.Ico 1 k).filter fun a => a.Coprime k,
              (a : ℝ)⁻¹) := by
    unfold reducedRatioPairs
    rw [Finset.sum_filter]
    rw [show
      (∑ ak ∈ (Finset.range p).product (Finset.range p),
        if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧
            ak.2.Coprime ak.1 then
          (((p - 1) / ak.1 : ℕ) : ℝ) /
            ((ak.2 : ℝ) * (ak.1 : ℝ)) else 0) =
        ∑ k ∈ Finset.range p, ∑ a ∈ Finset.range p,
          if 0 < k ∧ 0 < a ∧ a < k ∧ a.Coprime k then
            (((p - 1) / k : ℕ) : ℝ) /
              ((a : ℝ) * (k : ℝ)) else 0 by
        exact Finset.sum_product _ _ _]
    calc
      _ = ∑ k ∈ Finset.Icc 2 (p - 1), ∑ a ∈ Finset.range p,
          if 0 < k ∧ 0 < a ∧ a < k ∧ a.Coprime k then
            (((p - 1) / k : ℕ) : ℝ) /
              ((a : ℝ) * (k : ℝ)) else 0 := by
            symm
            apply Finset.sum_subset
            · intro k hk
              simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
              omega
            · intro k hkRange hkIcc
              have hklt : k < p := Finset.mem_range.mp hkRange
              have hkbad : k = 0 ∨ k = 1 := by
                simp only [Finset.mem_Icc, not_and_or, not_le] at hkIcc
                omega
              apply Finset.sum_eq_zero
              intro a ha
              rcases hkbad with rfl | rfl
              · simp
              · rw [if_neg]
                intro h
                omega
      _ = ∑ k ∈ Finset.Icc 2 (p - 1),
          (((p - 1) / k : ℕ) : ℝ) / (k : ℝ) *
            (∑ a ∈ (Finset.Ico 1 k).filter fun a => a.Coprime k,
              (a : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkRange : k < p := by
              have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
              have hkle : k ≤ p - 1 := (Finset.mem_Icc.mp hk).2
              have hpPos : 0 < p := by omega
              exact (Nat.lt_iff_le_pred hpPos).2 hkle
            rw [Finset.mul_sum]
            rw [Finset.sum_filter]
            have hsubset : Finset.Ico 1 k ⊆ Finset.range p := by
              intro a ha
              simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢
              omega
            let f : ℕ → ℝ := fun a =>
              if a.Coprime k then
                (((p - 1) / k : ℕ) : ℝ) / (k : ℝ) * (a : ℝ)⁻¹
              else 0
            calc
              (∑ a ∈ Finset.range p,
                  if 0 < k ∧ 0 < a ∧ a < k ∧ a.Coprime k then
                    (((p - 1) / k : ℕ) : ℝ) /
                      ((a : ℝ) * (k : ℝ)) else 0) =
                  ∑ a ∈ Finset.range p,
                    if a ∈ Finset.Ico 1 k then f a else 0 := by
                      apply Finset.sum_congr rfl
                      intro a _ha
                      by_cases haIco : a ∈ Finset.Ico 1 k
                      · have ha := Finset.mem_Ico.mp haIco
                        by_cases hcop : a.Coprime k
                        · rw [if_pos haIco]
                          rw [if_pos ⟨by omega, by omega, ha.2, hcop⟩]
                          change
                            (((p - 1) / k : ℕ) : ℝ) /
                                ((a : ℝ) * (k : ℝ)) =
                              if a.Coprime k then
                                (((p - 1) / k : ℕ) : ℝ) / (k : ℝ) *
                                  (a : ℝ)⁻¹
                              else 0
                          rw [if_pos hcop]
                          simp only [div_eq_mul_inv]
                          ring
                        · rw [if_pos haIco]
                          rw [if_neg (by
                            intro h
                            exact hcop h.2.2.2)]
                          simp [f, hcop]
                      · rw [if_neg haIco, if_neg]
                        intro h
                        apply haIco
                        exact Finset.mem_Ico.mpr ⟨h.2.1, h.2.2.1⟩
              _ = ∑ a ∈ Finset.Ico 1 k, f a := by
                    rw [← Finset.sum_filter]
                    have hfilter :
                        (Finset.range p).filter (fun a => a ∈ Finset.Ico 1 k) =
                          Finset.Ico 1 k := by
                      ext a
                      simp only [Finset.mem_filter]
                      constructor
                      · exact fun h => h.2
                      · intro ha
                        exact ⟨hsubset ha, ha⟩
                    rw [hfilter]
              _ = ∑ a ∈ Finset.Ico 1 k,
                    if a.Coprime k then
                      (((p - 1) / k : ℕ) : ℝ) / (k : ℝ) * (a : ℝ)⁻¹
                    else 0 := rfl
  rw [hsum]
  ring

/-- The reduced ratios with their admissible common scales are in bijection
with the strict upper triangle of the first window. -/
theorem scaledReducedRatios_card_eq_upperIndexPairs_card
    {p : ℕ} (hp2 : 2 ≤ p) :
    (scaledReducedRatios p).card = (upperIndexPairs p).card := by
  symm
  exact Finset.card_bij
    (fun ij _ => reducedTripleOfPair ij)
    (reducedTripleOfPair_mem hp2)
    (fun ij hij uv huv h =>
      reducedTripleOfPair_injective_on hp2 hij huv h)
    (reducedTripleOfPair_surjective_on hp2)

/-- The strict upper triangle on `p-1` points has the expected triangular
cardinality. -/
theorem upperIndexPairs_card (p : ℕ) :
    (upperIndexPairs p).card = (p - 1) * (p - 2) / 2 := by
  classical
  unfold upperIndexPairs
  rw [Finset.card_filter]
  rw [show
    (∑ ij ∈ (Finset.univ : Finset (FirstWindowIndex p)).product Finset.univ,
        if ij.1 < ij.2 then 1 else 0) =
      ∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        if i < j then 1 else 0 by
          exact Finset.sum_product _ _ _]
  have hinner (i : FirstWindowIndex p) :
      (∑ j : FirstWindowIndex p, if i < j then 1 else 0) =
        p - 2 - i.val := by
    rw [← Finset.card_filter]
    have heq :
        (Finset.univ.filter fun j : FirstWindowIndex p => i < j) =
          Finset.Ioi i := by
      ext j
      simp
    rw [heq]
    rw [Fin.card_Ioi]
    change (p - 1) - 1 - i.val = p - 2 - i.val
    omega
  simp_rw [hinner]
  rw [show p - 2 = (p - 1) - 1 by omega]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_reflect (fun i : ℕ => i) (p - 1),
    Finset.sum_range_id]

/-- Summing the scale multiplicity over primitive ratios counts every strict
pair in the first window exactly once. -/
theorem scaleMultiplicityMass_eq
    {p : ℕ} (hp2 : 2 ≤ p) :
    ∑ ak ∈ reducedRatioPairs p, (p - 1) / ak.1 =
      (p - 1) * (p - 2) / 2 := by
  classical
  have hcardFloor :
      (scaledReducedRatios p).card =
        ∑ ak ∈ reducedRatioPairs p, (p - 1) / ak.1 := by
    unfold scaledReducedRatios reducedRatioPairs
    rw [Finset.card_filter, Finset.sum_filter]
    rw [show
      (∑ r ∈ (Finset.range p).product
          ((Finset.range p).product (Finset.range p)),
        if 0 < r.1 ∧ 0 < r.2.1 ∧ r.2.1 < r.1 ∧
            r.2.1.Coprime r.1 ∧ 0 < r.2.2 ∧ r.2.2 * r.1 < p
          then 1 else 0) =
        ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
          ∑ t ∈ Finset.range p,
            if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
                0 < t ∧ t * a < p then 1 else 0 by
      calc
        _ = ∑ a ∈ Finset.range p,
            ∑ kt ∈ (Finset.range p).product (Finset.range p),
              if 0 < a ∧ 0 < kt.1 ∧ kt.1 < a ∧ kt.1.Coprime a ∧
                  0 < kt.2 ∧ kt.2 * a < p then 1 else 0 :=
            Finset.sum_product _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_product _ _ _]
    rw [show
      (∑ ak ∈ (Finset.range p).product (Finset.range p),
        if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧
            ak.2.Coprime ak.1 then (p - 1) / ak.1 else 0) =
        ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
            (p - 1) / a else 0 by
      exact Finset.sum_product _ _ _]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hpair : 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a
    · rw [if_pos hpair]
      have hpred (t : ℕ) :
          (0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p) ↔ (0 < t ∧ t * a < p) := by
        tauto
      simp_rw [hpred]
      rw [← Finset.card_filter]
      change (admissibleScales p a).card = _
      exact admissibleScales_card hpair.1
    · rw [if_neg hpair]
      apply Finset.sum_eq_zero
      intro t _ht
      rw [if_neg]
      intro h
      exact hpair ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  rw [← hcardFloor, scaledReducedRatios_card_eq_upperIndexPairs_card hp2,
    upperIndexPairs_card]

/-- The elementary part of three-term reciprocity is exactly the manuscript's
`X_p` correction and triangular constant term. -/
theorem offDiagonalElementaryRemainder_eq
    {p : ℕ} (hp : p.Prime) :
    offDiagonalElementaryRemainder p =
      (((2 / (3 * (p : ℝ) ^ 2) : ℝ) * elementaryRatioReservoir p -
          (((p - 1) * (p - 2) : ℕ) : ℝ) : ℝ) : ℂ) := by
  classical
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpoint : ∀ ak ∈ reducedRatioPairs p,
      8 * ((((p - 1) / ak.1 : ℕ) : ℂ) *
        ((-1 / 4 + (1 / 12) *
          ((ak.2 : ℚ) / ((ak.1 : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
            (ak.1 : ℚ) /
              (((p ^ 2 : ℕ) : ℚ) * (ak.2 : ℚ))) : ℚ) : ℂ)) =
        (((2 / (3 * (p : ℝ) ^ 2) : ℝ) *
            ((((p - 1) / ak.1 : ℕ) : ℝ) *
              ((ak.1 : ℝ) / (ak.2 : ℝ) +
                (ak.2 : ℝ) / (ak.1 : ℝ))) -
          2 * (((p - 1) / ak.1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro ak hak
    have h := hak
    simp [reducedRatioPairs] at h
    have ha : (ak.1 : ℝ) ≠ 0 := by exact_mod_cast h.2.1.ne'
    have hk : (ak.2 : ℝ) ≠ 0 := by exact_mod_cast h.2.2.1.ne'
    push_cast
    field_simp [hpR, ha, hk]
    ring
  unfold offDiagonalElementaryRemainder elementaryRatioReservoir
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hpoint]
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hmass := scaleMultiplicityMass_eq hp.two_le
  have hmassR :
      (∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℝ)) =
        (((p - 1) * (p - 2) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hmass
  have htri :
      (2 : ℝ) * (((p - 1) * (p - 2) / 2 : ℕ) : ℝ) =
        (((p - 1) * (p - 2) : ℕ) : ℝ) := by
    have heven : Even ((p - 1) * (p - 2)) := by
      rcases Nat.even_or_odd (p - 1) with h | h
      · exact h.mul_right (p - 2)
      · have hpred : Even ((p - 1) - 1) := by
          rw [Nat.even_sub (Nat.le_sub_one_of_lt hp.one_lt)]
          constructor
          · intro he
            exact (Nat.not_even_iff_odd.mpr h he).elim
          · intro he
            norm_num at he
        have hpred' : Even (p - 2) := by
          simpa [Nat.sub_sub] using hpred
        exact hpred'.mul_left (p - 1)
    have hnat := Nat.div_two_mul_two_of_even heven
    have hnat' :
        2 * (((p - 1) * (p - 2)) / 2) =
          (p - 1) * (p - 2) := by
      simpa [Nat.mul_comm] using hnat
    exact_mod_cast hnat'
  have htwomass :
      (2 : ℝ) * (∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℝ)) =
        (((p - 1) * (p - 2) : ℕ) : ℝ) := by
    rw [hmassR]
    exact htri
  have htwomass' :
      (2 : ℝ) * (∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℝ)) =
        ((p - 1 : ℕ) : ℝ) * ((p - 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul] using htwomass
  have htwomassC := congrArg (fun x : ℝ => (x : ℂ)) htwomass'
  push_cast at htwomassC
  apply sub_right_inj.mpr
  exact htwomassC

/-- The concrete prime carry energy in the exact diagonal, common-pole,
elementary-reservoir, and lower-modulus coordinates. -/
theorem primeCarryEnergy_exact_decomposition
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      (((p - 1 : ℕ) : ℝ) * ((p : ℝ) ^ 2 - 1) *
          ((p : ℝ) ^ 2 - 2) / (3 * (p : ℝ) ^ 2)) +
      (2 / 3 : ℝ) * (p : ℝ) ^ 2 * floorEulerSum p +
      (2 / (3 * (p : ℝ) ^ 2) : ℝ) * elementaryRatioReservoir p -
      (((p - 1) * (p - 2) : ℕ) : ℝ) +
      lowerModulusReservoir p := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcomplex :
      (primeCarryEnergy hp : ℂ) =
        (((((p - 1 : ℕ) : ℝ) * ((p : ℝ) ^ 2 - 1) *
            ((p : ℝ) ^ 2 - 2) /
              (3 * (p : ℝ) ^ 2)) : ℝ) : ℂ) +
          (((2 / 3 : ℝ) * (p : ℝ) ^ 2 * floorEulerSum p : ℝ) : ℂ) +
          (((2 / (3 * (p : ℝ) ^ 2) : ℝ) *
              elementaryRatioReservoir p -
              (((p - 1) * (p - 2) : ℕ) : ℝ) : ℝ) : ℂ) +
          offDiagonalModulusK p := by
    calc
      (primeCarryEnergy hp : ℂ) = dedekindCollisionEnergy hp :=
        primeCarryEnergy_eq_dedekindCollisionEnergy hp hpodd
      _ = 4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp +
          4 * primeSquareCollisionOffDiagonal hp :=
        dedekindCollisionEnergy_poleSplit hp
      _ = ((p - 1 : ℕ) : ℂ) * (((p ^ 2 : ℕ) : ℂ) - 1) *
            (((p ^ 2 : ℕ) : ℂ) - 2) /
              (3 * ((p ^ 2 : ℕ) : ℂ)) +
          (offDiagonalMain p + offDiagonalElementaryRemainder p +
            offDiagonalModulusA p + offDiagonalModulusK p) := by
              rw [dedekindCollisionEnergy_diagonal_closed hp,
                four_mul_offDiagonal_eq_fourWay hp]
      _ = _ := by
        rw [offDiagonalModulusA_eq_zero hp,
          offDiagonalMain_eq_floorEulerSum,
          offDiagonalElementaryRemainder_eq hp]
        push_cast
        ring
  have hre := congrArg Complex.re hcomplex
  unfold lowerModulusReservoir
  simp only [Complex.ofReal_re, Complex.add_re] at hre
  rw [hre]
  ring

/-- The manuscript's exact Rademacher-reservoir bridge, now proved directly
for the concrete capacity, carry energy, elementary ratio sum, and surviving
lower-modulus reservoir. -/
theorem exact_sampling_reservoir_bridge
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    samplingDefect hp =
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 -
        (2 / (3 * (p : ℝ) ^ 4) : ℝ) *
          (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p) -
        lowerModulusReservoir p / (p : ℝ) ^ 2 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [samplingDefect, continuousCapacity_eq_floorEulerSum,
    collisionEnergy_eq_primeCarryEnergy hp,
    primeCarryEnergy_exact_decomposition hp hpodd]
  push_cast
  rw [Nat.cast_sub hp.one_le, Nat.cast_sub hp.two_le]
  field_simp [hpR]
  ring

/-- An explicit unconditional sampling bound.  It is obtained independently
from the exact continuous pole estimate and the already proved concrete
cubic-energy estimate, so no asymptotic big-O premise is accepted. -/
theorem abs_samplingDefect_le_harmonic_sq
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |samplingDefect hp| ≤ 30 * (harmonic p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hHnonneg : (0 : ℝ) ≤ (harmonic p : ℝ) := by
    have hq : (0 : ℚ) ≤ harmonic p := by
      unfold harmonic
      positivity
    exact_mod_cast hq
  have hHone : (1 : ℝ) ≤ (harmonic p : ℝ) := by
    calc
      (1 : ℝ) = (harmonic 1 : ℝ) := by norm_num [harmonic]
      _ ≤ (harmonic p : ℝ) :=
        NField.Alignment.DedekindFourierMoment.harmonic_cast_mono
          hp.one_le
  have hcapacity :
      |continuousCapacity (p - 1) - (p : ℝ)| ≤
        6 * (harmonic p : ℝ) ^ 2 := by
    rw [continuousCapacity_eq_floorEulerSum]
    have hp2 := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hfloor := abs_floorEulerSum_sub_prime_le hp3
    rw [show
      ((p - 1 : ℕ) : ℝ) / 3 + (2 / 3 : ℝ) * floorEulerSum p -
          (p : ℝ) =
        -(1 / 3 : ℝ) + (2 / 3 : ℝ) *
          (floorEulerSum p - (p : ℝ)) by
      rw [Nat.cast_sub hp.one_le]
      ring]
    calc
      |-(1 / 3 : ℝ) + (2 / 3 : ℝ) *
          (floorEulerSum p - (p : ℝ))| ≤
          (1 / 3 : ℝ) + (2 / 3 : ℝ) *
            |floorEulerSum p - (p : ℝ)| := by
              calc
                _ ≤ |-(1 / 3 : ℝ)| +
                    |(2 / 3 : ℝ) *
                      (floorEulerSum p - (p : ℝ))| := abs_add_le _ _
                _ = _ := by norm_num [abs_mul]
      _ ≤ (1 / 3 : ℝ) + (2 / 3 : ℝ) *
          (8 * (harmonic p : ℝ) ^ 2) := by
            gcongr
      _ ≤ 6 * (harmonic p : ℝ) ^ 2 := by
            nlinarith [sq_nonneg ((harmonic p : ℝ) - 1)]
  have henergy := primeCarryEnergy_cubic_bound hp hpodd
  have henergyNormalized :
      |collisionEnergy hp / (p : ℝ) ^ 2 - (p : ℝ)| ≤
        24 * (harmonic p : ℝ) ^ 2 := by
    rw [collisionEnergy_eq_primeCarryEnergy hp]
    have hpSq : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hpR
    rw [show
      primeCarryEnergy hp / (p : ℝ) ^ 2 - (p : ℝ) =
        (primeCarryEnergy hp - (p : ℝ) ^ 3) / (p : ℝ) ^ 2 by
      field_simp [hpR.ne']]
    rw [abs_div, abs_of_pos hpSq]
    apply (div_le_iff₀ hpSq).2
    calc
      |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
          24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := henergy
      _ = 24 * (harmonic p : ℝ) ^ 2 * (p : ℝ) ^ 2 := by ring
  unfold samplingDefect
  rw [show
    continuousCapacity (p - 1) - collisionEnergy hp / (p : ℝ) ^ 2 =
      (continuousCapacity (p - 1) - (p : ℝ)) -
        (collisionEnergy hp / (p : ℝ) ^ 2 - (p : ℝ)) by ring]
  calc
    |(continuousCapacity (p - 1) - (p : ℝ)) -
        (collisionEnergy hp / (p : ℝ) ^ 2 - (p : ℝ))| ≤
      |continuousCapacity (p - 1) - (p : ℝ)| +
        |collisionEnergy hp / (p : ℝ) ^ 2 - (p : ℝ)| := abs_sub _ _
    _ ≤ 6 * (harmonic p : ℝ) ^ 2 +
        24 * (harmonic p : ℝ) ^ 2 := add_le_add hcapacity henergyNormalized
    _ = 30 * (harmonic p : ℝ) ^ 2 := by ring

/-- The same unconditional estimate in an explicit logarithmic envelope. -/
theorem abs_samplingDefect_le_log_sq
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |samplingDefect hp| ≤
      30 * (1 + Real.log (p : ℝ)) ^ 2 := by
  have h := abs_samplingDefect_le_harmonic_sq hp hpodd
  have hH := harmonic_le_one_add_log p
  have hHnonneg : (0 : ℝ) ≤ (harmonic p : ℝ) := by
    have hq : (0 : ℚ) ≤ harmonic p := by
      unfold harmonic
      positivity
    exact_mod_cast hq
  have hlognonneg : (0 : ℝ) ≤ 1 + Real.log (p : ℝ) := by
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    positivity
  calc
    |samplingDefect hp| ≤ 30 * (harmonic p : ℝ) ^ 2 := h
    _ ≤ 30 * (1 + Real.log (p : ℝ)) ^ 2 := by gcongr

end NField.Alignment.ExactSamplingReservoirBridge
