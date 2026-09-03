/-
Author: Alexander S. Petty
-/

import NField.Alignment.CoprimeEulerMass
import NField.Alignment.DedekindAbelRemainder
import NField.Alignment.PrimeSquareReducedRatio
import NField.Alignment.RademacherThreeTerm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cubic energy at a prime-square carry boundary

This file assembles the exact reduced-ratio pole split, three-modulus
reciprocity, Euler mass, first Dedekind moment, and finite Abel estimate.  Its
terminal theorem is the unconditional cubic law for the concrete prime carry
energy.
-/

namespace NField.Alignment.PrimeSquareCubicEnergy

open scoped BigOperators ZMod
open NField.Alignment.CoprimeEulerMass
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindFourierMoment
open NField.Alignment.DedekindReciprocity
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareReducedRatio
open NField.Alignment.PrimeSquareSawtoothEnergy
open NField.Alignment.RademacherThreeTerm

/-- The exact rational pole and constant contribution in one reduced ratio. -/
def reducedRatioElementaryTerm (p a k : ℕ) : ℚ :=
  -1 / 4 + (1 / 12) *
    (((p ^ 2 : ℕ) : ℚ) / ((k : ℚ) * (a : ℚ)) +
      (k : ℚ) / ((a : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
      (a : ℚ) / (((p ^ 2 : ℕ) : ℚ) * (k : ℚ)))

/-- Pointwise Rademacher reduction for every primitive ratio in the prime
window. -/
theorem reducedRatio_dedekindSum_eq_threeTerm
    {p a k : ℕ} [NeZero (p ^ 2)] [NeZero a] [NeZero k]
    (hp : p.Prime)
    (ha : 0 < a) (hk : 0 < k) (hka : k < a) (hap : a < p)
    (hcop : k.Coprime a) :
    dedekindSum ((smallNatUnit hp k)⁻¹ * smallNatUnit hp a) =
      ((reducedRatioElementaryTerm p a k : ℚ) : ℂ) -
        coefficientDedekindTerm a (p ^ 2)
          hcop.symm (smallNatUnit_coprime hp hk (hka.trans hap)).symm -
        coefficientDedekindTerm (p ^ 2) k
          (smallNatUnit_coprime hp ha hap).symm hcop := by
  have hkP := smallNatUnit_coprime hp hk (hka.trans hap)
  have haP := smallNatUnit_coprime hp ha hap
  have hthree := coefficientDedekindTerm_threeTerm
    (a := p ^ 2) (b := k) (c := a)
    (pow_pos hp.pos 2) hk ha hkP.symm haP.symm hcop
  have htarget :
      coefficientDedekindTerm k a hkP haP =
        dedekindSum ((smallNatUnit hp k)⁻¹ * smallNatUnit hp a) := by
    rw [arithmeticCoefficientDedekindTerm_eq_ratio]
    rw [smallNatUnit_eq_unitOfCoprime hp hkP,
      smallNatUnit_eq_unitOfCoprime hp haP]
  rw [← htarget]
  unfold reducedRatioElementaryTerm
  push_cast at hthree ⊢
  linear_combination hthree

/-! ## Exact four-way decomposition -/

/-- The large pole supplied by the `p²/(12ka)` reciprocity term. -/
noncomputable def offDiagonalMain (p : ℕ) : ℂ :=
  8 * ∑ ak ∈ reducedRatioPairs p,
    (((p - 1) / ak.1 : ℕ) : ℂ) *
      ((((p ^ 2 : ℕ) : ℚ) /
        (12 * (ak.2 : ℚ) * (ak.1 : ℚ)) : ℚ) : ℂ)

/-- The constant and the two reciprocal-size elementary terms. -/
noncomputable def offDiagonalElementaryRemainder (p : ℕ) : ℂ :=
  8 * ∑ ak ∈ reducedRatioPairs p,
    (((p - 1) / ak.1 : ℕ) : ℂ) *
      ((-1 / 4 + (1 / 12) *
        ((ak.2 : ℚ) / ((ak.1 : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
          (ak.1 : ℚ) /
            (((p ^ 2 : ℕ) : ℚ) * (ak.2 : ℚ))) : ℚ) : ℂ)

/-- The small-modulus term whose modulus is the larger reduced coordinate. -/
noncomputable def offDiagonalModulusA (p : ℕ) : ℂ :=
  -8 * ∑ ak ∈ reducedRatioPairs p,
    (((p - 1) / ak.1 : ℕ) : ℂ) *
      ((arithmeticCoefficientDedekindTerm (p ^ 2) ak.2 ak.1 : ℚ) : ℂ)

/-- The surviving small-modulus term whose modulus is the smaller reduced
coordinate. -/
noncomputable def offDiagonalModulusK (p : ℕ) : ℂ :=
  -8 * ∑ ak ∈ reducedRatioPairs p,
    (((p - 1) / ak.1 : ℕ) : ℂ) *
      ((arithmeticCoefficientDedekindTerm ak.1 (p ^ 2) ak.2 : ℚ) : ℂ)

/-- Exact finite four-way decomposition of the prime-square off-diagonal
energy. -/
theorem four_mul_offDiagonal_eq_fourWay
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    4 * primeSquareCollisionOffDiagonal hp =
      offDiagonalMain p + offDiagonalElementaryRemainder p +
        offDiagonalModulusA p + offDiagonalModulusK p := by
  rw [four_mul_primeSquareCollisionOffDiagonal_eq_reducedRatios hp]
  unfold offDiagonalMain offDiagonalElementaryRemainder
    offDiagonalModulusA offDiagonalModulusK
  let W := fun ak : ℕ × ℕ => (((p - 1) / ak.1 : ℕ) : ℂ)
  let D := fun ak : ℕ × ℕ =>
    dedekindSum ((smallNatUnit hp ak.2)⁻¹ * smallNatUnit hp ak.1)
  let M := fun ak : ℕ × ℕ =>
    ((((p ^ 2 : ℕ) : ℚ) /
      (12 * (ak.2 : ℚ) * (ak.1 : ℚ)) : ℚ) : ℂ)
  let R := fun ak : ℕ × ℕ =>
    ((-1 / 4 + (1 / 12) *
      ((ak.2 : ℚ) / ((ak.1 : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
        (ak.1 : ℚ) /
          (((p ^ 2 : ℕ) : ℚ) * (ak.2 : ℚ))) : ℚ) : ℂ)
  let A := fun ak : ℕ × ℕ =>
    ((arithmeticCoefficientDedekindTerm (p ^ 2) ak.2 ak.1 : ℚ) : ℂ)
  let K := fun ak : ℕ × ℕ =>
    ((arithmeticCoefficientDedekindTerm ak.1 (p ^ 2) ak.2 : ℚ) : ℂ)
  change 8 * ∑ ak ∈ reducedRatioPairs p, W ak * D ak =
    8 * ∑ ak ∈ reducedRatioPairs p, W ak * M ak +
      8 * ∑ ak ∈ reducedRatioPairs p, W ak * R ak +
      -8 * ∑ ak ∈ reducedRatioPairs p, W ak * A ak +
      -8 * ∑ ak ∈ reducedRatioPairs p, W ak * K ak
  have hpoint : ∀ ak ∈ reducedRatioPairs p,
      D ak = M ak + R ak - A ak - K ak := by
    intro ak hak
    have h := hak
    simp [reducedRatioPairs] at h
    rcases h with ⟨⟨haP, _hkP⟩, ha, hk, hka, hcop⟩
    letI : NeZero ak.1 := ⟨ha.ne'⟩
    letI : NeZero ak.2 := ⟨hk.ne'⟩
    have hred := reducedRatio_dedekindSum_eq_threeTerm hp
      ha hk hka haP hcop
    unfold coefficientDedekindTerm at hred
    unfold D A K
    rw [hred]
    unfold M R reducedRatioElementaryTerm
    push_cast
    ring
  have hsplit :
      (∑ ak ∈ reducedRatioPairs p,
        W ak * (M ak + R ak - A ak - K ak)) =
        (∑ ak ∈ reducedRatioPairs p, W ak * M ak) +
          (∑ ak ∈ reducedRatioPairs p, W ak * R ak) -
          (∑ ak ∈ reducedRatioPairs p, W ak * A ak) -
          (∑ ak ∈ reducedRatioPairs p, W ak * K ak) := by
    calc
      _ = ∑ ak ∈ reducedRatioPairs p,
          (W ak * M ak + W ak * R ak - W ak * A ak - W ak * K ak) := by
            apply Finset.sum_congr rfl
            intro ak _hak
            ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
  calc
    8 * ∑ ak ∈ reducedRatioPairs p, W ak * D ak =
        8 * ∑ ak ∈ reducedRatioPairs p,
          W ak * (M ak + R ak - A ak - K ak) := by
            congr 1
            apply Finset.sum_congr rfl
            intro ak hak
            rw [hpoint ak hak]
    _ = _ := by
      rw [hsplit]
      ring

/-! ## Cancellation at the larger reduced modulus -/

/-- Extending the coefficient term by zero on nonunits gives exactly the
periodic Dedekind residue sequence. -/
theorem coefficientDedekindTerm_filter_eq_residueSequence
    {m c x : ℕ} [NeZero m] (_hm : 2 ≤ m) (hcm : c.Coprime m) :
    (if _hxm : x.Coprime m then
        ((arithmeticCoefficientDedekindTerm c x m : ℚ) : ℂ)
      else 0) =
      residueDedekindSequence (ZMod.unitOfCoprime c hcm) x := by
  classical
  by_cases hxm : x.Coprime m
  · rw [dif_pos hxm]
    have hxunit : IsUnit (x : ZMod m) :=
      (ZMod.isUnit_iff_coprime x m).2 hxm
    unfold residueDedekindSequence
    rw [dif_pos hxunit]
    have hchosen : hxunit.unit = ZMod.unitOfCoprime x hxm := by
      apply Units.val_injective
      rw [hxunit.unit_spec, ZMod.coe_unitOfCoprime]
    rw [hchosen]
    rw [show ((arithmeticCoefficientDedekindTerm c x m : ℚ) : ℂ) =
        coefficientDedekindTerm c x hcm hxm by rfl,
      arithmeticCoefficientDedekindTerm_eq_ratio]
    rw [← dedekindSum_ratio_swap
      (ZMod.unitOfCoprime c hcm) (ZMod.unitOfCoprime x hxm)]
    congr 1
    exact mul_comm _ _
  · rw [dif_neg hxm]
    have hxnonunit : ¬IsUnit (x : ZMod m) := by
      simpa [ZMod.isUnit_iff_coprime] using hxm
    unfold residueDedekindSequence
    rw [dif_neg hxnonunit]

/-- The filtered coefficient terms over one complete reduced residue system
cancel exactly. -/
theorem sum_coefficientDedekindTerm_units_zero
    {m c : ℕ} [NeZero m] (hm : 2 ≤ m) (hcm : c.Coprime m) :
    (∑ x ∈ Finset.range m,
      if _hxm : x.Coprime m then
        ((arithmeticCoefficientDedekindTerm c x m : ℚ) : ℂ)
      else 0) = 0 := by
  simp_rw [coefficientDedekindTerm_filter_eq_residueSequence hm hcm]
  exact residueDedekindSequence_sum_period_of_two hm
    (ZMod.unitOfCoprime c hcm)

/-- The larger-modulus Rademacher remainder cancels exactly, one complete
reduced residue system at a time. -/
theorem offDiagonalModulusA_eq_zero
    {p : ℕ} (hp : p.Prime) : offDiagonalModulusA p = 0 := by
  classical
  unfold offDiagonalModulusA reducedRatioPairs
  rw [Finset.sum_filter]
  have houter :
      (∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℂ) *
            ((arithmeticCoefficientDedekindTerm (p ^ 2) k a : ℚ) : ℂ)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a haP
    have hap : a < p := Finset.mem_range.mp haP
    by_cases ha : 2 ≤ a
    · letI : NeZero a := ⟨(by omega : a ≠ 0)⟩
      have hPa : (p ^ 2).Coprime a :=
        (smallNatUnit_coprime hp (by omega : 0 < a) hap).symm
      have hsmall : Finset.range a ⊆ Finset.range p :=
        Finset.range_mono (Nat.le_of_lt hap)
      let G := fun k : ℕ =>
        if hka : k.Coprime a then
          ((arithmeticCoefficientDedekindTerm (p ^ 2) k a : ℚ) : ℂ)
        else 0
      let F := fun k : ℕ =>
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℂ) *
            ((arithmeticCoefficientDedekindTerm (p ^ 2) k a : ℚ) : ℂ)
        else 0
      have hrestrict :
          (∑ k ∈ Finset.range p, F k) =
          ∑ k ∈ Finset.range a,
            (((p - 1) / a : ℕ) : ℂ) * G k := by
        calc
          (∑ k ∈ Finset.range p, F k) =
              ∑ k ∈ Finset.range a, F k := by
                symm
                apply Finset.sum_subset hsmall
                intro k _hkp hkaRange
                have hak : a ≤ k := by
                  simpa only [Finset.mem_range, not_lt] using hkaRange
                unfold F
                rw [if_neg]
                intro h
                omega
          _ = ∑ k ∈ Finset.range a,
              (((p - 1) / a : ℕ) : ℂ) * G k := by
                apply Finset.sum_congr rfl
                intro k hkRange
                have hka : k < a := Finset.mem_range.mp hkRange
                unfold F G
                by_cases hcop : k.Coprime a
                · have hkpos : 0 < k := by
                    by_contra hkzero
                    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkzero
                    subst k
                    simp at hcop
                    omega
                  rw [if_pos ⟨by omega, hkpos, hka, hcop⟩, dif_pos hcop]
                · rw [if_neg (by
                    intro h
                    exact hcop h.2.2.2), dif_neg hcop, mul_zero]
      change (∑ k ∈ Finset.range p, F k) = 0
      rw [hrestrict, ← Finset.mul_sum]
      have hzero : (∑ k ∈ Finset.range a, G k) = 0 := by
        unfold G
        exact sum_coefficientDedekindTerm_units_zero ha hPa
      rw [hzero, mul_zero]
    · apply Finset.sum_eq_zero
      intro k hkP
      rw [if_neg]
      intro h
      omega
  have hproduct :
      (∑ ak ∈ (Finset.range p).product (Finset.range p),
        if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧ ak.2.Coprime ak.1 then
          (((p - 1) / ak.1 : ℕ) : ℂ) *
            ((arithmeticCoefficientDedekindTerm
              (p ^ 2) ak.2 ak.1 : ℚ) : ℂ)
        else 0) = 0 := by
    calc
      _ = ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
            (((p - 1) / a : ℕ) : ℂ) *
              ((arithmeticCoefficientDedekindTerm (p ^ 2) k a : ℚ) : ℂ)
          else 0 := Finset.sum_product _ _ _
      _ = 0 := houter
  rw [hproduct, mul_zero]

/-! ## Bound at the smaller reduced modulus -/

theorem arithmeticCoefficientDedekindTerm_comm (x y m : ℕ) :
    arithmeticCoefficientDedekindTerm x y m =
      arithmeticCoefficientDedekindTerm y x m := by
  unfold arithmeticCoefficientDedekindTerm
  apply Finset.sum_congr rfl
  intro t _ht
  ring

theorem arithmeticCoefficientDedekindTerm_mod_one (x y : ℕ) :
    arithmeticCoefficientDedekindTerm x y 1 = 0 := by
  simp [arithmeticCoefficientDedekindTerm, rationalSawtooth]

/-- One fixed smaller-modulus slice of the surviving remainder. -/
noncomputable def modulusKSlice (p k : ℕ) : ℂ :=
  if hk0 : k = 0 then 0 else by
    letI : NeZero k := ⟨hk0⟩
    exact if h : 2 ≤ k ∧ (p ^ 2).Coprime k then
      ∑ a ∈ Finset.Ico (k + 1) p,
        (((p - 1) / a : ℕ) : ℝ) •
          residueDedekindSequence (ZMod.unitOfCoprime (p ^ 2) h.2) a
    else 0

/-- Every smaller-modulus slice is uniformly bounded by `p H_p²`. -/
theorem norm_modulusKSlice_le
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    ‖modulusKSlice p k‖ ≤
      (p : ℝ) * (harmonic p : ℝ) ^ 2 := by
  have hPk : (p ^ 2).Coprime k :=
    (smallNatUnit_coprime hp (by omega : 0 < k) hkp).symm
  letI : NeZero k := ⟨(by omega : k ≠ 0)⟩
  rw [modulusKSlice, dif_neg (by omega : k ≠ 0), dif_pos ⟨hk, hPk⟩]
  have habel := norm_floorWeighted_residueDedekindSequence_le_of_two
    hk hkp (ZMod.unitOfCoprime (p ^ 2) hPk)
  have hmoment := dedekindFirstMoment_le (by omega : 0 < k)
  have hfloorNat : ((p - 1) / (k + 1)) * k ≤ p := by
    calc
      ((p - 1) / (k + 1)) * k ≤
          ((p - 1) / (k + 1)) * (k + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ k)
      _ ≤ p - 1 := Nat.div_mul_le_self _ _
      _ ≤ p := Nat.sub_le _ _
  have hfloor :
      ((((p - 1) / (k + 1) : ℕ) : ℝ) * (k : ℝ)) ≤ (p : ℝ) := by
    exact_mod_cast hfloorNat
  have hharmonic := harmonic_cast_mono (Nat.le_of_lt hkp)
  have hHkQ : (0 : ℚ) ≤ harmonic k := by
    unfold harmonic
    positivity
  have hHk : (0 : ℝ) ≤ (harmonic k : ℝ) := by exact_mod_cast hHkQ
  have hHpQ : (0 : ℚ) ≤ harmonic p := by
    unfold harmonic
    positivity
  have hHp : (0 : ℝ) ≤ (harmonic p : ℝ) := by exact_mod_cast hHpQ
  calc
    ‖∑ a ∈ Finset.Ico (k + 1) p,
        (((p - 1) / a : ℕ) : ℝ) •
          residueDedekindSequence (ZMod.unitOfCoprime (p ^ 2) hPk) a‖ ≤
        4 * (((p - 1) / (k + 1) : ℕ) : ℝ) *
          dedekindFirstMoment k := habel
    _ ≤ 4 * (((p - 1) / (k + 1) : ℕ) : ℝ) *
          ((k : ℝ) * (harmonic k : ℝ) ^ 2 / 4) := by
            gcongr
    _ = ((((p - 1) / (k + 1) : ℕ) : ℝ) * (k : ℝ)) *
          (harmonic k : ℝ) ^ 2 := by ring
    _ ≤ (p : ℝ) * (harmonic p : ℝ) ^ 2 := by
          gcongr

/-- The pair-indexed smaller-modulus remainder is exactly the sum of its
fixed-modulus Abel slices. -/
theorem offDiagonalModulusK_eq_slices
    {p : ℕ} (hp : p.Prime) :
    offDiagonalModulusK p =
      -8 * ∑ k ∈ Finset.range p, modulusKSlice p k := by
  classical
  unfold offDiagonalModulusK reducedRatioPairs
  rw [Finset.sum_filter]
  have hproduct :
      (∑ ak ∈ (Finset.range p).product (Finset.range p),
        if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧ ak.2.Coprime ak.1 then
          (((p - 1) / ak.1 : ℕ) : ℂ) *
            ((arithmeticCoefficientDedekindTerm
              ak.1 (p ^ 2) ak.2 : ℚ) : ℂ)
        else 0) =
      ∑ k ∈ Finset.range p, modulusKSlice p k := by
    calc
      _ = ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
            (((p - 1) / a : ℕ) : ℂ) *
              ((arithmeticCoefficientDedekindTerm a (p ^ 2) k : ℚ) : ℂ)
          else 0 := Finset.sum_product _ _ _
      _ = ∑ k ∈ Finset.range p, ∑ a ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
            (((p - 1) / a : ℕ) : ℂ) *
              ((arithmeticCoefficientDedekindTerm a (p ^ 2) k : ℚ) : ℂ)
          else 0 := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hkP
        have hkp : k < p := Finset.mem_range.mp hkP
        by_cases hk : 2 ≤ k
        · letI : NeZero k := ⟨(by omega : k ≠ 0)⟩
          have hPk : (p ^ 2).Coprime k :=
            (smallNatUnit_coprime hp (by omega : 0 < k) hkp).symm
          let β := ZMod.unitOfCoprime (p ^ 2) hPk
          let F := fun a : ℕ =>
            if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
              (((p - 1) / a : ℕ) : ℂ) *
                ((arithmeticCoefficientDedekindTerm a (p ^ 2) k : ℚ) : ℂ)
            else 0
          have hsmall : Finset.Ico (k + 1) p ⊆ Finset.range p := by
            intro a ha
            simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢
            exact ha.2
          have hrestrict :
              (∑ a ∈ Finset.range p, F a) =
                ∑ a ∈ Finset.Ico (k + 1) p,
                  (((p - 1) / a : ℕ) : ℝ) •
                    residueDedekindSequence β a := by
            calc
              (∑ a ∈ Finset.range p, F a) =
                  ∑ a ∈ Finset.Ico (k + 1) p, F a := by
                    symm
                    apply Finset.sum_subset hsmall
                    intro a haPmem haIco
                    have haP' : a < p := Finset.mem_range.mp haPmem
                    have haout : a ≤ k := by
                      simp only [Finset.mem_Ico, not_and_or, not_le,
                        not_lt] at haIco
                      omega
                    unfold F
                    rw [if_neg]
                    intro h
                    omega
              _ = ∑ a ∈ Finset.Ico (k + 1) p,
                  (((p - 1) / a : ℕ) : ℝ) •
                    residueDedekindSequence β a := by
                    apply Finset.sum_congr rfl
                    intro a haIco
                    have ha' := Finset.mem_Ico.mp haIco
                    have hka : k < a := by omega
                    have hapos : 0 < a := by omega
                    unfold F β
                    have hseq :=
                      coefficientDedekindTerm_filter_eq_residueSequence
                        (m := k) (c := p ^ 2) (x := a) hk hPk
                    by_cases hcop : k.Coprime a
                    · have hacop : a.Coprime k := hcop.symm
                      rw [if_pos ⟨hapos, by omega, hka, hcop⟩]
                      rw [dif_pos hacop] at hseq
                      rw [arithmeticCoefficientDedekindTerm_comm a (p ^ 2) k,
                        hseq]
                      simp
                    · have hacop : ¬a.Coprime k := by
                        simpa [Nat.coprime_comm] using hcop
                      rw [if_neg (by
                        intro h
                        exact hcop h.2.2.2)]
                      rw [dif_neg hacop] at hseq
                      rw [← hseq]
                      simp
          change (∑ a ∈ Finset.range p, F a) = modulusKSlice p k
          rw [hrestrict]
          rw [modulusKSlice, dif_neg (by omega : k ≠ 0),
            dif_pos ⟨hk, hPk⟩]
        · have hk01 : k = 0 ∨ k = 1 := by omega
          rcases hk01 with rfl | rfl
          · simp [modulusKSlice]
          · simp [modulusKSlice,
              arithmeticCoefficientDedekindTerm_mod_one]
  rw [hproduct]

/-- Summing the Abel slices gives the manuscript's `p² H_p²` remainder
scale, with an explicit constant. -/
theorem norm_offDiagonalModulusK_le
    {p : ℕ} (hp : p.Prime) :
    ‖offDiagonalModulusK p‖ ≤
      8 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
  rw [offDiagonalModulusK_eq_slices hp, norm_mul]
  norm_num
  have hHpQ : (0 : ℚ) ≤ harmonic p := by
    unfold harmonic
    positivity
  have hHp : (0 : ℝ) ≤ (harmonic p : ℝ) := by exact_mod_cast hHpQ
  have hpoint : ∀ k ∈ Finset.range p,
      ‖modulusKSlice p k‖ ≤ (p : ℝ) * (harmonic p : ℝ) ^ 2 := by
    intro k hkP
    have hkp : k < p := Finset.mem_range.mp hkP
    by_cases hk : 2 ≤ k
    · exact norm_modulusKSlice_le hp hk hkp
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp [modulusKSlice]
        positivity
      · simp [modulusKSlice]
        positivity
  calc
    8 * ‖∑ k ∈ Finset.range p, modulusKSlice p k‖ ≤
        8 * ∑ k ∈ Finset.range p, ‖modulusKSlice p k‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ 8 * ∑ _k ∈ Finset.range p,
          ((p : ℝ) * (harmonic p : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Finset.sum_le_sum
            intro k hkP
            exact hpoint k hkP
    _ = 8 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
          simp
          ring

/-! ## The off-diagonal main pole -/

/-- The real floor-weighted Euler sum underlying the large reciprocity pole. -/
noncomputable def floorEulerSum (p : ℕ) : ℝ :=
  ∑ ak ∈ reducedRatioPairs p,
    (((p - 1) / ak.1 : ℕ) : ℝ) /
      ((ak.2 : ℝ) * (ak.1 : ℝ))

theorem reducedRatioPairs_swap (p : ℕ) :
    (reducedRatioPairs p).image Prod.swap = reducedEulerPairs (p - 1) := by
  ext ka
  rcases ka with ⟨k, a⟩
  simp [reducedRatioPairs, reducedEulerPairs]
  omega

theorem reducedRatioEulerWeight_sum_eq_frontier
    {p : ℕ} (hp3 : 3 ≤ p) :
    (∑ ak ∈ reducedRatioPairs p, eulerPairWeight ak.2 ak.1) =
      1 - eulerFrontierPotential (p - 1) := by
  have hN : 2 ≤ p - 1 := by omega
  rw [← reducedEulerPairs_weight_sum_eq_one_sub_frontier hN]
  rw [← reducedRatioPairs_swap p]
  rw [Finset.sum_image]
  · rfl
  · intro x _hx y _hy hxy
    exact Prod.swap_injective hxy

/-- The complex main-pole object is exactly the scalar extension of the real
floor Euler sum. -/
theorem offDiagonalMain_eq_floorEulerSum (p : ℕ) :
    offDiagonalMain p =
      (((2 / 3 : ℝ) * (p : ℝ) ^ 2 * floorEulerSum p : ℝ) : ℂ) := by
  unfold offDiagonalMain floorEulerSum
  push_cast
  rw [Finset.mul_sum]
  rw [show
    (2 / 3 : ℂ) * (p : ℂ) ^ 2 *
        (∑ ak ∈ reducedRatioPairs p,
          (((p - 1) / ak.1 : ℕ) : ℂ) /
            ((ak.2 : ℂ) * (ak.1 : ℂ))) =
      ((2 / 3 : ℂ) * (p : ℂ) ^ 2) *
        (∑ ak ∈ reducedRatioPairs p,
          (((p - 1) / ak.1 : ℕ) : ℂ) /
            ((ak.2 : ℂ) * (ak.1 : ℂ))) by ring]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ak _hak
  ring

/-- The amount discarded by replacing real division with the natural-number
quotient. -/
noncomputable def quotientDefect (n a : ℕ) : ℝ :=
  (n : ℝ) / (a : ℝ) - ((n / a : ℕ) : ℝ)

/-- A natural quotient differs from the corresponding real quotient by a
number in the half-open unit interval. -/
theorem quotientDefect_nonneg_and_le_one
    {n a : ℕ} (ha : 0 < a) :
    0 ≤ quotientDefect n a ∧ quotientDefect n a ≤ 1 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlowNat : n / a * a ≤ n := Nat.div_mul_le_self n a
  have hhighNat : n < (n / a + 1) * a :=
    (Nat.div_lt_iff_lt_mul ha).mp (Nat.lt_succ_self (n / a))
  have hlow : ((n / a : ℕ) : ℝ) ≤ (n : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ haR]
    exact_mod_cast hlowNat
  have hhigh : (n : ℝ) / (a : ℝ) < ((n / a : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ haR]
    exact_mod_cast hhighNat
  unfold quotientDefect
  constructor <;> linarith

/-- Pointwise floor replacement in the main pole costs at most `1/(ka)`. -/
theorem floorEulerTerm_error_le
    {p a k : ℕ} (ha : 0 < a) (hk : 0 < k) :
    |(((p - 1) / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ)) -
        ((p - 1 : ℕ) : ℝ) * eulerPairWeight k a| ≤
      1 / ((k : ℝ) * (a : ℝ)) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hden : (0 : ℝ) < (k : ℝ) * (a : ℝ) := by positivity
  have hdef := quotientDefect_nonneg_and_le_one
    (n := p - 1) ha
  have heq :
      (((p - 1) / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ)) -
          ((p - 1 : ℕ) : ℝ) * eulerPairWeight k a =
        -(quotientDefect (p - 1) a) / ((k : ℝ) * (a : ℝ)) := by
    unfold quotientDefect eulerPairWeight
    field_simp [haR, hkR]
    ring
  rw [heq, abs_div, abs_neg, abs_of_nonneg hdef.1,
    abs_of_pos hden]
  exact div_le_div_of_nonneg_right hdef.2 hden.le

/-- The reciprocal mass of the primitive ratio triangle is bounded by the
square of the full harmonic sum. -/
theorem reciprocal_reducedRatioPairs_sum_le_harmonic_sq (p : ℕ) :
    (∑ ak ∈ reducedRatioPairs p,
      1 / ((ak.2 : ℝ) * (ak.1 : ℝ))) ≤
        (harmonic p : ℝ) ^ 2 := by
  classical
  let grid := (Finset.Icc 1 p).product (Finset.Icc 1 p)
  have hsubset : reducedRatioPairs p ⊆ grid := by
    intro ak hak
    have h := hak
    simp [reducedRatioPairs] at h
    rcases h with ⟨⟨haP, hkP⟩, ha, hk, hka, _hcop⟩
    simpa [grid] using
      (show ak.1 ∈ Finset.Icc 1 p ∧ ak.2 ∈ Finset.Icc 1 p from
        ⟨Finset.mem_Icc.mpr ⟨ha, Nat.le_of_lt haP⟩,
          Finset.mem_Icc.mpr ⟨hk, Nat.le_of_lt hkP⟩⟩)
  calc
    (∑ ak ∈ reducedRatioPairs p,
        1 / ((ak.2 : ℝ) * (ak.1 : ℝ))) ≤
        ∑ ak ∈ grid, 1 / ((ak.2 : ℝ) * (ak.1 : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro ak _hgrid _hnot
          positivity
    _ = (∑ a ∈ Finset.Icc 1 p, (a : ℝ)⁻¹) *
          (∑ k ∈ Finset.Icc 1 p, (k : ℝ)⁻¹) := by
            unfold grid
            rw [show
              (∑ ak ∈ (Finset.Icc 1 p).product (Finset.Icc 1 p),
                  1 / ((ak.2 : ℝ) * (ak.1 : ℝ))) =
                ∑ a ∈ Finset.Icc 1 p, ∑ k ∈ Finset.Icc 1 p,
                  1 / ((k : ℝ) * (a : ℝ)) by
                    exact Finset.sum_product _ _ _]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
            have hkPos : 0 < k := (Finset.mem_Icc.mp hk).1
            have haR : (a : ℝ) ≠ 0 := by exact_mod_cast haPos.ne'
            have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkPos.ne'
            field_simp [haR, hkR]
    _ = (harmonic p : ℝ) ^ 2 := by
          rw [harmonic_eq_sum_Icc]
          simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          ring

/-- Replacing every scale multiplicity by its real quotient changes the
finite Euler mass by at most `H_p²`. -/
theorem abs_floorEulerSum_sub_eulerMass_le (p : ℕ) :
    |floorEulerSum p -
        ((p - 1 : ℕ) : ℝ) *
          (∑ ak ∈ reducedRatioPairs p,
            eulerPairWeight ak.2 ak.1)| ≤
      (harmonic p : ℝ) ^ 2 := by
  unfold floorEulerSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ ak ∈ reducedRatioPairs p,
        ((((p - 1) / ak.1 : ℕ) : ℝ) /
            ((ak.2 : ℝ) * (ak.1 : ℝ)) -
          ((p - 1 : ℕ) : ℝ) * eulerPairWeight ak.2 ak.1)| ≤
        ∑ ak ∈ reducedRatioPairs p,
          |((((p - 1) / ak.1 : ℕ) : ℝ) /
              ((ak.2 : ℝ) * (ak.1 : ℝ)) -
            ((p - 1 : ℕ) : ℝ) * eulerPairWeight ak.2 ak.1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ak ∈ reducedRatioPairs p,
          1 / ((ak.2 : ℝ) * (ak.1 : ℝ)) := by
            apply Finset.sum_le_sum
            intro ak hak
            have h := hak
            simp [reducedRatioPairs] at h
            exact floorEulerTerm_error_le h.2.1 h.2.2.1
    _ ≤ (harmonic p : ℝ) ^ 2 :=
      reciprocal_reducedRatioPairs_sum_le_harmonic_sq p

/-- The complete floor-weighted Euler mass differs from `p` by at most eight
harmonic squares.  This includes both the quotient defects and the exact
Calkin--Wilf frontier. -/
theorem abs_floorEulerSum_sub_prime_le
    {p : ℕ} (hp3 : 3 ≤ p) :
    |floorEulerSum p - (p : ℝ)| ≤
      8 * (harmonic p : ℝ) ^ 2 := by
  let n : ℝ := ((p - 1 : ℕ) : ℝ)
  let F : ℝ := eulerFrontierPotential (p - 1)
  let Hp : ℝ := (harmonic p : ℝ)
  let Hn : ℝ := (harmonic (p - 1) : ℝ)
  have hnPos : 0 < n := by
    unfold n
    exact_mod_cast (show 0 < p - 1 by omega)
  have hFnonneg : 0 ≤ F := by
    exact eulerFrontierPotential_nonneg (p - 1)
  have hfront := eulerFrontierPotential_le (by omega : 2 ≤ p - 1)
  have hnF : n * F ≤ 4 + 2 * Hn := by
    calc
      n * F ≤ n * (4 / n + 2 * Hn / n) := by
        apply mul_le_mul_of_nonneg_left _ hnPos.le
        simpa [n, F, Hn] using hfront
      _ = 4 + 2 * Hn := by
        field_simp [hnPos.ne']
  have hHnHp : Hn ≤ Hp := by
    simpa [Hn, Hp] using
      harmonic_cast_mono (show p - 1 ≤ p by omega)
  have hHpOne : 1 ≤ Hp := by
    calc
      (1 : ℝ) = (harmonic 1 : ℝ) := by norm_num [harmonic]
      _ ≤ (harmonic p : ℝ) :=
        harmonic_cast_mono (show 1 ≤ p by omega)
      _ = Hp := by rfl
  have hmass := reducedRatioEulerWeight_sum_eq_frontier hp3
  have hfloor :
      |floorEulerSum p - n * (1 - F)| ≤ Hp ^ 2 := by
    have h := abs_floorEulerSum_sub_eulerMass_le p
    rw [hmass] at h
    simpa [n, F, Hp] using h
  have hmiddle : |n * (1 - F) - (p : ℝ)| = 1 + n * F := by
    have hpOne : 1 ≤ p := by omega
    have heq : n * (1 - F) - (p : ℝ) = -(1 + n * F) := by
      unfold n
      rw [Nat.cast_sub hpOne]
      ring
    rw [heq, abs_neg, abs_of_nonneg]
    positivity
  calc
    |floorEulerSum p - (p : ℝ)| ≤
        |floorEulerSum p - n * (1 - F)| +
          |n * (1 - F) - (p : ℝ)| :=
      abs_sub_le _ _ _
    _ ≤ Hp ^ 2 + (1 + n * F) := by
          rw [hmiddle]
          gcongr
    _ ≤ Hp ^ 2 + (5 + 2 * Hn) := by linarith
    _ ≤ 8 * Hp ^ 2 := by nlinarith

/-- Quantitative cubic estimate for the full main pole. -/
theorem norm_offDiagonalMain_sub_cubicPole_le
    {p : ℕ} (hp3 : 3 ≤ p) :
    ‖offDiagonalMain p - (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
      6 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
  rw [offDiagonalMain_eq_floorEulerSum]
  push_cast
  rw [show
    (2 / 3 : ℂ) * (p : ℂ) ^ 2 * (floorEulerSum p : ℂ) -
        (2 / 3 : ℂ) * (p : ℂ) ^ 3 =
      ((2 / 3 : ℝ) * (p : ℝ) ^ 2 : ℝ) *
        ((floorEulerSum p - (p : ℝ) : ℝ) : ℂ) by
          push_cast
          ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      0 ≤ (2 / 3 : ℝ) * (p : ℝ) ^ 2),
    Complex.norm_real, Real.norm_eq_abs]
  calc
    (2 / 3 : ℝ) * (p : ℝ) ^ 2 *
        |floorEulerSum p - (p : ℝ)| ≤
      (2 / 3 : ℝ) * (p : ℝ) ^ 2 *
        (8 * (harmonic p : ℝ) ^ 2) := by
          gcongr
          exact abs_floorEulerSum_sub_prime_le hp3
    _ ≤ 6 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
          have hprod : 0 ≤ (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
            positivity
          nlinarith

/-! ## The elementary reciprocity remainder -/

/-- The total scale multiplicity in the primitive ratio triangle is at most
`p²`. -/
theorem scaleMultiplicityMass_le (p : ℕ) :
    (∑ ak ∈ reducedRatioPairs p,
      (((p - 1) / ak.1 : ℕ) : ℝ)) ≤ (p : ℝ) ^ 2 := by
  classical
  unfold reducedRatioPairs
  rw [Finset.sum_filter]
  rw [show
    (∑ ak ∈ (Finset.range p).product (Finset.range p),
      if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧ ak.2.Coprime ak.1 then
        (((p - 1) / ak.1 : ℕ) : ℝ) else 0) =
      ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℝ) else 0 by
            exact Finset.sum_product _ _ _]
  have hslice : ∀ a ∈ Finset.range p,
      (∑ k ∈ Finset.range p,
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℝ) else 0) ≤ (p : ℝ) := by
    intro a haP
    have hap : a < p := Finset.mem_range.mp haP
    calc
      (∑ k ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
            (((p - 1) / a : ℕ) : ℝ) else 0) ≤
          ∑ k ∈ Finset.range p,
            if k < a then (((p - 1) / a : ℕ) : ℝ) else 0 := by
              apply Finset.sum_le_sum
              intro k hkP
              by_cases h :
                  0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a
              · rw [if_pos h, if_pos h.2.2.1]
              · rw [if_neg h]
                positivity
      _ = ∑ _k ∈ Finset.range a,
            (((p - 1) / a : ℕ) : ℝ) := by
              rw [← Finset.sum_filter]
              have hfilter :
                  (Finset.range p).filter (fun k => k < a) =
                    Finset.range a := by
                ext k
                simp
                omega
              rw [hfilter]
      _ = (a : ℝ) * (((p - 1) / a : ℕ) : ℝ) := by simp
      _ ≤ (p : ℝ) := by
            have hnat : a * ((p - 1) / a) ≤ p := by
              rw [Nat.mul_comm]
              exact (Nat.div_mul_le_self (p - 1) a).trans (Nat.sub_le p 1)
            exact_mod_cast hnat
  calc
    (∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℝ) else 0) ≤
      ∑ _a ∈ Finset.range p, (p : ℝ) := by
        apply Finset.sum_le_sum
        intro a haP
        exact hslice a haP
    _ = (p : ℝ) ^ 2 := by simp [pow_two]

/-- Each constant and reciprocal-size summand in the three-term relation has
absolute value at most one on the prime window. -/
theorem abs_reducedRatioElementaryRemainder_le_one
    {p a k : ℕ} (hp3 : 3 ≤ p) (ha : 0 < a) (hk : 0 < k)
    (hka : k < a) (hap : a < p) :
    |((-1 / 4 + (1 / 12) *
        ((k : ℚ) / ((a : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
          (a : ℚ) / (((p ^ 2 : ℕ) : ℚ) * (k : ℚ))) : ℚ) : ℝ)| ≤ 1 := by
  push_cast
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) hp3)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpSqOne : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have hfirst :
      (k : ℝ) / ((a : ℝ) * (p : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hkA : (k : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt hka)
    calc
      (k : ℝ) ≤ a := hkA
      _ = (a : ℝ) * 1 := by ring
      _ ≤ (a : ℝ) * (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hpSqOne haR.le
  have hsecond :
      (a : ℝ) / ((p : ℝ) ^ 2 * (k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have haP : (a : ℝ) ≤ p := by exact_mod_cast (Nat.le_of_lt hap)
    calc
      (a : ℝ) ≤ p := haP
      _ ≤ (p : ℝ) ^ 2 := by nlinarith
      _ = (p : ℝ) ^ 2 * 1 := by ring
      _ ≤ (p : ℝ) ^ 2 * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hkOne (sq_nonneg _)
  rw [abs_le]
  constructor
  · have hfirstNonneg :
        0 ≤ (k : ℝ) / ((a : ℝ) * (p : ℝ) ^ 2) := by positivity
    have hsecondNonneg :
        0 ≤ (a : ℝ) / ((p : ℝ) ^ 2 * (k : ℝ)) := by positivity
    linarith
  · linarith

/-- The constant and reciprocal-size terms contribute only quadratically. -/
theorem norm_offDiagonalElementaryRemainder_le
    {p : ℕ} (hp3 : 3 ≤ p) :
    ‖offDiagonalElementaryRemainder p‖ ≤ 8 * (p : ℝ) ^ 2 := by
  unfold offDiagonalElementaryRemainder
  rw [norm_mul, Complex.norm_ofNat]
  have hpoint : ∀ ak ∈ reducedRatioPairs p,
      ‖((((p - 1) / ak.1 : ℕ) : ℂ) *
        ((-1 / 4 + (1 / 12) *
          ((ak.2 : ℚ) / ((ak.1 : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
            (ak.1 : ℚ) /
              (((p ^ 2 : ℕ) : ℚ) * (ak.2 : ℚ))) : ℚ) : ℂ))‖ ≤
        (((p - 1) / ak.1 : ℕ) : ℝ) := by
    intro ak hak
    have h := hak
    simp [reducedRatioPairs] at h
    rcases h with ⟨⟨haP, _hkP⟩, ha, hk, hka, _hcop⟩
    rw [norm_mul, Complex.norm_natCast, Complex.norm_ratCast]
    have hsmall := abs_reducedRatioElementaryRemainder_le_one
      hp3 ha hk hka haP
    have hscale : (0 : ℝ) ≤ (((p - 1) / ak.1 : ℕ) : ℝ) := by positivity
    exact (mul_le_mul_of_nonneg_left hsmall hscale).trans_eq (mul_one _)
  calc
    8 * ‖∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℂ) *
          ((-1 / 4 + (1 / 12) *
            ((ak.2 : ℚ) / ((ak.1 : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
              (ak.1 : ℚ) /
                (((p ^ 2 : ℕ) : ℚ) * (ak.2 : ℚ))) : ℚ) : ℂ)‖ ≤
      8 * ∑ ak ∈ reducedRatioPairs p,
        ‖((((p - 1) / ak.1 : ℕ) : ℂ) *
          ((-1 / 4 + (1 / 12) *
            ((ak.2 : ℚ) / ((ak.1 : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
              (ak.1 : ℚ) /
                (((p ^ 2 : ℕ) : ℚ) * (ak.2 : ℚ))) : ℚ) : ℂ))‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ 8 * ∑ ak ∈ reducedRatioPairs p,
          (((p - 1) / ak.1 : ℕ) : ℝ) := by
            gcongr
            exact hpoint ak ‹ak ∈ reducedRatioPairs p›
    _ ≤ 8 * (p : ℝ) ^ 2 := by
          gcongr
          exact scaleMultiplicityMass_le p

/-! ## The diagonal pole and the assembled cubic law -/

/-- The closed diagonal expression lies within one quadratic unit of its
one-third cubic pole. -/
theorem abs_diagonalClosed_sub_cubicPole_le
    {p : ℕ} (hp3 : 3 ≤ p) :
    |((p - 1 : ℕ) : ℝ) * ((p : ℝ) ^ 2 - 1) *
          ((p : ℝ) ^ 2 - 2) / (3 * (p : ℝ) ^ 2) -
        (p : ℝ) ^ 3 / 3| ≤
      (p : ℝ) ^ 2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpOne : 1 ≤ p := by omega
  have hpNe : (p : ℝ) ≠ 0 := by positivity
  let A : ℝ :=
    (p : ℝ) ^ 4 + 3 * (p : ℝ) ^ 3 - 3 * (p : ℝ) ^ 2 -
      2 * (p : ℝ) + 2
  have hAeq :
      ((p - 1 : ℕ) : ℝ) * ((p : ℝ) ^ 2 - 1) *
            ((p : ℝ) ^ 2 - 2) / (3 * (p : ℝ) ^ 2) -
          (p : ℝ) ^ 3 / 3 =
        -A / (3 * (p : ℝ) ^ 2) := by
    unfold A
    rw [Nat.cast_sub hpOne]
    field_simp [hpNe]
    ring
  have hAnonneg : 0 ≤ A := by
    unfold A
    nlinarith [sq_nonneg ((p : ℝ) ^ 2 - 3),
      sq_nonneg ((p : ℝ) - 1)]
  have hAupper : A ≤ 3 * (p : ℝ) ^ 4 := by
    unfold A
    nlinarith [sq_nonneg ((p : ℝ) ^ 2 - 3),
      sq_nonneg ((p : ℝ) - 1)]
  have hden : (0 : ℝ) < 3 * (p : ℝ) ^ 2 := by positivity
  rw [hAeq, abs_div, abs_neg, abs_of_nonneg hAnonneg,
    abs_of_pos hden]
  rw [div_le_iff₀ hden]
  nlinarith

/-- The exact diagonal part of the Dedekind collision energy has the
one-third cubic main term with a quadratic error. -/
theorem norm_diagonalEnergy_sub_cubicPole_le
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ‖4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp -
        (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)‖ ≤
      (p : ℝ) ^ 2 := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  rw [dedekindCollisionEnergy_diagonal_closed hp]
  rw [show
    ((p - 1 : ℕ) : ℂ) * (((p ^ 2 : ℕ) : ℂ) - 1) *
          (((p ^ 2 : ℕ) : ℂ) - 2) /
            (3 * ((p ^ 2 : ℕ) : ℂ)) -
        (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ) =
      (((((p - 1 : ℕ) : ℝ) * ((p : ℝ) ^ 2 - 1) *
          ((p : ℝ) ^ 2 - 2) / (3 * (p : ℝ) ^ 2) -
          (p : ℝ) ^ 3 / 3) : ℝ) : ℂ) by
            push_cast
            ring]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_diagonalClosed_sub_cubicPole_le hp3

/-- The unconditional cubic law for the Dedekind form of the prime carry
energy.  Every term in the exact finite decomposition is included. -/
theorem norm_dedekindCollisionEnergy_sub_cube_le
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ‖dedekindCollisionEnergy hp - (((p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
      24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hD := norm_diagonalEnergy_sub_cubicPole_le hp hpodd
  have hM := norm_offDiagonalMain_sub_cubicPole_le hp3
  have hE := norm_offDiagonalElementaryRemainder_le hp3
  have hK := norm_offDiagonalModulusK_le hp
  have hHone : (1 : ℝ) ≤ (harmonic p : ℝ) := by
    calc
      (1 : ℝ) = (harmonic 1 : ℝ) := by norm_num [harmonic]
      _ ≤ (harmonic p : ℝ) :=
        harmonic_cast_mono (show 1 ≤ p by omega)
  rw [dedekindCollisionEnergy_poleSplit hp,
    four_mul_offDiagonal_eq_fourWay hp,
    offDiagonalModulusA_eq_zero hp]
  rw [show
    4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp +
          (offDiagonalMain p + offDiagonalElementaryRemainder p + 0 +
            offDiagonalModulusK p) -
        (((p : ℝ) ^ 3 : ℝ) : ℂ) =
      (((4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)) +
        (offDiagonalMain p -
          (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ))) +
        offDiagonalElementaryRemainder p) +
        offDiagonalModulusK p by
          push_cast
          ring]
  calc
    ‖(((4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)) +
        (offDiagonalMain p -
          (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ))) +
        offDiagonalElementaryRemainder p) +
        offDiagonalModulusK p‖ ≤
      (‖4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)‖ +
        ‖offDiagonalMain p -
          (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ)‖) +
        ‖offDiagonalElementaryRemainder p‖ +
        ‖offDiagonalModulusK p‖ := by
          calc
            _ ≤ ‖((4 * ((p - 1 : ℕ) : ℂ) *
                    primeSquareDiagonalDedekind hp -
                  (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)) +
                (offDiagonalMain p -
                  (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ))) +
                offDiagonalElementaryRemainder p‖ +
                ‖offDiagonalModulusK p‖ := norm_add_le _ _
            _ ≤ (‖(4 * ((p - 1 : ℕ) : ℂ) *
                    primeSquareDiagonalDedekind hp -
                  (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)) +
                (offDiagonalMain p -
                  (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ))‖ +
                ‖offDiagonalElementaryRemainder p‖) +
                ‖offDiagonalModulusK p‖ := by
                  gcongr
                  exact norm_add_le _ _
            _ ≤ _ := by
                  gcongr
                  exact norm_add_le _ _
    _ ≤ ((p : ℝ) ^ 2 +
          6 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2) +
          8 * (p : ℝ) ^ 2 +
          8 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
            gcongr
    _ ≤ 24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
          have hpSq : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
          nlinarith [sq_nonneg ((harmonic p : ℝ) - 1)]

/-- The same unconditional estimate stated for the manuscript's concrete
class-centered floor-jump energy. -/
theorem primeCarryEnergy_cubic_bound
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
      24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have h := norm_dedekindCollisionEnergy_sub_cube_le hp hpodd
  rw [← primeCarryEnergy_eq_dedekindCollisionEnergy hp hpodd] at h
  have heq :
      ((primeCarryEnergy hp - (p : ℝ) ^ 3 : ℝ) : ℂ) =
        (primeCarryEnergy hp : ℂ) - (((p : ℝ) ^ 3 : ℝ) : ℂ) := by
    push_cast
    ring
  have hreal :
      ‖((primeCarryEnergy hp - (p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
        24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
    rw [heq]
    exact h
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  exact hreal

/-- A logarithmic form of the quantitative cubic law. -/
theorem primeCarryEnergy_cubic_log_bound
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
      24 * (p : ℝ) ^ 2 * (1 + Real.log (p : ℝ)) ^ 2 := by
  have hcubic := primeCarryEnergy_cubic_bound hp hpodd
  have hH := harmonic_le_one_add_log p
  have hHnonneg : (0 : ℝ) ≤ (harmonic p : ℝ) := by
    have hq : (0 : ℚ) ≤ harmonic p := by
      unfold harmonic
      positivity
    exact_mod_cast hq
  have hlognonneg : (0 : ℝ) ≤ 1 + Real.log (p : ℝ) := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    positivity
  calc
    |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
        24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := hcubic
    _ ≤ 24 * (p : ℝ) ^ 2 * (1 + Real.log (p : ℝ)) ^ 2 := by
          gcongr

/-- The manuscript's pure `p² (log p)²` error scale, again with an explicit
constant rather than asymptotic notation. -/
theorem primeCarryEnergy_cubic_pureLog_bound
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
      96 * (p : ℝ) ^ 2 * (Real.log (p : ℝ)) ^ 2 := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hpPos : (0 : ℝ) < p := by positivity
  have hexp : Real.exp 1 < (p : ℝ) := by
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hp3)
  have hlogOne : (1 : ℝ) ≤ Real.log (p : ℝ) := by
    have hstrict : (1 : ℝ) < Real.log (p : ℝ) := by
      rw [← Real.exp_lt_exp]
      simpa [Real.exp_log hpPos] using hexp
    exact hstrict.le
  have hsquare :
      (1 + Real.log (p : ℝ)) ^ 2 ≤
        4 * (Real.log (p : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (p : ℝ) - 1)]
  calc
    |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
        24 * (p : ℝ) ^ 2 * (1 + Real.log (p : ℝ)) ^ 2 :=
      primeCarryEnergy_cubic_log_bound hp hpodd
    _ ≤ 96 * (p : ℝ) ^ 2 * (Real.log (p : ℝ)) ^ 2 := by
          nlinarith [sq_nonneg (p : ℝ)]


end NField.Alignment.PrimeSquareCubicEnergy
