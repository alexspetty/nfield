/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarryFiberCentering
import NField.Alignment.TheCollisionSpectrum

/-!
# Prime threshold-energy normalization

This module isolates the two exact normalizations of the prime-square carry
table.  It keeps the raw integer table, the half-centered table, and the
class-centered collision energy as distinct theorem objects.
-/

namespace NField.Alignment.PrimeThresholdEnergyNormalization

open scoped BigOperators ZMod
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.AnalyticCollisionTransform
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionPeriodicTable
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarryFiberCentering
open NField.Alignment.PrimeCarryTableColumnLaw
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.TheCollisionSpectrum

/-- The raw centered integer entry `S₁(a)` as a real number. -/
def rawPrimeCarryValue
    {p : ℕ} (_hp : p.Prime) (a : UnitClass (p ^ 2)) : ℝ :=
  (fluctuationTable p a.val.val : ℝ)

/-- The manuscript's threshold variance before residue-class centering. -/
noncomputable def primeThresholdVariance
    {p : ℕ} (hp : p.Prime) : ℝ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ a : UnitClass (p ^ 2), rawPrimeCarryValue hp a ^ 2

/-- The integer half-centered table `T_p(a) = 2 S₁(a) + 1`. -/
def primeHalfCenteredValue
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) : ℝ :=
  2 * rawPrimeCarryValue hp a + 1

/-- Square mass of the integer half-centered table. -/
noncomputable def primeHalfCenteredSquareMass
    {p : ℕ} (hp : p.Prime) : ℝ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ a : UnitClass (p ^ 2), primeHalfCenteredValue hp a ^ 2

/-- Canonical equivalence between the general lag-one modulus and the prime
square. -/
noncomputable def lagOneUnitAsPrimeSquareEquiv
    {p : ℕ} [NeZero (allLagModulus p 1)] :
    UnitClass (allLagModulus p 1) ≃ UnitClass (p ^ 2) :=
  Equiv.cast (by simp [allLagModulus])

/-- Canonical type-level identification of one lag-one unit with a
prime-square unit. -/
noncomputable def lagOneUnitAsPrimeSquare
    {p : ℕ} [NeZero (allLagModulus p 1)]
    (a : UnitClass (allLagModulus p 1)) : UnitClass (p ^ 2) :=
  lagOneUnitAsPrimeSquareEquiv a

/-- Reflection gives the exact real-valued raw-table relation. -/
theorem rawPrimeCarryValue_reflection
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    rawPrimeCarryValue hp a + rawPrimeCarryValue hp (-a) = -1 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  letI : NeZero (allLagModulus p 1) := by
    simpa [allLagModulus] using (inferInstance : NeZero (p ^ 2))
  have h := allLagUnitTable_reflection
    (b := p) (ell := 1) hp.two_le (by omega) a
  rw [allLagUnitTable_one_eq_fluctuationTable hp,
    allLagUnitTable_one_eq_fluctuationTable hp] at h
  unfold rawPrimeCarryValue
  exact_mod_cast h

/-- Reflection gives the exact raw threshold-count identity
`f_p(a) + f_p(p²-a) = p`. -/
theorem carryThresholdCount_reflection
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    carryThresholdCount p a.val.val +
        carryThresholdCount p (p ^ 2 - a.val.val) = (p : ℤ) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  letI : Fact (1 < p ^ 2) := ⟨by nlinarith [hp.two_le]⟩
  let A := a.val.val
  have hApos : 0 < A :=
    ZMod.val_pos.mpr (IsUnit.ne_zero a.isUnit)
  have hAlt : A < p ^ 2 := a.val.val_lt
  have hAcop : A.Coprime (p ^ 2) := by
    apply (ZMod.isUnit_iff_coprime A (p ^ 2)).mp
    unfold A
    rw [ZMod.natCast_zmod_val]
    exact a.isUnit
  have hpair := allLag_jump_pair_sum
    (b := p) (ell := 1) hp.two_le (by omega)
    hApos (by simpa [allLagModulus] using hAlt)
    (by simpa [allLagModulus] using hAcop)
  have hdiag : allLagDiagonal p 1 = diagonalSlices p := by
    ext n
    simp [allLagDiagonal, diagonalSlices]
  rw [carryThresholdCount_eq_diagonalSum,
    carryThresholdCount_eq_diagonalSum]
  rw [← hdiag]
  simpa [allLagModulus, Finset.sum_add_distrib] using hpair

/-- Reflection makes the integer half-centered carry table exactly odd. -/
theorem primeHalfCenteredValue_reflection
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    primeHalfCenteredValue hp (-a) = -primeHalfCenteredValue hp a := by
  have hreflect := rawPrimeCarryValue_reflection hp a
  unfold primeHalfCenteredValue
  linarith

/-- Reflection makes the residue-class centered collision table exactly odd. -/
theorem primeCarryCentered_reflection
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (a : UnitClass (p ^ 2)) :
    primeCarryCentered hp (-a) = -primeCarryCentered hp a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (allLagModulus p 1) :=
    ⟨by simpa [allLagModulus] using pow_ne_zero 2 hp.ne_zero⟩
  have hreflect := centeredLagOneSpectrum_odd
    (b := p) hp.two_le a
  rw [centeredLagOneSpectrum_eq_primeCarryCentered hp hpodd,
    centeredLagOneSpectrum_eq_primeCarryCentered hp hpodd] at hreflect
  exact hreflect

/-- The raw table has exact total mass `-φ(p²)/2`. -/
theorem sum_rawPrimeCarryValue
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    (∑ a : UnitClass (p ^ 2), rawPrimeCarryValue hp a) =
      -((p * (p - 1) : ℕ) : ℝ) / 2 := by
  classical
  let S : ℝ := ∑ a : UnitClass (p ^ 2), rawPrimeCarryValue hp a
  have hreindex :
      (∑ a : UnitClass (p ^ 2), rawPrimeCarryValue hp (-a)) = S := by
    simpa [S] using (Equiv.sum_comp (Equiv.neg (UnitClass (p ^ 2)))
      (rawPrimeCarryValue hp))
  have hpair :
      (∑ a : UnitClass (p ^ 2),
        (rawPrimeCarryValue hp a + rawPrimeCarryValue hp (-a))) =
          -((Fintype.card (UnitClass (p ^ 2)) : ℕ) : ℝ) := by
    simp_rw [rawPrimeCarryValue_reflection hp]
    simp
  rw [Finset.sum_add_distrib, hreindex] at hpair
  have hcard : Fintype.card (UnitClass (p ^ 2)) = p * (p - 1) := by
    rw [ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp (by decide : 0 < 2)]
    norm_num
  change S = _
  rw [hcard] at hpair
  linarith

/-- Exact half-centered normalization of the threshold variance. -/
theorem primeThresholdVariance_eq_halfCentered
    {p : ℕ} (hp : p.Prime) :
    primeThresholdVariance hp =
      (1 / 4 : ℝ) * primeHalfCenteredSquareMass hp +
        (1 / 4 : ℝ) * (p : ℝ) * ((p - 1 : ℕ) : ℝ) := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hsum := sum_rawPrimeCarryValue hp
  unfold primeThresholdVariance primeHalfCenteredSquareMass
    primeHalfCenteredValue
  rw [show
      (∑ a : UnitClass (p ^ 2),
        (2 * rawPrimeCarryValue hp a + 1) ^ 2) =
        4 * ∑ a : UnitClass (p ^ 2), rawPrimeCarryValue hp a ^ 2 +
          4 * ∑ a : UnitClass (p ^ 2), rawPrimeCarryValue hp a +
          (Fintype.card (UnitClass (p ^ 2)) : ℝ) by
      calc
        _ = ∑ a : UnitClass (p ^ 2),
            (4 * rawPrimeCarryValue hp a ^ 2 +
              4 * rawPrimeCarryValue hp a + 1) := by
                apply Finset.sum_congr rfl
                intro a _
                ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
          simp]
  have hcard : Fintype.card (UnitClass (p ^ 2)) = p * (p - 1) := by
    rw [ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp (by decide : 0 < 2)]
    norm_num
  rw [hcard]
  rw [hsum]
  push_cast
  ring

/-- On one residue-class fiber, subtracting the exact class mean removes its
mean-square contribution. -/
theorem primeCarryCentered_fiber_squareMass
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (hpodd : p ≠ 2) (u : UnitClass p) :
    (∑ a : Fiber (coarseUnitReduction p 1) u,
        ‖primeCarryCentered hp (lagOneUnitAsPrimeSquare a.val)‖ ^ 2) =
      (∑ a : Fiber (coarseUnitReduction p 1) u,
        rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val) ^ 2) -
        ((p - u.val.val : ℕ) : ℝ) ^ 2 / (p : ℝ) := by
  classical
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  letI : NeZero (p ^ 2) := by
    simpa [allLagModulus] using
      (inferInstance : NeZero (allLagModulus p 1))
  have hspos : 0 < u.val.val :=
    ZMod.val_pos.mpr (IsUnit.ne_zero u.isUnit)
  have hslt : u.val.val < p := u.val.val_lt
  let c : ℝ := ((p - u.val.val : ℕ) : ℝ) / (p : ℝ)
  have hpoint (a : Fiber (coarseUnitReduction p 1) u) :
      ‖primeCarryCentered hp (lagOneUnitAsPrimeSquare a.val)‖ ^ 2 =
        (rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val) + c) ^ 2 := by
    unfold primeCarryCentered rawPrimeCarryValue c
    have hred : (lagOneUnitAsPrimeSquare a.val).val.val % p =
        u.val.val := by
      change a.val.val.val % p = u.val.val
      have hv := congrArg
        (fun v : UnitClass p => v.val.val) a.property
      unfold coarseUnitReduction at hv
      rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast] at hv
      simpa [allLagModulus] using hv
    rw [hred]
    have hreal :
        ((fluctuationTable p
            (lagOneUnitAsPrimeSquare a.val).val.val : ℤ) : ℂ) +
            ((p - u.val.val : ℕ) : ℂ) / (p : ℂ) =
          (((fluctuationTable p
              (lagOneUnitAsPrimeSquare a.val).val.val : ℤ) : ℝ) +
            ((p - u.val.val : ℕ) : ℝ) / (p : ℝ) : ℝ) := by
      push_cast
      rfl
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsum :
      (∑ a : Fiber (coarseUnitReduction p 1) u,
        rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val)) =
          (u.val.val : ℝ) - p := by
    have hcolumn := fluctuationTable_column_sum hp hpodd hspos hslt
    have hreindex :
        (∑ a : Fiber (coarseUnitReduction p 1) u,
          rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val)) =
        ∑ q : Fin p,
          (fluctuationTable p (p * q.val + u.val.val) : ℝ) := by
      symm
      apply Fintype.sum_equiv (primeFiberEquiv hp u)
      intro q
      unfold rawPrimeCarryValue
      change
        (fluctuationTable p (p * q.val + u.val.val) : ℝ) =
          (fluctuationTable p
            (lagOneUnitAsPrimeSquare (primeFiberCoordinate hp u q)).val.val : ℝ)
      rw [show
        (lagOneUnitAsPrimeSquare (primeFiberCoordinate hp u q)).val.val =
        (primeFiberCoordinate hp u q).val.val by rfl,
        primeFiberCoordinate_val]
      ring_nf
    rw [hreindex, Fin.sum_univ_eq_sum_range
      (fun q : ℕ =>
        (fluctuationTable p (p * q + u.val.val) : ℝ)) p]
    rw [← Int.cast_sum, hcolumn]
    push_cast
    ring
  have hcard :
      Fintype.card (Fiber (coarseUnitReduction p 1) u) = p := by
    simpa using Fintype.card_congr (primeFiberEquiv hp u).symm
  simp_rw [hpoint]
  rw [show
      (∑ a : Fiber (coarseUnitReduction p 1) u,
        (rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val) + c) ^ 2) =
        (∑ a : Fiber (coarseUnitReduction p 1) u,
          rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val) ^ 2) +
          2 * c *
            ∑ a : Fiber (coarseUnitReduction p 1) u,
              rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val) +
          (Fintype.card (Fiber (coarseUnitReduction p 1) u) : ℝ) * c ^ 2 by
      calc
        _ = ∑ a : Fiber (coarseUnitReduction p 1) u,
            (rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a.val) ^ 2 +
              2 * c * rawPrimeCarryValue hp
                (lagOneUnitAsPrimeSquare a.val) + c ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]
          simp]
  rw [hsum, hcard]
  unfold c
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Nat.cast_sub (Nat.le_of_lt hslt)]
  field_simp [hp0]
  ring

private theorem sum_range_succ_sq_real (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2) =
      (n : ℝ) * (n + 1 : ℝ) * (2 * n + 1 : ℝ) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Closed residue-class mean-square correction. -/
theorem primeClassMeanSquareCorrection
    {p : ℕ} [NeZero p] (hp : p.Prime) :
    (∑ u : UnitClass p,
        ((p - u.val.val : ℕ) : ℝ) ^ 2 / (p : ℝ)) =
      ((p - 1 : ℕ) : ℝ) * ((2 * p - 1 : ℕ) : ℝ) / 6 := by
  classical
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  let F : UnitClass p → ℝ := fun u =>
    ((p - u.val.val : ℕ) : ℝ) ^ 2 / (p : ℝ)
  have hwindow :
      (∑ u : UnitClass p, F u) =
        ∑ i : FirstWindowIndex p,
          ((p - firstWindowNat i : ℕ) : ℝ) ^ 2 / (p : ℝ) := by
    calc
      (∑ u : UnitClass p, F u) =
          ∑ i : FirstWindowIndex p, F (lowerFirstWindowUnit hp i) :=
            (lowerFirstWindowEquiv hp).sum_comp F |>.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        unfold F
        rw [lowerFirstWindowUnit_val]
  have hreverse :
      (∑ i : FirstWindowIndex p,
          ((p - firstWindowNat i : ℕ) : ℝ) ^ 2 / (p : ℝ)) =
        ∑ i : FirstWindowIndex p,
          ((firstWindowNat i : ℕ) : ℝ) ^ 2 / (p : ℝ) := by
    have hreindex := Equiv.sum_comp
      (Fin.revPerm : Equiv.Perm (FirstWindowIndex p))
      (fun i : FirstWindowIndex p =>
        ((firstWindowNat i : ℕ) : ℝ) ^ 2 / (p : ℝ))
    calc
      _ = ∑ i : FirstWindowIndex p,
          ((firstWindowNat (Fin.rev i) : ℕ) : ℝ) ^ 2 /
            (p : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold firstWindowNat
        rw [Fin.val_rev]
        congr 3
        omega
      _ = _ := hreindex
  have hshift :
      (∑ i : FirstWindowIndex p,
          ((firstWindowNat i : ℕ) : ℝ) ^ 2) =
        ∑ k ∈ Finset.range p, (k : ℝ) ^ 2 := by
    unfold firstWindowNat
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ 2) (p - 1)]
    have hsplit := Finset.sum_range_succ'
      (fun k : ℕ => (k : ℝ) ^ 2) (p - 1)
    simpa [Nat.sub_add_cancel hp.one_le] using hsplit.symm
  change (∑ u : UnitClass p, F u) = _
  rw [hwindow, hreverse, ← Finset.sum_div, hshift,
    show p = (p - 1) + 1 by exact (Nat.sub_add_cancel hp.one_le).symm,
    sum_range_succ_sq_real (p - 1)]
  have hpm1 : (p - 1) + 1 = p := Nat.sub_add_cancel hp.one_le
  simp only [hpm1]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htwo : 1 ≤ p * 2 := by omega
  push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub htwo]
  field_simp [hp0]
  ring_nf
  rw [Nat.cast_sub htwo]
  push_cast
  ring

/-- Exact conversion from the raw threshold variance to the class-centered
collision energy. -/
theorem primeCarryEnergy_eq_thresholdVariance_sub_classMean
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      primeThresholdVariance hp -
        ((p - 1 : ℕ) : ℝ) * ((2 * p - 1 : ℕ) : ℝ) / 6 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (allLagModulus p 1) :=
    ⟨by simpa [allLagModulus] using pow_ne_zero 2 hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have henergy :
      primeCarryEnergy hp =
        ∑ a : UnitClass (allLagModulus p 1),
          ‖primeCarryCentered hp (lagOneUnitAsPrimeSquare a)‖ ^ 2 := by
    unfold primeCarryEnergy
    exact (lagOneUnitAsPrimeSquareEquiv.sum_comp
      (fun a => ‖primeCarryCentered hp a‖ ^ 2)).symm
  have hvariance :
      primeThresholdVariance hp =
        ∑ a : UnitClass (allLagModulus p 1),
          rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a) ^ 2 := by
    unfold primeThresholdVariance
    exact (lagOneUnitAsPrimeSquareEquiv.sum_comp
      (fun a => rawPrimeCarryValue hp a ^ 2)).symm
  rw [henergy, hvariance]
  calc
    (∑ a : UnitClass (allLagModulus p 1),
        ‖primeCarryCentered hp (lagOneUnitAsPrimeSquare a)‖ ^ 2) =
        ∑ u : UnitClass p,
          ∑ a : Fiber (coarseUnitReduction p 1) u,
            ‖primeCarryCentered hp
              (lagOneUnitAsPrimeSquare a.val)‖ ^ 2 := by
                symm
                exact Fintype.sum_fiberwise (coarseUnitReduction p 1)
                  (fun a => ‖primeCarryCentered hp
                    (lagOneUnitAsPrimeSquare a)‖ ^ 2)
    _ = ∑ u : UnitClass p,
          ((∑ a : Fiber (coarseUnitReduction p 1) u,
              rawPrimeCarryValue hp
                (lagOneUnitAsPrimeSquare a.val) ^ 2) -
            ((p - u.val.val : ℕ) : ℝ) ^ 2 / (p : ℝ)) := by
              apply Finset.sum_congr rfl
              intro u _
              exact primeCarryCentered_fiber_squareMass hp hpodd u
    _ = (∑ u : UnitClass p,
          ∑ a : Fiber (coarseUnitReduction p 1) u,
            rawPrimeCarryValue hp
              (lagOneUnitAsPrimeSquare a.val) ^ 2) -
          ∑ u : UnitClass p,
            ((p - u.val.val : ℕ) : ℝ) ^ 2 / (p : ℝ) := by
              rw [Finset.sum_sub_distrib]
    _ = (∑ a : UnitClass (allLagModulus p 1),
          rawPrimeCarryValue hp (lagOneUnitAsPrimeSquare a) ^ 2) -
        ((p - 1 : ℕ) : ℝ) * ((2 * p - 1 : ℕ) : ℝ) / 6 := by
          congr 1
          · exact Fintype.sum_fiberwise (coarseUnitReduction p 1)
              (fun a => rawPrimeCarryValue hp
                (lagOneUnitAsPrimeSquare a) ^ 2)
          · exact primeClassMeanSquareCorrection hp

/-- The same normalization written through the integer half-centered table. -/
theorem primeCarryEnergy_eq_halfCentered_sub_classMean
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      (1 / 4 : ℝ) * primeHalfCenteredSquareMass hp -
        ((p - 1 : ℕ) : ℝ) * ((p - 2 : ℕ) : ℝ) / 12 := by
  rw [primeCarryEnergy_eq_thresholdVariance_sub_classMean hp hpodd,
    primeThresholdVariance_eq_halfCentered hp]
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p := hp.one_le
  have htwop : 1 ≤ 2 * p := by omega
  push_cast [Nat.cast_sub hp2, Nat.cast_sub hp1, Nat.cast_sub htwop]
  ring

end NField.Alignment.PrimeThresholdEnergyNormalization
