/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSawtoothDistribution
import NField.Alignment.CollisionResiduePairing
import NField.Alignment.CollisionParityRows

/-!
# The literal profinite Dedekind pairing

The rows are the real midpoint sawtooth evaluated on the actual profinite
residues. Generalized CRT and the endpoint-complete multiplication formula
reduce their Haar pairing to the Dedekind sum on the common residue group.
Both multipliers are actual units; reduction supplies the inverse used in
the Dedekind argument. Positive periods one and common gcd one are included.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDedekindPairing

open scoped BigOperators Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionCharacterStructure
open CarryBoundarySpectra DedekindCollisionKernel CollisionSawtoothDistribution
open CollisionResiduePairing CollisionParityRows

def midpointSawtooth {d : ℕ} [NeZero d] (r : ZMod d) : ℝ :=
  (centeredSawtooth r).re

theorem midpointSawtooth_formula {d : ℕ} [NeZero d] (r : ZMod d) :
    midpointSawtooth r = if r = 0 then 0 else (r.val : ℝ) / d - 1/2 := by
  unfold midpointSawtooth centeredSawtooth
  split_ifs
  · rfl
  · simp only [Complex.sub_re, Complex.div_natCast_re, Complex.natCast_re,
      Complex.div_ofNat_re, Complex.one_re]

theorem midpointSawtooth_complex {d : ℕ} [NeZero d] (r : ZMod d) :
    (midpointSawtooth r : ℂ) = centeredSawtooth r := by
  rw [midpointSawtooth_formula]
  unfold centeredSawtooth
  split_ifs <;> push_cast <;> rfl

def twistedSawtooth {d : ℕ} [NeZero d] (a : UnitClass d) (x : Phase) : ℝ :=
  midpointSawtooth (a.val * (residueHom d x).toAdd)

theorem twistedSawtooth_one {d : ℕ} [NeZero d] (x : Phase) :
    twistedSawtooth (1 : UnitClass d) x = sawtoothPhase d x := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  simp [twistedSawtooth, midpointSawtooth_formula, sawtoothPhase, hd]

theorem twistedSawtooth_integer {d : ℕ} [NeZero d] (a : UnitClass d) (n : ℤ) :
    twistedSawtooth a (integerPhase n) = midpointSawtooth (a.val * (n : ZMod d)) := by
  rw [twistedSawtooth, residue_integer]

def realDedekindSum {d : ℕ} [NeZero d] (h : UnitClass d) : ℝ :=
  ∑ t : ZMod d, midpointSawtooth t * midpointSawtooth (h.val * t)

theorem realDedekindSum_complex {d : ℕ} [NeZero d] (h : UnitClass d) :
    (realDedekindSum h : ℂ) = dedekindSum h := by
  simp only [realDedekindSum, Complex.ofReal_sum, Complex.ofReal_mul,
    midpointSawtooth_complex, dedekindSum]

theorem twisted_dedekind_sum {q : ℕ} [NeZero q] (a b : UnitClass q) :
    (∑ t : ZMod q, centeredSawtooth (a.val * t) *
      centeredSawtooth (b.val * t)) = dedekindSum (b * a⁻¹) := by
  have hreindex := Equiv.sum_comp (a⁻¹.mulLeft)
    (fun t : ZMod q => centeredSawtooth (a.val * t) * centeredSawtooth (b.val * t))
  rw [← hreindex, dedekindSum]
  apply Finset.sum_congr rfl
  intro t _
  change centeredSawtooth (a.val * (a⁻¹.val * t)) *
    centeredSawtooth (b.val * (a⁻¹.val * t)) = _
  rw [← mul_assoc a.val, ← Units.val_mul]
  simp [Units.val_mul, mul_assoc]

theorem gcd_lcm_scalar {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (1 / (d.lcm e : ℂ)) = (d.gcd e : ℂ) / ((d : ℂ) * e) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hlC : (d.lcm e : ℂ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hd he).ne'
  have hprod : (d.gcd e : ℂ) * (d.lcm e : ℂ) = (d : ℂ) * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  field_simp [hdC, heC, hlC]
  simpa only [mul_comm] using hprod.symm

theorem twisted_pair_complex {d e : ℕ} [NeZero d] [NeZero e]
    [NeZero (d.gcd e)] (a : UnitClass d) (b : UnitClass e) :
    (∫ x, centeredSawtooth (a.val * (residueHom d x).toAdd) *
      centeredSawtooth (b.val * (residueHom e x).toAdd) ∂phaseHaar) =
      ((d.gcd e : ℂ) / ((d : ℂ) * e)) *
        dedekindSum (reduceUnit (Nat.gcd_dvd_right d e) b *
          (reduceUnit (Nat.gcd_dvd_left d e) a)⁻¹) := by
  rw [residue_table_pair_fibers
    (fun t => centeredSawtooth (a.val * t)) (fun t => centeredSawtooth (b.val * t))]
  simp_rw [twisted_sawtooth_fiber]
  rw [twisted_dedekind_sum,
    gcd_lcm_scalar (Nat.pos_of_ne_zero (NeZero.ne d))
      (Nat.pos_of_ne_zero (NeZero.ne e))]

theorem literal_dedekind_pairing {d e : ℕ} [NeZero d] [NeZero e]
    (a : UnitClass d) (b : UnitClass e) :
    letI : NeZero (d.gcd e) :=
      ⟨(Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero (NeZero.ne d))).ne'⟩
    (∫ x, twistedSawtooth a x * twistedSawtooth b x ∂phaseHaar) =
      ((d.gcd e : ℝ) / ((d : ℝ) * e)) *
        realDedekindSum (reduceUnit (Nat.gcd_dvd_right d e) b *
          (reduceUnit (Nat.gcd_dvd_left d e) a)⁻¹) := by
  letI : NeZero (d.gcd e) :=
    ⟨(Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero (NeZero.ne d))).ne'⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    realDedekindSum_complex, twistedSawtooth, midpointSawtooth_complex]
  exact twisted_pair_complex a b

def periodicSawtooth (z : ℝ) : ℝ :=
  if Int.fract z = 0 then 0 else Int.fract z - 1/2

theorem midpointSawtooth_natCast {d : ℕ} [NeZero d] (n : ℕ) :
    midpointSawtooth (n : ZMod d) =
      if n % d = 0 then 0 else ((n % d : ℕ) : ℝ) / d - 1/2 := by
  rw [midpointSawtooth_formula]
  simp only [ZMod.val_natCast, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

theorem midpointSawtooth_fract {d : ℕ} [NeZero d] (n : ℕ) :
    midpointSawtooth (n : ZMod d) = periodicSawtooth ((n : ℝ) / d) := by
  rw [midpointSawtooth_natCast, periodicSawtooth, Int.fract_div_natCast_eq_div_natCast_mod]
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hz : ((n % d : ℕ) : ℝ) / (d : ℝ) = 0 ↔ n % d = 0 := by
    rw [div_eq_zero_iff]
    simp only [hd, or_false, Nat.cast_eq_zero]
  simp only [hz]

theorem twistedSawtooth_literal {d : ℕ} [NeZero d] (a : UnitClass d) (x : Phase) :
    twistedSawtooth a x = periodicSawtooth
      ((a.val.val : ℝ) * (residueHom d x).toAdd.val / (d : ℝ)) := by
  have hr : a.val * (residueHom d x).toAdd =
      ((a.val.val * (residueHom d x).toAdd.val : ℕ) : ZMod d) := by simp
  rw [twistedSawtooth, hr, midpointSawtooth_fract, Nat.cast_mul]

theorem realDedekindSum_literal {d : ℕ} [NeZero d] (h : UnitClass d) :
    realDedekindSum h = ∑ t ∈ Finset.range d,
      periodicSawtooth ((t : ℝ) / d) *
        periodicSawtooth ((h.val.val : ℝ) * t / (d : ℝ)) := by
  have he (t : ZMod d) : midpointSawtooth t * midpointSawtooth (h.val * t) =
      periodicSawtooth ((t.val : ℝ) / d) *
        periodicSawtooth ((h.val.val : ℝ) * t.val / (d : ℝ)) := by
    have ht : t = (t.val : ZMod d) := (ZMod.natCast_zmod_val t).symm
    have hmul : h.val * t = ((h.val.val * t.val : ℕ) : ZMod d) := by simp
    rw [hmul, midpointSawtooth_fract, Nat.cast_mul]
    congr 1
    conv_lhs => rw [ht, midpointSawtooth_fract]
  rw [realDedekindSum]
  simp_rw [he]
  exact sum_zmod_val d (fun t => periodicSawtooth ((t : ℝ) / d) *
    periodicSawtooth ((h.val.val : ℝ) * t / (d : ℝ)))

theorem midpointSawtooth_mod_one (r : ZMod 1) : midpointSawtooth r = 0 := by
  have hr : r = 0 := Subsingleton.elim _ _
  simp [midpointSawtooth_formula, hr]

theorem twistedSawtooth_period_one (a : UnitClass 1) (x : Phase) :
    twistedSawtooth a x = 0 := midpointSawtooth_mod_one _

theorem realDedekindSum_mod_one (h : UnitClass 1) : realDedekindSum h = 0 := by
  simp [realDedekindSum, midpointSawtooth_mod_one]

theorem realDedekindSum_eq_zero_of_period_one {d : ℕ} [NeZero d]
    (hd : d = 1) (h : UnitClass d) : realDedekindSum h = 0 := by
  subst d
  exact realDedekindSum_mod_one h

theorem dedekind_pairing_coprime {d e : ℕ} [NeZero d] [NeZero e]
    (hde : d.Coprime e) (a : UnitClass d) (b : UnitClass e) :
    (∫ x, twistedSawtooth a x * twistedSawtooth b x ∂phaseHaar) = 0 := by
  letI : NeZero (d.gcd e) := ⟨by rw [hde.gcd_eq_one]; decide⟩
  rw [literal_dedekind_pairing,
    realDedekindSum_eq_zero_of_period_one hde.gcd_eq_one, mul_zero]

end NField.Alignment.CollisionDedekindPairing
