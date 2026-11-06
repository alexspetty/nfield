/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetWeightedCurvature
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The precise row-of-teeth endpoint correction

The function used in Huxley's Lemma 3.3 is one half minus the fractional
part, including its value one half at integers. Its two-coefficient sum
therefore differs from the midpoint Dedekind sum by one quarter of the
common reset count. The mixed terms cancel by actual residue reflection.
-/

noncomputable section

namespace NField.Alignment.CommonResetTeeth

open scoped BigOperators Classical
open DedekindReciprocity CarryBoundarySpectra CommonResetBernoulliLifts RademacherThreeTerm

def realSaw {m : ℕ} (x : ZMod m) : ℝ := (centeredSawtooth x).re

def residueTeeth {m : ℕ} (x : ZMod m) : ℝ := 1/2-(x.val : ℝ)/m

def rationalTeeth (a m : ℕ) : ℝ := 1/2-((a%m : ℕ) : ℝ)/m

def teethCoefficient (x y m : ℕ) : ℝ :=
  ∑ a ∈ Finset.range m, rationalTeeth (x*a) m*rationalTeeth (y*a) m

theorem residueTeeth_decomposition {m : ℕ} [NeZero m] (x : ZMod m) :
    residueTeeth x = -realSaw x+(if x=0 then (1/2 : ℝ) else 0) := by
  unfold residueTeeth realSaw centeredSawtooth
  by_cases hx : x=0
  · simp [hx]
  · have hval : ((x.val : ℂ)/(m : ℂ)-1/2).re=(x.val : ℝ)/m-1/2 := by
      rw [show (x.val : ℂ)/(m : ℂ)-1/2=(((x.val : ℝ)/m-1/2 : ℝ) : ℂ) by
        push_cast
        rfl]
      rfl
    simp only [hx, if_false, hval]
    ring

theorem realSaw_odd {m : ℕ} [NeZero m] (x : ZMod m) : realSaw (-x)=-realSaw x := by
  by_cases hm : m=1
  · subst m
    have hx : x=0 := Subsingleton.elim _ _
    simp [hx, realSaw, centeredSawtooth]
  · have hm2 : 2 ≤ m := by have hp := NeZero.pos m; omega
    simpa only [realSaw, Complex.neg_re] using congrArg Complex.re (centeredSawtooth_neg hm2 x)

theorem saw_zero_cross_sum {m : ℕ} [NeZero m] (a b : ZMod m) :
    (∑ z : ZMod m, if a*z=0 then realSaw (b*z) else 0)=0 := by
  let f : ZMod m → ℝ := fun z => if a*z=0 then realSaw (b*z) else 0
  have he := Equiv.sum_comp (Equiv.neg (ZMod m)) f
  have hp (z : ZMod m) : f (-z)=-f z := by
    simp only [f, mul_neg, neg_eq_zero, realSaw_odd]
    split_ifs <;> ring
  simp only [Equiv.neg_apply, hp, Finset.sum_neg_distrib] at he
  change (∑ z : ZMod m, f z)=0
  linarith

theorem simultaneous_zero_iff {m : ℕ} [NeZero m] (a b : ℕ) (z : ZMod m) :
    (a : ZMod m)*z=0 ∧ (b : ZMod m)*z=0 ↔ (a.gcd b : ZMod m)*z=0 := by
  have he (c : ℕ) : (c : ZMod m)*z=0 ↔ m ∣ c*z.val := by
    nth_rw 1 [← ZMod.natCast_zmod_val z]
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  rw [he, he, he, ← Nat.dvd_gcd_iff, Nat.gcd_mul_right]

theorem simultaneous_zero_count {m : ℕ} [NeZero m] (a b : ℕ) :
    (Finset.univ.filter (fun z : ZMod m => (a : ZMod m)*z=0 ∧ (b : ZMod m)*z=0)).card=
      (a.gcd b).gcd m := by
  have he := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) (a.gcd b)
  simp only [Nat.card_eq_fintype_card, ZMod.card] at he
  have happ (x : ZMod m) : (nsmulAddMonoidHom (a.gcd b)) x=(a.gcd b) • x := rfl
  simpa only [simultaneous_zero_iff, Fintype.card_subtype, AddMonoidHom.mem_ker,
    happ, nsmul_eq_mul, Nat.gcd_comm] using he

theorem residue_teeth_pair {m : ℕ} [NeZero m] (a b : ℕ) :
    (∑ z : ZMod m, residueTeeth ((a : ZMod m)*z)*residueTeeth ((b : ZMod m)*z)) =
      (∑ z : ZMod m, realSaw ((a : ZMod m)*z)*realSaw ((b : ZMod m)*z))+
        ((a.gcd b).gcd m : ℝ)/4 := by
  have hp (z : ZMod m) : residueTeeth ((a : ZMod m)*z)*residueTeeth ((b : ZMod m)*z) =
      realSaw ((a : ZMod m)*z)*realSaw ((b : ZMod m)*z)-
        (if (a : ZMod m)*z=0 then realSaw ((b : ZMod m)*z) else 0)/2-
        (if (b : ZMod m)*z=0 then realSaw ((a : ZMod m)*z) else 0)/2+
        (if (a : ZMod m)*z=0 ∧ (b : ZMod m)*z=0 then (1 : ℝ) else 0)/4 := by
    rw [residueTeeth_decomposition, residueTeeth_decomposition]
    by_cases ha : (a : ZMod m)*z=0 <;> by_cases hb : (b : ZMod m)*z=0 <;>
      simp [ha, hb] <;> ring
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    saw_zero_cross_sum, zero_div, sub_zero]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    simultaneous_zero_count]

theorem realSaw_nat {m : ℕ} [NeZero m] (a : ℕ) :
    realSaw (a : ZMod m)=(rationalSawtooth a m : ℝ) := by
  have he := congrArg Complex.re (rationalSawtooth_val_eq_centeredSawtooth (a : ZMod m))
  simp only [ZMod.val_natCast, rationalSawtooth, Nat.mod_mod] at he
  simpa only [realSaw, rationalSawtooth, Complex.ratCast_re] using he.symm

/-- Title: `The actual row-of-teeth coefficient equals the midpoint coefficient plus the common-reset quarter`. -/
theorem teethCoefficient_exact {m : ℕ} (hm : 0 < m) (a b : ℕ) :
    teethCoefficient a b m=(arithmeticCoefficientDedekindTerm a b m : ℝ)+
      ((a.gcd b).gcd m : ℝ)/4 := by
  letI : NeZero m := ⟨hm.ne'⟩
  have he := residue_teeth_pair (m := m) a b
  have hleft : (∑ z : ZMod m, residueTeeth ((a : ZMod m)*z)*residueTeeth ((b : ZMod m)*z))=
      teethCoefficient a b m := by
    unfold teethCoefficient
    rw [← sum_residue_values]
    apply Finset.sum_congr rfl
    intro z hz
    unfold residueTeeth rationalTeeth
    have ha : ((a : ZMod m)*z).val=(a*z.val)%m := by
      nth_rw 1 [← ZMod.natCast_zmod_val z]
      rw [← Nat.cast_mul, ZMod.val_natCast]
    have hb : ((b : ZMod m)*z).val=(b*z.val)%m := by
      nth_rw 1 [← ZMod.natCast_zmod_val z]
      rw [← Nat.cast_mul, ZMod.val_natCast]
    rw [ha, hb]
  have hright : (∑ z : ZMod m, realSaw ((a : ZMod m)*z)*realSaw ((b : ZMod m)*z))=
      (arithmeticCoefficientDedekindTerm a b m : ℝ) := by
    unfold arithmeticCoefficientDedekindTerm
    push_cast
    rw [← sum_residue_values]
    apply Finset.sum_congr rfl
    intro z hz
    have hc (c : ℕ) : realSaw ((c : ZMod m)*z)=(rationalSawtooth (c*z.val) m : ℝ) := by
      calc
        _ = realSaw ((c*z.val : ℕ) : ZMod m) :=
          congrArg realSaw (by rw [Nat.cast_mul, ZMod.natCast_zmod_val])
        _ = _ := realSaw_nat _
    rw [hc, hc]
  rwa [hleft, hright] at he

end NField.Alignment.CommonResetTeeth
