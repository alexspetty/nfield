/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.ClockRow
import NField.Alignment.CommonResetTeeth
import NField.Alignment.CommonResetHalfFrequencies
/-! # The actual binary clock source

Counts refer to the original harmonics 1 through p-1. Their bounds,
reflection and half-grid pairing retain the entire source.
-/

noncomputable section

namespace NField.ResetForests.ClockRows

open scoped BigOperators
open NField.Alignment
open CommonResetBernoulliLifts CommonResetTeeth CommonResetHalfFrequencies
open RademacherThreeTerm DedekindReciprocity

def prefixResidueCount {d : ℕ} (N : ℕ) (t : ZMod d) : ℕ :=
  ∑ j ∈ Finset.range N, if ((j+1 : ℕ) : ZMod d)=t then 1 else 0

theorem residue_count_bounds {d : ℕ} [NeZero d] (N : ℕ) (t : ZMod d) :
    N/d ≤ prefixResidueCount N t ∧ prefixResidueCount N t ≤ N/d+1 := by
  classical
  let f := fun j : ℕ => if ((j+1 : ℕ) : ZMod d)=t then (1 : ℕ) else 0
  have hshift (a j : ℕ) : f (a*d+j)=f j := by
    simp [f, Nat.cast_add, Nat.cast_mul]
  have hfull : (∑ j ∈ Finset.range d, f j)=1 := by
    rw [← sum_residue_values f]
    simp only [f, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    simp only [← eq_sub_iff_add_eq]
    simp
  have htail : (∑ j ∈ Finset.range (N%d), f j) ≤ 1 := by
    change (∑ j ∈ Finset.range (N%d), if ((j+1 : ℕ) : ZMod d)=t then (1 : ℕ) else 0)≤1
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haN, hat⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbN, hbt⟩ := Finset.mem_filter.mp hb
    have hr := Nat.mod_lt N (NeZero.pos d)
    have hal : a+1<d := by have := Finset.mem_range.mp haN; omega
    have hbl : b+1<d := by have := Finset.mem_range.mp hbN; omega
    have he := congrArg ZMod.val (hat.trans hbt.symm)
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hal, Nat.mod_eq_of_lt hbl] at he
    omega
  have hN : N=(N/d)*d+N%d := by simpa only [mul_comm] using (Nat.div_add_mod N d).symm
  have he : prefixResidueCount N t=N/d+(∑ j ∈ Finset.range (N%d), f j) := by
    unfold prefixResidueCount
    change (∑ j ∈ Finset.range N, f j)=_
    nth_rw 1 [hN]
    rw [Finset.sum_range_add, DedekindFourierMoment.sum_range_mul_blocks f]
    simp only [hshift, hfull, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range]
  rw [he]
  omega

def clockCount {d : ℕ} (p : ℕ) (v : ZMod d) : ℕ :=
  prefixResidueCount (p-1) ((p : ZMod d)*v)

theorem clock_count_literal {d : ℕ} (p : ℕ) (v : ZMod d) :
    clockCount p v =
      ((Finset.Ico 1 p).filter (fun j : ℕ => (j : ZMod d)=(p : ZMod d)*v)).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
  simp only [clockCount, prefixResidueCount, add_comm]

theorem clock_count_reflection {d p : ℕ} [NeZero d] (hp : 1 ≤ p) (v : ZMod d) :
    clockCount p (1-v)=clockCount p v := by
  unfold clockCount prefixResidueCount
  rw [← Finset.sum_range_reflect
    (fun j => if ((j+1 : ℕ) : ZMod d)=(p : ZMod d)*v then (1 : ℕ) else 0) (p-1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j+1 ≤ p := by have := Finset.mem_range.mp hj; omega
  have hidx : p-1-1-j+1=p-(j+1) := by have := Finset.mem_range.mp hj; omega
  rw [hidx, Nat.cast_sub hjp]
  have hi : ((j+1 : ℕ) : ZMod d)=(p : ZMod d)*(1-v) ↔
      (p : ZMod d)-((j+1 : ℕ) : ZMod d)=(p : ZMod d)*v := by
    constructor <;> intro h <;> linear_combination -h
  simp only [hi]

def clockGamma {d : ℕ} (p : ℕ) (v : ZMod d) : ℝ :=
  (clockCount p v : ℝ)-(clockCount p (v+1) : ℝ)

theorem clock_gamma_abs_le_one {d : ℕ} [NeZero d] (p : ℕ) (v : ZMod d) :
    |clockGamma p v| ≤ 1 := by
  have ha := residue_count_bounds (p-1) ((p : ZMod d)*v)
  have hb := residue_count_bounds (p-1) ((p : ZMod d)*(v+1))
  have ha0 : (((p-1)/d : ℕ) : ℝ) ≤ (clockCount p v : ℝ) := by exact_mod_cast ha.1
  have ha1 : (clockCount p v : ℝ) ≤ (((p-1)/d : ℕ) : ℝ)+1 := by exact_mod_cast ha.2
  have hb0 : (((p-1)/d : ℕ) : ℝ) ≤ (clockCount p (v+1) : ℝ) := by exact_mod_cast hb.1
  have hb1 : (clockCount p (v+1) : ℝ) ≤ (((p-1)/d : ℕ) : ℝ)+1 := by exact_mod_cast hb.2
  rw [clockGamma, abs_le]
  constructor <;> linarith

def gridCorrelation {d : ℕ} [NeZero d] (b v : ZMod d) : ℝ :=
  ∑ x : ZMod d, realSaw (v*x)*realSaw (b*x)

theorem grid_correlation_nat {d : ℕ} [NeZero d] (p a : ℕ) :
    gridCorrelation (p : ZMod d) (a : ZMod d) = Core.completeCorrelation p a d := by
  have hpoint (x : ZMod d) (c : ℕ) :
      realSaw ((c : ZMod d)*x)=(DedekindReciprocity.rationalSawtooth (c*x.val) d : ℝ) := by
    rw [← realSaw_nat]
    congr 1
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  unfold gridCorrelation
  simp_rw [hpoint]
  rw [sum_residue_values
    (fun x => (rationalSawtooth (a*x) d : ℝ)*(rationalSawtooth (p*x) d : ℝ))]
  unfold Core.completeCorrelation arithmeticCoefficientDedekindTerm
  push_cast
  rfl

theorem grid_correlation_odd {d : ℕ} [NeZero d] (b v : ZMod d) :
    gridCorrelation b (-v) = -gridCorrelation b v := by
  simp only [gridCorrelation, neg_mul, realSaw_odd, Finset.sum_neg_distrib]

theorem prime_square_correlation_pullback {d p : ℕ} [NeZero d]
    (hpd : p.Coprime d) (j : ZMod d) :
    gridCorrelation ((p^2 : ℕ) : ZMod d) j =
      gridCorrelation (p : ZMod d) ((ZMod.unitOfCoprime p hpd)⁻¹.val*j) := by
  let u := ZMod.unitOfCoprime p hpd
  let f := fun x : ZMod d => realSaw ((u⁻¹.val*j)*x)*realSaw ((p : ZMod d)*x)
  have he := Equiv.sum_comp u.mulLeft f
  have hpoint (x : ZMod d) : f (u.val*x)=realSaw (j*x)*realSaw (((p^2 : ℕ) : ZMod d)*x) := by
    have hfirst : (u⁻¹.val*j)*(u.val*x)=j*x := by
      calc
        _ = (u⁻¹.val*u.val)*(j*x) := by ring
        _ = _ := by simp
    have hsecond : (p : ZMod d)*(u.val*x)=(((p^2 : ℕ) : ZMod d)*x) := by
      dsimp [u]
      push_cast
      ring
    simp only [f, hfirst, hsecond]
  simp only [Units.mulLeft_apply, hpoint] at he
  exact he

theorem complete_clock_count_reading {d p : ℕ} [NeZero d] (hpd : p.Coprime d) :
    (∑ j ∈ Finset.Ico 1 p, Core.completeCorrelation (p^2) j d) =
      ∑ v : ZMod d, (clockCount p v : ℝ)*gridCorrelation (p : ZMod d) v := by
  classical
  let u := ZMod.unitOfCoprime p hpd
  have hpoint (a : ℕ) : Core.completeCorrelation (p^2) a d =
      gridCorrelation (p : ZMod d) (u⁻¹.val*(a : ZMod d)) := by
    rw [← grid_correlation_nat, prime_square_correlation_pullback hpd]
  simp_rw [hpoint]
  rw [Finset.sum_Ico_eq_sum_range]
  symm
  simp only [clockCount, prefixResidueCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he (v : ZMod d) : ((j+1 : ℕ) : ZMod d)=(p : ZMod d)*v ↔
      v=u⁻¹.val*((j+1 : ℕ) : ZMod d) := by
    have hu : (p : ZMod d)=u.val := (ZMod.coe_unitOfCoprime p hpd).symm
    constructor
    · intro h
      calc
        v = u⁻¹.val*((p : ZMod d)*v) := by rw [hu]; simp
        _ = _ := by rw [← h]
    · intro h
      rw [h, hu]
      simp [← mul_assoc]
  simp_rw [he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [add_comm 1 j]

theorem lower_residue_sum {d : ℕ} [NeZero d] (f : ZMod d → ℝ) :
    (∑ v ∈ lowerResidues d, f v) =
      ∑ a ∈ Finset.Icc 1 ((d-1)/2), f (a : ZMod d) := by
  unfold lowerResidues
  rw [Finset.sum_filter]
  have he : (∑ v : ZMod d, if 0<v.val ∧ 2*v.val<d then f v else 0) =
      ∑ a ∈ Finset.range d, if 0<a ∧ 2*a<d then f (a : ZMod d) else 0 := by
    have hp := sum_residue_values (m := d)
      (fun a => if 0<a ∧ 2*a<d then f (a : ZMod d) else 0)
    simpa only [ZMod.natCast_zmod_val] using hp
  rw [he, ← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

theorem binary_source_pairing {d p : ℕ} [NeZero d] (hp : 1 ≤ p)
    (R : ZMod d → ℝ) (hodd : ∀ v, R (-v)=-R v) :
    (∑ v : ZMod d, (clockCount p v : ℝ)*R v) =
      ∑ a ∈ Finset.Icc 1 ((d-1)/2), clockGamma p (a : ZMod d)*R (a : ZMod d) := by
  have hneg (v : ZMod d) : clockCount p (-v)=clockCount p (v+1) := by
    have h := clock_count_reflection hp (v+1)
    simpa only [show (1 : ZMod d)-(v+1)=-v by ring] using h
  have hG (v : ZMod d) : clockGamma p (-v)=-clockGamma p v := by
    unfold clockGamma
    rw [hneg, show -v+1=(1 : ZMod d)-v by ring, clock_count_reflection hp]
    ring
  have he := Equiv.sum_comp (Equiv.neg (ZMod d))
    (fun v => (clockCount p v : ℝ)*R v)
  simp only [Equiv.neg_apply, hneg, hodd, mul_neg, Finset.sum_neg_distrib] at he
  have hfull : (∑ v : ZMod d, clockGamma p v*R v) =
      2*(∑ v : ZMod d, (clockCount p v : ℝ)*R v) := by
    simp only [clockGamma, sub_mul, Finset.sum_sub_distrib]
    linarith
  have hpair := residue_sum_pair (fun v : ZMod d => clockGamma p v*R v)
    (by intro v; rw [hG, hodd, neg_mul_neg])
    (by
      intro v hv
      have hr := hodd v
      rw [hv] at hr
      have hz : R v=0 := by linarith
      rw [hz, mul_zero])
  rw [lower_residue_sum] at hpair
  linarith

theorem complete_clock_binary_source {d p : ℕ} [NeZero d]
    (hp : 1 ≤ p) (hpd : p.Coprime d) :
    (∑ j ∈ Finset.Icc 1 (p-1), Core.completeCorrelation (p^2) j d) =
      ∑ a ∈ Finset.Icc 1 ((d-1)/2),
        clockGamma p (a : ZMod d)*Core.completeCorrelation p a d := by
  have hset : Finset.Icc 1 (p-1)=Finset.Ico 1 p := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, complete_clock_count_reading hpd,
    binary_source_pairing hp _ (grid_correlation_odd (p : ZMod d))]
  simp_rw [grid_correlation_nat]

theorem whole_clock_work_bound {d p : ℕ} (hp : p.Prime)
    (hd : 2 ≤ d) (hdp : d < p) :
    |∑ j ∈ Finset.Icc 1 (p-1), Core.completeCorrelation (p^2) j d| ≤
      (d : ℝ)/4*(harmonic (d/2) : ℝ)^2 := by
  letI : NeZero d := ⟨by omega⟩
  have hpd := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega : 0 < d) hdp)
  rw [complete_clock_binary_source (by have := hp.two_le; omega) hpd]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 ((d-1)/2),
        |clockGamma p (a : ZMod d)*Core.completeCorrelation p a d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 ((d-1)/2), |Core.completeCorrelation p a d| := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (clock_gamma_abs_le_one p _) (abs_nonneg _)).trans_eq
        (one_mul _)
    _ ≤ ∑ a ∈ Finset.range d, |Core.completeCorrelation p a d| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        have h := Finset.mem_Icc.mp ha
        simp only [Finset.mem_range]
        omega
      · intro a _ _
        exact abs_nonneg _
    _ ≤ _ := complete_clock_row_estimate p d hp hd hdp

end NField.ResetForests.ClockRows
