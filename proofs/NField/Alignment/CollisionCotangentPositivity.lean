/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeCotangent
import NField.Alignment.CollisionSpectralSupport

/-!
# Strict positivity of the actual unit cotangent sum

Each complete residue block is paired with its complementary residues.
Cotangent and the difference of the reciprocal squares have the same
sign. The residue one gives a strict contribution when q>2. Passing to
the already convergent original series preserves a positive first block.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCotangentPositivity

open scoped BigOperators Topology
open Filter Finset
open CollisionCotangentSeries CollisionCotangentLValue CollisionFiniteSineTransform
open CollisionAmplitudeCotangent CollisionHarmonicSeed CollisionAmplitudeArithmetic CollisionJordanVariance

def unitCotangentResidue (q a : ℕ) : ℝ :=
  if a.Coprime q then Real.cot (Real.pi*(a : ℝ)/(q : ℝ)) else 0

def residueSquare (q m a : ℕ) : ℝ := 1/((a+m*q : ℕ) : ℝ)^2

def pairedCotangentResidue (q m a : ℕ) : ℝ :=
  unitCotangentResidue q a*(residueSquare q m a-residueSquare q m (q-a))

def cotangentBlock (q m : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico 1 q, unitCotangentTerm q (a+m*q)

theorem unitCotangentTerm_progression {q a : ℕ} (hq : 0<q)
    (ha : a∈Finset.Ico 1 q) (m : ℕ) :
    unitCotangentTerm q (a+m*q)=unitCotangentResidue q a*residueSquare q m a := by
  have ha0 := (Finset.mem_Ico.mp ha).1
  have haq := (Finset.mem_Ico.mp ha).2
  have hmod : (a+m*q)%q=a := by simp [Nat.add_mod,Nat.mod_eq_of_lt haq]
  have hdiv : ¬q∣a+m*q := by
    intro hd
    have he := Nat.mod_eq_zero_of_dvd hd
    rw [hmod] at he
    omega
  simp only [unitCotangentTerm,cotangentTerm,if_neg hdiv,
    Nat.coprime_add_mul_right_left,unitCotangentResidue]
  rw [← cotangent_mod hq (a+m*q),hmod]
  split_ifs <;> simp [residueSquare,div_eq_mul_inv]

theorem unitCotangentResidue_complement {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    unitCotangentResidue q (q-a)= -unitCotangentResidue q a := by
  simp only [unitCotangentResidue,Nat.coprime_self_sub_left ha,cotangent_complement hq ha]
  split_ifs <;> simp

theorem pairedCotangentResidue_complement {q a : ℕ} (hq : 0<q) (ha : a≤q) (m : ℕ) :
    pairedCotangentResidue q m (q-a)=pairedCotangentResidue q m a := by
  rw [pairedCotangentResidue,unitCotangentResidue_complement hq ha,
    Nat.sub_sub_self ha,pairedCotangentResidue]
  ring

theorem cotangentBlock_pairing {q : ℕ} (hq : 0<q) (m : ℕ) :
    cotangentBlock q m=(1/2 : ℝ)*∑ a ∈ Finset.Ico 1 q, pairedCotangentResidue q m a := by
  have hraw : cotangentBlock q m=
      ∑ a ∈ Finset.Ico 1 q, unitCotangentResidue q a*residueSquare q m a := by
    exact Finset.sum_congr rfl (fun a ha => unitCotangentTerm_progression hq ha m)
  have hcomp : (∑ a ∈ Finset.Ico 1 q, unitCotangentResidue q a*residueSquare q m (q-a))=
      -cotangentBlock q m := by
    calc
      _ = -(∑ a ∈ Finset.Ico 1 q, unitCotangentResidue q (q-a)*residueSquare q m (q-a)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        rw [unitCotangentResidue_complement hq (Finset.mem_Ico.mp ha).2.le]
        ring
      _ = _ := by
        rw [DedekindInverseResidueTransform.sum_Ico_one_complement q
          (fun a => unitCotangentResidue q a*residueSquare q m a),hraw]
  simp only [pairedCotangentResidue,mul_sub,Finset.sum_sub_distrib]
  rw [← hraw,hcomp]
  ring

theorem cotangent_nonneg_lower_half {q a : ℕ} (hq : 0<q) (ha : 0<a) (haq : 2*a≤q) :
    0 ≤ Real.cot (Real.pi*(a : ℝ)/(q : ℝ)) := by
  have hangle0 : 0<Real.pi*(a : ℝ)/(q : ℝ) := by positivity
  have hangle : Real.pi*(a : ℝ)/(q : ℝ)≤Real.pi/2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hq)).2
    have h := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr haq : (2*a : ℕ)≤(q : ℝ)) Real.pi_pos.le
    push_cast at h
    nlinarith
  rw [Real.cot_eq_cos_div_sin]
  exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hangle⟩)
    (Real.sin_nonneg_of_mem_Icc ⟨hangle0.le,by linarith [Real.pi_pos]⟩)

theorem cotangent_pos_lower_half {q a : ℕ} (hq : 0<q) (ha : 0<a) (haq : 2*a<q) :
    0 < Real.cot (Real.pi*(a : ℝ)/(q : ℝ)) := by
  have hangle0 : 0<Real.pi*(a : ℝ)/(q : ℝ) := by positivity
  have hangle : Real.pi*(a : ℝ)/(q : ℝ)<Real.pi/2 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hq)).2
    have h := mul_lt_mul_of_pos_left (Nat.cast_lt.mpr haq : ((2*a : ℕ) : ℝ)<(q : ℝ)) Real.pi_pos
    push_cast at h
    nlinarith
  rw [Real.cot_eq_cos_div_sin]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hangle⟩)
    (Real.sin_pos_of_pos_of_lt_pi hangle0 (by linarith [Real.pi_pos]))

theorem residueSquare_antitone {q m a b : ℕ} (ha : 0<a) (hab : a≤b) :
    residueSquare q m b≤residueSquare q m a := by
  unfold residueSquare
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr (Nat.add_le_add_right hab _)) 2

theorem residueSquare_strictAnti {q m a b : ℕ} (ha : 0<a) (hab : a<b) :
    residueSquare q m b<residueSquare q m a := by
  unfold residueSquare
  apply one_div_lt_one_div_of_lt (by positivity)
  have hlt : ((a+m*q : ℕ) : ℝ)<((b+m*q : ℕ) : ℝ) :=
    Nat.cast_lt.mpr (Nat.add_lt_add_right hab _)
  nlinarith [show (0 : ℝ)<((a+m*q : ℕ) : ℝ) by positivity]

theorem pairedCotangentResidue_nonneg_lower {q a : ℕ} (hq : 0<q) (ha : 0<a)
    (haq : 2*a≤q) (m : ℕ) : 0 ≤ pairedCotangentResidue q m a := by
  unfold pairedCotangentResidue unitCotangentResidue
  split_ifs
  · exact mul_nonneg (cotangent_nonneg_lower_half hq ha haq)
      (sub_nonneg.mpr (residueSquare_antitone ha (by omega : a≤q-a)))
  · simp

theorem pairedCotangentResidue_nonneg {q a : ℕ} (hq : 0<q)
    (ha : a∈Finset.Ico 1 q) (m : ℕ) : 0 ≤ pairedCotangentResidue q m a := by
  have ha0 := (Finset.mem_Ico.mp ha).1
  have haq := (Finset.mem_Ico.mp ha).2
  by_cases hh : 2*a≤q
  · exact pairedCotangentResidue_nonneg_lower hq ha0 hh m
  · rw [← pairedCotangentResidue_complement hq haq.le m]
    exact pairedCotangentResidue_nonneg_lower hq (by omega) (by omega) m

theorem pairedCotangentResidue_one_pos {q : ℕ} (hq : 2<q) (m : ℕ) :
    0 < pairedCotangentResidue q m 1 := by
  unfold pairedCotangentResidue unitCotangentResidue
  rw [if_pos (Nat.coprime_one_left q)]
  exact mul_pos (cotangent_pos_lower_half (by omega) (by omega) (by omega))
    (sub_pos.mpr (residueSquare_strictAnti (by omega) (by omega : 1<q-1)))

theorem cotangentBlock_pos {q : ℕ} (hq : 2<q) (m : ℕ) : 0 < cotangentBlock q m := by
  rw [cotangentBlock_pairing (by omega : 0<q)]
  apply mul_pos (by norm_num)
  apply Finset.sum_pos' (fun a ha => pairedCotangentResidue_nonneg (by omega) ha m)
  exact ⟨1,Finset.mem_Ico.mpr ⟨by omega,by omega⟩,pairedCotangentResidue_one_pos hq m⟩

theorem unitCotangentSum_block_limit {q : ℕ} (hq : 0<q) :
    Tendsto (fun n => ∑ m ∈ Finset.range n, cotangentBlock q m) atTop (𝓝 (unitCotangentSum q)) := by
  have ht := (unitCotangentTerm_summable hq).hasSum.tendsto_sum_nat.comp
    (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hq) tendsto_id)
  have heq (n : ℕ) : (∑ k ∈ Finset.range (n*q), unitCotangentTerm q k)=
      ∑ m ∈ Finset.range n, cotangentBlock q m := by
    rw [DedekindInverseResidueTransform.sum_range_mul_blocks hq,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply DedekindReciprocity.sum_range_eq_sum_Ico_one _ hq
    simp [unitCotangentTerm,cotangentTerm]
  simpa only [Function.comp_def,heq,unitCotangentSum] using ht

theorem unitCotangentSum_pos {q : ℕ} (hq : 2<q) : 0 < unitCotangentSum q := by
  have hlower : cotangentBlock q 0≤unitCotangentSum q := by
    apply ge_of_tendsto (unitCotangentSum_block_limit (by omega : 0<q))
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Finset.single_le_sum (fun m _ => (cotangentBlock_pos hq m).le)
      (Finset.mem_range.mpr hn)
  exact lt_of_lt_of_le (cotangentBlock_pos hq 0) hlower

theorem original_amplitude_strict_bounds {q : ℕ} (hq : 2<q) :
    0 < amplitude q ∧ amplitude q<1/2 := by
  refine ⟨CollisionSpectralSupport.amplitude_pos (by omega),?_⟩
  rw [literal_amplitude_cotangent (by omega : 1<q)]
  have hpos : 0<Real.pi/(2*(q : ℝ)*zetaThree*deltaThree q)*unitCotangentSum q :=
    mul_pos (div_pos Real.pi_pos (by positivity [zetaThree_pos,deltaThree_pos q]))
      (unitCotangentSum_pos hq)
  linarith

end NField.Alignment.CollisionCotangentPositivity
