/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimitiveFourier
import NField.Alignment.DigitHistogramFourierEnergy

/-!
# Primitive cosecant-square identity

Finite Parseval for the actual centered remainder row gives the complete
cosecant sum. Reduction of rational addresses and divisor inversion then
give the primitive-denominator identity, independently of infinite Fourier
completeness.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCosecantIdentity

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionRemainderCovariance
open CollisionPrimitiveFourier DedekindFourierMoment
open CollisionReciprocalBudget CollisionJordanVariance

def rangeDFT (q a : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range q, F n * negativeRoot q a ^ n

theorem rangeDFT_eq_dft {q : ℕ} [NeZero q] (a : ℕ) (F : ℕ → ℂ) :
    rangeDFT q a F = ZMod.dft (fun x : ZMod q => F x.val) (a : ZMod q) := by
  rw [rangeDFT, ZMod.dft_apply]
  rw [← CollisionRamanujan.sum_zmod_val_complex]
  apply Finset.sum_congr rfl
  intro x _
  rw [negativeRoot_eq_stdAddChar]
  have he : - (x * (a : ZMod q)) = x.val • (-(a : ZMod q)) := by
    simp [nsmul_eq_mul]
  rw [he, AddChar.map_nsmul_eq_pow]
  simp [smul_eq_mul, mul_comm]

theorem rangeDFT_parseval {q : ℕ} (hq : 0 < q) (F : ℕ → ℂ) :
    (∑ a ∈ Finset.range q, ‖rangeDFT q a F‖^2) =
      (q : ℝ) * ∑ n ∈ Finset.range q, ‖F n‖^2 := by
  letI : NeZero q := ⟨hq.ne'⟩
  have h := zmodDft_parseval_complex (fun x : ZMod q => F x.val)
  have he := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, neg_mul, sub_neg_eq_add, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] at he
  simp_rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq] at he
  rw [← ProfiniteRemainderMeasure.sum_zmod_val q (fun a => ‖rangeDFT q a F‖^2),
    ← ProfiniteRemainderMeasure.sum_zmod_val q (fun a => ‖F a‖^2)]
  simpa only [rangeDFT_eq_dft, ZMod.natCast_zmod_val] using he

theorem centeredDFT_zero {q : ℕ} (hq : 0 < q) :
    rangeDFT q 0 (fun n => (centeredRemainder q n : ℂ)) = 0 := by
  simp only [rangeDFT, negativeRoot, Nat.cast_zero, mul_zero, zero_div,
    neg_zero, Complex.exp_zero, one_pow, mul_one]
  rw [← Complex.ofReal_sum, centered_cycle_sum hq, Complex.ofReal_zero]

theorem centeredDFT_nonzero {q a : ℕ} (hq : 0 < q) (ha : 0 < a) (haq : a < q) :
    rangeDFT q a (fun n => (centeredRemainder q n : ℂ)) =
      -(q : ℂ)/(1-negativeRoot q a) := by
  let z := negativeRoot q a
  have hz : z ≠ 1 := negativeRoot_ne_one hq ha haq
  have hp : z^q=1 := negativeRoot_pow_modulus hq
  have hs : (∑ n ∈ Finset.range q, z^n)=0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hz.symm)
    rw [mul_zero, mul_neg_geom_sum, hp, sub_self]
  have ht (n : ℕ) (hn : n ∈ Finset.range q) :
      (centeredRemainder q n : ℂ)*z^n =
        (n : ℂ)*z^n - (((q : ℂ)-1)/2)*z^n := by
    rw [centeredRemainder, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
    push_cast
    ring
  change (∑ n ∈ Finset.range q, (centeredRemainder q n : ℂ)*z^n) = _
  rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hs, mul_zero, sub_zero]
  apply (eq_div_iff (sub_ne_zero.mpr hz.symm)).mpr
  simpa only [mul_comm] using weighted_geometric_sum hp hz

def chordEnergy (q a : ℕ) : ℝ := (‖1-negativeRoot q a‖^2)⁻¹

def primitiveChordEnergy (q : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Ico 1 q).filter (fun a => a.Coprime q), chordEnergy q a

theorem centeredDFT_norm_sq {q a : ℕ} (hq : 0 < q) (ha : 0 < a) (haq : a < q) :
    ‖rangeDFT q a (fun n => (centeredRemainder q n : ℂ))‖^2 =
      (q : ℝ)^2*chordEnergy q a := by
  rw [centeredDFT_nonzero hq ha haq, norm_div, norm_neg, Complex.norm_natCast, div_pow]
  rfl

theorem complete_chord_sum {q : ℕ} (hq : 0 < q) :
    (∑ a ∈ Finset.Ico 1 q, chordEnergy q a) = ((q : ℝ)^2-1)/12 := by
  have hp := rangeDFT_parseval hq (fun n => (centeredRemainder q n : ℂ))
  have hnorm (n : ℕ) : ‖(centeredRemainder q n : ℂ)‖^2 = centeredRemainder q n^2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hnorm, centered_cycle_square] at hp
  have hI : (Finset.range q).erase 0 = Finset.Ico 1 q := by
    ext a; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]; omega
  have he := Finset.sum_erase_add (Finset.range q)
    (fun a => ‖rangeDFT q a (fun n => (centeredRemainder q n : ℂ))‖^2)
    (Finset.mem_range.mpr hq : 0 ∈ Finset.range q)
  rw [hI, centeredDFT_zero hq, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at he
  rw [← he] at hp
  have ht (a : ℕ) (ha : a ∈ Finset.Ico 1 q) :
      ‖rangeDFT q a (fun n => (centeredRemainder q n : ℂ))‖^2 =
        (q : ℝ)^2*chordEnergy q a :=
    centeredDFT_norm_sq hq (Finset.mem_Ico.mp ha).1 (Finset.mem_Ico.mp ha).2
  rw [Finset.sum_congr rfl ht, ← Finset.mul_sum] at hp
  have hqR : (q : ℝ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  apply mul_left_cancel₀ hqR
  rw [hp]
  ring

theorem primitive_chord_divisors {q : ℕ} (hq : 0 < q) :
    (∑ d ∈ q.divisors, primitiveChordEnergy d) =
      ∑ a ∈ Finset.Ico 1 q, chordEnergy q a := by
  change (∑ d ∈ q.divisors, ∑ a ∈ (Finset.Ico 1 d).filter (fun a => a.Coprime d),
    chordEnergy d a) = _
  rw [← Finset.sum_sigma q.divisors
    (fun d => (Finset.Ico 1 d).filter (fun a => a.Coprime d))
    (fun p => chordEnergy p.1 p.2)]
  change (∑ p ∈ primitiveAddresses q, chordEnergy p.1 p.2) = _
  symm
  apply Finset.sum_bij (fun a _ => reducedAddress q a)
  · intro a ha; exact reducedAddress_mem ha
  · intro a ha b hb he
    have hr := congrArg (fun p : Σ _ : ℕ, ℕ => (q/p.1)*p.2) he
    simpa only [reducedAddress_restore ha, reducedAddress_restore hb] using hr
  · intro p hp
    exact ⟨(q/p.1)*p.2, (primitiveAddress_restore p hp).1, (primitiveAddress_restore p hp).2⟩
  · intro a ha
    have hg := Nat.gcd_pos_of_pos_left q (Finset.mem_Ico.mp ha).1
    have hgC : (a.gcd q : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    simp only [chordEnergy, reducedAddress, negativeRoot]
    congr 4
    rw [Nat.cast_div (Nat.gcd_dvd_left a q) hgC,
      Nat.cast_div (Nat.gcd_dvd_right a q) hgC]
    field_simp

theorem primitive_chord_sum {q : ℕ} (hq : 2 ≤ q) :
    primitiveChordEnergy q = jordanTwo q/12 := by
  let f : ℕ → ℝ := fun n => (jordanTwo n-(if n=1 then 1 else 0))/12
  have hs (n : ℕ) (hn : 0 < n) :
      (∑ d ∈ n.divisors, primitiveChordEnergy d) = ∑ d ∈ n.divisors, f d := by
    rw [primitive_chord_divisors hn, complete_chord_sum hn]
    simp only [f, ← Finset.sum_div, Finset.sum_sub_distrib, sum_jordanTwo_divisors]
    simp [Nat.one_mem_divisors.mpr hn.ne']
  have he := divisor_sums_injective primitiveChordEnergy f hs q (by omega)
  simpa [f, show q ≠ 1 by omega] using he

theorem chordEnergy_eq_cosecant {q : ℕ} (hq : 0 < q) (a : ℕ) :
    chordEnergy q a = (Real.sin (Real.pi*(a : ℝ)/(q : ℝ))^2)⁻¹/4 := by
  rw [chordEnergy, norm_one_sub_negativeRoot hq, mul_pow, sq_abs, mul_inv_rev]
  norm_num
  ring

/-- The supporting primitive cosecant-square formula, with all endpoints fixed. -/
theorem primitive_cosecant_square {q : ℕ} (hq : 2 ≤ q) :
    (∑ a ∈ (Finset.Ico 1 q).filter (fun a => a.Coprime q),
      (Real.sin (Real.pi*(a : ℝ)/(q : ℝ))^2)⁻¹) = jordanTwo q/3 := by
  have he := primitive_chord_sum hq
  simp only [primitiveChordEnergy, chordEnergy_eq_cosecant (by omega : 0 < q),
    ← Finset.sum_div] at he
  linarith

end NField.Alignment.CollisionCosecantIdentity
