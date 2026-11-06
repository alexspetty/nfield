/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMassInverse
import NField.Alignment.CollisionHarmonicSeed

/-!
# Absolute Möbius inversion over multiples for signed coefficients

Quadratic coefficient decay justifies both infinite rearrangements. The
values may be real, complex, or vectors in a complete real normed space.
This supplies the infinite arithmetic inversion step of the angular inverse.
-/

noncomputable section

namespace NField.Alignment.SignedMultipleInverse

open scoped BigOperators
open CollisionGeneralWeightCriterion CollisionMassInverse CollisionHarmonicSeed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def multipleAmplitude (f : ℕ → E) (q : ℕ) : E :=
  ∑' n, if q ∣ n then f n else 0

def inverseTerm (f : ℕ → E) (k : ℕ) (jn : ℕ × ℕ) : E :=
  (ArithmeticFunction.moebius jn.1 : ℝ) • (if k * jn.1 ∣ jn.2 then f jn.2 else 0)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem amplitude_as_multiples (f : ℕ → E) {q : ℕ} (hq : 0 < q) :
    multipleAmplitude f q = ∑' n, f (q * n) := by
  have hi : Function.Injective (fun n : ℕ => q * n) :=
    fun a b h => Nat.mul_left_cancel hq h
  have hh := hi.tsum_eq (f := fun n => if q ∣ n then f n else 0) (by
    intro n hn
    by_cases hd : q ∣ n
    · rcases hd with ⟨m, hm⟩
      exact ⟨m, hm.symm⟩
    · simp [Function.mem_support, hd] at hn)
  simpa only [multipleAmplitude, dvd_mul_right, if_true] using hh.symm

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Title: `Quadratic decay makes the coefficient norms summable`. -/
theorem quadratic_decay_norm_summable (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) : Summable (fun n => ‖f n‖) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg (f n)) hbound
  simpa only [mul_one_div] using hp.mul_left C

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem quadratic_decay_zero (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) : f 0 = 0 := by
  have h := hbound 0
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem norm_amplitude_bound (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) (q : ℕ) :
    generalAmplitude (fun n => ‖f n‖) q ≤
      (C * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) / (q : ℝ) ^ 2 := by
  by_cases hq : q = 0
  · simp [hq, generalAmplitude, quadratic_decay_zero f hbound]
  have hqpos := Nat.pos_of_ne_zero hq
  have hs := quadratic_decay_norm_summable f hbound
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  rw [generalAmplitude, ← tsum_multiples hqpos]
  calc
    (∑' n, ‖f (q * n)‖) ≤
        ∑' n : ℕ, (C / (q : ℝ) ^ 2) * (1 / (n : ℝ) ^ 2) := by
      apply (hs.comp_injective (fun a b h => Nat.mul_left_cancel hqpos h)).tsum_le_tsum _
        (hp.mul_left (C / (q : ℝ) ^ 2))
      intro n
      have h := hbound (q * n)
      simpa only [Function.comp_def, Nat.cast_mul, mul_pow, div_mul_eq_div_mul_one_div] using h
    _ = _ := by rw [tsum_mul_left]; ring

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem norm_amplitudes_summable (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) :
    Summable (generalAmplitude (fun n => ‖f n‖)) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le
    (fun q => generalAmplitude_nonneg _ (fun n => norm_nonneg (f n)) q)
    (norm_amplitude_bound f hbound)
  simpa only [mul_one_div] using hp.mul_left (C * ∑' n : ℕ, 1 / (n : ℝ) ^ 2)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem amplitude_norm_le (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) (q : ℕ) :
    ‖multipleAmplitude f q‖ ≤ generalAmplitude (fun n => ‖f n‖) q := by
  have hs := generalAmplitude_summable _ (fun n => norm_nonneg (f n))
    (quadratic_decay_norm_summable f hbound) q
  have he (n : ℕ) : ‖if q ∣ n then f n else 0‖ = if q ∣ n then ‖f n‖ else 0 := by
    split_ifs <;> simp
  have hs' : Summable (fun n => ‖if q ∣ n then f n else 0‖) := by
    simpa only [he] using hs
  simpa only [multipleAmplitude, generalAmplitude, he] using
    norm_tsum_le_tsum_norm hs'

omit [CompleteSpace E] in
/-- Title: `The Möbius inverse over multiples converges absolutely`. -/
theorem inverse_series_norm_summable (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) {k : ℕ} (hk : 0 < k) :
    Summable (fun j => ‖(ArithmeticFunction.moebius j : ℝ) • multipleAmplitude f (k * j)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => ?_)
    ((norm_amplitudes_summable f hbound).comp_injective
      (fun a b h => Nat.mul_left_cancel hk h))
  rw [norm_smul]
  exact ((mul_le_mul_of_nonneg_right (moebius_real_norm_le j) (norm_nonneg _)).trans_eq
    (one_mul _)).trans (amplitude_norm_le f hbound (k * j))

theorem inverse_term_summable (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) {k : ℕ} (hk : 0 < k) :
    Summable (inverseTerm f k) := by
  have hs := quadratic_decay_norm_summable f hbound
  have hpos : ∀ jn : ℕ × ℕ, 0 ≤
      (if k * jn.1 ∣ jn.2 then ‖f jn.2‖ else 0) := by
    intro jn
    split_ifs <;> positivity
  have hmajor : Summable
      (fun jn : ℕ × ℕ => if k * jn.1 ∣ jn.2 then ‖f jn.2‖ else 0) := by
    apply (summable_prod_of_nonneg hpos).mpr
    refine ⟨fun j => generalAmplitude_summable _ (fun n => norm_nonneg (f n)) hs (k * j), ?_⟩
    exact (norm_amplitudes_summable f hbound).comp_injective
      (fun a b h => Nat.mul_left_cancel hk h)
  apply Summable.of_norm_bounded hmajor
  intro jn
  unfold inverseTerm
  rw [norm_smul]
  split_ifs
  · exact (mul_le_mul_of_nonneg_right (moebius_real_norm_le jn.1) (norm_nonneg _)).trans_eq
      (one_mul _)
  · simp

omit [CompleteSpace E] in
theorem inverse_term_column (f : ℕ → E) (h0 : f 0 = 0)
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (∑' j, inverseTerm f k (j, n)) = if n = k then f k else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [inverseTerm, h0, hk.ne'.symm]
  have hp (j : ℕ) : inverseTerm f k (j, n) =
      (if k * j ∣ n then (ArithmeticFunction.moebius j : ℝ) else 0) • f n := by
    unfold inverseTerm
    split_ifs <;> simp
  simp_rw [hp]
  have hc : Summable (fun j : ℕ =>
      if k * j ∣ n then (ArithmeticFunction.moebius j : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := n.divisors)
    intro j hj
    rw [if_neg]
    intro hdiv
    exact hj (Nat.mem_divisors.mpr ⟨(Nat.dvd_mul_left j k).trans hdiv, hn⟩)
  rw [hc.tsum_smul_const, moebius_multiple_sum hk (Nat.pos_of_ne_zero hn)]
  split_ifs with hnk
  · simp [hnk]
  · simp

/-- Title: `Absolute Möbius inversion over multiples under quadratic decay`.

 The signed, absolutely justified inverse needed for arithmetic Fourier recovery. -/
theorem quadratic_decay_multiple_inverse (f : ℕ → E) {C : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ C / (n : ℝ) ^ 2) {k : ℕ} (hk : 0 < k) :
    f k = ∑' j, (ArithmeticFunction.moebius j : ℝ) • multipleAmplitude f (k * j) := by
  have hs := inverse_term_summable f hbound hk
  have h0 := quadratic_decay_zero f hbound
  have hrow (j : ℕ) : (∑' n, inverseTerm f k (j, n)) =
      (ArithmeticFunction.moebius j : ℝ) • multipleAmplitude f (k * j) := by
    unfold inverseTerm multipleAmplitude
    exact tsum_const_smul'' (f := fun n : ℕ => if k * j ∣ n then f n else 0)
      (ArithmeticFunction.moebius j : ℝ)
  have hu : Summable (Function.uncurry (fun j n => inverseTerm f k (j, n))) := hs
  calc
    f k = ∑' n, ∑' j, inverseTerm f k (j, n) := by
      simp_rw [inverse_term_column f h0 hk]
      simp
    _ = ∑' j, ∑' n, inverseTerm f k (j, n) := hu.tsum_comm
    _ = _ := tsum_congr hrow

end NField.Alignment.SignedMultipleInverse
