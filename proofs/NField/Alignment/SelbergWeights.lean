/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Explicit truncated Selberg upper weights

Möbius inversion on the divisors constructs normalized weights with finite
support. The diagonalized main term is exactly the inverse normalizer;
unit divisor-count remainders give an error at most the fourth power of
the cutoff when inverse density is bounded by the divisor.

The finite lambda-square reindexing follows Mathlib's SelbergSieve module
by Arend Mellendijk (2024), released under Apache 2.0.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace NField.Alignment.SelbergWeights

theorem sum_multiples_complement {N l : ℕ} (hN : N ≠ 0) (hl : l ∣ N)
    (F : ℕ → ℝ) :
    (∑ d ∈ N.divisors, if l ∣ d then F d else 0) =
      ∑ e ∈ (N/l).divisors, F (N/e) := by
  rw [← Nat.sum_div_divisors N (fun d => if l ∣ d then F d else 0)]
  have heq : ∀ e ∈ N.divisors, l ∣ N/e ↔ e ∣ N/l := by
    intro e he
    rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors he),
      Nat.dvd_div_iff_mul_dvd hl, Nat.mul_comm]
  simp_rw [sum_congr rfl (fun e he => if_congr (heq e he) rfl rfl)]
  rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd hN (Nat.div_dvd_of_dvd hl)]

/-- Inverse of the sum over multiples on the divisors of `N`. -/
def multipleMobius (N : ℕ) (Y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ e ∈ (N/d).divisorsAntidiagonal, (μ e.1 : ℝ) * Y (N/e.2)

theorem sum_multipleMobius {N l : ℕ} (hN : N ≠ 0) (hl : l ∣ N)
    (Y : ℕ → ℝ) :
    (∑ d ∈ N.divisors, if l ∣ d then multipleMobius N Y d else 0) = Y l := by
  rw [sum_multiples_complement hN hl]
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => ∑ e ∈ n.divisorsAntidiagonal, (μ e.1 : ℝ) * Y (N/e.2))
    (g := fun n => Y (N/n))).mpr (fun _ _ => rfl)
  have hq : N/l ≠ 0 := ne_zero_of_dvd_ne_zero hN (Nat.div_dvd_of_dvd hl)
  calc
    (∑ e ∈ (N/l).divisors, multipleMobius N Y (N/e)) =
        ∑ e ∈ (N/l).divisors,
          ∑ x ∈ e.divisorsAntidiagonal, (μ x.1 : ℝ) * Y (N/x.2) := by
      apply sum_congr rfl
      intro e he
      have heN : e ∣ N := (Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hl)
      simp only [multipleMobius, Nat.div_div_self heN hN]
    _ = Y (N/(N/l)) := hinv _ (Nat.pos_of_ne_zero hq)
    _ = Y l := by rw [Nat.div_div_self hl hN]

theorem multipleMobius_one (N : ℕ) (Y : ℕ → ℝ) :
    multipleMobius N Y 1 = ∑ d ∈ N.divisors, (μ d : ℝ) * Y d := by
  simp only [multipleMobius, Nat.div_one]
  rw [Nat.sum_divisorsAntidiagonal' (fun d e => (μ d : ℝ) * Y (N/e))]
  exact Nat.sum_div_divisors N (fun d => (μ d : ℝ) * Y d)


theorem multipleMobius_eq_sum {N d : ℕ} (hN : N ≠ 0) (hd : d ∣ N)
    (Y : ℕ → ℝ) :
    multipleMobius N Y d =
      ∑ k ∈ N.divisors, if d ∣ k then (μ (k/d) : ℝ) * Y k else 0 := by
  rw [sum_multiples_complement hN hd, multipleMobius,
    Nat.sum_divisorsAntidiagonal' (fun k e => (μ k : ℝ) * Y (N/e))]
  simp only [Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- The positive truncated denominator in the Selberg main term. -/
def normalizer (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ z then s.selbergTerms d else 0

/-- Prescribed coordinates in the diagonalized quadratic form. -/
def target (s : BoundingSieve) (z : ℝ) (d : ℕ) : ℝ :=
  if (d : ℝ) ≤ z then (μ d : ℝ) * s.selbergTerms d / normalizer s z else 0

/-- Explicit truncated weights obtained by inversion on the divisor lattice. -/
def weight (s : BoundingSieve) (z : ℝ) (d : ℕ) : ℝ :=
  multipleMobius s.prodPrimes (target s z) d / s.nu d

theorem normalizer_nonneg (s : BoundingSieve) (z : ℝ) : 0 ≤ normalizer s z := by
  apply sum_nonneg
  intro d hd
  split_ifs
  · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
  · exact le_rfl

theorem one_le_normalizer (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    1 ≤ normalizer s z := by
  have h1 : (1 : ℕ) ∈ s.prodPrimes.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩
  have h := single_le_sum (f := fun d : ℕ =>
    if (d : ℝ) ≤ z then s.selbergTerms d else 0)
    (fun d hd => by
      split_ifs
      · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
      · exact le_rfl) h1
  simpa only [normalizer, Nat.cast_one, if_pos hz,
    s.selbergTerms_isMultiplicative.1] using h

theorem normalizer_pos (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    0 < normalizer s z := lt_of_lt_of_le zero_lt_one (one_le_normalizer s hz)

theorem weight_transform (s : BoundingSieve) (z : ℝ) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * weight s z d else 0) =
      target s z l := by
  have he : ∀ d ∈ s.prodPrimes.divisors,
      s.nu d * weight s z d = multipleMobius s.prodPrimes (target s z) d := by
    intro d hd
    unfold weight
    exact mul_div_cancel₀ _ (s.nu_ne_zero (Nat.dvd_of_mem_divisors hd))
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then multipleMobius s.prodPrimes (target s z) d else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [he d hd]
    _ = target s z l := sum_multipleMobius s.prodPrimes_ne_zero hl _

theorem moebius_target (s : BoundingSieve) (z : ℝ) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (μ d : ℝ) * target s z d =
      if (d : ℝ) ≤ z then s.selbergTerms d / normalizer s z else 0 := by
  have hm : (μ d : ℝ)^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  unfold target
  split_ifs
  · calc
      _ = (μ d : ℝ)^2 * s.selbergTerms d / normalizer s z := by ring
      _ = _ := by rw [hm, one_mul]
  · simp

theorem weight_one (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) : weight s z 1 = 1 := by
  unfold weight
  rw [s.nu_mult.1, div_one, multipleMobius_one]
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ z then s.selbergTerms d / normalizer s z else 0 := by
      apply sum_congr rfl
      intro d hd
      exact moebius_target s z (Nat.dvd_of_mem_divisors hd)
    _ = normalizer s z / normalizer s z := by
      rw [normalizer, sum_div]
      simp only [ite_div, zero_div]
    _ = 1 := div_self (normalizer_pos s hz).ne'

theorem mainSum_weight (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (weight s z)) = (normalizer s z)⁻¹ := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hG := (normalizer_pos s hz).ne'
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ z then s.selbergTerms d else 0) / normalizer s z ^ 2 := by
      apply sum_congr rfl
      intro d hd
      have hdN := Nat.dvd_of_mem_divisors hd
      rw [weight_transform s z hdN]
      have hg := (s.selbergTerms_pos hdN).ne'
      have hm : (μ d : ℝ)^2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_dvd_prodPrimes hdN)
      unfold target
      split_ifs
      · rw [div_pow, mul_pow, hm, one_mul]
        field_simp
      · simp
    _ = normalizer s z / normalizer s z ^ 2 := by rw [← sum_div]; rfl
    _ = (normalizer s z)⁻¹ := by field_simp


theorem abs_target (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    |target s z d| = if (d : ℝ) ≤ z then s.selbergTerms d / normalizer s z else 0 := by
  have hm : |(μ d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  unfold target
  split_ifs
  · rw [abs_div, abs_mul, hm, one_mul,
      abs_of_pos (s.selbergTerms_pos hd), abs_of_pos (normalizer_pos s hz)]
  · exact abs_zero

theorem sum_abs_target (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |target s z d|) = 1 := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ z then s.selbergTerms d / normalizer s z else 0 := by
      apply sum_congr rfl
      intro d hd
      exact abs_target s hz (Nat.dvd_of_mem_divisors hd)
    _ = normalizer s z / normalizer s z := by
      rw [normalizer, sum_div]
      simp only [ite_div, zero_div]
    _ = 1 := div_self (normalizer_pos s hz).ne'

theorem abs_weight_le (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∣ s.prodPrimes) : |weight s z d| ≤ (s.nu d)⁻¹ := by
  have hM : |multipleMobius s.prodPrimes (target s z) d| ≤ 1 := by
    rw [multipleMobius_eq_sum s.prodPrimes_ne_zero hd]
    calc
      _ ≤ ∑ k ∈ s.prodPrimes.divisors,
          |if d ∣ k then (μ (k/d) : ℝ) * target s z k else 0| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ s.prodPrimes.divisors, |target s z k| := by
        apply sum_le_sum
        intro k hk
        split_ifs
        · rw [abs_mul]
          have hm : |(μ (k/d) : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k/d)
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (abs_nonneg _)
        · simp only [abs_zero, abs_nonneg]
      _ = 1 := sum_abs_target s hz
  rw [weight, abs_div, abs_of_pos (s.nu_pos_of_dvd_prodPrimes hd), inv_eq_one_div]
  exact div_le_div_of_nonneg_right hM (s.nu_pos_of_dvd_prodPrimes hd).le

theorem weight_zero_of_lt (s : BoundingSieve) {z : ℝ} {d : ℕ}
    (hd : d ∣ s.prodPrimes) (hzd : z < (d : ℝ)) : weight s z d = 0 := by
  unfold weight
  rw [multipleMobius_eq_sum s.prodPrimes_ne_zero hd]
  suffices (∑ k ∈ s.prodPrimes.divisors,
      if d ∣ k then (μ (k/d) : ℝ) * target s z k else 0) = 0 by rw [this, zero_div]
  apply sum_eq_zero
  intro k hk
  by_cases hdk : d ∣ k
  · have hkpos : 0 < k := Nat.pos_of_mem_divisors hk
    have hdkR : (d : ℝ) ≤ k := by exact_mod_cast Nat.le_of_dvd hkpos hdk
    simp [hdk, target, not_le.mpr (hzd.trans_le hdkR)]
  · simp [hdk]

/-- Reindex the finite lambda-square expansion by its unique least common multiple.
This is the finite expansion used in Mathlib's Selberg sieve. -/
theorem sum_lambdaSquared (N : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ N.divisors, BoundingSieve.lambdaSquared w d) =
      (∑ d ∈ N.divisors, w d)^2 := by
  unfold BoundingSieve.lambdaSquared
  have hex : (∑ d ∈ N.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then w d1 * w d2 else 0) =
      ∑ d ∈ N.divisors, ∑ d1 ∈ N.divisors, ∑ d2 ∈ N.divisors,
        if d = Nat.lcm d1 d2 then w d1 * w d2 else 0 := by
    apply sum_congr rfl
    intro d hd
    rw [Nat.mem_divisors] at hd
    suffices ∀ d1 d2, (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
      simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter,
        ite_sum_zero, ← ite_and, this]
    simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
  rw [hex, sum_comm]
  simp_rw [sq, sum_mul, mul_sum]
  apply sum_congr rfl
  intro d1 hd1
  rw [sum_comm]
  apply sum_congr rfl
  intro d2 hd2
  have hlcm : d1.lcm d2 ∈ N.divisors := Nat.mem_divisors.mpr
    ⟨Nat.lcm_dvd_iff.mpr ⟨Nat.dvd_of_mem_divisors hd1, Nat.dvd_of_mem_divisors hd2⟩,
      (Nat.mem_divisors.mp hd1).2⟩
  exact sum_ite_eq_of_mem' _ _ _ hlcm

theorem abs_lambdaSquared_le (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤ BoundingSieve.lambdaSquared (fun k => |w k|) d := by
  unfold BoundingSieve.lambdaSquared
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  split_ifs <;> simp [abs_mul]

theorem errSum_le_sq (s : BoundingSieve) (w : ℕ → ℝ)
    (hr : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ 1) :
    s.errSum (BoundingSieve.lambdaSquared w) ≤ (∑ d ∈ s.prodPrimes.divisors, |w d|)^2 := by
  rw [← sum_lambdaSquared]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ |BoundingSieve.lambdaSquared w d| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (hr d (Nat.dvd_of_mem_divisors hd)) (abs_nonneg _)
    _ ≤ _ := abs_lambdaSquared_le w d


theorem sum_abs_weight_le (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z)
    (hnu : ∀ d, d ∣ s.prodPrimes → (s.nu d)⁻¹ ≤ (d : ℝ)) :
    (∑ d ∈ s.prodPrimes.divisors, |weight s z d|) ≤ z^2 := by
  let D := s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z)
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have hcard : D.card ≤ ⌊z⌋₊ := by
    calc
      D.card ≤ (Icc 1 ⌊z⌋₊).card := card_le_card (by
        intro d hd
        rcases mem_filter.mp hd with ⟨hdN, hdz⟩
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdN,
          (Nat.le_floor_iff hz0).mpr hdz⟩)
      _ = ⌊z⌋₊ := by simp
  calc
    _ = ∑ d ∈ D, |weight s z d| := by
      symm
      apply sum_subset (filter_subset _ _)
      intro d hdN hdD
      have hdz : z < (d : ℝ) := lt_of_not_ge (fun h => hdD (mem_filter.mpr ⟨hdN, h⟩))
      rw [weight_zero_of_lt s (Nat.dvd_of_mem_divisors hdN) hdz, abs_zero]
    _ ≤ ∑ d ∈ D, z := by
      apply sum_le_sum
      intro d hd
      rcases mem_filter.mp hd with ⟨hdN, hdz⟩
      exact (abs_weight_le s hz (Nat.dvd_of_mem_divisors hdN)).trans
        ((hnu d (Nat.dvd_of_mem_divisors hdN)).trans hdz)
    _ = (D.card : ℝ) * z := by simp
    _ ≤ (⌊z⌋₊ : ℝ) * z := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hz0
    _ ≤ z*z := mul_le_mul_of_nonneg_right (Nat.floor_le hz0) hz0
    _ = z^2 := by ring

theorem errSum_weight_le (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z)
    (hnu : ∀ d, d ∣ s.prodPrimes → (s.nu d)⁻¹ ≤ (d : ℝ))
    (hr : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ 1) :
    s.errSum (BoundingSieve.lambdaSquared (weight s z)) ≤ z^4 := by
  refine (errSum_le_sq s (weight s z) hr).trans ?_
  have h := sum_abs_weight_le s hz hnu
  have h0 : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, |weight s z d| :=
    sum_nonneg (fun _ _ => abs_nonneg _)
  nlinarith [sq_nonneg ((∑ d ∈ s.prodPrimes.divisors, |weight s z d|) - z^2)]

theorem siftedSum_le (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z)
    (hnu : ∀ d, d ∣ s.prodPrimes → (s.nu d)⁻¹ ≤ (d : ℝ))
    (hr : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ 1) :
    s.siftedSum ≤ s.totalMass / normalizer s z + z^4 := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared (weight s z) (weight_one s hz))
  rw [mainSum_weight s hz] at h
  exact h.trans (add_le_add le_rfl (errSum_weight_le s hz hnu hr))

end NField.Alignment.SelbergWeights
