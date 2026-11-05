/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudePolynomialMoment
import NField.Alignment.DivisorSmallPowerBound
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Bounds for the exact finite fourth-moment formula

This module keeps the literal coefficients, positive index intervals and
ordered off-diagonal pairs from the paper. The diagonal is controlled by
the proved divisor-square series.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeFourthMomentBound

open scoped BigOperators
open NField.Alignment.MagnitudePolynomialMoment
open NField.Alignment.DivisorSmallPowerBound
open NField.Alignment.CollisionPeriodicLValue
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.SpectralRepulsion

theorem coefficient_diagonal_bound (T U : ℕ) :
    (∑ u ∈ Finset.Icc 1 U, coefficient T u ^ 2) ≤
      ∑' n : ℕ, divisorSquareWeight n := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 U, divisorSquareWeight u := by
      apply Finset.sum_le_sum
      intro u _
      unfold divisorSquareWeight
      rw [← div_pow]
      exact pow_le_pow_left₀ (coefficient_nonneg T u) (coefficient_le_divisor_weight T u) 2
    _ ≤ _ := divisor_square_sum_le _

theorem ordered_off_diagonal_split (q : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) :
    (∑ u ∈ s, ∑ v ∈ s with u%q=v%q ∧ u≠v, c u*c v) =
      2 * ∑ u ∈ s, ∑ v ∈ s with u%q=v%q ∧ u<v, c u*c v := by
  classical
  have h (u v : ℕ) :
      (if u%q=v%q ∧ u≠v then c u*c v else 0) =
        (if u%q=v%q ∧ u<v then c u*c v else 0) +
        (if v%q=u%q ∧ v<u then c v*c u else 0) := by
    by_cases hmod : u%q=v%q
    · by_cases huv : u<v
      · have hne : u≠v := by omega
        have hnot : ¬ v<u := by omega
        simp [hmod, huv, hne, hnot]
      · by_cases hvu : v<u
        · have hne : u≠v := by omega
          simp [hmod, huv, hvu, hne, mul_comm]
        · have heq : u=v := by omega
          subst v
          simp
    · have hmod' : ¬ v%q=u%q := Ne.symm hmod
      simp [hmod, hmod']
  simp only [Finset.sum_filter]
  simp_rw [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := s) (t := s)
    (f := fun u v => if v%q=u%q ∧ v<u then c v*c u else 0)]
  ring

/-- Every larger congruent positive index has the literal form `u+kq`,
with `1 <= k <= q^3` inside the paper's fourth-power box. -/
theorem larger_congruent_interval_subset (q u : ℕ) (hq : 0 < q) :
    ((Finset.Icc 1 (q^4)).filter (fun v => u%q=v%q ∧ u<v)) ⊆
      (Finset.Icc 1 (q^3)).image (fun k => u+q*k) := by
  intro v hv
  obtain ⟨hv, hmod, huv⟩ := Finset.mem_filter.mp hv
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add huv.le).mp hmod
  have hkpos : 0 < k := by
    by_contra h
    have : k=0 := by omega
    simp [this] at hk
    omega
  have hkbound : q*k ≤ q*q^3 := by
    have hvbound := (Finset.mem_Icc.mp hv).2
    rw [pow_succ' q 3] at hvbound
    omega
  have hkmax : k ≤ q^3 := Nat.le_of_mul_le_mul_left hkbound hq
  exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hkpos, hkmax⟩, hk.symm⟩

theorem larger_congruent_reciprocal_bound (q u : ℕ) (hq : 0 < q) :
    (∑ v ∈ Finset.Icc 1 (q^4) with u%q=v%q ∧ u<v, (1 : ℝ)/v) ≤
      ∑ k ∈ Finset.Icc 1 (q^3), (1 : ℝ)/(u+q*k) := by
  classical
  calc
    _ ≤ ∑ v ∈ (Finset.Icc 1 (q^3)).image (fun k => u+q*k), (1 : ℝ)/v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (larger_congruent_interval_subset q u hq)
      intro v _ _
      positivity
    _ = _ := by
      rw [Finset.sum_image]
      · simp only [Nat.cast_add, Nat.cast_mul]
      · intro k _ l _ h
        have heq : q*k=q*l := Nat.add_left_cancel h
        exact Nat.eq_of_mul_eq_mul_left hq heq

noncomputable def harmonicSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (1 : ℝ)/n

theorem harmonicSum_nonneg (N : ℕ) : 0 ≤ harmonicSum N := by
  unfold harmonicSum
  positivity

theorem harmonicSum_le_log (N : ℕ) : harmonicSum N ≤ 1 + Real.log N := by
  simpa only [harmonicSum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div] using harmonic_le_one_add_log N

theorem reciprocal_progression_bound (q u : ℕ) (hq : 0 < q) :
    (∑ k ∈ Finset.Icc 1 (q^3), (1 : ℝ)/(u+q*k)) ≤
      (1/(q : ℝ))*harmonicSum (q^3) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold harmonicSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  calc
    (1 : ℝ)/(u+q*k) ≤ 1/((q : ℝ)*k) :=
      one_div_le_one_div_of_le (mul_pos hqR hkR) (le_add_of_nonneg_left (Nat.cast_nonneg u))
    _ = (1/(q : ℝ))*(1/(k : ℝ)) := by ring

noncomputable def reciprocalGrid (q : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 (q^4), (1 : ℝ)/u *
    ∑ k ∈ Finset.Icc 1 (q^3), (1 : ℝ)/(u+q*k)

theorem reciprocal_grid_bound (q : ℕ) (hq : 0 < q) :
    reciprocalGrid q ≤ (1/(q : ℝ))*harmonicSum (q^4)*harmonicSum (q^3) := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 (q^4), (1 : ℝ)/u *
        ((1/(q : ℝ))*harmonicSum (q^3)) := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left (reciprocal_progression_bound q u hq) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold harmonicSum
      ring

theorem coefficient_pair_bound (T u v : ℕ) (D : ℝ)
    (hD : (u.divisors.card : ℝ)*(v.divisors.card : ℝ) ≤ D) :
    coefficient T u * coefficient T v ≤ D * ((1 : ℝ)/u) * ((1 : ℝ)/v) := by
  calc
    _ ≤ ((u.divisors.card : ℝ)/u)*((v.divisors.card : ℝ)/v) :=
      mul_le_mul (coefficient_le_divisor_weight T u) (coefficient_le_divisor_weight T v)
        (coefficient_nonneg T v) (by positivity)
    _ = ((u.divisors.card : ℝ)*(v.divisors.card : ℝ))/((u : ℝ)*v) := by
      rw [div_mul_div_comm]
    _ ≤ D/((u : ℝ)*v) := div_le_div_of_nonneg_right hD (by positivity)
    _ = _ := by ring

noncomputable def offDiagonal (q T : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 (q^4),
    ∑ v ∈ Finset.Icc 1 (q^4) with u%q=v%q ∧ u≠v, coefficient T u * coefficient T v

/-- The first displayed off-diagonal inequality, with one positive constant
independent of q. The factor two for ordered pairs is retained. -/
theorem off_diagonal_le_reciprocal_grid :
    ∃ C : ℝ, 0 < C ∧ ∀ q T : ℕ, 0 < q →
      offDiagonal q T ≤ C*(q : ℝ)^(1/2 : ℝ)*reciprocalGrid q := by
  obtain ⟨C, hC, hpair⟩ := divisor_pair_box_bound
  refine ⟨2*C, by positivity, ?_⟩
  intro q T hq
  rw [offDiagonal, ordered_off_diagonal_split]
  calc
    _ ≤ 2 * ∑ u ∈ Finset.Icc 1 (q^4),
        ∑ v ∈ Finset.Icc 1 (q^4) with u%q=v%q ∧ u<v,
          (C*(q : ℝ)^(1/2 : ℝ))*((1 : ℝ)/u)*((1 : ℝ)/v) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact coefficient_pair_bound T u v _ (hpair q u v hq hu (Finset.mem_filter.mp hv).1)
    _ = (2*C)*(q : ℝ)^(1/2 : ℝ) *
        ∑ u ∈ Finset.Icc 1 (q^4), (1 : ℝ)/u *
          ∑ v ∈ Finset.Icc 1 (q^4) with u%q=v%q ∧ u<v, (1 : ℝ)/v := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ (2*C)*(q : ℝ)^(1/2 : ℝ)*reciprocalGrid q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left (larger_congruent_reciprocal_bound q u hq) (by positivity)

theorem harmonicSum_power_le_log (q k : ℕ) (hq : 0 < q) :
    harmonicSum (q^k) ≤ (1/Real.log 2 + (k : ℝ))*Real.log (2*(q : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hinv : (1/Real.log 2)*Real.log 2 = 1 := one_div_mul_cancel h2.ne'
  calc
    harmonicSum (q^k) ≤ 1 + (k : ℝ)*Real.log q := by
      simpa only [Nat.cast_pow, Real.log_pow] using harmonicSum_le_log (q^k)
    _ ≤ (1/Real.log 2 + (k : ℝ))*Real.log (2*(q : ℝ)) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hqR.ne']
      nlinarith [mul_nonneg (one_div_pos.mpr h2).le hlogq,
        mul_nonneg (Nat.cast_nonneg k) h2.le]

noncomputable def gridConstant : ℝ :=
  (1/Real.log 2 + 4)*(1/Real.log 2 + 3)

theorem gridConstant_pos : 0 < gridConstant := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gridConstant
  positivity

theorem reciprocal_grid_log_bound (q : ℕ) (hq : 0 < q) :
    reciprocalGrid q ≤ gridConstant/(q : ℝ) * (Real.log (2*(q : ℝ)))^2 := by
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (2*(q : ℝ)) := Real.log_nonneg (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ (1/(q : ℝ))*harmonicSum (q^4)*harmonicSum (q^3) := reciprocal_grid_bound q hq
    _ ≤ (1/(q : ℝ))*((1/Real.log 2+4)*Real.log (2*(q : ℝ))) *
        ((1/Real.log 2+3)*Real.log (2*(q : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (harmonicSum_power_le_log q 4 hq) (by positivity)
      · exact harmonicSum_power_le_log q 3 hq
      · exact harmonicSum_nonneg _
      · positivity
    _ = _ := by unfold gridConstant; ring

noncomputable def logDecay (q : ℕ) : ℝ :=
  (q : ℝ)^(-1/2 : ℝ) * (Real.log (2*(q : ℝ)))^2

/-- The exact logarithmic off-diagonal estimate, with an absolute constant. -/
theorem off_diagonal_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q T : ℕ, 0 < q → offDiagonal q T ≤ C*logDecay q := by
  obtain ⟨C, hC, hbound⟩ := off_diagonal_le_reciprocal_grid
  refine ⟨C*gridConstant, mul_pos hC gridConstant_pos, ?_⟩
  intro q T hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : (q : ℝ)^(1/2 : ℝ)/(q : ℝ) = (q : ℝ)^(-1/2 : ℝ) := by
    simpa only [show (1/2 : ℝ)-1 = -1/2 by norm_num, Real.rpow_one]
      using (Real.rpow_sub hqR (1/2 : ℝ) 1).symm
  calc
    offDiagonal q T ≤ C*(q : ℝ)^(1/2 : ℝ)*reciprocalGrid q := hbound q T hq
    _ ≤ C*(q : ℝ)^(1/2 : ℝ)*(gridConstant/(q : ℝ)*(Real.log (2*(q : ℝ)))^2) :=
      mul_le_mul_of_nonneg_left (reciprocal_grid_log_bound q hq) (by positivity)
    _ = (C*gridConstant)*((q : ℝ)^(1/2 : ℝ)/(q : ℝ))*(Real.log (2*(q : ℝ)))^2 := by ring
    _ = (C*gridConstant)*logDecay q := by rw [hpow]; unfold logDecay; ring

theorem logDecay_le (q : ℕ) (hq : 0 < q) :
    logDecay q ≤ 16*(2 : ℝ)^(1/2 : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (2*(q : ℝ)) := Real.log_nonneg (by linarith)
  have hpow := pow_le_pow_left₀ hlog
    (Real.log_le_rpow_div (by positivity : 0 ≤ 2*(q : ℝ))
      (by norm_num : 0 < (1/4 : ℝ))) 2
  have hsquare : (((2*(q : ℝ))^(1/4 : ℝ))/(1/4 : ℝ))^2 =
      16*(2 : ℝ)^(1/2 : ℝ)*(q : ℝ)^(1/2 : ℝ) := by
    rw [div_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 2*(q : ℝ)) (1/4 : ℝ) 2]
    norm_num
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hqR.le]
    ring
  have hcancel : (q : ℝ)^(-1/2 : ℝ)*(q : ℝ)^(1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hqR]
    norm_num
  calc
    logDecay q ≤ (q : ℝ)^(-1/2 : ℝ) *
        (((2*(q : ℝ))^(1/4 : ℝ))/(1/4 : ℝ))^2 :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hqR.le _)
    _ = 16*(2 : ℝ)^(1/2 : ℝ) := by
      rw [hsquare]
      calc
        _ = (16*(2 : ℝ)^(1/2 : ℝ)) *
            ((q : ℝ)^(-1/2 : ℝ)*(q : ℝ)^(1/2 : ℝ)) := by ring
        _ = _ := by rw [hcancel, mul_one]

theorem residue_pair_sum_le_diagonal_add_off (q T : ℕ) :
    (∑ u ∈ Finset.Icc 1 (q^4),
      ∑ v ∈ Finset.Icc 1 (q^4) with u%q=v%q ∧ (u*v).Coprime q,
        coefficient T u * coefficient T v) ≤
      (∑ u ∈ Finset.Icc 1 (q^4), coefficient T u ^ 2) + offDiagonal q T := by
  classical
  rw [offDiagonal, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u hu
  have h (v : ℕ) :
      (if u%q=v%q then coefficient T u * coefficient T v else 0) =
        (if v=u then coefficient T u ^ 2 else 0) +
        (if u%q=v%q ∧ u≠v then coefficient T u * coefficient T v else 0) := by
    by_cases huv : u=v
    · subst v
      simp [pow_two]
    · have hvu : v≠u := Ne.symm huv
      by_cases hmod : u%q=v%q <;> simp [huv, hvu, hmod]
  calc
    _ ≤ ∑ v ∈ Finset.Icc 1 (q^4) with u%q=v%q, coefficient T u * coefficient T v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨hmem, hmod, _⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hmem, hmod⟩
      · intro v _ _
        exact mul_nonneg (coefficient_nonneg T u) (coefficient_nonneg T v)
    _ = _ := by
      simp only [Finset.sum_filter]
      simp_rw [h]
      rw [Finset.sum_add_distrib]
      simp [hu]

/-- The full-character fourth moment of the actual finite truncation has
one absolute upper bound, independent of its nonzero modulus. -/
theorem uniform_polynomial_fourth_moment_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ (q : ℕ) [NeZero q],
      uniformAverage (fun χ : Character q => ‖orderedLPartial χ (q^2)‖^4) ≤ M := by
  obtain ⟨C, hC, hbound⟩ := off_diagonal_log_bound
  let D : ℝ := ∑' n : ℕ, divisorSquareWeight n
  let K : ℝ := 16*(2 : ℝ)^(1/2 : ℝ)
  have hD : 0 ≤ D := tsum_nonneg divisorSquareWeight_nonneg
  have hK : 0 < K := by unfold K; positivity
  refine ⟨D+C*K+1, by positivity, ?_⟩
  intro q _
  rw [modulus_square_fourth_moment]
  calc
    _ ≤ (∑ u ∈ Finset.Icc 1 (q^4), coefficient (q^2) u ^ 2) + offDiagonal q (q^2) :=
      residue_pair_sum_le_diagonal_add_off q (q^2)
    _ ≤ D + C*logDecay q := add_le_add (coefficient_diagonal_bound _ _) (hbound q _ (NeZero.pos q))
    _ ≤ D + C*K := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (logDecay_le q (NeZero.pos q)) hC.le)
    _ ≤ D + C*K + 1 := by linarith

end NField.Alignment.MagnitudeFourthMomentBound
