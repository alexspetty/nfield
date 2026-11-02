/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRemainderDynamics
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Unit collision mass and infinite remainder readout

The convergent primitive mass is connected to the actual infinite age sum.
Finite source identities and summation limits remain separate proof steps.
-/

noncomputable section

namespace NField.Alignment.CollisionMassReadout

open scoped BigOperators
open Filter
open NField.Alignment.CollisionRemainderDynamics
open NField.Alignment.SecondaryCapacityLedger

@[simp] theorem collisionWeight_zero : collisionWeight 0 = 0 := by
  simp [collisionWeight]

@[simp] theorem collisionWeight_one : collisionWeight 1 = 0 := by
  simp [collisionWeight, reducedHarmonicStar]

theorem sum_range_weights (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), collisionWeight k) =
      ∑ k ∈ Finset.Icc 2 N, collisionWeight k := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    have hkN := Finset.mem_range.mp hk
    have hk2 : k < 2 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      omega
    interval_cases k <;> simp

theorem collisionWeight_hasSum : HasSum collisionWeight 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg collisionWeight_nonneg 1).mpr
  have he : (fun N => ∑ k ∈ Finset.range (N + 1), collisionWeight k) =
      (fun N => ∑ k ∈ Finset.Icc 2 N, collisionWeight k) := by
    funext N
    exact sum_range_weights N
  have h : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), collisionWeight k)
      atTop (nhds 1) := by rw [he]; exact collision_mass_limit
  exact (tendsto_add_atTop_iff_nat 1).mp h

theorem collisionWeight_summable : Summable collisionWeight := collisionWeight_hasSum.summable

theorem collisionWeight_tsum : (∑' k, collisionWeight k) = 1 := collisionWeight_hasSum.tsum_eq

theorem remainder_age_summable (N : ℕ) :
    Summable (fun k => collisionWeight k * ((N % k : ℕ) : ℝ)) := by
  apply Summable.of_nonneg_of_le (f := fun k => collisionWeight k * (N : ℝ))
    (fun k => mul_nonneg (collisionWeight_nonneg k) (Nat.cast_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N k)
      (collisionWeight_nonneg k))
  exact collisionWeight_summable.mul_right (N : ℝ)

def deficit (N : ℕ) : ℝ :=
  (2 / 3 : ℝ) * ∑' k, collisionWeight k * ((N % k : ℕ) : ℝ)

theorem sum_range_zero_one (f : ℕ → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 0) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), f k) = ∑ k ∈ Finset.Icc 2 N, f k := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    have hkN := Finset.mem_range.mp hk
    have hk2 : k < 2 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      omega
    interval_cases k <;> assumption

theorem finite_age_sum (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), collisionWeight k * ((N % k : ℕ) : ℝ)) =
      fractionalFloorTerm N := by
  rw [sum_range_zero_one _ (by simp) (by simp)]
  unfold fractionalFloorTerm collisionWeight
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The entire positive infinite age sum is a finite part plus the retained
mass at the unresolved periods. This also proves its exact normalization. -/
theorem remainder_age_tsum (N : ℕ) :
    (∑' k, collisionWeight k * ((N % k : ℕ) : ℝ)) =
      fractionalFloorTerm N + (N : ℝ) * reducedEulerTailMass N := by
  have hs := (remainder_age_summable N).sum_add_tsum_nat_add (N + 1)
  have hw := collisionWeight_summable.sum_add_tsum_nat_add (N + 1)
  have hmod (i : ℕ) : N % (i + (N + 1)) = N := Nat.mod_eq_of_lt (by omega)
  simp only [hmod, tsum_mul_right] at hs
  rw [finite_age_sum] at hs
  rw [collisionWeight_tsum, sum_range_weights] at hw
  unfold reducedEulerTailMass reducedEulerPartialMass
  change (∑' k, collisionWeight k * ((N % k : ℕ) : ℝ)) =
    fractionalFloorTerm N + (N : ℝ) *
      (1 - ∑ k ∈ Finset.Icc 2 N, collisionWeight k)
  nlinarith [congrArg (fun x : ℝ => (N : ℝ) * x) hw]

theorem deficit_eq_capacity (N : ℕ) :
    deficit N = (N : ℝ) - continuousCapacity N := by
  rw [deficit, remainder_age_tsum, exact_continuous_defect_ledger]
  ring

theorem deficit_nonneg (N : ℕ) : 0 ≤ deficit N := by
  unfold deficit
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg (fun k => mul_nonneg (collisionWeight_nonneg k) (Nat.cast_nonneg _))

theorem deficit_le (N : ℕ) : deficit N ≤ (2 / 3 : ℝ) * N := by
  unfold deficit
  have h := (remainder_age_summable N).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N k)
      (collisionWeight_nonneg k)) (collisionWeight_summable.mul_right (N : ℝ))
  rw [tsum_mul_right, collisionWeight_tsum, one_mul] at h
  linarith

theorem deficit_over_resolution_tendsto_zero :
    Tendsto (fun N : ℕ => deficit N / (N : ℝ)) atTop (nhds 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hpoint (k : ℕ) : Tendsto
      (fun N : ℕ => collisionWeight k * ((N % k : ℕ) : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    by_cases hk : k = 0
    · subst k
      simp
    · have hkpos := Nat.pos_of_ne_zero hk
      apply squeeze_zero' (g := fun N : ℕ => collisionWeight k * (k : ℝ) / (N : ℝ))
      · exact Eventually.of_forall (fun N => div_nonneg
          (mul_nonneg (collisionWeight_nonneg k) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      · filter_upwards [eventually_ge_atTop 1] with N hN
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast (Nat.mod_lt N hkpos).le) (collisionWeight_nonneg k)
      · simpa [div_eq_mul_inv] using hi.const_mul (collisionWeight k * (k : ℝ))
  have hb : ∀ᶠ N : ℕ in atTop, ∀ k,
      ‖collisionWeight k * ((N % k : ℕ) : ℝ) / (N : ℝ)‖ ≤ collisionWeight k := by
    filter_upwards [eventually_ge_atTop 1] with N hN k
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (mul_nonneg (collisionWeight_nonneg k) (Nat.cast_nonneg _)) hNR.le)]
    apply (div_le_iff₀ hNR).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N k)
      (collisionWeight_nonneg k)
  have ht := tendsto_tsum_of_dominated_convergence collisionWeight_summable hpoint hb
  simp only [tsum_zero] at ht
  have he : (fun N : ℕ => deficit N / (N : ℝ)) =
      (fun N : ℕ => (2 / 3 : ℝ) *
        ∑' k, collisionWeight k * ((N % k : ℕ) : ℝ) / (N : ℝ)) := by
    funext N
    rw [deficit, tsum_div_const]
    ring
  rw [he]
  simpa using ht.const_mul (2 / 3 : ℝ)

theorem capacity_leading_law :
    Tendsto (fun N : ℕ => continuousCapacity N / (N : ℝ)) atTop (nhds 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub deficit_over_resolution_tendsto_zero
  have he : (fun N : ℕ => 1 - deficit N / (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => continuousCapacity N / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [deficit_eq_capacity]
    field_simp
    ring
  have ht' : Tendsto (fun N : ℕ => 1 - deficit N / (N : ℝ)) atTop (nhds 1) := by
    simpa using ht
  exact ht'.congr' he

theorem harmonic_real_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem harmonic_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [harmonic_real_sum]
  positivity

theorem reducedHarmonicStar_le_harmonic {k N : ℕ} (hkN : k ≤ N) :
    reducedHarmonicStar k ≤ (harmonic N : ℝ) := by
  rw [harmonic_real_sum]
  unfold reducedHarmonicStar
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    exact Finset.mem_Icc.mpr ⟨ha'.1, by omega⟩
  · intro a _ _
    positivity

theorem collisionWeight_log_bound {k : ℕ} (_hk : 1 ≤ k) :
    collisionWeight k ≤ (1 + Real.log k) / (k : ℝ)^2 := by
  unfold collisionWeight
  exact div_le_div_of_nonneg_right
    ((reducedHarmonicStar_le_harmonic (le_refl k)).trans (harmonic_le_one_add_log k))
    (sq_nonneg _)

theorem fractionalFloorTerm_le_harmonic_sq (N : ℕ) :
    fractionalFloorTerm N ≤ (harmonic N : ℝ)^2 := by
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 2 N) :
      ((N % k : ℕ) : ℝ) / (k : ℝ)^2 * reducedHarmonicStar k ≤
        (harmonic N : ℝ) * (k : ℝ)⁻¹ := by
    have hk' := Finset.mem_Icc.mp hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    calc
      _ ≤ (k : ℝ) / (k : ℝ)^2 * (harmonic N : ℝ) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right
            (by exact_mod_cast (Nat.mod_lt N (by omega)).le) (sq_nonneg _)
        · exact reducedHarmonicStar_le_harmonic hk'.2
        · unfold reducedHarmonicStar; positivity
        · positivity
      _ = _ := by field_simp
  calc
    fractionalFloorTerm N ≤
        ∑ k ∈ Finset.Icc 2 N, (harmonic N : ℝ) * (k : ℝ)⁻¹ :=
      Finset.sum_le_sum hterm
    _ = (harmonic N : ℝ) * ∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (harmonic N : ℝ) * ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (harmonic_nonneg N)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        have hk' := Finset.mem_Icc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩
      · intro k _ _
        positivity
    _ = (harmonic N : ℝ)^2 := by rw [← harmonic_real_sum]; ring

theorem deficit_harmonic_bound {N : ℕ} (hN : 2 ≤ N) :
    deficit N ≤ (2 / 3 : ℝ) * ((harmonic N : ℝ)^2 + 2 * (harmonic N : ℝ) + 4) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have htail := CoprimeEulerMass.eulerFrontierPotential_le hN
  rw [← reducedEulerTailMass_eq_frontier hN] at htail
  have hmul := mul_le_mul_of_nonneg_left htail hNR.le
  have ht : (N : ℝ) * reducedEulerTailMass N ≤ 4 + 2 * (harmonic N : ℝ) := by
    have hc : (N : ℝ) * (4 / (N : ℝ) + 2 * (harmonic N : ℝ) / (N : ℝ)) =
        4 + 2 * (harmonic N : ℝ) := by field_simp
    rwa [hc] at hmul
  rw [deficit, remainder_age_tsum]
  nlinarith [fractionalFloorTerm_le_harmonic_sq N]

theorem deficit_log_bound {N : ℕ} (hN : 2 ≤ N) :
    deficit N ≤ 6 * (1 + Real.log N)^2 := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hH := harmonic_nonneg N
  have hHlog := harmonic_le_one_add_log N
  have hs : (harmonic N : ℝ)^2 ≤ (1 + Real.log N)^2 := by nlinarith
  have hb := deficit_harmonic_bound hN
  nlinarith [sq_nonneg (Real.log (N : ℝ))]

theorem deficit_isBigO_log_sq :
    Asymptotics.IsBigO atTop deficit (fun N : ℕ => (Real.log (2 * (N : ℝ)))^2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨24, ?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 2, hlog] with N hN hlogN
  rw [Real.norm_eq_abs, abs_of_nonneg (deficit_nonneg N), Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmono : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hNR (by linarith)
  have hsq : (1 + Real.log (N : ℝ))^2 ≤ 4 * (Real.log (2 * (N : ℝ)))^2 := by
    nlinarith [sq_nonneg (2 * Real.log (2 * (N : ℝ)) - (1 + Real.log (N : ℝ))),
      mul_nonneg (show 0 ≤ 2 * Real.log (2 * (N : ℝ)) - (1 + Real.log (N : ℝ)) by linarith)
        (show 0 ≤ 2 * Real.log (2 * (N : ℝ)) + (1 + Real.log (N : ℝ)) by linarith)]
  nlinarith [deficit_log_bound hN]

theorem collisionWeight_isBigO_log_div_sq :
    Asymptotics.IsBigO atTop collisionWeight
      (fun k : ℕ => Real.log (2 * (k : ℝ)) / (k : ℝ)^2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2, ?_⟩
  have hlog : ∀ᶠ k : ℕ in atTop, 1 ≤ Real.log (k : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 2, hlog] with k hk hlogk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmono : Real.log (k : ℝ) ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_le_log hkR (by linarith)
  have hl : 0 ≤ Real.log (2 * (k : ℝ)) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (collisionWeight_nonneg k), Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hl (sq_nonneg _))]
  calc
    _ ≤ (1 + Real.log (k : ℝ)) / (k : ℝ)^2 := collisionWeight_log_bound (by omega)
    _ ≤ (2 * Real.log (2 * (k : ℝ))) / (k : ℝ)^2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by ring

end NField.Alignment.CollisionMassReadout
