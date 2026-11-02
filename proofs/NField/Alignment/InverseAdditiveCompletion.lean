/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteIntervalCompletion
import NField.Alignment.InverseResiduePrefixCompletion
import NField.Alignment.EndpointReciprocityBridge

/-!
# Completion of the actual incomplete inverse additive sum

The complete sums are explicit finite Kloosterman sums. Completion is a
proved finite identity; their square-root estimate remains a separate input.
-/

set_option autoImplicit false
namespace NField.Alignment.InverseAdditiveCompletion

open scoped BigOperators ZMod
open AddChar
open InverseResiduePrefixCompletion FiniteIntervalCompletion SpectralPower

noncomputable def inversePhase {q : ℕ} [NeZero q]
    (r : ℕ) (j x : ZMod q) : ℂ :=
  if h : IsUnit x then
    ZMod.stdAddChar (j * ((r : ZMod q) * h.unit⁻¹.val)) else 0

/-- The complete Kloosterman sum, with the sign matching Mathlib's DFT. -/
noncomputable def completeInverseSum {q : ℕ} [NeZero q]
    (r : ℕ) (j t : ZMod q) : ℂ :=
  ∑ x : ZMod q, if h : IsUnit x then
    ZMod.stdAddChar (j * ((r : ZMod q) * h.unit⁻¹.val) - x * t) else 0

theorem inverse_phase_natCast {q : ℕ} [NeZero q]
    (r n : ℕ) (j : ZMod q) :
    inversePhase r j (n : ZMod q) =
      if hn : n.Coprime q then ZMod.stdAddChar
        (j * ((r : ZMod q) * (ZMod.unitOfCoprime n hn)⁻¹.val)) else 0 := by
  unfold inversePhase
  by_cases hn : n.Coprime q
  · have hu : IsUnit (n : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      exact hn
    rw [dif_pos hu, dif_pos hn]
    have heq : hu.unit = ZMod.unitOfCoprime n hn := by
      apply Units.ext
      exact hu.unit_spec
    rw [heq]
  · have hu : ¬IsUnit (n : ZMod q) := by
      simpa only [ZMod.isUnit_iff_coprime] using hn
    rw [dif_neg hu, dif_neg hn]

theorem inverse_phase_dft {q : ℕ} [NeZero q]
    (r : ℕ) (j t : ZMod q) :
    ZMod.dft (inversePhase r j) t = completeInverseSum r j t := by
  classical
  rw [ZMod.dft_apply]
  unfold completeInverseSum
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : IsUnit x
  · simp only [inversePhase, dif_pos hx, smul_eq_mul]
    rw [← map_add_eq_mul]
    congr 1
    ring
  · simp [inversePhase, hx]

theorem inverse_additive_prefix_eq_range {q : ℕ} [NeZero q]
    (r X : ℕ) (j : ZMod q) :
    inverseAdditivePrefix q r X j =
      ∑ a ∈ Finset.range X, inversePhase r j ((1 + a : ℕ) : ZMod q) := by
  unfold inverseAdditivePrefix
  simp_rw [Nat.add_comm 1, inverse_phase_natCast]
  exact (EndpointReciprocityBridge.sum_range_shift_eq_Icc _ X).symm

/-- Exact completion at all frequencies, including t=0. -/
theorem inverse_additive_prefix_completion {q : ℕ} [NeZero q]
    (r X : ℕ) (j : ZMod q) :
    inverseAdditivePrefix q r X j = (q : ℂ)⁻¹ *
      ∑ t : ZMod q, ZMod.stdAddChar t * intervalFourier q X (-t) *
        completeInverseSum r j t := by
  rw [inverse_additive_prefix_eq_range, interval_fourier]
  simp only [Nat.cast_one, mul_one, inverse_phase_dft]

/-- Completion retains the contribution of the zero Fourier mode. -/
theorem inverse_additive_prefix_norm_of_complete {q : ℕ} [NeZero q]
    (hq : 0 < q) (r X : ℕ) (j : ZMod q) {U : ℝ} (hU : 0 ≤ U)
    (hcomplete : ∀ t : ZMod q, ‖completeInverseSum r j t‖ ≤ U) :
    ‖inverseAdditivePrefix q r X j‖ ≤ U * ((X : ℝ) / q + (harmonic q : ℝ)) := by
  rw [inverse_additive_prefix_eq_range]
  apply interval_norm_le_of_dft hq _ hU
  intro t
  simpa only [inverse_phase_dft] using hcomplete t

/-- Literal classical unit-sum form of the complete transform. -/
theorem complete_inverse_sum_eq_units {q : ℕ} [NeZero q]
    (r : ℕ) (j t : ZMod q) :
    completeInverseSum r j t = ∑ u : (ZMod q)ˣ,
      ZMod.stdAddChar (j * ((r : ZMod q) * u⁻¹.val) - u.val * t) := by
  classical
  let F : ZMod q → ℂ := fun x => if h : IsUnit x then
    ZMod.stdAddChar (j * ((r : ZMod q) * h.unit⁻¹.val) - x * t) else 0
  have hnonunit : (∑ x ∈ (Finset.univ : Finset (ZMod q)) with ¬IsUnit x, F x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dif_neg (Finset.mem_filter.mp hx).2
  have hfilter := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod q)) IsUnit F
  rw [hnonunit, add_zero] at hfilter
  calc
    completeInverseSum r j t = ∑ x : ZMod q, F x := rfl
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod q)) with IsUnit x, F x := hfilter.symm
    _ = ∑ x : {x : ZMod q // IsUnit x}, F x.val := by
      exact Finset.sum_subtype ((Finset.univ : Finset (ZMod q)).filter IsUnit)
        (by intro x; simp) F
    _ = _ := by
      symm
      apply Fintype.sum_equiv CarryBoundarySpectra.unitsEquivIsUnit
      intro u
      have hu : (CarryBoundarySpectra.unitsEquivIsUnit (m := q) u).property.unit = u := by
        apply Units.ext
        exact (CarryBoundarySpectra.unitsEquivIsUnit (m := q) u).property.unit_spec
      simp only [F, dif_pos (CarryBoundarySpectra.unitsEquivIsUnit (m := q) u).property, hu]
      rfl

/-- At zero completion frequency the transform is the complete unit
additive-character sum, after the inverse permutation. It is not dropped. -/
theorem complete_inverse_sum_zero {q : ℕ} [NeZero q]
    (r : ℕ) (j : ZMod q) :
    completeInverseSum r j 0 =
      ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (j * ((r : ZMod q) * u.val)) := by
  rw [complete_inverse_sum_eq_units]
  simp only [mul_zero, sub_zero]
  simpa using Equiv.sum_comp (Equiv.inv ((ZMod q)ˣ))
    (fun u : (ZMod q)ˣ => ZMod.stdAddChar (j * ((r : ZMod q) * u.val)))

/-- The genuine complete-sum source estimate still required by SEC-03.
The frequency t ranges over every residue, including zero. This is a
proposition naming the remaining theorem, not an axiom or proof of it. -/
def CompleteInverseSumEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q (hq : 2 ≤ q),
    letI : NeZero q := ⟨by omega⟩
    ∀ r (j : ZMod q), r.Coprime q → j ≠ 0 → ∀ t : ZMod q,
      ‖completeInverseSum r j t‖ ≤
        C * (q : ℝ).sqrt * q.divisors.card *
          ((j.val.gcd q : ℕ) : ℝ).sqrt

/-- Completion proves the precise manuscript input from the complete-sum
estimate. The logarithm and the zero-frequency cost are derived here. -/
theorem weil_estermann_prefix_of_complete (hcomplete : CompleteInverseSumEstimate) :
    WeilEstermannInversePrefixEstimate := by
  obtain ⟨C, hC, hbound⟩ := hcomplete
  refine ⟨3 * C, by positivity, ?_⟩
  intro q hq
  letI : NeZero q := ⟨by omega⟩
  intro r X j hr _hX hXq hj
  let U : ℝ := C * (q : ℝ).sqrt * q.divisors.card *
    ((j.val.gcd q : ℕ) : ℝ).sqrt
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hX : (X : ℝ) / q ≤ 1 := (div_le_one hqR).mpr (by exact_mod_cast hXq)
  have hH : (harmonic q : ℝ) ≤ 1 + Real.log q := by
    exact_mod_cast harmonic_le_one_add_log q
  have hlogq : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hscale : (X : ℝ) / q + (harmonic q : ℝ) ≤ 3 * Real.log (2 * q) := by
    rw [Real.log_mul (by norm_num) hqR.ne']
    linarith
  calc
    ‖inverseAdditivePrefix q r X j‖ ≤ U * ((X : ℝ) / q + (harmonic q : ℝ)) :=
      inverse_additive_prefix_norm_of_complete (by omega) r X j hU (hbound q hq r j hr hj)
    _ ≤ U * (3 * Real.log (2 * q)) := mul_le_mul_of_nonneg_left hscale hU
    _ = _ := by dsimp [U]; ring

end NField.Alignment.InverseAdditiveCompletion
