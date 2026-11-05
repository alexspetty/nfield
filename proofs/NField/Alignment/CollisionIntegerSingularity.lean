/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialTheorem

/-!
# Canonical cutoff singularities on the integer orbit

These statements concern the continuous finite cutoff functions at their
integer addresses, not point values assigned to an L² equivalence class.
-/

noncomputable section

namespace NField.Alignment.CollisionIntegerSingularity

open scoped BigOperators
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialReflection SecondaryCapacityLedger

theorem collisionWeight_lower {k : ℕ} (hk : 2 ≤ k) :
    1/(k : ℝ)^2 ≤ collisionWeight k := by
  have hh : (1 : ℝ) ≤ reducedHarmonicStar k := by
    unfold reducedHarmonicStar
    have h := Finset.single_le_sum (f := fun a : ℕ => (a : ℝ)⁻¹)
      (s := (Finset.Ico 1 k).filter (fun a => a.Coprime k))
      (fun a _ => by positivity)
      (show 1 ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k) by simp; omega)
    simpa using h
  exact div_le_div_of_nonneg_right hh (sq_nonneg _)

theorem stationaryAge_harmonic_lower {M : ℕ} (hM : 1 ≤ M) :
    ((harmonic M : ℝ)-1)/6 ≤ stationaryAge collisionWeight M := by
  have hkbound (k : ℕ) (hk : k ∈ Finset.Icc 2 M) :
      (1/2 : ℝ)*(k : ℝ)⁻¹ ≤ collisionWeight k * ((k : ℝ)-1) := by
    have hk2 := (Finset.mem_Icc.mp hk).1
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hkp : (0 : ℝ) < k := by linarith
    calc
      _ ≤ (1/(k : ℝ)^2) * ((k : ℝ)-1) := by
        field_simp
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (collisionWeight_lower hk2) (by linarith)
  have hsum := Finset.sum_le_sum hkbound
  rw [← Finset.mul_sum] at hsum
  have hhar : (harmonic M : ℝ) = 1 + ∑ k ∈ Finset.Icc 2 M, (k : ℝ)⁻¹ := by
    rw [harmonic_real_sum, ← Finset.sum_erase_add _ _ (Finset.left_mem_Icc.mpr hM)]
    simp only [Finset.Icc_erase_left, Nat.cast_one, inv_one]
    rw [add_comm, show Finset.Ioc 1 M = Finset.Icc 2 M from by ext k; simp; omega]
  unfold stationaryAge
  rw [hhar]
  linarith

theorem stationaryAge_tendsto_atTop :
    Tendsto (stationaryAge collisionWeight) atTop atTop := by
  have hlog : Tendsto (fun M : ℕ => Real.log ((M+1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hh : Tendsto (fun M : ℕ => (harmonic M : ℝ)) atTop atTop :=
    tendsto_atTop_mono log_add_one_le_harmonic hlog
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hh.eventually_ge_atTop (6*B+1), eventually_ge_atTop 1] with M hB hM
  linarith [stationaryAge_harmonic_lower hM]

def tailMass (M : ℕ) : ℝ := ∑' j, collisionWeight (j+(M+1))

theorem tailMass_nonneg (M : ℕ) : 0 ≤ tailMass M := by
  exact tsum_nonneg (fun j => collisionWeight_nonneg _)

theorem tailMass_tendsto_zero : Tendsto tailMass atTop (nhds 0) := by
  have hpartial := collisionWeight_hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have htotal (M : ℕ) : tailMass M = 1 - ∑ k ∈ Finset.range (M+1), collisionWeight k := by
    have h := collisionWeight_summable.sum_add_tsum_nat_add (M+1)
    rw [collisionWeight_tsum] at h
    change (∑ k ∈ Finset.range (M+1), collisionWeight k) + tailMass M = 1 at h
    linarith
  simp_rw [show tailMass = (fun M => 1 - ∑ k ∈ Finset.range (M+1), collisionWeight k) from funext htotal]
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hpartial
  simpa only [Function.comp_def, sub_self] using h

theorem integer_cutoff_identity {M n : ℕ} (hnM : n ≤ M) :
    finiteAge collisionWeight M n = deficit n - stationaryAge collisionWeight M -
      (2/3 : ℝ)*(n : ℝ)*tailMass M := by
  have hs := (remainder_age_summable n).sum_add_tsum_nat_add (M+1)
  have ht : (∑' j, collisionWeight (j+(M+1))*((n%(j+(M+1)) : ℕ) : ℝ)) =
      (n : ℝ)*tailMass M := by
    have hmod (j : ℕ) : n%(j+(M+1)) = n := Nat.mod_eq_of_lt (by omega)
    simp_rw [hmod]
    rw [tsum_mul_right]
    unfold tailMass
    ring
  rw [ht, sum_range_zero_one _ (by simp) (by simp)] at hs
  have hage := finite_age_gap collisionWeight M n
  unfold deficit
  linarith

theorem nonnegative_integer_cutoff_atBot (n : ℕ) :
    Tendsto (fun M => finiteAge collisionWeight M n) atTop atBot := by
  apply tendsto_atBot.mpr
  intro B
  filter_upwards [stationaryAge_tendsto_atTop.eventually_ge_atTop (deficit n-B),
    eventually_ge_atTop n] with M hB hM
  rw [integer_cutoff_identity hM]
  have ht : 0 ≤ (2/3 : ℝ)*(n : ℝ)*tailMass M :=
    mul_nonneg (by positivity) (tailMass_nonneg M)
  linarith

theorem integer_difference_tendsto (n : ℕ) :
    Tendsto (fun M => finiteAge collisionWeight M n - finiteAge collisionWeight M 0)
      atTop (nhds (deficit n)) := by
  have h := (tendsto_const_nhds (x := deficit n)).sub
    (tailMass_tendsto_zero.const_mul ((2/3 : ℝ)*(n : ℝ)))
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop n] with M hM
  rw [integer_cutoff_identity hM, finite_age_zero]
  ring

theorem integer_diagonal_identity (n : ℕ) :
    deficit n - stationaryAge collisionWeight n = finiteAge collisionWeight n n +
      (2/3 : ℝ)*(n : ℝ)*tailMass n := by
  rw [integer_cutoff_identity (le_refl n)]
  ring

theorem negative_integer_cutoff_atTop (n : ℕ) :
    Tendsto (fun M => potentialMap collisionWeight M (integerPhase (-(n : ℤ)-1))) atTop atTop := by
  have he (M : ℕ) : potentialMap collisionWeight M (integerPhase (-(n : ℤ)-1)) =
      -finiteAge collisionWeight M n := by
    have hr : integerPhase (-(n : ℤ)-1) = reflection (integerPhase (n : ℤ)) := by
      apply Subtype.ext
      funext H
      change (QuotientGroup.mk' H.toSubgroup) (Multiplicative.ofAdd (-(n : ℤ)-1)) =
        (QuotientGroup.mk' H.toSubgroup) (Multiplicative.ofAdd (-1 : ℤ)) /
          (QuotientGroup.mk' H.toSubgroup) (Multiplicative.ofAdd (n : ℤ))
      rw [← map_div (QuotientGroup.mk' H.toSubgroup)]
      congr 1
      change -(n : ℤ)-1 = -1-(n : ℤ)
      ring
    rw [hr, potentialMap_reflection, potentialMap_integer]
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [(nonnegative_integer_cutoff_atBot n).eventually_le_atBot (-B)] with M hM
  rw [he]
  linarith

theorem negative_phase_cutoff_atTop (z : ℤ) (hz : z < 0) :
    Tendsto (fun M => potentialMap collisionWeight M (integerPhase z)) atTop atTop := by
  have he : z = -(((-z-1).toNat : ℕ) : ℤ)-1 := by omega
  rw [he]
  exact negative_integer_cutoff_atTop _

/-- The entire fixed-integer singularity statement, for actual finite cutoff values. -/
theorem canonical_cutoff_singularity :
    (∀ M n : ℕ, n ≤ M → finiteAge collisionWeight M n =
      deficit n - stationaryAge collisionWeight M - (2/3 : ℝ)*(n : ℝ)*tailMass M) ∧
    (∀ n : ℕ, Tendsto (fun M => finiteAge collisionWeight M n) atTop atBot) ∧
    (∀ z : ℤ, z < 0 → Tendsto (fun M => potentialMap collisionWeight M (integerPhase z))
      atTop atTop) ∧
    (∀ n : ℕ, Tendsto (fun M => finiteAge collisionWeight M n - finiteAge collisionWeight M 0)
      atTop (nhds (deficit n))) := by
  exact ⟨fun _ _ h => integer_cutoff_identity h, nonnegative_integer_cutoff_atBot,
    negative_phase_cutoff_atTop, integer_difference_tendsto⟩

end NField.Alignment.CollisionIntegerSingularity
