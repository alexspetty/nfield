/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityGramCosts

/-! # The full scalar and joint certificate chain for the prescribed family -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityScalarCertificates
open scoped BigOperators
open UnityNativeHilbert UnityFiniteGram UnityPrescribedDetectors UnityDetectorBandCost UnityGramCosts
variable {ι : Type*} [Fintype ι]

/-- The maximum scalar quotient, with zero assigned to an empty family. -/
def maxQuotient (b c : ι → ℝ) : ℝ :=
  if h : (Finset.univ : Finset ι).Nonempty then
    Finset.univ.sup' h (fun i => (b i)^2/c i) else 0

theorem quotient_le_max (b c : ι → ℝ) (i : ι) : (b i)^2/c i≤maxQuotient b c := by
  classical
  have h : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
  rw [maxQuotient, dif_pos h]
  exact Finset.le_sup' (fun j => (b j)^2/c j) (Finset.mem_univ i)

theorem maxQuotient_le (b c : ι → ℝ) (a : ℝ) (ha : 0≤a)
    (h : ∀i, (b i)^2/c i≤a) : maxQuotient b c≤a := by
  classical
  unfold maxQuotient
  split_ifs
  · exact Finset.sup'_le _ _ (fun i _ => h i)
  · exact ha

theorem maxQuotient_nonneg (b c : ι → ℝ) (hc : ∀i, 0≤c i) : 0≤maxQuotient b c := by
  classical
  by_cases h : Nonempty ι
  · obtain ⟨i⟩ := h
    exact (div_nonneg (sq_nonneg _) (hc i)).trans (quotient_le_max b c i)
  · have he : ¬(Finset.univ : Finset ι).Nonempty := by
      rintro ⟨i, _⟩
      exact h ⟨i⟩
    simp only [maxQuotient, dif_neg he, le_refl]

/-- The maximum raw quotient dominates its exact weighted average. -/
theorem weighted_average_le_max (b c : ι → ℝ) (hc : ∀i, 0≤c i)
    (hz : ∀i, c i=0 → b i=0) (hC : 0<∑ i, c i) :
    (∑ i, (b i)^2)/(∑ i, c i)≤maxQuotient b c := by
  apply (div_le_iff₀ hC).mpr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hci : c i=0
  · simp only [hci, hz i hci, zero_pow (by omega : 2≠0), mul_zero, le_refl]
  · exact (div_le_iff₀ (lt_of_le_of_ne (hc i) (Ne.symm hci))).mp (quotient_le_max b c i)

def rawMaximum (N : ℕ) : ℝ :=
  maxQuotient (fun h : eligible N => signedReadings N h) (fun h => bandCost N h)

def conditionedMaximum (N : ℕ) : ℝ :=
  maxQuotient (fun h : eligible N => signedReadings N h) (fun h => ‖detector N h‖^2)

theorem raw_zero_reading (N : ℕ) (h : eligible N) (hz : bandCost N h=0) :
    signedReadings N h=0 := by
  have hd := detector_cost N h
  change ‖detector N h‖^2≤bandCost N h at hd
  rw [hz] at hd
  have hv : detector N h=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (detector N h)])
  change inner ℝ (UnityNativeHilbert.residual N) (detector N h)=0
  rw [hv, inner_zero_right]

theorem raw_quotient_le_conditioned (N : ℕ) (h : eligible N) :
    (signedReadings N h)^2/bandCost N h≤(signedReadings N h)^2/‖detector N h‖^2 := by
  by_cases hv : detector N h=0
  · have hb : signedReadings N h=0 := by
      change inner ℝ (UnityNativeHilbert.residual N) (detector N h)=0
      rw [hv, inner_zero_right]
    simp only [hb, zero_pow (by omega : 2≠0), zero_div, le_refl]
  · exact div_le_div_of_nonneg_left (sq_nonneg _)
      (sq_pos_of_pos (norm_pos_iff.mpr hv)) (detector_cost N h)

theorem conditionedMaximum_le_capture (N : ℕ) : conditionedMaximum N≤capture N := by
  apply maxQuotient_le _ _ _ (capture_nonneg N)
  intro h
  rw [capture_eq_jointGain]
  exact jointGain_scalar_quotient (detectorFamily N) (UnityNativeHilbert.residual N) h

theorem rawMaximum_le_conditioned (N : ℕ) : rawMaximum N≤conditionedMaximum N := by
  apply maxQuotient_le _ _ _ (maxQuotient_nonneg _ _ (fun i => sq_nonneg _))
  intro h
  exact (raw_quotient_le_conditioned N h).trans
    (quotient_le_max (fun i : eligible N => signedReadings N i) (fun i => ‖detector N i‖^2) h)

theorem readings_average_le_rawMaximum (N : ℕ) (hT : 0<totalCost N) :
    ‖signedReadings N‖^2/totalCost N≤rawMaximum N := by
  have he : (∑ h : eligible N, bandCost N h)=totalCost N :=
    Finset.sum_coe_sort (eligible N) (bandCost N)
  rw [EuclideanSpace.real_norm_sq_eq, ← he]
  exact weighted_average_le_max _ _ (fun h => bandCost_nonneg N h)
    (raw_zero_reading N) (he.symm ▸ hT)

/-- Title: `The complete scalar and joint capture certificate chain`.

 Every inequality in the paper's displayed scalar/joint certificate chain. -/
theorem prescribed_certificate_chain (N : ℕ) (hT : 0<totalCost N) :
    conditionedMaximum N≤capture N ∧ rawMaximum N≤conditionedMaximum N ∧
    ‖signedReadings N‖^2/totalCost N≤rawMaximum N ∧
    (1/2:ℝ)*‖signedReadings N‖^2≤‖signedReadings N‖^2/totalCost N := by
  refine ⟨conditionedMaximum_le_capture N, rawMaximum_le_conditioned N,
    readings_average_le_rawMaximum N hT, ?_⟩
  have h := div_le_div_of_nonneg_left (sq_nonneg ‖signedReadings N‖) hT (totalCost_le_two N)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

/-- Title: `The prescribed Rayleigh certificate retains all Gram cross terms`.

 The exact prescribed Rayleigh certificate keeps all within-family cross terms. -/
theorem prescribed_rayleigh (N : ℕ) (x : EuclideanSpace ℝ (eligible N))
    (hx : 0 < inner ℝ (detectorGram N x) x) :
    |inner ℝ (signedReadings N) x|^2/inner ℝ (detectorGram N x) x≤capture N := by
  rw [capture_eq_jointGain]
  exact jointGain_rayleigh_quotient (detectorFamily N) _ x hx

end NField.Alignment.UnityScalarCertificates
