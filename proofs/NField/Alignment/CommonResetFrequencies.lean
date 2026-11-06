/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTrigonometric

/-! # The full finite source with all three frequency indices -/

noncomputable section

namespace NField.Alignment.CommonResetFrequencies

open scoped BigOperators
open CommonResetFourier CommonResetEndpoint CommonResetHalfFrequencies
open CommonResetSineEndpoint CommonResetTrigonometric DedekindInverseResidueTransform

def frequencyTerm {t : ℕ} [NeZero t] (N q : ℕ) (u : (ZMod t)ˣ)
    (v j : ZMod t) : ℝ :=
  (4/(t : ℝ)^2)*cotangentResidue u.val*cotangentResidue v*sinePrefix N j*
    characterSine (j*((q : ZMod t)*v*(↑(u⁻¹) : ZMod t)))

theorem inverseResidue_of_unit {t : ℕ} [NeZero t] (u : (ZMod t)ˣ) :
    inverseResidue u.val.val t = (↑(u⁻¹) : ZMod t).val := by
  unfold inverseResidue
  rw [dif_neg (NeZero.ne t), dif_pos (ZMod.val_coe_unit_coprime u)]
  have he : ZMod.unitOfCoprime u.val.val (ZMod.val_coe_unit_coprime u) = u := by
    apply Units.ext
    simp only [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
  rw [he]

/-- Title: `The three-frequency term equals the printed cotangent and sine formula`. -/
theorem frequencyTerm_literal {t : ℕ} [NeZero t] (N q : ℕ) (u : (ZMod t)ˣ)
    (v j : ZMod t) (hj : j ∈ lowerResidues t) :
    frequencyTerm N q u v j =
      (4/(t : ℝ)^2)*Real.cot (Real.pi*(u.val.val : ℝ)/(t : ℝ))*
        Real.cot (Real.pi*(v.val : ℝ)/(t : ℝ))*
        (Real.sin (Real.pi*(j.val : ℝ)*(N : ℝ)/(t : ℝ))*
          Real.sin (Real.pi*(j.val : ℝ)*((N : ℝ)+1)/(t : ℝ))/
            Real.sin (Real.pi*(j.val : ℝ)/(t : ℝ)))*
        Real.sin (2*Real.pi*(j.val : ℝ)*(q : ℝ)*(v.val : ℝ)*
          (inverseResidue u.val.val t : ℝ)/(t : ℝ)) := by
  rw [frequencyTerm, sinePrefix_closed N j hj]
  have hphase : characterSine (j*((q : ZMod t)*v*(↑(u⁻¹) : ZMod t))) =
      Real.sin (2*Real.pi*(j.val : ℝ)*(q : ℝ)*(v.val : ℝ)*
        (inverseResidue u.val.val t : ℝ)/(t : ℝ)) := by
    have h := characterSine_nat_mul (q*v.val*inverseResidue u.val.val t) j
    rw [Nat.cast_mul, Nat.cast_mul, inverseResidue_of_unit, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at h
    rw [mul_comm j]
    rw [h]
    congr 1
    push_cast
    rw [inverseResidue_of_unit]
    ring
  rw [hphase]
  rfl

theorem endpointFrequency_expansion {t : ℕ} [NeZero t] (N q : ℕ)
    (u : (ZMod t)ˣ) (v : ZMod t) :
    endpointFrequency q (N%t) u v =
      (t : ℝ)*∑ j ∈ lowerResidues t, frequencyTerm N q u v j := by
  rw [endpointFrequency, endpoint_half_sine (N%t) (Nat.mod_lt N (NeZero.pos t))]
  simp only [← sinePrefix_mod N, Finset.mul_sum, frequencyTerm]
  apply Finset.sum_congr rfl
  intro j _
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  field_simp

def completeFrequencies (N q t : ℕ) : ℝ :=
  if ht : 2 ≤ t then
    letI : NeZero t := ⟨by omega⟩
    (harmonic (N/t) : ℝ)*∑ u ∈ lowerUnits t, ∑ v ∈ lowerResidues t,
      ∑ j ∈ lowerResidues t, frequencyTerm N q u v j
  else 0

theorem completedConductor_eq_frequencies (N q t : ℕ) :
    completedConductor N q t = completeFrequencies N q t := by
  unfold completedConductor completeFrequencies
  split_ifs with ht
  · simp only [endpointFrequency_expansion, ← Finset.mul_sum]
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    field_simp
  · rfl

/-- Title: `The entire interior source is the complete three-frequency sum`. -/
theorem complete_frequency_source (N q : ℕ)
    (hq : ∀ k ∈ Finset.Icc 1 N, q.Coprime k) :
    CommonResetSampling.interiorSource N q =
      ∑ t ∈ Finset.Icc 2 N, completeFrequencies N q t := by
  rw [completed_source N q hq]
  exact Finset.sum_congr rfl (fun t _ => completedConductor_eq_frequencies N q t)

end NField.Alignment.CommonResetFrequencies
