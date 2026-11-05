/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAtomicSpectra

/-!
# The potential's atomic Fourier moments

Reflection pairs the primitive addresses. The coboundary second difference
cancels each inverse chord weight, and the exact total mass supplies the
zeroth moment. Uniqueness then identifies the actual Haar covariance.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPotentialSpectralMoments

open scoped BigOperators ComplexConjugate
open MeasureTheory CollisionSpectralWeights CollisionAtomicSpectra CollisionRamanujan
open CollisionWeightMultiples CollisionCosecantIdentity DedekindFourierMoment
open CollisionPrimitiveFourier CollisionSpectralMomentRecurrence
open CollisionPotentialConvergence CollisionPotentialHilbert CollisionOdometerRecurrence

theorem phase_add (q : ℕ) (h k : ℤ) (a : ℕ) :
    phase q (h+k) a = phase q h a*phase q k a := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem phase_zero (q a : ℕ) : phase q 0 a = 1 := by simp [phase]

theorem phase_conj (q : ℕ) (h : ℤ) (a : ℕ) : conj (phase q h a)=phase q (-h) a := by
  unfold phase
  rw [← Complex.exp_conj]
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    map_intCast, map_natCast, Int.cast_neg]
  congr 1
  ring

theorem negativeRoot_phase (q a : ℕ) : negativeRoot q a=phase q (-1) a := by
  unfold negativeRoot phase
  push_cast
  congr 1
  ring

def reflectedAddress (i : SpectralAddress) : SpectralAddress :=
  ⟨i.1, ⟨i.1-i.2.1, primitiveNumerators_complement i.2.2⟩⟩

theorem reflectedAddress_involutive : Function.Involutive reflectedAddress := by
  rintro ⟨q,⟨a,ha⟩⟩
  have h := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
  simp only [reflectedAddress, Nat.sub_sub_self h.le]

def reflection : SpectralAddress ≃ SpectralAddress :=
  ⟨reflectedAddress, reflectedAddress, reflectedAddress_involutive,
    reflectedAddress_involutive⟩

theorem phase_reflected (i : SpectralAddress) (h : ℤ) :
    phase (reflectedAddress i).1 h (reflectedAddress i).2.1 = phase i.1 (-h) i.2.1 := by
  have hq : 0 < i.1 := by have := address_period i; omega
  letI : NeZero i.1 := ⟨hq.ne'⟩
  change phase i.1 h (i.1-i.2.1) = _
  rw [phase_std hq, phase_std hq]
  congr 1
  rw [Nat.cast_sub (address_bounds i).2.le, ZMod.natCast_self, zero_sub, Int.cast_neg]
  ring

theorem potentialMass_reflected (i : SpectralAddress) :
    potentialMass (reflectedAddress i)=potentialMass i := by
  rw [potentialMass_literal, potentialMass_literal]
  change (1/9 : ℝ)*CollisionJordanVariance.amplitude i.1^2*
    (Real.sin (Real.pi*((i.1-i.2.1 : ℕ) : ℝ)/(i.1 : ℝ))^2)⁻¹ = _
  have hq : (i.1 : ℝ) ≠ 0 := by exact_mod_cast (show i.1≠0 by have := address_period i; omega)
  have he : Real.pi*((i.1-i.2.1 : ℕ) : ℝ)/(i.1 : ℝ) =
      Real.pi-Real.pi*(i.2.1 : ℝ)/(i.1 : ℝ) := by
    rw [Nat.cast_sub (address_bounds i).2.le]
    field_simp
  rw [he, Real.sin_pi_sub]

def potentialMoment (h : ℤ) : ℂ := ∫ t, fourierCharacter h t ∂potentialMeasure

theorem potentialMoment_series (h : ℤ) :
    potentialMoment h = ∑' i, (potentialMass i : ℂ)*phase i.1 h i.2.1 :=
  atomicMeasure_fourier _ potentialMass_nonneg potentialMass_summable h

theorem potentialMoment_even (h : ℤ) : potentialMoment (-h)=potentialMoment h := by
  rw [potentialMoment_series, potentialMoment_series]
  calc
    _ = ∑' i, (potentialMass (reflection i) : ℂ)*
        phase (reflection i).1 h (reflection i).2.1 := by
      apply tsum_congr
      intro i
      rw [show reflection i=reflectedAddress i from rfl, potentialMass_reflected, phase_reflected]
    _ = _ := reflection.tsum_eq
      (fun i : SpectralAddress => (potentialMass i : ℂ)*phase i.1 h i.2.1)

theorem potentialMoment_zero : potentialMoment 0=(‖collisionPotential‖^2 : ℝ) := by
  rw [potentialMoment_series]
  simp only [phase_zero, mul_one]
  rw [← Complex.ofReal_tsum, potentialMass_total]

theorem chord_second_difference (q a : ℕ) :
    (‖1-negativeRoot q a‖^2 : ℝ) = (2 : ℂ)-phase q (-1) a-phase q 1 a := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sub, map_one,
    negativeRoot_phase, phase_conj]
  norm_num only
  have hm : phase q (-1) a*phase q 1 a=1 := by
    rw [← phase_add]
    norm_num only
    exact phase_zero q a
  linear_combination hm

theorem potentialMass_second_difference (i : SpectralAddress) (h : ℤ) :
    2*((potentialMass i : ℂ)*phase i.1 h i.2.1)-
      (potentialMass i : ℂ)*phase i.1 (h-1) i.2.1-
      (potentialMass i : ℂ)*phase i.1 (h+1) i.2.1 =
      (incrementMass i : ℂ)*phase i.1 h i.2.1 := by
  have hz : ‖1-negativeRoot i.1 i.2.1‖^2 ≠ 0 := by
    apply pow_ne_zero
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr
      (negativeRoot_primitive_ne_one (address_period i) (address_coprime i)).symm)
  have hc := chord_second_difference i.1 i.2.1
  have hcancel : (chordEnergy i.1 i.2.1 : ℂ)*
      ((2 : ℂ)-phase i.1 (-1) i.2.1-phase i.1 1 i.2.1)=1 := by
    rw [← hc, chordEnergy, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hz)
  rw [show h-1=h+(-1) by omega, phase_add, phase_add]
  simp only [potentialMass, Complex.ofReal_mul]
  linear_combination (incrementMass i : ℂ)*phase i.1 h i.2.1 * hcancel

theorem potentialMoment_second_difference (h : ℤ) :
    2*potentialMoment h-potentialMoment (h-1)-potentialMoment (h+1)=
      (incrementCovariance h : ℂ) := by
  have hs (j : ℤ) := weightedPhase_summable _ potentialMass_nonneg potentialMass_summable j
  simp only [potentialMoment_series]
  rw [← tsum_mul_left, ← (hs h |>.mul_left (2 : ℂ)).tsum_sub (hs (h-1)),
    ← ((hs h |>.mul_left (2 : ℂ)).sub (hs (h-1))).tsum_sub (hs (h+1))]
  simp_rw [potentialMass_second_difference]
  rw [← atomicMeasure_fourier _ incrementMass_nonneg incrementMass_summable]
  exact incrementMeasure_fourier h

theorem potentialMeasure_fourier (h : ℤ) :
    (∫ t, fourierCharacter h t ∂potentialMeasure) =
      (haarCovariance collisionPotential h : ℂ) := by
  have he := potential_spectral_moments_unique potentialMoment potentialMoment_even
    potentialMoment_zero potentialMoment_second_difference
  exact congrFun he h

end NField.Alignment.CollisionPotentialSpectralMoments
