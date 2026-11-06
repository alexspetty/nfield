/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerTransformBounds
import NField.Alignment.SquareLockAsymptoticScales

/-! # Literal printed bounds, with the small-prime and single-carrier scales retained -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryPrintedBounds
open scoped BigOperators
open PrimeCarrierDamping PrimeSecondaryCoefficient PrimeSquareCubicEnergy PrimeSquareReducedRatio
  DedekindAbelRemainder DedekindFourierMoment DedekindInverseResidueTransform

theorem harmonic_le_three_log_double {k : ℕ} (hk : 1 ≤ k) :
    (harmonic k : ℝ) ≤ 3*Real.log (2*(k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hhalf : (1/2 : ℝ) ≤ Real.log (2*(k : ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hlog : Real.log (k : ℝ) ≤ Real.log (2*(k : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  linarith [harmonic_le_one_add_log k]

/-- Title: `One carrier is controlled by its own harmonic number`. -/
theorem one_carrier_harmonic_bound {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    ‖modulusKSlice p k‖ ≤ (p : ℝ)*(harmonic k : ℝ)^2 := by
  have hPk : (p^2).Coprime k := (smallNatUnit_coprime hp (by omega) hkp).symm
  letI : NeZero k := ⟨by omega⟩
  have hb := norm_floorWeighted_residueDedekindSequence_le_of_two hk hkp
    (ZMod.unitOfCoprime (p^2) hPk)
  have hmoment := dedekindFirstMoment_le (by omega : 0 < k)
  have hfloor : (((p-1)/(k+1) : ℕ) : ℝ)*(k : ℝ) ≤ p := by
    exact_mod_cast (Nat.mul_le_mul_left ((p-1)/(k+1)) (Nat.le_succ k)).trans
      ((Nat.div_mul_le_self _ _).trans (Nat.sub_le p 1))
  rw [modulusKSlice,dif_neg (by omega : k≠0),dif_pos ⟨hk,hPk⟩]
  calc
    _ ≤ 4*(((p-1)/(k+1) : ℕ) : ℝ)*dedekindFirstMoment k := hb
    _ ≤ 4*(((p-1)/(k+1) : ℕ) : ℝ)*((k : ℝ)*(harmonic k : ℝ)^2/4) := by gcongr
    _ = ((((p-1)/(k+1) : ℕ) : ℝ)*(k : ℝ))*(harmonic k : ℝ)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfloor (sq_nonneg _)

/-- Title: `The first absolute Dedekind moment has the printed logarithmic bound`. -/
theorem first_absolute_moment_logarithmic {k : ℕ} [NeZero k] (hk : 2 ≤ k) :
    dedekindFirstMoment k ≤ (9/4 : ℝ)*(k : ℝ)*Real.log (2*(k : ℝ))^2 := by
  have hh := harmonic_le_three_log_double (by omega : 1 ≤ k)
  have hH : 0 ≤ (harmonic k : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
  calc
    _ ≤ (k : ℝ)*(harmonic k : ℝ)^2/4 := dedekindFirstMoment_le (by omega)
    _ ≤ (k : ℝ)*(3*Real.log (2*(k : ℝ)))^2/4 := by gcongr
    _ = _ := by ring

/-- Title: `The elementary one-carrier bound uses the carrier logarithm`. -/
theorem one_carrier_quadratic_logarithmic {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    ‖modulusKSlice p k‖ ≤ 9*(p : ℝ)*Real.log (2*(k : ℝ))^2 := by
  have hh := harmonic_le_three_log_double (by omega : 1 ≤ k)
  have hH : 0 ≤ (harmonic k : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
  calc
    _ ≤ (p : ℝ)*(harmonic k : ℝ)^2 := one_carrier_harmonic_bound hp hk hkp
    _ ≤ (p : ℝ)*(3*Real.log (2*(k : ℝ)))^2 := by gcongr
    _ = _ := by ring

/-- Title: `The all-prime sampling bound has exactly the printed scale`. -/
theorem sampling_bound_printed :
    ∃ C : ℝ,0 ≤ C ∧ ∀ p : ℕ,p.Prime → p≠2 →
      |primeSamplingDefect p| ≤ C*primePrintedSamplingScale p := by
  obtain ⟨C,hC,hb⟩ := primeSamplingDefect_strict_bound_from_analytic_inputs
    IntegerTransformBounds.ambient_inverse_bound
  refine ⟨3*C,by positivity,?_⟩
  intro p hp hodd
  calc
    _ ≤ C*primeStrictSamplingScale p := hb p hp
    _ ≤ C*(3*primePrintedSamplingScale p) :=
      mul_le_mul_of_nonneg_left (primeStrictSamplingScale_le_printed (by have := hp.two_le; omega)) hC
    _ = _ := by ring

theorem printed_scale_le_log_square {p : ℕ} (hp : 3 ≤ p) :
    primePrintedSamplingScale p ≤ 8*Real.log (p : ℝ)^2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hl3 : (1 : ℝ) ≤ Real.log 3 := Real.log_three_gt_d9.le.trans' (by norm_num)
  have hlog3 : 2 ≤ Real.log (3*(p : ℝ)) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ)<3) hpR
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hden : (1/2 : ℝ) ≤ Real.log (Real.log (3*(p : ℝ))) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) hlog3)
  unfold primePrintedSamplingScale
  apply (div_le_iff₀ (by linarith : 0 < Real.log (Real.log (3*(p : ℝ))))).mpr
  have hdouble := SquareLockAsymptoticScales.log_double_le (by omega : 2 ≤ p)
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  nlinarith [mul_le_mul_of_nonneg_right hden (sq_nonneg (Real.log (p : ℝ)))]

/-- Title: `The actual sampling defect has the unconditional quadratic logarithmic bound`. -/
theorem sampling_bound_quadratic_logarithmic :
    ∃ C : ℝ,0 ≤ C ∧ ∀ p : ℕ,p.Prime → p≠2 →
      |primeSamplingDefect p| ≤ C*Real.log (p : ℝ)^2 := by
  obtain ⟨C,hC,hb⟩ := sampling_bound_printed
  refine ⟨8*C,by positivity,?_⟩
  intro p hp hodd
  calc
    _ ≤ C*primePrintedSamplingScale p := hb p hp hodd
    _ ≤ C*(8*Real.log (p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (printed_scale_le_log_square (by have := hp.two_le; omega)) hC
    _ = _ := by ring

end NField.Alignment.SecondaryPrintedBounds
