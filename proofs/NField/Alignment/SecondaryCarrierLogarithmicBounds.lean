/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerTransformBounds
import NField.Alignment.PrimeCarrierDamping

/-! # The printed individual and absolute carrier bounds -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryCarrierLogarithmicBounds
open scoped BigOperators Classical
open DedekindInverseResidueTransform DedekindCarrierFourierBound DedekindAbelRemainder
  PrimeCarrierDamping PrimeSquareCubicEnergy PrimeSquareReducedRatio ReciprocalDivisorMomentBound

theorem own_transform_bound : UniformAdditiveTransformEstimate :=
  uniform_additive_transform_bound IntegerTransformBounds.ambient_inverse_bound

/-- Title: `Every integer carrier interval has the logarithmic transform bound`. -/
theorem integer_carrier_prefix_log_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (k : ℕ) [NeZero k],2 ≤ k → ∀ β : (ZMod k)ˣ,
      ∀ a : ℤ,∀ length : ℕ,
      ‖∑ j ∈ Finset.range length,residueDedekindFunction β ((a : ZMod k)+(j : ZMod k))‖ ≤
        C*(k : ℝ)*logarithmicCarrierSamplingScale k*reciprocalDivisorSum k^3 := by
  obtain ⟨C,hC,htransform⟩ := own_transform_bound
  refine ⟨2*C,by positivity,?_⟩
  intro k inst hk β a length
  let U := C*inverseResidueHarmonicScale k*reciprocalDivisorSum k^3
  have hσ : 0 ≤ reciprocalDivisorSum k^3 := pow_nonneg (reciprocalDivisorSum_nonneg _) _
  have hU : 0 ≤ U := by dsimp [U]; positivity [inverseResidueHarmonicScale_nonneg hk]
  have hb := norm_residueDedekindSequence_interval_le_of_transform hk β hU
    (fun t => htransform k t hk) (a : ZMod k).val length
  have he : (∑ j ∈ Finset.range length,
      residueDedekindFunction β ((a : ZMod k)+(j : ZMod k)))=
      ∑ j ∈ Finset.range length,residueDedekindSequence β ((a : ZMod k).val+j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← residueDedekindFunction_natCast]
    simp
  rw [he]
  calc
    _ ≤ (k : ℝ)*U*(harmonic k : ℝ) := hb
    _ = C*(k : ℝ)*strictCarrierSamplingScale k*reciprocalDivisorSum k^3 := by
      simp only [U,strictCarrierSamplingScale,if_pos hk]
      ring
    _ ≤ C*(k : ℝ)*(2*logarithmicCarrierSamplingScale k)*reciprocalDivisorSum k^3 := by
      gcongr
      exact strictCarrierSamplingScale_le_logarithmic k
    _ = _ := by ring

/-- Title: `One carrier has the printed logarithmic damping bound`. -/
theorem one_carrier_log_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p k : ℕ),p.Prime → 2 ≤ k → k<p →
      ‖modulusKSlice p k‖ ≤
        C*(p : ℝ)*logarithmicCarrierSamplingScale k*reciprocalDivisorSum k^3 := by
  obtain ⟨C,hC,htransform⟩ := own_transform_bound
  refine ⟨4*C,by positivity,?_⟩
  intro p k hp hk hkp
  have hPk : (p^2).Coprime k := (smallNatUnit_coprime hp (by omega) hkp).symm
  letI : NeZero k := ⟨by omega⟩
  let β : (ZMod k)ˣ := ZMod.unitOfCoprime (p^2) hPk
  let U := C*inverseResidueHarmonicScale k*reciprocalDivisorSum k^3
  have hσ : 0 ≤ reciprocalDivisorSum k^3 := pow_nonneg (reciprocalDivisorSum_nonneg _) _
  have hH : 0 ≤ (harmonic k : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity [inverseResidueHarmonicScale_nonneg hk]
  have hb := norm_floorWeighted_residueDedekindSequence_le_of_transform hk hkp β hU
    (fun t => htransform k t hk)
  have hfloor : (((p-1)/(k+1) : ℕ) : ℝ)*(k : ℝ) ≤ p := by
    exact_mod_cast (Nat.mul_le_mul_left ((p-1)/(k+1)) (Nat.le_succ k)).trans
      ((Nat.div_mul_le_self _ _).trans (Nat.sub_le p 1))
  rw [modulusKSlice,dif_neg (by omega : k≠0),dif_pos ⟨hk,hPk⟩]
  calc
    _ ≤ 2*(((p-1)/(k+1) : ℕ) : ℝ)*((k : ℝ)*U*(harmonic k : ℝ)) := hb
    _ = 2*((((p-1)/(k+1) : ℕ) : ℝ)*(k : ℝ))*U*(harmonic k : ℝ) := by ring
    _ ≤ 2*(p : ℝ)*U*(harmonic k : ℝ) := by gcongr
    _ = 2*C*(p : ℝ)*strictCarrierSamplingScale k*reciprocalDivisorSum k^3 := by
      simp only [U,strictCarrierSamplingScale,if_pos hk]
      ring
    _ ≤ 2*C*(p : ℝ)*(2*logarithmicCarrierSamplingScale k)*reciprocalDivisorSum k^3 := by
      gcongr
      exact strictCarrierSamplingScale_le_logarithmic k
    _ = _ := by ring

/-- Title: `The sum of absolute carrier contributions has logarithmic damping`. -/
theorem absolute_carrier_sum_log_bound :
    ∃ K : ℝ,0 ≤ K ∧ ∀ p,p.Prime →
      (∑ k ∈ Finset.Ico 2 p,‖modulusKSlice p k‖) ≤ K*logarithmicCarrierReservoirScale p := by
  obtain ⟨C,hC,hambient⟩ := IntegerTransformBounds.ambient_inverse_bound
  obtain ⟨M,hM,hmoment⟩ := bounded_reciprocal_divisor_moments 3 (by omega)
  refine ⟨4*C*M,by positivity,?_⟩
  intro p hp
  have hscale := inverseResidueHarmonicScale_nonneg hp.two_le
  have hH : 0 ≤ (harmonic p : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
  have hsum : (∑ k ∈ Finset.Ico 2 p,reciprocalDivisorSum k^3) ≤ M*p := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg
      (show Finset.Ico 2 p ⊆ Finset.Icc 1 p by
        intro k hk
        simp only [Finset.mem_Ico,Finset.mem_Icc] at hk ⊢
        omega)
      (fun k _ _ => pow_nonneg (reciprocalDivisorSum_nonneg k) 3)).trans
    exact hmoment p
  calc
    _ ≤ ∑ k ∈ Finset.Ico 2 p,2*C*(p : ℝ)*inverseResidueHarmonicScale p*
        (harmonic p : ℝ)*reciprocalDivisorSum k^3 := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_modulusKSlice_le_of_ambient_inverse_estimate hp
        (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2 hC hambient
    _ = 2*C*(p : ℝ)*inverseResidueHarmonicScale p*(harmonic p : ℝ)*
        ∑ k ∈ Finset.Ico 2 p,reciprocalDivisorSum k^3 := by rw [Finset.mul_sum]
    _ ≤ 2*C*(p : ℝ)*inverseResidueHarmonicScale p*(harmonic p : ℝ)*(M*p) := by gcongr
    _ = 2*C*M*strictCarrierReservoirScale p := by
      simp only [strictCarrierReservoirScale,strictCarrierSamplingScale,if_pos hp.two_le]
      ring
    _ ≤ 2*C*M*(2*logarithmicCarrierReservoirScale p) := by
      gcongr
      exact strictCarrierReservoirScale_le_logarithmic p
    _ = _ := by ring

end NField.Alignment.SecondaryCarrierLogarithmicBounds
