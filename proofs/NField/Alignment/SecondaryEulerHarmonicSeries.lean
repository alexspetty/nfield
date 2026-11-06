/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CollisionHarmonicSeed

/-! # The Euler harmonic-series route to the coprime normalization -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryEulerHarmonicSeries
open CollisionHarmonicSeed CollisionAmplitudeArithmetic CollisionRemainderDynamics
  CollisionMassReadout SecondaryCapacityLedger

/-- Title: `Euler's harmonic reciprocal-square sum`. -/
theorem harmonic_reciprocal_square_has_sum :
    HasSum (fun k : ℕ => (harmonic (k-1):ℝ)/(k:ℝ)^2) zetaThree :=
  harmonicKernel_hasSum

/-- Title: `Coprime normalization through the zeta-three harmonic series`. -/
theorem coprime_euler_harmonic_identity :
    (∑' k : ℕ,reducedHarmonicStar k/(k:ℝ)^2)=
      zetaThree⁻¹*∑' k : ℕ,(harmonic (k-1):ℝ)/(k:ℝ)^2 := by
  change (∑' k,collisionWeight k)=zetaThree⁻¹*∑' k,harmonicKernel k
  rw [collisionWeight_tsum,harmonicKernel_hasSum.tsum_eq,inv_mul_cancel₀ zetaThree_pos.ne']

end NField.Alignment.SecondaryEulerHarmonicSeries
