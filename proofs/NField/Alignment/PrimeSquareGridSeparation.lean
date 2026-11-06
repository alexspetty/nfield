/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealBernoulliJumpData
import NField.Alignment.PrimeSquareReducedRatio

/-! # The nonzero prime-square grid avoids all boundary jumps -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.PrimeSquareGridSeparation
open RealBernoulliBoundaryLimits RealBernoulliJumpData PrimeSquareReducedRatio

theorem nonzero_grid_fract {p A r : ℕ} (hp : p.Prime) (hA : 0 < A)
    (hAp : A < p^2) (hr : r ∈ Finset.range (p-1)) :
    Int.fract (((r+1 : ℕ) : ℝ)*((A : ℝ)/(p:ℝ)^2)) ≠ 0 := by
  have hrp : r+1 < p := by have := Finset.mem_range.mp hr; omega
  have hcop := smallNatUnit_coprime hp (by omega : 0 < r+1) hrp
  have hp0 : (p : ℝ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  rw [← mul_div_assoc, ← Nat.cast_mul, ← Nat.cast_pow,
    Int.fract_div_natCast_eq_div_natCast_mod]
  intro hzero
  have hmod : (r+1)*A % p^2 = 0 := by
    have hnum := (div_eq_zero_iff.mp hzero).resolve_right (by exact_mod_cast hp0)
    exact_mod_cast hnum
  have hdvd : p^2 ∣ A := hcop.symm.dvd_mul_left.mp (Nat.dvd_of_mod_eq_zero hmod)
  exact (Nat.le_of_dvd hA hdvd).not_gt hAp

/-- Title: `The nonzero sampling grid avoids every Bernoulli jump`. -/
theorem nonzero_grid_halfJump {p A : ℕ} (hp : p.Prime) (hA : 0 < A)
    (hAp : A < p^2) : halfJump (p-1) ((A : ℝ)/(p:ℝ)^2) = 0 := by
  unfold halfJump
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun r hr => nonzero_grid_fract hp hA hAp hr

/-- Title: `The actual derivative at every nonzero prime-square grid point`. -/
theorem boundary_derivative_on_grid {p A : ℕ} (hp : p.Prime) (hA : 0 < A)
    (hAp : A < p^2) :
    HasDerivAt (realBoundary (p-1)) (realSlope (p-1)) ((A : ℝ)/(p:ℝ)^2) :=
  boundary_deriv (fun _ hr => nonzero_grid_fract hp hA hAp hr)

end NField.Alignment.PrimeSquareGridSeparation
