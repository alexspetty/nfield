/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealPeriodicZetaEndpointLimit
import NField.Alignment.PrimitiveAnalyticSpecialValues
import NField.Alignment.LandscapeSourceMoments
import NField.Alignment.CenteredCollisionClosure

/-!
# The Analytic Collision Transform

## Coverage

All nine named results and all 63 display blocks have formal counterparts. The
cotangent kernel endpoint holds for every real argument strictly between zero
and one, including irrational arguments. Cross-conductor control and zero
location remain outside these claims.

## Scope and assumptions

The cotangent endpoint theorem has domain `0 < x < 1`; it does not include the
endpoints zero and one. It applies to every real argument in that interval,
not only rational residues. The coefficient, primitive fibers and analytic
observable use the manuscript's definitions and normalizations. Zero
multiplicities are those of the specified analytic observable. Cross-conductor
control and any zero-location assertion are outside the formalized claims.
-/

namespace NField.Papers.AnalyticCollisionTransform

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.AnalyticCollisionTransform

/-! ## The fixed diagonal -/

/-- The general direct boundary specializes to the manuscript's lag-one
diagonal exactly. -/
theorem exact_lag_one_diagonal_boundary
    (b : ℕ) [NeZero (allLagModulus b 1)]
    (χ : Character (allLagModulus b 1)) :
    directDiagonalBoundary b 1 χ =
      ∑ n ∈ diagonalSlices b, (χ (n + 1) - χ n) :=
  directDiagonalBoundary_lag_one b χ

/-- The direct diagonal contains exactly `b^ell` slices. -/
theorem exact_diagonal_cardinality {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell :=
  directDiagonal_cardinality hb2 hell

/-- Both endpoint slices are present before their singular kernel terms are
paired and cancelled. -/
theorem exact_diagonal_endpoints {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    0 ∈ allLagDiagonal b ell ∧
      allLagModulus b ell - 1 ∈ allLagDiagonal b ell :=
  directDiagonal_endpoints hb2 hell

/-! ## The open-strip factor -/

/-- The manuscript's common analytic prefactor never vanishes in the open
critical strip. -/
theorem exact_strip_prefactor_nonzero
    {m : ℕ} [NeZero m] {s : ℂ} (hs : s ∈ criticalStrip) :
    collisionStripPrefactor m s ≠ 0 :=
  collisionStripPrefactor_ne_zero hs

/-- The same prefactor is analytic at every point of the open strip. -/
theorem exact_strip_prefactor_analytic
    {m : ℕ} [NeZero m] {s : ℂ} (hs : s ∈ criticalStrip) :
    AnalyticAt ℂ (collisionStripPrefactor m) s :=
  collisionStripPrefactor_analyticAt hs

/-! ## Active and inactive character channels -/

/-- A vanishing fixed diagonal boundary makes the corresponding transform
channel vanish wherever the periodic-zeta factorization holds. -/
theorem inactive_character_channel
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (A : ℂ → ℂ) (χ : Character (allLagModulus b ell)) (s : ℂ)
    (hfactor : A s =
      collisionStripPrefactor (allLagModulus b ell) s *
        directDiagonalBoundary b ell χ *
          DirichletCharacter.LFunction (star χ) s)
    (hinactive : directDiagonalBoundary b ell χ = 0) :
    A s = 0 :=
  inactive_boundary_channel A (directDiagonalBoundary b ell χ)
    (DirichletCharacter.LFunction (star χ)) s hfactor hinactive

/-- An active transform and its continued conjugate L-function have the same
pointwise zeros in the open strip. -/
theorem active_character_zero_iff
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (A : ℂ → ℂ) (χ : Character (allLagModulus b ell))
    {s : ℂ} (hs : s ∈ criticalStrip)
    (hfactor : A s =
      collisionStripPrefactor (allLagModulus b ell) s *
        directDiagonalBoundary b ell χ *
          DirichletCharacter.LFunction (star χ) s)
    (hactive : directDiagonalBoundary b ell χ ≠ 0) :
    A s = 0 ↔ DirichletCharacter.LFunction (star χ) s = 0 :=
  active_boundary_zero_iff A (directDiagonalBoundary b ell χ)
    (DirichletCharacter.LFunction (star χ)) hs hfactor hactive

/-- The active transform and continued L-function have equal zero
multiplicity throughout the strip. -/
theorem active_character_zero_multiplicity
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (A : ℂ → ℂ) (χ : Character (allLagModulus b ell))
    (hodd : χ.Odd) {s : ℂ} (hs : s ∈ criticalStrip)
    (hfactor : Set.EqOn A
      (fun z => collisionStripPrefactor (allLagModulus b ell) z *
        directDiagonalBoundary b ell χ *
          DirichletCharacter.LFunction (star χ) z) criticalStrip)
    (hactive : directDiagonalBoundary b ell χ ≠ 0) :
    analyticOrderAt A s =
      analyticOrderAt (DirichletCharacter.LFunction (star χ)) s :=
  active_character_same_zero_multiplicity A χ hodd
    (directDiagonalBoundary b ell χ) hs hfactor hactive

/-! ## Boundary values -/

/-- At the left edge the Bernoulli-boundary value is exactly `i*pi` times
the finite collision coefficient. -/
theorem exact_left_boundary_recovery
    (m : ℕ) (B D : ℂ) :
    analyticLeftBoundaryValue m B D =
      Complex.I * (Real.pi : ℂ) *
        finiteCollisionBoundaryCoefficient m B D :=
  left_boundary_exact_recovery m B D

/-- The opposite boundary carries the separate Gauss twist. -/
theorem exact_right_boundary_gauss_twist
    (m : ℕ) (φ tau tauBar B D L : ℂ)
    (hpi : (Real.pi : ℂ) ≠ 0) (hφ : φ ≠ 0)
    (htau : tau * tauBar = -(m : ℂ))
    (hB : B = Complex.I / (Real.pi : ℂ) * tau * L) :
    Complex.I * (m : ℂ) / ((Real.pi : ℂ) * φ) * D * L =
      -tauBar / φ * B * D :=
  right_boundary_gauss_substitution m φ tau tauBar B D L
    hpi hφ htau hB

#check exact_lag_one_diagonal_boundary
#check exact_diagonal_cardinality
#check exact_diagonal_endpoints
#check exact_strip_prefactor_nonzero
#check exact_strip_prefactor_analytic
#check inactive_character_channel
#check active_character_zero_iff
#check active_character_zero_multiplicity
#check exact_left_boundary_recovery
#check exact_right_boundary_gauss_twist

end NField.Papers.AnalyticCollisionTransform

#check NField.Alignment.PrimitiveAnalyticKernel.hurwitz_character_sum
#check NField.Alignment.PrimitiveAnalyticKernel.periodic_kernel_base_sum
#check NField.Alignment.PrimitiveAnalyticKernel.periodic_kernel_model_sum
#check NField.Alignment.PrimitiveAnalyticKernel.coefficient_eq_inverse_sum
#check NField.Alignment.PrimitiveAnalyticKernel.primitive_centering_preserves_coefficient
#check NField.Alignment.PrimitiveAnalyticKernel.kernel_boundary_coefficient
#check NField.Alignment.PrimitiveAnalyticKernel.centered_kernel_boundary_factorization
#check NField.Alignment.PrimitiveAnalyticKernel.kernel_boundary_eq_paired
#check NField.Alignment.PrimitiveAnalyticKernel.diagonal_interior_eq_filter
#check NField.Alignment.PrimitiveAnalyticKernel.actual_finite_collision_coefficient
#check NField.Alignment.PrimitiveAnalyticKernel.actual_inactive_channel
#check NField.Alignment.PrimitiveAnalyticKernel.actual_active_zero_iff
#check NField.Alignment.PrimitiveAnalyticKernel.actual_active_zero_order
#check NField.Alignment.PrimitiveAnalyticEndpoints.periodic_kernel_gauss_sum
#check NField.Alignment.PrimitiveAnalyticEndpoints.periodic_kernel_left_sum
#check NField.Alignment.PrimitiveAnalyticEndpoints.odd_l_function_zero
#check NField.Alignment.PrimitiveAnalyticEndpoints.periodic_kernel_right_sum
#check NField.Alignment.PrimitiveAnalyticEndpoints.kernel_boundary_coefficient_gauss
#check NField.Alignment.PrimitiveAnalyticEndpoints.centered_kernel_boundary_gauss_factorization
#check NField.Alignment.PrimitiveAnalyticEndpoints.centered_kernel_boundary_differentiable
#check NField.Alignment.PrimitiveAnalyticEndpoints.actual_left_boundary
#check NField.Alignment.PrimitiveAnalyticEndpoints.actual_right_boundary
#check NField.Alignment.PrimitiveAnalyticEndpoints.actual_collision_recovery
#check NField.Alignment.PrimitiveAnalyticSpecialValues.hurwitz_odd_zero
#check NField.Alignment.PrimitiveAnalyticSpecialValues.hurwitz_zero
#check NField.Alignment.PrimitiveAnalyticSpecialValues.nonprincipal_l_function_zero
#check NField.Alignment.PrimitiveAnalyticSpecialValues.periodic_kernel_right_cotangent
#check NField.Alignment.PrimitiveAnalyticSpecialValues.periodic_kernel_left_log
#check NField.Alignment.PrimitiveAnalyticSpecialValues.periodic_kernel_differentiable
#check NField.Alignment.PrimitiveAnalyticSpecialValues.real_kernel_differentiable
#check NField.Alignment.PrimitiveAnalyticSpecialValues.periodic_kernel_residue
#check NField.Alignment.PrimitiveAnalyticSpecialValues.real_kernel_connection
#check NField.Alignment.PrimitiveAnalyticSpecialValues.periodic_amplitude_left_limit
#check NField.Alignment.PrimitiveAnalyticSpecialValues.primitive_odd_gauss_product
#check NField.Alignment.PrimitiveAnalyticSpecialValues.bernoulli_one_functional_relation
#check NField.Alignment.PrimitiveAnalyticSpecialValues.actual_right_l_value
#check NField.Alignment.PrimitiveAnalyticSpecialValues.nonzero_residue_mem_unit_interval
#check NField.Alignment.PrimitiveAnalyticSpecialValues.interior_arguments_ne_zero
#check NField.Alignment.PrimitiveAnalyticSpecialValues.centered_kernel_boundary_printed_mean
#check NField.Alignment.PrimitiveReductionFiber.primitive_fiber_sum_zero
#check NField.Alignment.PrimitiveReductionFiber.primitive_reduction_weight_sum_zero
#check NField.Alignment.CenteredPowerFibers.coarseUnitReduction_fiber_card
#check NField.Alignment.SawtoothLValue.primitiveOdd_gaussSum_normSq

#check NField.Alignment.RealPeriodicZetaEndpoint.real_kernel_right_cotangent
