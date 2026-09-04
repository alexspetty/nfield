/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthWeight
import NField.Alignment.DepthWeightedBoundaryFactorization

/-!
# Conductor-depth boundary factorization

This module composes the intrinsic prime-power response theorem with finite
cyclic summation by parts. The resulting statements are the cell-difference
and signed-boundary forms of the conductor-stratified carry factorization.
-/

namespace NField.Alignment.ConductorDepthFactorization

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.ConductorDepthWeight
open NField.Alignment.DepthWeightedBoundaryFactorization

/-- Cell-difference form of the exact conductor-stratified factorization. -/
theorem conductorDepth_carry_factorization
    {p t s : ℕ} [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t)
    (w : ZMod (p ^ t * p ^ s) → ℂ)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    characterCarryTransform w
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ) =
      -(twistedTransform (m := p ^ t) centeredSawtooth ψ 1 *
        depthDifferencePairing w (conductorDepthWeight p t s ψ)) := by
  exact carryTransform_of_exact_response w _ _ _
    (conductorDepthWeight_exact_response hp ht hψ)

/-- Signed-boundary-chain form of the exact conductor-stratified factorization. -/
theorem conductorDepth_boundary_factorization
    {p t s : ℕ} [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t)
    (w : ZMod (p ^ t * p ^ s) → ℂ)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    characterCarryTransform w
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ) =
      -(twistedTransform (m := p ^ t) centeredSawtooth ψ 1 *
        depthBoundaryPairing w (conductorDepthWeight p t s ψ)) := by
  exact carryTransform_of_exact_boundary_response w _ _ _
    (conductorDepthWeight_exact_response hp ht hψ)

end NField.Alignment.ConductorDepthFactorization
