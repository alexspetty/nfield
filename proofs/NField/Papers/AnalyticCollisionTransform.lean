/-
Author: Alexander S. Petty
-/

import NField.Alignment.AnalyticCollisionTransform

/-!
# The Analytic Collision Transform

Reader-facing theorem map for the Lean companion to
`papers/the_analytic_collision_transform.tex`.

## Checked here

* The fixed first/last-digit diagonal has exactly the manuscript's lag-one
  form, its general cardinality is `b^ell`, and both singular endpoint slices
  belong to it.
* The exact gamma-sine-power prefactor from the manuscript is defined with
  Euler's totient normalization.  Lean proves that it is analytic and nonzero
  throughout the open critical strip.
* Mathlib's analytically continued Dirichlet L-function for the conjugate of
  an odd character is analytic.
* Once the periodic-zeta factorization is supplied, a zero diagonal boundary
  kills the channel, while an active boundary gives exactly the same zeros as
  the continued L-function.
* The equality is proved at the level of `analyticOrderAt`, so multiplicities
  agree rather than only the zero sets.
* Lean checks the exact left-boundary recovery factor `i*pi` and the separate
  Gauss-twisted right-boundary substitution.

## Boundary

Mathlib contains Hurwitz zeta functions and continued Dirichlet L-functions,
but this companion does not yet prove the manuscript's periodic-zeta model
sum over primitive congruence fibers.  The main transform factorization is
therefore an explicit hypothesis of the zero-visibility and multiplicity
theorems, not a hidden declaration.  The prior finite companion also
does not yet join every concrete floor-jump slice to its Bernoulli transform
in one theorem.  Consequently the analytic factorization and the fully
concrete finite-coefficient bridge remain the two stated assembly boundaries.

The zero theorem is conditional only on that factorization.  It makes no
critical-line, zero-free-region, cross-conductor, or GRH claim.  No manuscript
contradiction appeared in the formalized layer, and no unchecked declaration
is used.
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
