/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectrumLandscape
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The analytic collision transform

Reusable finite-diagonal, strip-prefactor, boundary-recovery, and
zero-multiplicity algebra for the Lean companion to
"The Analytic Collision Transform".
-/

namespace NField.Alignment.AnalyticCollisionTransform

open scoped BigOperators ComplexConjugate Topology
open Set Filter
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionSpectrumLandscape

/-! ## The fixed finite diagonal -/

/-- The direct oriented character boundary on the first/last-digit
diagonal.  Its type makes explicit that it has no analytic parameter. -/
noncomputable def directDiagonalBoundary
    (b ell : ℕ) [NeZero (allLagModulus b ell)]
    (χ : Character (allLagModulus b ell)) : ℂ :=
  ∑ n ∈ allLagDiagonal b ell, (χ (n + 1) - χ n)

/-- At lag one the general first/last-digit diagonal is exactly the familiar
`(b + 1)d` diagonal. -/
theorem allLagDiagonal_one_eq_diagonalSlices (b : ℕ) :
    allLagDiagonal b 1 = diagonalSlices b := by
  unfold allLagDiagonal diagonalSlices
  ext n
  simp only [Nat.reduceSub, pow_zero, pow_one]
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨⟨d, k⟩, hdk, rfl⟩
    have hd := (Finset.mem_product.mp hdk).1
    have hk := (Finset.mem_product.mp hdk).2
    have hklt : k < 1 := Finset.mem_range.mp hk
    have hk0 : k = 0 := by omega
    subst k
    apply Finset.mem_image.mpr
    refine ⟨d, hd, ?_⟩
    simp
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨d, hd, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(d, 0), Finset.mem_product.mpr ⟨hd, by simp⟩, ?_⟩
    simp

/-- Consequently the general direct boundary specializes exactly to the
lag-one diagonal boundary used by the finite collision coefficient. -/
theorem directDiagonalBoundary_lag_one
    (b : ℕ) [NeZero (allLagModulus b 1)]
    (χ : Character (allLagModulus b 1)) :
    directDiagonalBoundary b 1 χ =
      ∑ n ∈ diagonalSlices b, (χ (n + 1) - χ n) := by
  unfold directDiagonalBoundary
  rw [allLagDiagonal_one_eq_diagonalSlices]

/-- The fixed diagonal has the exact cardinality asserted in the analytic
transform at every positive lag. -/
theorem directDiagonal_cardinality {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell :=
  allLagDiagonal_card hb2 hell

/-- Both endpoint slices used in the manuscript's paired kernel belong to
the fixed diagonal. -/
theorem directDiagonal_endpoints {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    0 ∈ allLagDiagonal b ell ∧
      allLagModulus b ell - 1 ∈ allLagDiagonal b ell :=
  ⟨allLagDiagonal_zero_mem hb2, allLagDiagonal_last_mem hb2 hell⟩

/-! ## The analytic strip prefactor -/

/-- The open critical strip used by the transform. -/
def criticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

theorem criticalStrip_isOpen : IsOpen criticalStrip := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- The character-independent analytic factor in the manuscript's main
factorization. -/
noncomputable def collisionStripPrefactor (m : ℕ) (s : ℂ) : ℂ :=
  (2 * Complex.I * Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.Gamma s /
      (m.totient : ℂ)) *
    (((m : ℂ) / (2 * (Real.pi : ℂ))) ^ s)

private theorem strip_sine_ne_zero {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hk
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    Real.pi_ne_zero
  have hsEq : s = 2 * (k : ℂ) := by
    apply (mul_left_cancel₀ hpi)
    calc
      (Real.pi : ℂ) * s = 2 * ((Real.pi : ℂ) * s / 2) := by ring
      _ = 2 * ((k : ℂ) * (Real.pi : ℂ)) := by rw [hk]
      _ = (Real.pi : ℂ) * (2 * (k : ℂ)) := by ring
  have hre : s.re = 2 * (k : ℝ) := by
    rw [hsEq]
    simp
  have hkpos : 0 < k := by
    by_contra hknot
    have hkle : k ≤ 0 := le_of_not_gt hknot
    have : (k : ℝ) ≤ 0 := by exact_mod_cast hkle
    linarith
  have hkone : 1 ≤ k := by omega
  have : (1 : ℝ) ≤ k := by exact_mod_cast hkone
  linarith

/-- The strip prefactor never vanishes in the open critical strip. -/
theorem collisionStripPrefactor_ne_zero
    {m : ℕ} [NeZero m] {s : ℂ} (hs : s ∈ criticalStrip) :
    collisionStripPrefactor m s ≠ 0 := by
  rcases hs with ⟨hs0, hs1⟩
  have htwoI : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  have hsin := strip_sine_ne_zero hs0 hs1
  have hGamma : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs0
  have htot : (m.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  have hbase : (m : ℂ) / (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (NeZero.ne m)
    · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : ((m : ℂ) / (2 * (Real.pi : ℂ))) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  unfold collisionStripPrefactor
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero (mul_ne_zero htwoI hsin) hGamma) htot) hpow

private theorem Gamma_analyticAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact Complex.differentiableAt_Gamma z fun n hzn => by
    have hre := congrArg Complex.re hzn
    simp at hre
    linarith

/-- The strip prefactor is analytic at every point of the open strip. -/
theorem collisionStripPrefactor_analyticAt
    {m : ℕ} [NeZero m] {s : ℂ} (hs : s ∈ criticalStrip) :
    AnalyticAt ℂ (collisionStripPrefactor m) s := by
  rcases hs with ⟨hs0, _hs1⟩
  have hGamma := Gamma_analyticAt_of_re_pos hs0
  have hbase : (m : ℂ) / (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (NeZero.ne m)
    · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : AnalyticAt ℂ
      (fun z : ℂ => ((m : ℂ) / (2 * (Real.pi : ℂ))) ^ z) s :=
    (differentiable_id.const_cpow (Or.inl hbase)).analyticAt s
  unfold collisionStripPrefactor
  fun_prop

/-! ## The actual Dirichlet L-function channel -/

/-- An odd character is nonprincipal, and its conjugate L-function is
analytic everywhere. -/
theorem conjugateLFunction_analyticAt_of_odd
    {m : ℕ} [NeZero m] (χ : Character m) (hodd : χ.Odd) (s : ℂ) :
    AnalyticAt ℂ (DirichletCharacter.LFunction (star χ)) s := by
  have hχ : χ ≠ 1 := by
    intro h
    apply hodd.not_even
    rw [h]
    unfold DirichletCharacter.Even
    exact MulChar.one_apply isUnit_neg_one
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    apply star_injective
    simpa using h
  exact (DirichletCharacter.differentiable_LFunction hstar).analyticAt s

/-! ## Consequences of the periodic-zeta factorization -/

/-- A zero diagonal boundary makes the analytic channel identically zero
wherever the main factorization holds. -/
theorem inactive_boundary_channel
    {m : ℕ} (A : ℂ → ℂ) (D : ℂ)
    (L : ℂ → ℂ) (s : ℂ)
    (hfactor : A s = collisionStripPrefactor m s * D * L s)
    (hD : D = 0) :
    A s = 0 := by
  rw [hfactor, hD]
  ring

/-- For an active boundary, the transform and its L-function have exactly
the same pointwise zeros in the open strip. -/
theorem active_boundary_zero_iff
    {m : ℕ} [NeZero m] (A : ℂ → ℂ) (D : ℂ)
    (L : ℂ → ℂ) {s : ℂ} (hs : s ∈ criticalStrip)
    (hfactor : A s = collisionStripPrefactor m s * D * L s)
    (hD : D ≠ 0) :
    A s = 0 ↔ L s = 0 := by
  rw [hfactor, mul_eq_zero]
  simp [collisionStripPrefactor_ne_zero hs, hD]

/-- The multiplicity statement behind zero visibility.  If the periodic-zeta
factorization holds on the strip, multiplication by its analytic nonzero
prefactor and an active fixed boundary leaves the analytic order unchanged. -/
theorem active_boundary_analyticOrderAt
    {m : ℕ} [NeZero m] (A : ℂ → ℂ) (D : ℂ)
    (L : ℂ → ℂ) {s : ℂ} (hs : s ∈ criticalStrip)
    (hfactor : Set.EqOn A
      (fun z => collisionStripPrefactor m z * D * L z) criticalStrip)
    (hL : AnalyticAt ℂ L s) (hD : D ≠ 0) :
    analyticOrderAt A s = analyticOrderAt L s := by
  have hevent : A =ᶠ[𝓝 s]
      fun z => collisionStripPrefactor m z * D * L z := by
    filter_upwards [criticalStrip_isOpen.mem_nhds hs] with z hz
    exact hfactor hz
  rw [analyticOrderAt_congr hevent]
  let P : ℂ → ℂ := fun z => collisionStripPrefactor m z * D
  have hP : AnalyticAt ℂ P s :=
    (collisionStripPrefactor_analyticAt hs).mul (analyticAt_const)
  have hPs : P s ≠ 0 :=
    mul_ne_zero (collisionStripPrefactor_ne_zero hs) hD
  change analyticOrderAt (P * L) s = analyticOrderAt L s
  rw [analyticOrderAt_mul hP hL,
    (hP.analyticOrderAt_eq_zero).mpr hPs, zero_add]

/-- The manuscript's multiplicity conclusion specialized to Mathlib's
continued Dirichlet L-function. -/
theorem active_character_same_zero_multiplicity
    {m : ℕ} [NeZero m] (A : ℂ → ℂ)
    (χ : Character m) (hodd : χ.Odd) (D : ℂ)
    {s : ℂ} (hs : s ∈ criticalStrip)
    (hfactor : Set.EqOn A
      (fun z => collisionStripPrefactor m z * D *
        DirichletCharacter.LFunction (star χ) z) criticalStrip)
    (hD : D ≠ 0) :
    analyticOrderAt A s =
      analyticOrderAt (DirichletCharacter.LFunction (star χ)) s :=
  active_boundary_analyticOrderAt A D
    (DirichletCharacter.LFunction (star χ)) hs hfactor
    (conjugateLFunction_analyticAt_of_odd χ hodd s) hD

/-! ## Exact boundary recovery algebra -/

/-- The finite collision coefficient written in the Bernoulli-boundary
factorized form. -/
noncomputable def finiteCollisionBoundaryCoefficient
    (m : ℕ) (B D : ℂ) : ℂ :=
  -(B * D) / (m.totient : ℂ)

/-- The removable left-boundary value of the analytic transform. -/
noncomputable def analyticLeftBoundaryValue
    (m : ℕ) (B D : ℂ) : ℂ :=
  -(Complex.I * (Real.pi : ℂ)) / (m.totient : ℂ) * B * D

/-- The left-boundary value recovers the complete complex finite collision
coefficient with the single universal factor `i*pi`. -/
theorem left_boundary_exact_recovery (m : ℕ) (B D : ℂ) :
    analyticLeftBoundaryValue m B D =
      Complex.I * (Real.pi : ℂ) * finiteCollisionBoundaryCoefficient m B D := by
  unfold analyticLeftBoundaryValue finiteCollisionBoundaryCoefficient
  ring

/-- Pure algebra for the Gauss-twisted opposite boundary. -/
theorem right_boundary_gauss_substitution
    (m : ℕ) (φ tau tauBar B D L : ℂ)
    (hpi : (Real.pi : ℂ) ≠ 0) (hφ : φ ≠ 0)
    (htau : tau * tauBar = -(m : ℂ))
    (hB : B = Complex.I / (Real.pi : ℂ) * tau * L) :
    Complex.I * (m : ℂ) / ((Real.pi : ℂ) * φ) * D * L =
      -tauBar / φ * B * D := by
  rw [hB]
  field_simp
  have htau' : tauBar * tau = -(m : ℂ) := by
    rw [mul_comm]
    exact htau
  rw [show D * L * tauBar * tau = D * L * (tauBar * tau) by ring,
    htau']
  ring

end NField.Alignment.AnalyticCollisionTransform
