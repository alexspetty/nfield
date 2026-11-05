/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.AnalyticCollisionTransform
import NField.Alignment.PrimitiveReductionFiber
import NField.Alignment.LandscapeActualSpectrum
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! # Primitive transforms of the actual periodic-zeta kernel

The kernel is Mathlib's analytically continued exponential zeta function.
The proof uses its functional equation and the existing primitive finite
transform, including nonunit multipliers.
-/

noncomputable section
namespace NField.Alignment.PrimitiveAnalyticKernel

open scoped BigOperators ComplexConjugate
open CollisionCharacterStructure CarryBoundarySpectra AnalyticCollisionTransform

/-- The periodic-zeta kernel at a residue, with the parameter of the manuscript. -/
def periodicKernel {q : ℕ} [NeZero q] (a : ZMod q) (s : ℂ) : ℂ :=
  HurwitzZeta.expZeta (ZMod.toAddCircle a) (1 - s)

/-- The unnormalized common factor of every primitive odd model sum. -/
def periodicAmplitude (q : ℕ) (s : ℂ) : ℂ :=
  2 * Complex.I * Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.Gamma s *
    (((q : ℂ) / (2 * (Real.pi : ℂ))) ^ s)

theorem hurwitz_character_sum {q : ℕ} [NeZero q]
    (χ : Character q) (s : ℂ) :
    (∑ a : ZMod q, HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s * χ a) =
      (q : ℂ) ^ s * DirichletCharacter.LFunction χ s := by
  unfold DirichletCharacter.LFunction ZMod.LFunction
  rw [Complex.cpow_neg]
  have hq : (q : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem strip_parameter_avoids_integers {s : ℂ} (hs : s ∈ criticalStrip) :
    ∀ n : ℕ, s ≠ 1 - n := by
  intro n hn
  have hre := congrArg Complex.re hn
  simp at hre
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hzero : n = 0
  · simp [hzero] at hre
    linarith [hs.2]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    linarith [hs.1]

theorem inverse_odd {q : ℕ} (χ : Character q) (hodd : χ.Odd) :
    (χ⁻¹).Odd := by
  change χ⁻¹ (-1) = -1
  rw [MulChar.inv_apply_eq_inv', hodd]
  norm_num

theorem periodic_kernel_base_sum {q : ℕ} [NeZero q]
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    {s : ℂ} (hs : s ∈ criticalStrip) :
    twistedTransform (fun a : ZMod q => periodicKernel a s) χ⁻¹ 1 =
      periodicAmplitude q s * DirichletCharacter.LFunction χ⁻¹ s := by
  let U := ∑ a : ZMod q, HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s * χ⁻¹ a
  have hU : U = (q : ℂ) ^ s * DirichletCharacter.LFunction χ⁻¹ s :=
    hurwitz_character_sum χ⁻¹ s
  have hV : (∑ a : ZMod q,
      HurwitzZeta.hurwitzZeta (-ZMod.toAddCircle a) s * χ⁻¹ a) = -U := by
    have h := twistedTransform_eq_inv_mul
      (fun a : ZMod q => HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s)
      (inverse_isPrimitive hprim) (-1 : ZMod q)
    have hodd' : χ (-1 : ZMod q) = -1 := hodd
    simpa only [twistedTransform, neg_one_mul, map_neg, one_mul, inv_inv,
      hodd', U] using h
  unfold twistedTransform periodicKernel
  simp only [one_mul]
  simp_rw [HurwitzZeta.expZeta_one_sub _ (strip_parameter_avoids_integers hs)]
  have hsum : (∑ a : ZMod q,
      ((2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
        (Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s +
          Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) *
            HurwitzZeta.hurwitzZeta (-ZMod.toAddCircle a) s)) * χ⁻¹ a) =
      ((2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s) *
        (Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) * U -
          Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) * U) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hV]
    ring
  rw [hsum, hU]
  have hsin : Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) -
      Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) =
      2 * Complex.I * Complex.sin ((Real.pi : ℂ) * s / 2) := by
    rw [Complex.sin]
    have h1 : (Real.pi : ℂ) * s / 2 * Complex.I =
        (Real.pi : ℂ) * Complex.I * s / 2 := by ring
    have h2 : -((Real.pi : ℂ) * s / 2) * Complex.I =
        -(Real.pi : ℂ) * Complex.I * s / 2 := by ring
    rw [h1, h2]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hpow : ((2 * (Real.pi : ℂ)) ^ (-s)) * (q : ℂ) ^ s =
      ((q : ℂ) / (2 * (Real.pi : ℂ))) ^ s := by
    have hden : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hraw := Complex.mul_cpow_ofReal_nonneg
      (by positivity : (0 : ℝ) ≤ (q : ℝ) / (2 * Real.pi))
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi) s
    have hproduct : (q : ℂ) ^ s =
        ((q : ℂ) / (2 * (Real.pi : ℂ))) ^ s * (2 * (Real.pi : ℂ)) ^ s := by
      simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
        Complex.ofReal_ofNat, div_mul_cancel₀ _ hden] using hraw
    have hnonzero : (2 * (Real.pi : ℂ)) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hden)
    rw [Complex.cpow_neg, hproduct]
    field_simp
  unfold periodicAmplitude
  calc
    _ = (Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) -
          Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2)) * Complex.Gamma s *
        (((2 * (Real.pi : ℂ)) ^ (-s)) * (q : ℂ) ^ s) *
          DirichletCharacter.LFunction χ⁻¹ s := by ring
    _ = _ := by rw [hsin, hpow]

/-- The literal model sum, for every multiplier including nonunits. -/
theorem periodic_kernel_model_sum {q : ℕ} [NeZero q]
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    {s : ℂ} (hs : s ∈ criticalStrip) (n : ZMod q) :
    (∑ a : UnitClass q, periodicKernel (n * a.val) s * χ⁻¹ a.val) =
      χ n * periodicAmplitude q s * DirichletCharacter.LFunction χ⁻¹ s := by
  have h := twistedTransform_eq_inv_mul
    (fun a : ZMod q => periodicKernel a s) (inverse_isPrimitive hprim) n
  rw [inv_inv, periodic_kernel_base_sum χ hprim hodd hs] at h
  unfold twistedTransform at h
  rw [sum_character_pairing_eq_units] at h
  simpa only [mul_assoc] using h

open CenteredCollisionSum CollisionTransformStrip NeutralityTheorem
  PrimitiveReductionFiber

/-- A centered character coefficient in the literal inverse-character convention. -/
theorem coefficient_eq_inverse_sum {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (χ : Character q) :
    collisionCoefficient F χ =
      (q.totient : ℂ)⁻¹ * ∑ a : UnitClass q, F a * χ⁻¹ a.val := by
  unfold collisionCoefficient finiteCoefficient
  rw [ZMod.card_units_eq_totient]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [MulChar.star_apply']

/-- Subtracting actual reduction-fiber means preserves a primitive coefficient. -/
theorem primitive_centering_preserves_coefficient {q d : ℕ} [NeZero q] [NeZero d]
    (hd : d ∣ q) (hdlt : d < q) (F : UnitClass q → ℂ)
    (χ : Character q) (hprim : χ.IsPrimitive) :
    collisionCoefficient (centeredSignal (ZMod.unitsMap hd) F) χ =
      collisionCoefficient F χ := by
  rw [coefficient_eq_inverse_sum, coefficient_eq_inverse_sum]
  simp only [centeredSignal, sub_mul, Finset.sum_sub_distrib]
  rw [primitive_reduction_weight_sum_zero hd hdlt χ⁻¹ (inverse_isPrimitive hprim),
    sub_zero]

/-- The oriented finite kernel boundary before fiber centering. -/
def kernelBoundary {q : ℕ} [NeZero q] (D : Finset ℕ)
    (a : UnitClass q) (s : ℂ) : ℂ :=
  ∑ n ∈ D, (periodicKernel (((n + 1 : ℕ) : ZMod q) * a.val) s -
    periodicKernel ((n : ZMod q) * a.val) s)

/-- A primitive odd transform separates any fixed finite oriented boundary. -/
theorem kernel_boundary_coefficient {q : ℕ} [NeZero q]
    (D : Finset ℕ) (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    {s : ℂ} (hs : s ∈ criticalStrip) :
    collisionCoefficient (fun a => kernelBoundary D a s) χ =
      collisionStripPrefactor q s *
        (∑ n ∈ D, (χ ((n + 1 : ℕ) : ZMod q) - χ (n : ZMod q))) *
          DirichletCharacter.LFunction χ⁻¹ s := by
  rw [coefficient_eq_inverse_sum]
  unfold kernelBoundary
  simp_rw [Finset.sum_mul, sub_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib, periodic_kernel_model_sum χ hprim hodd hs]
  simp only [← sub_mul, ← Finset.sum_mul]
  unfold periodicAmplitude collisionStripPrefactor
  ring

/-- The actual analytic observable with the actual base-fiber centering. -/
def centeredKernelBoundary (b ell : ℕ) [NeZero b] [NeZero (allLagModulus b ell)]
    (s : ℂ) : UnitClass (allLagModulus b ell) → ℂ :=
  centeredSignal (coarseUnitReduction b ell)
    (fun a => kernelBoundary (allLagDiagonal b ell) a s)

/-- The full fixed-diagonal transform, with no factorization hypothesis. -/
theorem centered_kernel_boundary_factorization {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    {s : ℂ} (hs : s ∈ criticalStrip) :
    collisionCoefficient (centeredKernelBoundary b ell s) χ =
      collisionStripPrefactor (allLagModulus b ell) s *
        directDiagonalBoundary b ell χ * DirichletCharacter.LFunction χ⁻¹ s := by
  have hd : b ∣ allLagModulus b ell := dvd_pow_self b (by omega)
  have hdlt : b < allLagModulus b ell := by
    unfold allLagModulus
    calc
      b = b ^ 1 := (pow_one b).symm
      _ < b ^ (ell + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  unfold centeredKernelBoundary coarseUnitReduction
  rw [primitive_centering_preserves_coefficient hd hdlt _ χ hprim]
  simpa only [directDiagonalBoundary, Nat.cast_add, Nat.cast_one] using
    kernel_boundary_coefficient (allLagDiagonal b ell) χ hprim hodd hs

/-- The formal zero-argument terms cancel exactly, leaving the paired endpoints. -/
theorem kernel_boundary_eq_paired {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (D : Finset ℕ) (hzero : 0 ∈ D) (hlast : q - 1 ∈ D)
    (a : UnitClass q) (s : ℂ) :
    kernelBoundary D a s = periodicKernel a.val s - periodicKernel (-a.val) s +
      ∑ n ∈ (D.erase 0).erase (q - 1),
        (periodicKernel (((n + 1 : ℕ) : ZMod q) * a.val) s -
          periodicKernel ((n : ZMod q) * a.val) s) := by
  let f : ℕ → ℂ := fun n => periodicKernel (((n+1 : ℕ) : ZMod q) * a.val) s -
    periodicKernel ((n : ZMod q) * a.val) s
  have hlast' : q - 1 ∈ D.erase 0 := Finset.mem_erase.mpr ⟨by omega, hlast⟩
  have hsplit := Finset.sum_erase_add D f hzero
  have hsplit' := Finset.sum_erase_add (D.erase 0) f hlast'
  have hf0 : f 0 = periodicKernel a.val s - periodicKernel (0 : ZMod q) s := by simp [f]
  have hflast : f (q - 1) = periodicKernel (0 : ZMod q) s - periodicKernel (-a.val) s := by
    have hcast : ((q - 1 : ℕ) : ZMod q) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      simp
    simp [f, hcast]
  change (∑ n ∈ D, f n) = periodicKernel a.val s - periodicKernel (-a.val) s +
    ∑ n ∈ (D.erase 0).erase (q - 1), f n
  rw [hf0] at hsplit
  rw [hflast] at hsplit'
  linear_combination -hsplit - hsplit'

/-- Erasing the endpoint slices selects exactly the printed interior interval. -/
theorem diagonal_interior_eq_filter {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ((allLagDiagonal b ell).erase 0).erase (allLagModulus b ell - 1) =
      (allLagDiagonal b ell).filter
        (fun n => 1 ≤ n ∧ n ≤ allLagModulus b ell - 2) := by
  ext n
  simp only [Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨hLast, hZero, hn⟩
    have hnlt := allLagDiagonal_index_lt hb hell hn
    exact ⟨hn, by omega⟩
  · rintro ⟨hn, hleft, hright⟩
    have hnlt := allLagDiagonal_index_lt hb hell hn
    exact ⟨by omega, by omega, hn⟩

/-- The literal finite coefficient has the direct boundary used by the analytic family. -/
theorem actual_finite_collision_coefficient {b : ℕ}
    [NeZero b] [NeZero (b ^ 2)] [NeZero (allLagModulus b 1)]
    (hb : b.Prime) (hbodd : b ≠ 2)
    (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) :
    collisionCoefficient (TheCollisionSpectrum.centeredLagOneSpectrum b) χ =
      -(CollisionSpectrumLandscape.generalizedBernoulliOne χ⁻¹ *
          directDiagonalBoundary b 1 χ) / ((b ^ 2).totient : ℂ) := by
  rw [LandscapeActualSpectrum.actual_centered_collision_coefficient hb hbodd χ hprim]
  rw [directDiagonalBoundary_lag_one]
  simp only [LandscapeActualSpectrum.diagonalBoundary, star_sum, star_sub, star_star]
  rfl

/-- Silent channels of the actual centered observable vanish in the open strip. -/
theorem actual_inactive_channel {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hD : directDiagonalBoundary b ell χ = 0) {s : ℂ} (hs : s ∈ criticalStrip) :
    collisionCoefficient (centeredKernelBoundary b ell s) χ = 0 := by
  rw [centered_kernel_boundary_factorization hb hell χ hprim hodd hs, hD]
  simp

/-- Active channels have precisely the zeros of the actual inverse-character L-function. -/
theorem actual_active_zero_iff {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hD : directDiagonalBoundary b ell χ ≠ 0) {s : ℂ} (hs : s ∈ criticalStrip) :
    collisionCoefficient (centeredKernelBoundary b ell s) χ = 0 ↔
      DirichletCharacter.LFunction χ⁻¹ s = 0 := by
  rw [centered_kernel_boundary_factorization hb hell χ hprim hodd hs]
  exact mul_eq_zero_iff_left
    (mul_ne_zero (collisionStripPrefactor_ne_zero (m := allLagModulus b ell) hs) hD)

/-- The zero multiplicities agree for the actual observable, without a factorization premise. -/
theorem actual_active_zero_order {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hD : directDiagonalBoundary b ell χ ≠ 0) {s : ℂ} (hs : s ∈ criticalStrip) :
    analyticOrderAt (fun z => collisionCoefficient (centeredKernelBoundary b ell z) χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) s := by
  apply active_boundary_analyticOrderAt (m := allLagModulus b ell)
    (fun z => collisionCoefficient (centeredKernelBoundary b ell z) χ)
    (directDiagonalBoundary b ell χ) (DirichletCharacter.LFunction χ⁻¹) hs
  · intro z hz
    exact centered_kernel_boundary_factorization hb hell χ hprim hodd hz
  · have hne : χ⁻¹ ≠ 1 := by
      intro heq
      have ho := inverse_odd χ hodd
      change χ⁻¹ (-1) = -1 at ho
      rw [heq, MulChar.one_apply (isUnit_one.neg)] at ho
      norm_num at ho
    exact (DirichletCharacter.differentiable_LFunction hne).analyticAt s
  · exact hD

end NField.Alignment.PrimitiveAnalyticKernel
