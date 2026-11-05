/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveAnalyticKernel

/-! # Exact endpoints of the primitive periodic-zeta transform

Mathlib's discrete Fourier identity and primitive Dirichlet functional
equation combine with the already proved first odd special value.
-/

noncomputable section
namespace NField.Alignment.PrimitiveAnalyticEndpoints

open scoped BigOperators ComplexConjugate
open CollisionCharacterStructure CarryBoundarySpectra AnalyticCollisionTransform
  PrimitiveAnalyticKernel SawtoothLValue

theorem l_function_const_mul {q : ℕ} [NeZero q]
    (c : ℂ) (f : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun a => c * f a) s = c * ZMod.LFunction f s := by
  unfold ZMod.LFunction
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- A finite character transform of the continued kernel is a genuine continued L-function. -/
theorem periodic_kernel_gauss_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd) (s : ℂ) :
    twistedTransform (fun a : ZMod q => periodicKernel a s) χ⁻¹ 1 =
      gaussSum χ⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ (1 - s) := by
  have hχ0 : χ⁻¹ (0 : ZMod q) = 0 := (χ⁻¹).map_zero' (by omega)
  have hdft : ZMod.dft ((χ⁻¹ : Character q) : ZMod q → ℂ) =
      fun k => -(gaussSum χ⁻¹ ZMod.stdAddChar) * χ k := by
    funext k
    rw [(inverse_isPrimitive hprim).fourierTransform_eq_inv_mul_gaussSum]
    simp only [inv_inv, hodd.eval_neg]
    ring
  have hdf := ZMod.LFunction_dft ((χ⁻¹ : Character q) : ZMod q → ℂ)
    (s := 1-s) (Or.inl hχ0)
  rw [hdft, l_function_const_mul] at hdf
  have hreflect := twistedTransform_eq_inv_mul
    (fun a : ZMod q => periodicKernel a s) (inverse_isPrimitive hprim) (-1 : ZMod q)
  have hodd' : χ (-1 : ZMod q) = -1 := hodd
  simp only [inv_inv, hodd', neg_one_mul] at hreflect
  have hdf' : -(gaussSum χ⁻¹ ZMod.stdAddChar) *
      DirichletCharacter.LFunction χ (1-s) =
      twistedTransform (fun a : ZMod q => periodicKernel a s) χ⁻¹ (-1) := by
    unfold twistedTransform periodicKernel
    simp only [neg_one_mul]
    simpa only [DirichletCharacter.LFunction, mul_comm] using hdf
  rw [hreflect] at hdf'
  linear_combination hdf'

/-- The left endpoint uses the inverse character's Bernoulli value. -/
theorem periodic_kernel_left_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    twistedTransform (fun a : ZMod q => periodicKernel a 0) χ⁻¹ 1 =
      -(Complex.I * (Real.pi : ℂ) * bernoulliOne χ⁻¹) := by
  rw [periodic_kernel_gauss_sum hq χ hprim hodd]
  simp only [sub_zero]
  have h := primitiveOdd_LFunction_bernoulliOne hq
    (inverse_isPrimitive hprim) (inverse_odd χ hodd)
  simp only [inv_inv] at h
  linear_combination -h

/-- The actual continued Dirichlet function has the first Bernoulli value at zero. -/
theorem odd_l_function_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 = -bernoulliOne χ := by
  have hgamma2 : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    norm_num [Complex.Gammaℝ_def, Complex.cpow_neg_one, Complex.Gamma_one]
  have hzero := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0
    (Or.inr (by omega : q ≠ 1))
  rw [hodd.gammaFactor_def] at hzero
  simp only [zero_add, Complex.Gammaℝ_one, div_one] at hzero
  have hone := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1
    (Or.inl (by norm_num : (1 : ℂ) ≠ 0))
  rw [(inverse_odd χ hodd).gammaFactor_def] at hone
  norm_num only [show (1 : ℂ) + 1 = 2 by norm_num, hgamma2] at hone
  have hfe := hprim.completedLFunction_one_sub (1 : ℂ)
  rw [DirichletCharacter.rootNumber, if_neg hodd.not_even, pow_one] at hfe
  norm_num only [sub_self, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hfe
  have hpow : (q : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hfe' : DirichletCharacter.completedLFunction χ 0 =
      gaussSum χ ZMod.stdAddChar / Complex.I *
        DirichletCharacter.completedLFunction χ⁻¹ 1 := by
    rw [hfe]
    field_simp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hphase := primitiveOdd_LFunction_bernoulliOne hq hprim hodd
  rw [hzero, hfe']
  have hone' : DirichletCharacter.completedLFunction χ⁻¹ 1 =
      DirichletCharacter.LFunction χ⁻¹ 1 / (Real.pi : ℂ) := by
    field_simp [hpi] at hone ⊢
    exact hone.symm
  rw [hone']
  field_simp [hpi, Complex.I_ne_zero]
  linear_combination -hphase

/-- The right endpoint changes the Bernoulli character and retains the Gauss twist. -/
theorem periodic_kernel_right_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    twistedTransform (fun a : ZMod q => periodicKernel a 1) χ⁻¹ 1 =
      -(gaussSum χ⁻¹ ZMod.stdAddChar) * bernoulliOne χ := by
  rw [periodic_kernel_gauss_sum hq χ hprim hodd]
  simp only [sub_self]
  rw [odd_l_function_zero hq χ hprim hodd]
  ring

open CenteredCollisionSum CollisionTransformStrip NeutralityTheorem

/-- An arbitrary finite boundary keeps the same entire Dirichlet channel. -/
theorem kernel_boundary_coefficient_gauss {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (D : Finset ℕ) (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd) (s : ℂ) :
    collisionCoefficient (fun a => kernelBoundary D a s) χ =
      (q.totient : ℂ)⁻¹ *
        (∑ n ∈ D, (χ ((n + 1 : ℕ) : ZMod q) - χ (n : ZMod q))) *
          gaussSum χ⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ (1 - s) := by
  have hmodel (n : ZMod q) :
      (∑ a : UnitClass q, periodicKernel (n * a.val) s * χ⁻¹ a.val) =
        χ n * gaussSum χ⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ (1 - s) := by
    have h := twistedTransform_eq_inv_mul
      (fun a : ZMod q => periodicKernel a s) (inverse_isPrimitive hprim) n
    rw [inv_inv, periodic_kernel_gauss_sum hq χ hprim hodd] at h
    unfold twistedTransform at h
    rw [sum_character_pairing_eq_units] at h
    simpa only [mul_assoc] using h
  rw [coefficient_eq_inverse_sum]
  unfold kernelBoundary
  simp_rw [Finset.sum_mul, sub_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib, hmodel]
  simp only [← sub_mul, ← Finset.sum_mul]
  ring

/-- The centered diagonal transform is entire in the analytic parameter. -/
theorem centered_kernel_boundary_gauss_factorization {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (s : ℂ) :
    collisionCoefficient (centeredKernelBoundary b ell s) χ =
      ((allLagModulus b ell).totient : ℂ)⁻¹ * directDiagonalBoundary b ell χ *
        gaussSum χ⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ (1 - s) := by
  have hd : b ∣ allLagModulus b ell := dvd_pow_self b (by omega)
  have hdlt : b < allLagModulus b ell := by
    unfold allLagModulus
    calc
      b = b ^ 1 := (pow_one b).symm
      _ < b ^ (ell + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hq : 2 ≤ allLagModulus b ell := by omega
  unfold centeredKernelBoundary coarseUnitReduction
  rw [primitive_centering_preserves_coefficient hd hdlt _ χ hprim]
  simpa only [directDiagonalBoundary, Nat.cast_add, Nat.cast_one] using
    kernel_boundary_coefficient_gauss hq (allLagDiagonal b ell) χ hprim hodd s

theorem centered_kernel_boundary_differentiable {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    Differentiable ℂ (fun s => collisionCoefficient (centeredKernelBoundary b ell s) χ) := by
  have hne : χ ≠ 1 := by
    intro heq
    have ho : χ (-1) = -1 := hodd
    rw [heq, MulChar.one_apply (isUnit_one.neg)] at ho
    norm_num at ho
  have hL := DirichletCharacter.differentiable_LFunction hne
  have heq := funext (centered_kernel_boundary_gauss_factorization hb hell χ hprim hodd)
  rw [heq]
  fun_prop

/-- The exact left-boundary value of the actual centered observable. -/
theorem actual_left_boundary {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    collisionCoefficient (centeredKernelBoundary b ell 0) χ =
      -(Complex.I * (Real.pi : ℂ) / ((allLagModulus b ell).totient : ℂ) *
        bernoulliOne χ⁻¹ * directDiagonalBoundary b ell χ) := by
  have hq : 2 ≤ allLagModulus b ell := by
    unfold allLagModulus
    have hp : b ^ 0 < b ^ (ell + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    simp only [pow_zero] at hp
    omega
  rw [centered_kernel_boundary_gauss_factorization hb hell χ hprim hodd]
  simp only [sub_zero]
  have h := primitiveOdd_LFunction_bernoulliOne hq
    (inverse_isPrimitive hprim) (inverse_odd χ hodd)
  simp only [inv_inv] at h
  linear_combination -(((allLagModulus b ell).totient : ℂ)⁻¹ *
    directDiagonalBoundary b ell χ) * h

/-- The exact right-boundary value of the actual centered observable. -/
theorem actual_right_boundary {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    collisionCoefficient (centeredKernelBoundary b ell 1) χ =
      -(gaussSum χ⁻¹ ZMod.stdAddChar / ((allLagModulus b ell).totient : ℂ) *
        bernoulliOne χ * directDiagonalBoundary b ell χ) := by
  have hq : 2 ≤ allLagModulus b ell := by
    unfold allLagModulus
    have hp : b ^ 0 < b ^ (ell + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    simp only [pow_zero] at hp
    omega
  rw [centered_kernel_boundary_gauss_factorization hb hell χ hprim hodd]
  simp only [sub_self]
  rw [odd_l_function_zero hq χ hprim hodd]
  ring

/-- At lag one the actual left endpoint is exactly i*pi times the actual finite coefficient. -/
theorem actual_collision_recovery {b : ℕ}
    [NeZero b] [NeZero (b ^ 2)] [NeZero (allLagModulus b 1)]
    (hb : b.Prime) (hbodd : b ≠ 2)
    (χ : Character (b ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    collisionCoefficient (centeredKernelBoundary b 1 0) χ =
      Complex.I * (Real.pi : ℂ) *
        collisionCoefficient (TheCollisionSpectrum.centeredLagOneSpectrum b) χ := by
  rw [actual_left_boundary hb.two_le (by omega : 1 ≤ 1) χ hprim hodd,
    actual_finite_collision_coefficient hb hbodd χ hprim,
    LandscapeActualSpectrum.generalizedBernoulliOne_eq_full]
  change -(Complex.I * (Real.pi : ℂ) / ((b ^ 2).totient : ℂ) *
    bernoulliOne χ⁻¹ * directDiagonalBoundary b 1 χ) = _
  ring

end NField.Alignment.PrimitiveAnalyticEndpoints
