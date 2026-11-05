/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveAnalyticEndpoints
import NField.Alignment.CenteredPowerFibers
import NField.Alignment.DedekindInverseResidueTransform

/-! # Classical special values used by the analytic collision transform

The rational Hurwitz value and cotangent value are assembled from the existing
sawtooth special value and finite Fourier transform. The proofs concern
Mathlib's continued functions, including every nonzero rational argument
occurring in the manuscript's observable.
-/

noncomputable section
namespace NField.Alignment.PrimitiveAnalyticSpecialValues

open scoped BigOperators ComplexConjugate
open CollisionCharacterStructure CarryBoundarySpectra AnalyticCollisionTransform
  PrimitiveAnalyticKernel PrimitiveAnalyticEndpoints SawtoothLValue
  DedekindFourierMoment DedekindInverseResidueTransform

theorem hurwitz_odd_zero {q : ℕ} [NeZero q] (j : ZMod q) :
    HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) 0 = -centeredSawtooth j := by
  by_cases hj : j = 0
  · subst j
    have h := HurwitzZeta.hurwitzZetaOdd_neg (0 : UnitAddCircle) 0
    simp only [neg_zero] at h
    have hz : HurwitzZeta.hurwitzZetaOdd (0 : UnitAddCircle) 0 = 0 := by
      linear_combination h / 2
    simpa [centeredSawtooth] using hz
  · have h := HurwitzZeta.hurwitzZetaOdd_one_sub (ZMod.toAddCircle j)
      (s := 1) (by
        intro n hn
        have hre := congrArg Complex.re hn
        simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    rw [sinZeta_one_eq_neg_pi_mul_centeredSawtooth j hj] at h
    norm_num only [sub_self, Complex.cpow_neg_one, Complex.Gamma_one,
      Complex.sin_pi_div_two, mul_one] at h
    rw [h]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem hurwitz_zero {q : ℕ} [NeZero q] (j : ZMod q) :
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) 0 =
      -centeredSawtooth j - if j = 0 then (1 / 2 : ℂ) else 0 := by
  rw [HurwitzZeta.hurwitzZeta, HurwitzZeta.hurwitzZetaEven_apply_zero,
    hurwitz_odd_zero]
  by_cases hj : j = 0
  · simp [hj, centeredSawtooth]
    ring
  · simp [hj, ZMod.toAddCircle_eq_zero]

/-- The Bernoulli special value for every nonprincipal character, without primitivity or parity. -/
theorem nonprincipal_l_function_zero {q : ℕ} [NeZero q] (hq : q ≠ 1)
    (χ : Character q) (hne : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 = -bernoulliOne χ := by
  have hχ0 := χ.map_zero' hq
  have hsum := centeredSawtooth_transform_eq_bernoulliOne hq hne
  unfold twistedTransform at hsum
  simp only [one_mul] at hsum
  unfold DirichletCharacter.LFunction ZMod.LFunction
  simp only [neg_zero, Complex.cpow_zero, one_mul]
  simp_rw [hurwitz_zero, mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hfirst : (∑ j : ZMod q, χ j * centeredSawtooth j) = bernoulliOne χ := by
    simpa only [mul_comm] using hsum
  rw [hfirst]
  simp [mul_ite, hχ0]

/-- Mathlib's continued kernel has the printed cotangent value at every nonzero residue. -/
theorem periodic_kernel_right_cotangent {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (j : ZMod q) (hj : j ≠ 0) :
    periodicKernel j 1 = -(1 / 2 : ℂ) + Complex.I / 2 *
      Complex.cot ((Real.pi : ℂ) * ((j.val : ℂ) / (q : ℂ))) := by
  unfold periodicKernel
  simp only [sub_self]
  rw [← ZMod.LFunction_stdAddChar_eq_expZeta j 0 (Or.inl hj)]
  unfold ZMod.LFunction
  simp only [neg_zero, Complex.cpow_zero, one_mul]
  simp_rw [hurwitz_zero, mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hsum : (∑ k : ZMod q, ZMod.stdAddChar (j * k) * centeredSawtooth k) =
      -(ZMod.dft (centeredSawtooth : ZMod q → ℂ) j) := by
    have hodd : Function.Odd (centeredSawtooth : ZMod q → ℂ) := centeredSawtooth_neg hq
    have h := (ZMod.dft_odd_iff.mpr hodd) j
    rw [ZMod.dft_apply] at h
    simpa only [mul_neg, neg_neg, smul_eq_mul, mul_comm] using h
  rw [hsum]
  have hfourier : ZMod.dft (centeredSawtooth : ZMod q → ℂ) j =
      Complex.I / 2 * Complex.cot ((Real.pi : ℂ) * ((j.val : ℂ) / (q : ℂ))) := by
    have hval : 0 < j.val := Nat.pos_of_ne_zero (by simpa using hj)
    have h := sawtoothFourier_eq_cotangent (NeZero.pos q) hval j.val_lt
    rw [sawtoothFourier_eq_dft, ZMod.natCast_zmod_val] at h
    exact h
  rw [hfourier]
  simp [mul_ite]
  ring

/-- The principal logarithm is the regular left value at every observable argument. -/
theorem periodic_kernel_left_log {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    periodicKernel j 0 = -Complex.log (1 - ZMod.stdAddChar j) := by
  simpa only [periodicKernel, sub_zero] using expZeta_one_eq_neg_log j hj

/-- Every nonzero residue argument has an entire kernel in the manuscript parameter. -/
theorem periodic_kernel_differentiable {q : ℕ} [NeZero q]
    (j : ZMod q) (hj : j ≠ 0) : Differentiable ℂ (periodicKernel j) := by
  have h := HurwitzZeta.differentiable_expZeta_of_ne_zero
    (ZMod.toAddCircle_eq_zero.not.mpr hj)
  exact h.comp (by fun_prop)

/-- Real arguments strictly inside the unit interval give an entire kernel. -/
theorem real_kernel_differentiable (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Differentiable ℂ (fun s => HurwitzZeta.expZeta (x : UnitAddCircle) (1 - s)) := by
  have hx0 : (x : UnitAddCircle) ≠ 0 := by
    intro h
    have hz := (AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hx.1.le, hx.2⟩).mp h
    exact hx.1.ne' hz
  exact (HurwitzZeta.differentiable_expZeta_of_ne_zero hx0).comp (by fun_prop)

/-- Residue notation and the printed least representative use the same circle point. -/
theorem periodic_kernel_residue {q : ℕ} [NeZero q] (j : ZMod q) (s : ℂ) :
    periodicKernel j s =
      HurwitzZeta.expZeta (((j.val : ℝ) / q : ℝ) : UnitAddCircle) (1 - s) := by
  rw [periodicKernel, ZMod.toAddCircle_apply]

/-- The classical Hurwitz connection, including nonrational spatial arguments. -/
theorem real_kernel_connection (x : ℝ) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ 1 - n) :
    HurwitzZeta.expZeta (x : UnitAddCircle) (1 - s) =
      Complex.Gamma s / ((2 * (Real.pi : ℂ)) ^ s) *
        (Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) *
          HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s +
        Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) *
          HurwitzZeta.hurwitzZeta ((1 - x : ℝ) : UnitAddCircle) s) := by
  rw [HurwitzZeta.expZeta_one_sub _ hs, Complex.cpow_neg]
  have hreflect : ((1-x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  rw [hreflect]
  ring

/-- The removable gamma-sine amplitude at zero, in the full complex punctured neighborhood. -/
theorem periodic_amplitude_left_limit {q : ℕ} [NeZero q] :
    Filter.Tendsto (periodicAmplitude q) (nhdsWithin 0 ({0}ᶜ))
      (nhds (Complex.I * (Real.pi : ℂ))) := by
  have hsin : Filter.Tendsto
      (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z / 2) / z)
      (nhdsWithin 0 ({0}ᶜ)) (nhds ((Real.pi : ℂ) / 2)) := by
    have hd : HasDerivAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z / 2))
        ((Real.pi : ℂ) / 2) 0 := by
      simpa [Function.comp_def] using (Complex.hasDerivAt_sin ((Real.pi : ℂ) * 0 / 2)).comp 0
        (((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const 2)
    simpa [smul_eq_mul, div_eq_inv_mul] using hd.tendsto_slope_zero
  have hpow : Filter.Tendsto (fun z : ℂ => ((q : ℂ) / (2 * (Real.pi : ℂ))) ^ z)
      (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
    have hq : (q : ℂ) / (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne q))
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    simpa using (continuousAt_const_cpow hq (b := (0 : ℂ))).tendsto.mono_left
      nhdsWithin_le_nhds
  have h := ((hsin.mul Complex.tendsto_self_mul_Gamma_nhds_zero).const_mul
    (2 * Complex.I)).mul hpow
  have heq : (fun z : ℂ => 2 * Complex.I *
      (Complex.sin ((Real.pi : ℂ) * z / 2) / z * (z * Complex.Gamma z)) *
        ((q : ℂ) / (2 * (Real.pi : ℂ))) ^ z) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
      periodicAmplitude q := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    unfold periodicAmplitude
    field_simp [hz0]
  convert h.congr' heq using 1
  congr 1
  ring

/-- The phase-sensitive product of the two primitive odd Gauss sums. -/
theorem primitive_odd_gauss_product {q : ℕ} [NeZero q]
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = -(q : ℂ) := by
  have hdft : ZMod.dft (χ : ZMod q → ℂ) =
      fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar := by
    funext k
    exact hprim.fourierTransform_eq_inv_mul_gaussSum k
  have hdouble := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) (1 : ZMod q)
  rw [hdft, ZMod.dft_mul_const, ZMod.dft_comp_neg] at hdouble
  change (ZMod.dft ((χ⁻¹ : Character q) : ZMod q → ℂ) (-1)) *
    gaussSum χ ZMod.stdAddChar = (q : ℂ) * χ (-1) at hdouble
  rw [(inverse_isPrimitive hprim).fourierTransform_eq_inv_mul_gaussSum] at hdouble
  have ho : χ (-1 : ZMod q) = -1 := hodd
  simp only [neg_neg, inv_inv, map_one, one_mul, ho, mul_neg_one] at hdouble
  simpa only [mul_comm] using hdouble

/-- The odd Bernoulli relation in the exact phase convention printed in the manuscript. -/
theorem bernoulli_one_functional_relation {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : Character q) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    bernoulliOne χ = Complex.I / (Real.pi : ℂ) *
      gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1 := by
  have h := primitiveOdd_LFunction_bernoulliOne hq hprim hodd
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  have h' := congrArg (fun z : ℂ => Complex.I * z) h
  ring_nf at h'
  simp only [Complex.I_sq] at h'
  linear_combination h'

open CenteredCollisionSum CollisionTransformStrip

/-- The actual right endpoint also has the printed L(1) expression. -/
theorem actual_right_l_value {b ell : ℕ}
    [NeZero b] [NeZero (allLagModulus b ell)] (hb : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    collisionCoefficient (centeredKernelBoundary b ell 1) χ =
      Complex.I * (allLagModulus b ell : ℂ) /
        ((Real.pi : ℂ) * ((allLagModulus b ell).totient : ℂ)) *
          directDiagonalBoundary b ell χ * DirichletCharacter.LFunction χ⁻¹ 1 := by
  have hq : 2 ≤ allLagModulus b ell := by
    unfold allLagModulus
    have hp : b ^ 0 < b ^ (ell + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    simp only [pow_zero] at hp
    omega
  rw [actual_right_boundary hb hell χ hprim hodd,
    bernoulli_one_functional_relation hq χ hprim hodd]
  have hprod := primitive_odd_gauss_product χ hprim hodd
  calc
    _ = -(Complex.I / ((Real.pi : ℂ) * ((allLagModulus b ell).totient : ℂ)) *
        directDiagonalBoundary b ell χ * DirichletCharacter.LFunction χ⁻¹ 1) *
        (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) := by ring
    _ = _ := by rw [hprod]; ring

/-- The least nonzero residue divided by the modulus is strictly inside the unit interval. -/
theorem nonzero_residue_mem_unit_interval {q : ℕ} [NeZero q]
    (j : ZMod q) (hj : j ≠ 0) : (j.val : ℝ) / q ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos (Nat.cast_pos.mpr (ZMod.val_pos.mpr hj))
      (Nat.cast_pos.mpr (NeZero.pos q))
  · exact (div_lt_one (Nat.cast_pos.mpr (NeZero.pos q))).mpr (Nat.cast_lt.mpr j.val_lt)

/-- No interior diagonal difference evaluates a zero residue, even when its index is a nonunit. -/
theorem interior_arguments_ne_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (a : UnitClass q) {n : ℕ} (hn : 1 ≤ n ∧ n ≤ q - 2) :
    ((n : ZMod q) * a.val) ≠ 0 ∧ (((n + 1 : ℕ) : ZMod q) * a.val) ≠ 0 := by
  have hnlt : n < q := by omega
  have hn1lt : n + 1 < q := by omega
  have hcast (k : ℕ) (hk0 : k ≠ 0) (hklt : k < q) : (k : ZMod q) ≠ 0 := by
    intro hk
    have hval := congrArg ZMod.val hk
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hklt, ZMod.val_zero] at hval
    exact hk0 hval
  exact ⟨a.mul_left_eq_zero.not.mpr (hcast n (by omega) hnlt),
    a.mul_left_eq_zero.not.mpr (hcast (n+1) (by omega) hn1lt)⟩

/-- The actual fiber mean has exactly the manuscript's denominator b^ell. -/
theorem centered_kernel_boundary_printed_mean (b ell : ℕ) [NeZero b]
    [NeZero (allLagModulus b ell)] (a : UnitClass (allLagModulus b ell)) (s : ℂ) :
    centeredKernelBoundary b ell s a = kernelBoundary (allLagDiagonal b ell) a s -
      (b ^ ell : ℂ)⁻¹ *
        ∑ u : Fiber (NeutralityTheorem.coarseUnitReduction b ell)
          (NeutralityTheorem.coarseUnitReduction b ell a),
          kernelBoundary (allLagDiagonal b ell) u.val s := by
  simp only [centeredKernelBoundary, centeredSignal, CenteredPowerFibers.coarse_fiberMean]

end NField.Alignment.PrimitiveAnalyticSpecialValues
