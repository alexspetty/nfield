/-
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindReciprocity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Fourier bounds for the first Dedekind moment

This file develops the additive finite Fourier transform of the centered
sawtooth directly.  The development is internal: the transform formula,
root-of-unity estimates, and the resulting first-moment bound do not rely on
an imported Dedekind-sum theorem.
-/

namespace NField.Alignment.DedekindFourierMoment

open scoped BigOperators ZMod
open NField.Alignment.DedekindReciprocity
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.CarryBoundarySpectra

/-- The negative additive root used by the finite Fourier convention. -/
noncomputable def negativeRoot (m n : ℕ) : ℂ :=
  Complex.exp
    (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (m : ℂ)))

theorem negativeRoot_pow_modulus
    {m n : ℕ} (hm : 0 < m) : negativeRoot m n ^ m = 1 := by
  unfold negativeRoot
  rw [← Complex.exp_nat_mul]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hexp :
      (m : ℂ) *
          (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (m : ℂ))) =
        -((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    field_simp [hmC]
  rw [hexp, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I]
  simp

theorem negativeRoot_ne_one
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    negativeRoot m n ≠ 1 := by
  unfold negativeRoot
  intro h
  have h' : Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (m : ℂ)) = 1 := by
    rw [Complex.exp_neg] at h
    simpa using h
  rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'] at h'
  exact (Nat.not_dvd_of_pos_of_lt hn hnm) h'

/-- The weighted finite geometric sum at a nontrivial root of unity. -/
theorem weighted_geometric_sum
    {m : ℕ} {z : ℂ} (hzpow : z ^ m = 1) (hz : z ≠ 1) :
    (1 - z) * (∑ j ∈ Finset.range m, (j : ℂ) * z ^ j) = -(m : ℂ) := by
  have hgeom : ∑ j ∈ Finset.range m, z ^ j = 0 := by
    apply (mul_left_cancel₀ (sub_ne_zero.mpr hz.symm))
    rw [mul_zero, mul_neg_geom_sum, hzpow, sub_self]
  have hshift :
      z * (∑ j ∈ Finset.range m, (j : ℂ) * z ^ j) =
        ∑ j ∈ Finset.range m, (j : ℂ) * z ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [pow_succ]
    ring_nf
  rw [sub_mul, one_mul, hshift, ← Finset.sum_sub_distrib]
  have htel (M : ℕ) :
      (∑ j ∈ Finset.range M,
          ((j : ℂ) * z ^ j - (j : ℂ) * z ^ (j + 1))) =
        (∑ j ∈ Finset.range M, z ^ j) - 1 + z ^ M -
          (M : ℂ) * z ^ M := by
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
        push_cast
        rw [pow_succ]
        ring
  calc
    (∑ j ∈ Finset.range m,
        ((j : ℂ) * z ^ j - (j : ℂ) * z ^ (j + 1))) =
        (∑ j ∈ Finset.range m, z ^ j) - 1 + z ^ m -
          (m : ℂ) * z ^ m := htel m
    _ = -(m : ℂ) := by rw [hgeom, hzpow]; ring

/-- The centered sawtooth's unnormalized additive Fourier coefficient. -/
noncomputable def sawtoothFourier (m n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range m,
    ((rationalSawtooth j m : ℚ) : ℂ) * negativeRoot m n ^ j

/-- Exact finite Fourier transform of the centered sawtooth away from the
zero frequency. -/
theorem sawtoothFourier_eq_root_ratio
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    sawtoothFourier m n =
      -(1 + negativeRoot m n) / (2 * (1 - negativeRoot m n)) := by
  let z := negativeRoot m n
  have hzpow : z ^ m = 1 := negativeRoot_pow_modulus hm
  have hz : z ≠ 1 := negativeRoot_ne_one hm hn hnm
  have hgeom : ∑ j ∈ Finset.range m, z ^ j = 0 := by
    apply (mul_left_cancel₀ (sub_ne_zero.mpr hz.symm))
    rw [mul_zero, mul_neg_geom_sum, hzpow, sub_self]
  have hweighted := weighted_geometric_sum hzpow hz
  have hdenom : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold sawtoothFourier
  have hpoint (j : ℕ) (hj : j ∈ Finset.range m) :
      (((rationalSawtooth j m : ℚ) : ℂ) * negativeRoot m n ^ j) =
        (((j : ℂ) / (m : ℂ) - 1 / 2) * z ^ j) -
          (if j = 0 then (-1 / 2 : ℂ) * z ^ j else 0) := by
    have hjm : j < m := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp [rationalSawtooth, z]
      ring
    · rw [rationalSawtooth_of_lt (Nat.pos_of_ne_zero hj0) hjm]
      push_cast
      simp [hj0, z]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hzeroCorrection :
      (∑ j ∈ Finset.range m,
        if j = 0 then (-1 / 2 : ℂ) * z ^ j else 0) = -1 / 2 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _hj hj0
      simp [hj0]
    · simp [hm]
  rw [hzeroCorrection]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  calc
    (∑ j ∈ Finset.range m,
        ((j : ℂ) / (m : ℂ) - 1 / 2) * z ^ j) - -1 / 2 =
        (∑ j ∈ Finset.range m,
          ((1 / (m : ℂ)) * ((j : ℂ) * z ^ j) -
            (1 / 2) * z ^ j)) + 1 / 2 := by
            ring_nf
            congr 1
            apply Finset.sum_congr rfl
            intro j _hj
            field_simp [hmC]
    _ = (1 / (m : ℂ)) *
            (∑ j ∈ Finset.range m, (j : ℂ) * z ^ j) -
          (1 / 2) * (∑ j ∈ Finset.range m, z ^ j) + 1 / 2 := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (1 / (m : ℂ)) *
          (∑ j ∈ Finset.range m, (j : ℂ) * z ^ j) + 1 / 2 := by
            rw [hgeom]
            ring
    _ = -(1 + z) / (2 * (1 - z)) := by
          have hW :
              (∑ j ∈ Finset.range m, (j : ℂ) * z ^ j) =
                -(m : ℂ) / (1 - z) := by
            apply (eq_div_iff hdenom).2
            rw [← hweighted]
            ring
          rw [hW]
          field_simp [hmC, hdenom]
          ring

/-- The explicit exponential root is the standard additive character at the
negative frequency. -/
theorem negativeRoot_eq_stdAddChar
    {m n : ℕ} [NeZero m] :
    negativeRoot m n = ZMod.stdAddChar (-(n : ZMod m)) := by
  rw [show (-(n : ZMod m)) = ((-(n : ℤ) : ℤ) : ZMod m) by norm_num,
    ZMod.stdAddChar_coe]
  unfold negativeRoot
  congr 1
  push_cast
  ring

/-- The range-indexed coefficient above is exactly Mathlib's discrete Fourier
transform of the centered sawtooth. -/
theorem sawtoothFourier_eq_dft
    {m n : ℕ} [NeZero m] :
    sawtoothFourier m n =
      ZMod.dft (centeredSawtooth : ZMod m → ℂ) (n : ZMod m) := by
  classical
  unfold sawtoothFourier
  rw [← Fin.sum_univ_eq_sum_range]
  rw [ZMod.dft_apply]
  rw [← (ZMod.finEquiv m).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show ((ZMod.finEquiv m).toEquiv j : ZMod m) =
      (j.val : ZMod m) by
    simpa using NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast j]
  rw [← rationalSawtooth_val_eq_centeredSawtooth (j.val : ZMod m)]
  rw [show (j.val : ZMod m).val = j.val by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt]]
  rw [show ZMod.stdAddChar (-((j.val : ZMod m) * (n : ZMod m))) =
      negativeRoot m n ^ j.val by
    rw [negativeRoot_eq_stdAddChar]
    rw [show -((j.val : ZMod m) * (n : ZMod m)) =
        j.val • (-(n : ZMod m)) by
      simp [nsmul_eq_mul, mul_comm]]
    exact AddChar.map_nsmul_eq_pow _ _ _]
  simp only [smul_eq_mul]
  ring

/-- Finite Fourier inversion for the centered sawtooth in the convention used
by `sawtoothFourier`. -/
theorem centeredSawtooth_fourier_inversion
    {m : ℕ} [NeZero m] (x : ZMod m) :
    centeredSawtooth x =
      (m : ℂ)⁻¹ * ∑ n : ZMod m,
        ZMod.stdAddChar (n * x) *
          ZMod.dft (centeredSawtooth : ZMod m → ℂ) n := by
  have h := congrFun
    (ZMod.dft.symm_apply_apply (centeredSawtooth : ZMod m → ℂ)) x
  rw [ZMod.invDFT_apply] at h
  simpa only [smul_eq_mul] using h.symm

/-- Reindexing by a unit turns the inner additive character sum into the
corresponding Fourier coefficient. -/
theorem sawtooth_twisted_additive_sum
    {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) (n : ZMod m) :
    (∑ x : ZMod m,
        ZMod.stdAddChar (n * x) * centeredSawtooth (u.val * x)) =
      ZMod.dft (centeredSawtooth : ZMod m → ℂ) (-(u⁻¹.val * n)) := by
  let e : ZMod m ≃ ZMod m := u.mulLeft
  let g := fun y : ZMod m =>
    ZMod.stdAddChar (n * (u⁻¹.val * y)) * centeredSawtooth y
  have hreindex := e.sum_comp g
  have hdft :
      ZMod.dft (centeredSawtooth : ZMod m → ℂ) (-(u⁻¹.val * n)) =
        ∑ y : ZMod m, g y := by
    rw [ZMod.dft_apply]
    unfold g
    apply Finset.sum_congr rfl
    intro y _hy
    simp only [smul_eq_mul]
    congr 1
    ring_nf
  rw [hdft, ← hreindex]
  unfold g e
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [Units.mulLeft_apply]
  have hcancel : u⁻¹.val * (u.val * x) = x := by
    rw [← mul_assoc, ← Units.val_mul]
    simp
  rw [hcancel]

/-- Exact additive-Fourier expansion of a Dedekind correlation. -/
theorem dedekindSum_eq_additiveFourier
    {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) :
    dedekindSum u =
      (m : ℂ)⁻¹ * ∑ n : ZMod m,
        ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
          ZMod.dft (centeredSawtooth : ZMod m → ℂ)
            (-(u⁻¹.val * n)) := by
  unfold dedekindSum
  conv_lhs =>
    enter [2, x]
    rw [centeredSawtooth_fourier_inversion x]
  calc
    (∑ x : ZMod m,
        ((m : ℂ)⁻¹ * ∑ n : ZMod m,
            ZMod.stdAddChar (n * x) *
              ZMod.dft (centeredSawtooth : ZMod m → ℂ) n) *
          centeredSawtooth (u.val * x)) =
        ∑ x : ZMod m, ∑ n : ZMod m,
          (m : ℂ)⁻¹ *
            (ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
              (ZMod.stdAddChar (n * x) * centeredSawtooth (u.val * x))) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n _hn
          ring
    _ = ∑ n : ZMod m, ∑ x : ZMod m,
          (m : ℂ)⁻¹ *
            (ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
              (ZMod.stdAddChar (n * x) * centeredSawtooth (u.val * x))) := by
          rw [Finset.sum_comm]
    _ = ∑ n : ZMod m, (m : ℂ)⁻¹ *
          ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
            (∑ x : ZMod m,
              ZMod.stdAddChar (n * x) * centeredSawtooth (u.val * x)) := by
          apply Finset.sum_congr rfl
          intro n _hn
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    _ = (m : ℂ)⁻¹ * ∑ n : ZMod m,
          ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
            (∑ x : ZMod m,
              ZMod.stdAddChar (n * x) * centeredSawtooth (u.val * x)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _hn
          ring
    _ = _ := by
          apply congrArg (fun z : ℂ => (m : ℂ)⁻¹ * z)
          apply Finset.sum_congr rfl
          intro n _hn
          rw [sawtooth_twisted_additive_sum]

/-- The triangle-inequality form of the additive Fourier expansion. -/
theorem norm_dedekindSum_le_additiveFourier
    {m : ℕ} [NeZero m] (hm : 0 < m) (u : (ZMod m)ˣ) :
    ‖dedekindSum u‖ ≤
      (1 / (m : ℝ)) * ∑ n : ZMod m,
        ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) n‖ *
          ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ)
            (-(u⁻¹.val * n))‖ := by
  rw [dedekindSum_eq_additiveFourier]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [inv_eq_one_div]
  gcongr
  simpa only [norm_mul] using
    (norm_sum_le Finset.univ (fun n : ZMod m =>
      ZMod.dft (centeredSawtooth : ZMod m → ℂ) n *
        ZMod.dft (centeredSawtooth : ZMod m → ℂ)
          (-(u⁻¹.val * n))))

/-! ## Explicit bounds for the sawtooth transform -/

theorem negativeRoot_norm_one (m n : ℕ) : ‖negativeRoot m n‖ = 1 := by
  unfold negativeRoot
  rw [Complex.norm_exp]
  norm_num

theorem norm_one_sub_negativeRoot
    {m n : ℕ} (hm : 0 < m) :
    ‖1 - negativeRoot m n‖ =
      2 * |Real.sin (Real.pi * (n : ℝ) / (m : ℝ))| := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have harg :
      -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (m : ℂ)) =
        Complex.I * ((-2 * Real.pi * (n : ℝ) / (m : ℝ) : ℝ) : ℂ) := by
    push_cast
    field_simp [hmR]
  unfold negativeRoot
  rw [harg, ← norm_neg, neg_sub,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show -2 * Real.pi * (n : ℝ) / (m : ℝ) / 2 =
      -(Real.pi * (n : ℝ) / (m : ℝ)) by ring,
    Real.sin_neg]
  simp [Real.norm_eq_abs]

/-- Distance of a nonzero frequency from the two ends of a complete residue
interval. -/
def circularDistance (m n : ℕ) : ℕ := min n (m - n)

theorem circularDistance_pos
    {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    0 < circularDistance m n := by
  unfold circularDistance
  simp only [lt_min_iff]
  omega

theorem sine_pi_ratio_lower
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (htwice : 2 * d ≤ m) :
    2 * (d : ℝ) / (m : ℝ) ≤
      Real.sin (Real.pi * (d : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) ≤ d := by positivity
  have htwiceR : 2 * (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast htwice
  have hx0 : 0 ≤ Real.pi * (d : ℝ) / (m : ℝ) := by positivity
  have hxhalf : Real.pi * (d : ℝ) / (m : ℝ) ≤ Real.pi / 2 := by
    apply (div_le_div_iff₀ hmR (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hx0 hxhalf
  convert hsin using 1
  field_simp [hmR.ne', Real.pi_ne_zero]

/-- The chord of a nontrivial additive root is bounded below by its circular
distance. -/
theorem negativeRoot_chord_lower
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    4 * (circularDistance m n : ℝ) / (m : ℝ) ≤
      ‖1 - negativeRoot m n‖ := by
  rw [norm_one_sub_negativeRoot hm]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hhalf : 2 * n ≤ m
  · have hdist : circularDistance m n = n := by
      unfold circularDistance
      rw [min_eq_left]
      omega
    rw [hdist]
    have hs := sine_pi_ratio_lower hm hn hhalf
    have hsin0 : 0 ≤ Real.sin (Real.pi * (n : ℝ) / (m : ℝ)) :=
      le_trans (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) / (m : ℝ)) hs
    rw [abs_of_nonneg hsin0]
    calc
      4 * (n : ℝ) / (m : ℝ) = 2 * (2 * (n : ℝ) / (m : ℝ)) := by ring
      _ ≤ 2 * Real.sin (Real.pi * (n : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
  · have hmnpos : 0 < m - n := by omega
    have htwice : 2 * (m - n) ≤ m := by omega
    have hdist : circularDistance m n = m - n := by
      unfold circularDistance
      rw [min_eq_right]
      omega
    rw [hdist]
    have hs := sine_pi_ratio_lower hm hmnpos htwice
    have hsubcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hnm)]
    have hangle :
        Real.pi * ((m - n : ℕ) : ℝ) / (m : ℝ) =
          Real.pi - Real.pi * (n : ℝ) / (m : ℝ) := by
      rw [hsubcast]
      field_simp [hmR.ne']
    rw [hangle, Real.sin_pi_sub] at hs
    have hsin0 : 0 ≤ Real.sin (Real.pi * (n : ℝ) / (m : ℝ)) :=
      le_trans (by positivity :
        (0 : ℝ) ≤ 2 * ((m - n : ℕ) : ℝ) / (m : ℝ)) hs
    rw [abs_of_nonneg hsin0]
    calc
      4 * ((m - n : ℕ) : ℝ) / (m : ℝ) =
          2 * (2 * ((m - n : ℕ) : ℝ) / (m : ℝ)) := by ring
      _ ≤ 2 * Real.sin (Real.pi * (n : ℝ) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)

/-- Pointwise harmonic envelope for every nonzero sawtooth frequency. -/
theorem norm_sawtoothFourier_le
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    ‖sawtoothFourier m n‖ ≤
      (m : ℝ) / (4 * (circularDistance m n : ℝ)) := by
  rw [sawtoothFourier_eq_root_ratio hm hn hnm]
  let z := negativeRoot m n
  have hdist : (0 : ℝ) < circularDistance m n := by
    exact_mod_cast circularDistance_pos hn hnm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hchordLower := negativeRoot_chord_lower hm hn hnm
  have hbase :
      (0 : ℝ) < 4 * (circularDistance m n : ℝ) / (m : ℝ) := by
    positivity
  have hchord : (0 : ℝ) < ‖1 - z‖ := lt_of_lt_of_le hbase hchordLower
  have hnum : ‖1 + z‖ ≤ 2 := by
    calc
      ‖1 + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ = 2 := by simp [z, negativeRoot_norm_one]; norm_num
  calc
    ‖-(1 + z) / (2 * (1 - z))‖ =
        ‖1 + z‖ / (2 * ‖1 - z‖) := by
          rw [norm_div, norm_neg, norm_mul]
          norm_num
    _ ≤ 2 / (2 * ‖1 - z‖) := by gcongr
    _ = 1 / ‖1 - z‖ := by field_simp [hchord.ne']
    _ ≤ 1 / (4 * (circularDistance m n : ℝ) / (m : ℝ)) :=
      one_div_le_one_div_of_le hbase hchordLower
    _ = (m : ℝ) / (4 * (circularDistance m n : ℝ)) := by
      field_simp [hmR.ne', hdist.ne']

/-- The zero-frequency sawtooth coefficient vanishes exactly. -/
theorem sawtoothFourier_zero
    {m : ℕ} (hm : 0 < m) : sawtoothFourier m 0 = 0 := by
  unfold sawtoothFourier negativeRoot
  simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Complex.exp_zero,
    one_pow, mul_one]
  rw [sum_range_eq_sum_Ico_one
    (fun j => ((rationalSawtooth j m : ℚ) : ℂ)) hm]
  · have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hpoint (j : ℕ) (hj : j ∈ Finset.Ico 1 m) :
        ((rationalSawtooth j m : ℚ) : ℂ) =
          (j : ℂ) / (m : ℂ) - 1 / 2 := by
      rw [rationalSawtooth_of_lt (Finset.mem_Ico.mp hj).1
        (Finset.mem_Ico.mp hj).2]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hpoint]
    simp_rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_div]
    have hsum :
        (∑ j ∈ Finset.Ico 1 m, (j : ℂ)) =
          (m : ℂ) * ((m : ℂ) - 1) / 2 := by
      rw [show (∑ j ∈ Finset.Ico 1 m, (j : ℂ)) =
          ∑ j ∈ Finset.range m, (j : ℂ) by
        symm
        exact sum_range_eq_sum_Ico_one (fun j => (j : ℂ)) hm (by simp)]
      have h := congrArg (fun q : ℚ => (q : ℂ)) (rational_sum_range_id m)
      push_cast at h
      exact h
    rw [hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.Ico 1 m).card = m - 1 by simp,
      Nat.cast_sub (by omega : 1 ≤ m)]
    field_simp [hmC]
    norm_num
  · simp [rationalSawtooth]

/-- Total absolute mass of the additive sawtooth transform. -/
noncomputable def sawtoothFourierNormMass (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, ‖sawtoothFourier m n‖

theorem one_div_circularDistance_le
    {m n : ℕ} (_hn : 0 < n) (_hnm : n < m) :
    1 / (circularDistance m n : ℝ) ≤
      1 / (n : ℝ) + 1 / ((m - n : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hmnR : (0 : ℝ) ≤ 1 / ((m - n : ℕ) : ℝ) := by positivity
  unfold circularDistance
  by_cases hle : n ≤ m - n
  · rw [min_eq_left hle]
    exact le_add_of_nonneg_right hmnR
  · rw [min_eq_right (Nat.le_of_not_ge hle)]
    exact le_add_of_nonneg_left hnR

theorem circularReciprocal_sum_le_harmonic
    {m : ℕ} (_hm : 0 < m) :
    (∑ n ∈ Finset.Ico 1 m, 1 / (circularDistance m n : ℝ)) ≤
      2 * (harmonic m : ℝ) := by
  let f := fun n : ℕ => 1 / (n : ℝ)
  have hreflect :
      (∑ n ∈ Finset.Ico 1 m, f (m - n)) =
        ∑ n ∈ Finset.Ico 1 m, f n := by
    simpa using Finset.sum_Ico_reflect f 1 (by omega : m ≤ m + 1)
  have hharmonic :
      (∑ n ∈ Finset.Ico 1 m, f n) ≤ (harmonic m : ℝ) := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ))
      (harmonic_eq_sum_Icc (n := m))
    simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hcast
    rw [hcast]
    simp only [f, one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hnmem
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hnmem ⊢
      omega
    · intro n _hnIcc _hnIco
      positivity
  calc
    (∑ n ∈ Finset.Ico 1 m, 1 / (circularDistance m n : ℝ)) ≤
        ∑ n ∈ Finset.Ico 1 m, (f n + f (m - n)) := by
          apply Finset.sum_le_sum
          intro n hnmem
          have hn' := Finset.mem_Ico.mp hnmem
          exact one_div_circularDistance_le hn'.1 hn'.2
    _ = (∑ n ∈ Finset.Ico 1 m, f n) +
          ∑ n ∈ Finset.Ico 1 m, f (m - n) := by
          rw [Finset.sum_add_distrib]
    _ = 2 * (∑ n ∈ Finset.Ico 1 m, f n) := by rw [hreflect]; ring
    _ ≤ 2 * (harmonic m : ℝ) := by gcongr

/-- The full additive Fourier mass is at most one half of `m` times the
harmonic number. -/
theorem sawtoothFourierNormMass_le
    {m : ℕ} (hm : 0 < m) :
    sawtoothFourierNormMass m ≤ (m : ℝ) * (harmonic m : ℝ) / 2 := by
  unfold sawtoothFourierNormMass
  rw [sum_range_eq_sum_Ico_one (fun n => ‖sawtoothFourier m n‖) hm
    (by rw [sawtoothFourier_zero hm, norm_zero])]
  calc
    (∑ n ∈ Finset.Ico 1 m, ‖sawtoothFourier m n‖) ≤
        ∑ n ∈ Finset.Ico 1 m,
          (m : ℝ) / (4 * (circularDistance m n : ℝ)) := by
            apply Finset.sum_le_sum
            intro n hnmem
            have hn' := Finset.mem_Ico.mp hnmem
            exact norm_sawtoothFourier_le hm hn'.1 hn'.2
    _ = ((m : ℝ) / 4) *
          (∑ n ∈ Finset.Ico 1 m,
            1 / (circularDistance m n : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _hn
            ring
    _ ≤ ((m : ℝ) / 4) * (2 * (harmonic m : ℝ)) := by
          gcongr
          exact circularReciprocal_sum_le_harmonic hm
    _ = (m : ℝ) * (harmonic m : ℝ) / 2 := by ring

/-! ## Multiplicative orbits of additive frequencies -/

/-- Split a range of length `d*q` into `d` consecutive blocks of length
`q`. -/
theorem sum_range_mul_blocks
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (d q : ℕ) :
    (∑ j ∈ Finset.range (d * q), f j) =
      ∑ t ∈ Finset.range d, ∑ s ∈ Finset.range q, f (t * q + s) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- A coprime multiplier permutes a complete natural residue interval for an
arbitrary target function. -/
theorem sum_mul_mod_coprime
    {R : Type*} [AddCommMonoid R] {q h : ℕ}
    (hq : 0 < q) (hhq : h.Coprime q) (f : ℕ → R) :
    (∑ s ∈ Finset.range q, f ((h * s) % q)) =
      ∑ r ∈ Finset.range q, f r := by
  letI : NeZero q := ⟨hq.ne'⟩
  let e := coprimeResidueEquiv hhq
  calc
    (∑ s ∈ Finset.range q, f ((h * s) % q)) =
        ∑ s : Fin q, f ((h * s.val) % q) := by
          exact (Fin.sum_univ_eq_sum_range
            (fun s : ℕ => f ((h * s) % q)) q).symm
    _ = ∑ s : Fin q, f ((e s).val) := by
          apply Finset.sum_congr rfl
          intro s _hs
          rw [coprimeResidueEquiv_val]
    _ = ∑ r : Fin q, f r.val := e.sum_comp (fun r : Fin q => f r.val)
    _ = ∑ r ∈ Finset.range q, f r := by
          rw [Fin.sum_univ_eq_sum_range]

/-- Exact orbit decomposition for multiplication after a common factor has
been separated. -/
theorem sum_mul_mod_of_factorization
    {R : Type*} [AddCommMonoid R]
    {m n d q h : ℕ} (_hd : 0 < d) (hq : 0 < q)
    (hm : m = d * q) (hn : n = d * h) (hhq : h.Coprime q)
    (f : ℕ → R) :
    (∑ j ∈ Finset.range m, f ((n * j) % m)) =
      d • ∑ r ∈ Finset.range q, f (d * r) := by
  subst m
  subst n
  rw [sum_range_mul_blocks
    (fun j => f ((d * h * j) % (d * q))) d q]
  have hpoint (t s : ℕ) :
      (d * h * (t * q + s)) % (d * q) = d * ((h * s) % q) := by
    calc
      (d * h * (t * q + s)) % (d * q) =
          (((d * q) * (h * t) + d * (h * s)) % (d * q)) := by
            congr 1
            ring
      _ = (d * (h * s)) % (d * q) := by
            rw [Nat.add_mod]
            simp
      _ = d * ((h * s) % q) := Nat.mul_mod_mul_left d (h * s) q
  simp_rw [hpoint]
  have hinner :
      (∑ s ∈ Finset.range q, f (d * ((h * s) % q))) =
        ∑ r ∈ Finset.range q, f (d * r) :=
    sum_mul_mod_coprime hq hhq (fun r => f (d * r))
  rw [hinner]
  simp

/-- Scaling a frequency and modulus by the same positive factor scales the
circular distance by that factor. -/
theorem circularDistance_mul_left
    {d q r : ℕ} (_hrq : r ≤ q) :
    circularDistance (d * q) (d * r) = d * circularDistance q r := by
  unfold circularDistance
  rw [← Nat.mul_sub_left_distrib]
  exact (mul_min d r (q - r)).symm

/-- A convenient zero-aware version of the harmonic pointwise envelope. -/
noncomputable def frequencyEnvelope (q r : ℕ) : ℝ :=
  if r = 0 then 0 else (q : ℝ) / (4 * (circularDistance q r : ℝ))

theorem norm_scaled_sawtoothFourier_le_envelope
    {d q r : ℕ} (hd : 0 < d) (hq : 0 < q) (hrq : r < q) :
    ‖sawtoothFourier (d * q) (d * r)‖ ≤ frequencyEnvelope q r := by
  by_cases hr : r = 0
  · subst r
    simp [frequencyEnvelope, sawtoothFourier_zero (Nat.mul_pos hd hq)]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    rw [frequencyEnvelope, if_neg hr]
    have hfreqpos : 0 < d * r := Nat.mul_pos hd hrpos
    have hfreqlt : d * r < d * q := (Nat.mul_lt_mul_left hd).2 hrq
    have hbound := norm_sawtoothFourier_le
      (Nat.mul_pos hd hq) hfreqpos hfreqlt
    rw [circularDistance_mul_left (Nat.le_of_lt hrq)] at hbound
    push_cast at hbound
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hdist : (circularDistance q r : ℝ) ≠ 0 := by
      exact_mod_cast (circularDistance_pos hrpos hrq).ne'
    convert hbound using 1
    field_simp [hdR, hdist]

theorem frequencyEnvelope_sum_le
    {q : ℕ} (hq : 0 < q) :
    (∑ r ∈ Finset.range q, frequencyEnvelope q r) ≤
      (q : ℝ) * (harmonic q : ℝ) / 2 := by
  rw [sum_range_eq_sum_Ico_one (frequencyEnvelope q) hq
    (by simp [frequencyEnvelope])]
  calc
    (∑ r ∈ Finset.Ico 1 q, frequencyEnvelope q r) =
        ((q : ℝ) / 4) *
          (∑ r ∈ Finset.Ico 1 q,
            1 / (circularDistance q r : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              have hr' := Finset.mem_Ico.mp hr
              rw [frequencyEnvelope, if_neg (by omega)]
              ring
    _ ≤ ((q : ℝ) / 4) * (2 * (harmonic q : ℝ)) := by
          gcongr
          exact circularReciprocal_sum_le_harmonic hq
    _ = (q : ℝ) * (harmonic q : ℝ) / 2 := by ring

theorem harmonic_cast_mono
    {q m : ℕ} (hqm : q ≤ m) :
    (harmonic q : ℝ) ≤ (harmonic m : ℝ) := by
  have hqcast := congrArg (fun x : ℚ => (x : ℝ))
    (harmonic_eq_sum_Icc (n := q))
  have hmcast := congrArg (fun x : ℚ => (x : ℝ))
    (harmonic_eq_sum_Icc (n := m))
  simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hqcast hmcast
  rw [hqcast, hmcast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hqm⟩
  · intro n _hnm _hnq
    positivity

/-- Every multiplicative orbit of a nonzero additive frequency has the same
uniform harmonic mass bound. -/
theorem sawtoothFourier_mul_orbit_sum_le
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (_hnm : n < m) :
    (∑ j ∈ Finset.range m, ‖sawtoothFourier m ((n * j) % m)‖) ≤
      (m : ℝ) * (harmonic m : ℝ) / 2 := by
  let d := n.gcd m
  let q := m / d
  let h := n / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left m hn
  have hdn : d ∣ n := Nat.gcd_dvd_left n m
  have hdm : d ∣ m := Nat.gcd_dvd_right n m
  have hq : 0 < q := Nat.div_pos (Nat.gcd_le_right n hm) hd
  have hmfac : m = d * q := by
    symm
    exact Nat.mul_div_cancel' hdm
  have hnfac : n = d * h := by
    symm
    exact Nat.mul_div_cancel' hdn
  have hcop : h.Coprime q := Nat.coprime_div_gcd_div_gcd hd
  have horbit := sum_mul_mod_of_factorization hd hq hmfac hnfac hcop
    (fun r => ‖sawtoothFourier m r‖)
  rw [horbit, nsmul_eq_mul]
  have hpoint :
      (∑ r ∈ Finset.range q, ‖sawtoothFourier m (d * r)‖) ≤
        ∑ r ∈ Finset.range q, frequencyEnvelope q r := by
    apply Finset.sum_le_sum
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    rw [hmfac]
    exact norm_scaled_sawtoothFourier_le_envelope hd hq hrq
  calc
    (d : ℝ) *
        (∑ r ∈ Finset.range q, ‖sawtoothFourier m (d * r)‖) ≤
        (d : ℝ) * ∑ r ∈ Finset.range q, frequencyEnvelope q r := by
          gcongr
    _ ≤ (d : ℝ) * ((q : ℝ) * (harmonic q : ℝ) / 2) := by
          gcongr
          exact frequencyEnvelope_sum_le hq
    _ ≤ (d : ℝ) * ((q : ℝ) * (harmonic m : ℝ) / 2) := by
          gcongr
          simpa [q] using harmonic_cast_mono (Nat.div_le_self m d)
    _ = (m : ℝ) * (harmonic m : ℝ) / 2 := by
          rw [hmfac]
          push_cast
          ring

theorem norm_dft_centeredSawtooth_eq
    {m : ℕ} [NeZero m] (x : ZMod m) :
    ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) x‖ =
      ‖sawtoothFourier m x.val‖ := by
  rw [sawtoothFourier_eq_dft]
  rw [ZMod.natCast_zmod_val]

theorem dft_centeredSawtooth_normMass_eq
    {m : ℕ} [NeZero m] :
    (∑ x : ZMod m,
      ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) x‖) =
      sawtoothFourierNormMass m := by
  classical
  rw [show (∑ x : ZMod m,
      ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) x‖) =
      ∑ x : ZMod m, ‖sawtoothFourier m x.val‖ by
    apply Finset.sum_congr rfl
    intro x _hx
    exact norm_dft_centeredSawtooth_eq x]
  calc
    (∑ x : ZMod m, ‖sawtoothFourier m x.val‖) =
        ∑ x : Fin m,
          ‖sawtoothFourier m (((ZMod.finEquiv m).toEquiv x).val)‖ :=
      ((ZMod.finEquiv m).toEquiv.sum_comp
        (fun x : ZMod m => ‖sawtoothFourier m x.val‖)).symm
    _ = ∑ x : Fin m, ‖sawtoothFourier m x.val‖ := by
          apply Finset.sum_congr rfl
          intro x _hx
          have hval : ((ZMod.finEquiv m).toEquiv x).val = x.val := by
            rw [show ((ZMod.finEquiv m).toEquiv x : ZMod m) =
                (x.val : ZMod m) by
              simpa using
                NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast x,
              ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]
          rw [hval]
    _ = sawtoothFourierNormMass m := by
          unfold sawtoothFourierNormMass
          exact Fin.sum_univ_eq_sum_range
            (fun n : ℕ => ‖sawtoothFourier m n‖) m

/-- A multiplicative unit orbit is a subset of the complete additive
multiplier orbit.  The latter remains uniformly bounded even when the
frequency and modulus have a common factor. -/
theorem dft_centeredSawtooth_unitOrbit_sum_le
    {m : ℕ} [NeZero m] (hm : 0 < m) (n : ZMod m) :
    (∑ u : (ZMod m)ˣ,
        ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ)
          (-(u⁻¹.val * n))‖) ≤
      (m : ℝ) * (harmonic m : ℝ) / 2 := by
  classical
  let A := fun x : ZMod m =>
    ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) x‖
  let φ := fun u : (ZMod m)ˣ => -(u⁻¹.val)
  have hφ : Function.Injective φ := by
    intro u v huv
    apply inv_injective
    apply Units.val_injective
    exact neg_injective huv
  have hsubset : Finset.univ.image φ ⊆ (Finset.univ : Finset (ZMod m)) :=
    Finset.subset_univ _
  calc
    (∑ u : (ZMod m)ˣ, A (-(u⁻¹.val * n))) =
        ∑ u : (ZMod m)ˣ, A (φ u * n) := by
          apply Finset.sum_congr rfl
          intro u _hu
          simp only [φ]
          rw [neg_mul]
    _ = ∑ x ∈ Finset.univ.image φ, A (x * n) := by
          rw [Finset.sum_image hφ.injOn]
    _ ≤ ∑ x : ZMod m, A (x * n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro x _hx _hnot
          positivity
    _ = ∑ x : ZMod m, ‖sawtoothFourier m (x * n).val‖ := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact norm_dft_centeredSawtooth_eq (x * n)
    _ = ∑ x : Fin m,
          ‖sawtoothFourier m ((x.val * n.val) % m)‖ := by
          rw [← (ZMod.finEquiv m).toEquiv.sum_comp]
          apply Finset.sum_congr rfl
          intro x _hx
          have hval : ((ZMod.finEquiv m).toEquiv x).val = x.val := by
            rw [show ((ZMod.finEquiv m).toEquiv x : ZMod m) =
                (x.val : ZMod m) by
              simpa using
                NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast x,
              ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]
          rw [ZMod.val_mul, hval]
    _ = ∑ x ∈ Finset.range m,
          ‖sawtoothFourier m ((x * n.val) % m)‖ := by
          exact Fin.sum_univ_eq_sum_range
            (fun x : ℕ => ‖sawtoothFourier m ((x * n.val) % m)‖) m
    _ = ∑ x ∈ Finset.range m,
          ‖sawtoothFourier m ((n.val * x) % m)‖ := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Nat.mul_comm]
    _ ≤ (m : ℝ) * (harmonic m : ℝ) / 2 := by
          by_cases hn : n = 0
          · subst n
            simp [sawtoothFourier_zero hm]
            have hHq : (0 : ℚ) ≤ harmonic m := by
              unfold harmonic
              positivity
            have hH : (0 : ℝ) ≤ (harmonic m : ℝ) := by
              exact_mod_cast hHq
            positivity
          · exact sawtoothFourier_mul_orbit_sum_le hm
              (ZMod.val_pos.mpr hn) n.val_lt

/-- The absolute first moment of the Dedekind correlation over all unit
arguments. -/
noncomputable def dedekindFirstMoment (m : ℕ) [NeZero m] : ℝ :=
  ∑ u : (ZMod m)ˣ, ‖dedekindSum u‖

/-- Explicit first-moment estimate obtained from the additive Fourier
transform.  This is the quantitative form needed by the Abel remainder. -/
theorem dedekindFirstMoment_le
    {m : ℕ} [NeZero m] (hm : 0 < m) :
    dedekindFirstMoment m ≤
      (m : ℝ) * (harmonic m : ℝ) ^ 2 / 4 := by
  classical
  let A := fun n : ZMod m =>
    ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) n‖
  let B := (m : ℝ) * (harmonic m : ℝ) / 2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hHq : (0 : ℚ) ≤ harmonic m := by
    unfold harmonic
    positivity
  have hH : (0 : ℝ) ≤ (harmonic m : ℝ) := by
    exact_mod_cast hHq
  have hB : 0 ≤ B := by
    unfold B
    positivity
  calc
    dedekindFirstMoment m ≤
        ∑ u : (ZMod m)ˣ, (1 / (m : ℝ)) *
          ∑ n : ZMod m, A n * A (-(u⁻¹.val * n)) := by
            unfold dedekindFirstMoment
            apply Finset.sum_le_sum
            intro u _hu
            exact norm_dedekindSum_le_additiveFourier hm u
    _ = (1 / (m : ℝ)) * ∑ u : (ZMod m)ˣ,
          ∑ n : ZMod m, A n * A (-(u⁻¹.val * n)) := by
            rw [Finset.mul_sum]
    _ = (1 / (m : ℝ)) * ∑ n : ZMod m,
          A n * ∑ u : (ZMod m)ˣ, A (-(u⁻¹.val * n)) := by
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro n _hn
            rw [Finset.mul_sum]
    _ ≤ (1 / (m : ℝ)) * ∑ n : ZMod m, A n * B := by
            gcongr
            exact dft_centeredSawtooth_unitOrbit_sum_le hm n
    _ = (1 / (m : ℝ)) *
          (∑ n : ZMod m, A n) * B := by
            rw [← Finset.sum_mul]
            ring
    _ = (1 / (m : ℝ)) * sawtoothFourierNormMass m * B := by
            rw [← dft_centeredSawtooth_normMass_eq]
    _ ≤ (1 / (m : ℝ)) * B * B := by
            gcongr
            exact sawtoothFourierNormMass_le hm
    _ = (m : ℝ) * (harmonic m : ℝ) ^ 2 / 4 := by
            unfold B
            field_simp [hmR.ne']
            ring

end NField.Alignment.DedekindFourierMoment
