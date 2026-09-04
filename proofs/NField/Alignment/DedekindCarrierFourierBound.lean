/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindInverseResidueTransform
import NField.Alignment.SpectralPower

/-!
# Additive Fourier bounds for Dedekind carrier slices

This module is the finite Fourier step in the all-prime carrier argument.  It
identifies the transform of the actual inverse-residue Dedekind sequence with
the unit-supported additive transform.  No asymptotic estimate enters here.
-/

namespace NField.Alignment.DedekindCarrierFourierBound

open scoped BigOperators ZMod
open AddChar
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.DedekindReciprocity
open NField.Alignment.DedekindFourierMoment
open NField.Alignment.SpectralPower

/-- The actual periodic Dedekind carrier sequence, represented on its residue
ring rather than on natural representatives. -/
noncomputable def residueDedekindFunction
    {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) (a : ZMod k) : ℂ :=
  if h : IsUnit a then dedekindSum (β * h.unit⁻¹) else 0

theorem residueDedekindFunction_natCast
    {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) (a : ℕ) :
    residueDedekindFunction β (a : ZMod k) =
      residueDedekindSequence β a := by
  unfold residueDedekindFunction residueDedekindSequence
  rfl

/-- The kernel-valued form of the unit additive transform. -/
noncomputable def kernelUnitTransform (k t : ℕ) : ℂ :=
  if hk : k = 0 then 0 else by
    letI : NeZero k := ⟨hk⟩
    exact ∑ h : (ZMod k)ˣ,
      dedekindSum h * ZMod.stdAddChar (-((t : ZMod k) * h.val))

theorem kernelUnitTransform_eq_unitDedekindTransform
    {k t : ℕ} (hk : 0 < k) :
    kernelUnitTransform k t = unitDedekindTransform k t := by
  letI : NeZero k := ⟨hk.ne'⟩
  unfold kernelUnitTransform unitDedekindTransform
  rw [dif_neg hk.ne', dif_neg hk.ne']
  apply Finset.sum_congr rfl
  intro h _hh
  have hcop : h.val.val.Coprime k := ZMod.val_coe_unit_coprime h
  have heq : ZMod.unitOfCoprime h.val.val hcop = h := by
    apply Units.ext
    change (h.val.val : ZMod k) = h.val
    exact ZMod.natCast_zmod_val h.val
  have hd : dedekindSum h =
      ((arithmeticDedekindSum h.val.val k : ℚ) : ℂ) := by
    rw [← heq]
    simpa using dedekindSum_unitOfCoprime_eq_arithmeticDedekindSum hcop
  rw [hd]

/-- The complete DFT of the actual carrier sequence is the manuscript's unit
additive transform at the unit-shifted frequency. -/
theorem dft_residueDedekindFunction_eq
    {k : ℕ} [NeZero k] (hk : 0 < k)
    (β : (ZMod k)ˣ) (n : ZMod k) :
    ZMod.dft (residueDedekindFunction β) n =
      kernelUnitTransform k (n * β.val).val := by
  classical
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod k)) IsUnit
      (fun a => ZMod.stdAddChar (-(a * n)) * residueDedekindFunction β a)
  have hnonunit :
      (∑ a ∈ (Finset.univ : Finset (ZMod k)) with ¬IsUnit a,
        ZMod.stdAddChar (-(a * n)) * residueDedekindFunction β a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : ¬IsUnit a := by simpa using (Finset.mem_filter.mp ha).2
    simp [residueDedekindFunction, hnot]
  calc
    (∑ a : ZMod k,
        ZMod.stdAddChar (-(a * n)) * residueDedekindFunction β a) =
      ∑ a ∈ (Finset.univ : Finset (ZMod k)) with IsUnit a,
        ZMod.stdAddChar (-(a * n)) * residueDedekindFunction β a := by
          rw [← hpartition, hnonunit, add_zero]
    _ = ∑ a : {a : ZMod k // IsUnit a},
        ZMod.stdAddChar (-(a.val * n)) *
          dedekindSum (β * a.property.unit⁻¹) := by
          rw [show
            (∑ a ∈ (Finset.univ : Finset (ZMod k)) with IsUnit a,
              ZMod.stdAddChar (-(a * n)) * residueDedekindFunction β a) =
              ∑ a : {a : ZMod k // IsUnit a},
                ZMod.stdAddChar (-(a.val * n)) *
                  residueDedekindFunction β a.val by
            exact Finset.sum_subtype
              ((Finset.univ : Finset (ZMod k)).filter IsUnit)
              (by intro a; simp)
              (fun a => ZMod.stdAddChar (-(a * n)) *
                residueDedekindFunction β a)]
          apply Finset.sum_congr rfl
          intro a _ha
          simp [residueDedekindFunction, a.property]
    _ = ∑ u : (ZMod k)ˣ,
        ZMod.stdAddChar (-(u.val * n)) * dedekindSum (β * u⁻¹) := by
          symm
          apply Fintype.sum_equiv unitsEquivIsUnit
          intro u
          have hunit :
              (unitsEquivIsUnit (m := k) u).property.unit = u := by
            apply Units.val_injective
            exact (unitsEquivIsUnit (m := k) u).property.unit_spec
          have hval : (unitsEquivIsUnit (m := k) u).val = u.val := by
            rw [← (unitsEquivIsUnit (m := k) u).property.unit_spec, hunit]
          rw [hunit]
          rw [hval]
    _ = ∑ h : (ZMod k)ˣ,
        dedekindSum h *
          ZMod.stdAddChar (-(((n * β.val).val : ZMod k) * h.val)) := by
          let e : (ZMod k)ˣ ≃ (ZMod k)ˣ := Equiv.mulRight β
          rw [← e.sum_comp]
          apply Finset.sum_congr rfl
          intro h _hh
          dsimp [e]
          have hdedekind : dedekindSum (β * (h * β)⁻¹) = dedekindSum h := by
            rw [show β * (h * β)⁻¹ = h⁻¹ by
            rw [mul_inv_rev, ← mul_assoc]
            simp, dedekindSum_inv]
          have hchar :
              ZMod.stdAddChar (-((h * β).val * n)) =
                ZMod.stdAddChar
                  (-(((n * β.val).val : ZMod k) * h.val)) := by
            apply congrArg ZMod.stdAddChar
            rw [ZMod.natCast_zmod_val]
            simp only [Units.val_mul]
            ring
          have hchar' :
              ZMod.stdAddChar (-(h.val * β.val * n)) =
                ZMod.stdAddChar
                  (-(((n * β.val).val : ZMod k) * h.val)) := by
            rw [← Units.val_mul]
            exact hchar
          rw [hdedekind, hchar']
          ring
    _ = kernelUnitTransform k (n * β.val).val := by
          unfold kernelUnitTransform
          rw [dif_neg hk.ne']

/-- A nonzero interval frequency has the standard reciprocal-chord bound. -/
theorem norm_intervalFourier_le_circular
    {k length : ℕ} [NeZero k] (hk : 0 < k)
    {n : ZMod k} (hn : n ≠ 0) :
    ‖intervalFourier k length n‖ ≤
      (k : ℝ) / (2 * (NField.Alignment.DedekindFourierMoment.circularDistance k n.val : ℝ)) := by
  have hnpos : 0 < n.val := ZMod.val_pos.mpr hn
  have hnlt : n.val < k := n.val_lt
  have hroot : ZMod.stdAddChar (-n) = negativeRoot k n.val := by
    rw [negativeRoot_eq_stdAddChar]
    congr 2
    exact (ZMod.natCast_zmod_val n).symm
  have hchord := negativeRoot_chord_lower hk hnpos hnlt
  have hdist : (0 : ℝ) < NField.Alignment.DedekindFourierMoment.circularDistance k n.val := by
    exact_mod_cast NField.Alignment.DedekindFourierMoment.circularDistance_pos hnpos hnlt
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [intervalFourier_eq_geom_quotient k length hn]
  have hnum : ‖(ZMod.stdAddChar (-n)) ^ length - 1‖ ≤ 2 := by
    calc
      ‖(ZMod.stdAddChar (-n)) ^ length - 1‖ ≤
          ‖(ZMod.stdAddChar (-n)) ^ length‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, AddChar.norm_apply, one_pow]; norm_num
  have hden : (0 : ℝ) < ‖ZMod.stdAddChar (-n) - 1‖ := by
    rw [hroot, show negativeRoot k n.val - 1 =
        -(1 - negativeRoot k n.val) by ring, norm_neg]
    exact lt_of_lt_of_le (by positivity :
      (0 : ℝ) < 4 * (NField.Alignment.DedekindFourierMoment.circularDistance k n.val : ℝ) / (k : ℝ)) hchord
  rw [norm_div]
  calc
    ‖(ZMod.stdAddChar (-n)) ^ length - 1‖ /
        ‖ZMod.stdAddChar (-n) - 1‖ ≤
      2 / ‖ZMod.stdAddChar (-n) - 1‖ := by gcongr
    _ ≤ 2 / (4 * (NField.Alignment.DedekindFourierMoment.circularDistance k n.val : ℝ) / (k : ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      rw [hroot, show negativeRoot k n.val - 1 =
          -(1 - negativeRoot k n.val) by ring, norm_neg]
      exact hchord
    _ = (k : ℝ) / (2 * (NField.Alignment.DedekindFourierMoment.circularDistance k n.val : ℝ)) := by
      field_simp [hkR.ne', hdist.ne']
      ring

/-- Exact finite Fourier inversion for an arbitrary interval of the actual
Dedekind carrier sequence. -/
theorem residueDedekindInterval_fourier
    {k : ℕ} [NeZero k]
    (β : (ZMod k)ˣ) (start length : ℕ) :
    (∑ j ∈ Finset.range length,
        residueDedekindSequence β (start + j)) =
      (k : ℂ)⁻¹ * ∑ n : ZMod k,
        ZMod.stdAddChar (n * (start : ZMod k)) *
          intervalFourier k length (-n) *
            ZMod.dft (residueDedekindFunction β) n := by
  have hinversion (x : ZMod k) :
      residueDedekindFunction β x =
        (k : ℂ)⁻¹ * ∑ n : ZMod k,
          ZMod.stdAddChar (n * x) *
            ZMod.dft (residueDedekindFunction β) n := by
    have h := congrFun
      (ZMod.dft.symm_apply_apply (residueDedekindFunction β)) x
    rw [ZMod.invDFT_apply] at h
    simpa [smul_eq_mul] using h.symm
  calc
    (∑ j ∈ Finset.range length,
        residueDedekindSequence β (start + j)) =
      ∑ j ∈ Finset.range length,
        residueDedekindFunction β ((start + j : ℕ) : ZMod k) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [residueDedekindFunction_natCast]
    _ = ∑ j ∈ Finset.range length,
        ((k : ℂ)⁻¹ * ∑ n : ZMod k,
          ZMod.stdAddChar (n * ((start + j : ℕ) : ZMod k)) *
            ZMod.dft (residueDedekindFunction β) n) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hinversion]
    _ = (k : ℂ)⁻¹ * ∑ j ∈ Finset.range length,
        ∑ n : ZMod k,
          ZMod.stdAddChar (n * ((start + j : ℕ) : ZMod k)) *
            ZMod.dft (residueDedekindFunction β) n := by
          rw [Finset.mul_sum]
    _ = (k : ℂ)⁻¹ * ∑ n : ZMod k,
        ∑ j ∈ Finset.range length,
          ZMod.stdAddChar (n * ((start + j : ℕ) : ZMod k)) *
            ZMod.dft (residueDedekindFunction β) n := by
          rw [Finset.sum_comm]
    _ = (k : ℂ)⁻¹ * ∑ n : ZMod k,
        ZMod.stdAddChar (n * (start : ZMod k)) *
          intervalFourier k length (-n) *
            ZMod.dft (residueDedekindFunction β) n := by
          congr 1
          apply Finset.sum_congr rfl
          intro n _hn
          unfold intervalFourier
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Nat.cast_add, mul_add, map_add_eq_mul]
          congr 2
          apply congrArg ZMod.stdAddChar
          ring

theorem dft_residueDedekindFunction_zero
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) (β : (ZMod k)ˣ) :
    ZMod.dft (residueDedekindFunction β) 0 = 0 := by
  rw [ZMod.dft_apply_zero]
  calc
    (∑ a : ZMod k, residueDedekindFunction β a) =
        ∑ a : Fin k,
          residueDedekindFunction β ((ZMod.finEquiv k).toEquiv a) := by
            exact ((ZMod.finEquiv k).toEquiv.sum_comp
              (residueDedekindFunction β)).symm
    _ = ∑ a : Fin k, residueDedekindSequence β a.val := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [show ((ZMod.finEquiv k).toEquiv a : ZMod k) =
              (a.val : ZMod k) by
            simpa using
              NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast a]
          exact residueDedekindFunction_natCast β a.val
    _ = ∑ a ∈ Finset.range k, residueDedekindSequence β a := by
          exact Fin.sum_univ_eq_sum_range (residueDedekindSequence β) k
    _ = 0 := residueDedekindSequence_sum_period_of_two hk β

theorem sum_nonzero_circular_reciprocal_le
    {k : ℕ} [NeZero k] (hk : 0 < k) :
    (∑ n : ZMod k, if n = 0 then 0 else
      1 / (NField.Alignment.DedekindFourierMoment.circularDistance
        k n.val : ℝ)) ≤ 2 * (harmonic k : ℝ) := by
  let w : ℕ → ℝ := fun n => if n = 0 then 0 else
    1 / (NField.Alignment.DedekindFourierMoment.circularDistance k n : ℝ)
  calc
    (∑ n : ZMod k, if n = 0 then 0 else
        1 / (NField.Alignment.DedekindFourierMoment.circularDistance
          k n.val : ℝ)) =
      ∑ n : Fin k, w n.val := by
        rw [← (ZMod.finEquiv k).toEquiv.sum_comp]
        apply Finset.sum_congr rfl
        intro n _hn
        rw [show ((ZMod.finEquiv k).toEquiv n : ZMod k) =
            (n.val : ZMod k) by
          simpa using
            NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast n]
        unfold w
        by_cases hn0 : n.val = 0
        · rw [hn0]
          simp
        · rw [if_neg hn0, if_neg (by
            intro hzero
            have hval := congrArg ZMod.val hzero
            apply hn0
            simpa [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt] using hval)]
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt]
    _ = ∑ n ∈ Finset.range k, w n := by
          exact Fin.sum_univ_eq_sum_range w k
    _ = ∑ n ∈ Finset.Ico 1 k,
        1 / (NField.Alignment.DedekindFourierMoment.circularDistance k n : ℝ) := by
          rw [NField.Alignment.DedekindReciprocity.sum_range_eq_sum_Ico_one
            w hk]
          · apply Finset.sum_congr rfl
            intro n hn
            unfold w
            rw [if_neg (Nat.ne_of_gt (Finset.mem_Ico.mp hn).1)]
          · simp [w]
    _ ≤ 2 * (harmonic k : ℝ) :=
      NField.Alignment.DedekindFourierMoment.circularReciprocal_sum_le_harmonic hk

/-- Fourier inversion and the reciprocal-chord sum turn a uniform additive
transform estimate into the interval-prefix estimate used by Abel summation. -/
theorem norm_residueDedekindSequence_interval_le_of_transform
    {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (β : (ZMod k)ˣ) {U : ℝ} (hU : 0 ≤ U)
    (htransform : ∀ t,
      ‖unitDedekindTransform k t‖ / (k : ℝ) ≤ U)
    (start length : ℕ) :
    ‖∑ j ∈ Finset.range length,
        residueDedekindSequence β (start + j)‖ ≤
      (k : ℝ) * U * (harmonic k : ℝ) := by
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hH : (0 : ℝ) ≤ (harmonic k : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic k by
      unfold harmonic
      positivity)
  have hdft : ∀ n : ZMod k,
      ‖ZMod.dft (residueDedekindFunction β) n‖ ≤ (k : ℝ) * U := by
    intro n
    rw [dft_residueDedekindFunction_eq hkpos β n,
      kernelUnitTransform_eq_unitDedekindTransform hkpos]
    have h := htransform (n * β.val).val
    simpa [mul_comm] using (div_le_iff₀ hkR).mp h
  let weight : ZMod k → ℝ := fun n => if n = 0 then 0 else
    1 / (NField.Alignment.DedekindFourierMoment.circularDistance
      k n.val : ℝ)
  let A : ℝ := (k : ℝ) ^ 2 * U / 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hterm : ∀ n : ZMod k,
      ‖ZMod.stdAddChar (n * (start : ZMod k)) *
          intervalFourier k length (-n) *
            ZMod.dft (residueDedekindFunction β) n‖ ≤ A * weight n := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [dft_residueDedekindFunction_zero hk β, mul_zero, norm_zero]
      simp [weight]
    · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
      have hinter := norm_intervalFourier_le_circular hkpos
        (length := length) hneg
      have hvalneg : (-n).val = k - n.val := by
        letI : NeZero n := ⟨hn⟩
        exact ZMod.val_neg_of_ne_zero n
      have hdistNeg :
          NField.Alignment.DedekindFourierMoment.circularDistance k (-n).val =
            NField.Alignment.DedekindFourierMoment.circularDistance k n.val := by
        rw [hvalneg]
        unfold NField.Alignment.DedekindFourierMoment.circularDistance
        omega
      rw [hdistNeg] at hinter
      rw [norm_mul, norm_mul, AddChar.norm_apply, one_mul]
      have hfreq := hdft n
      have hdist : (0 : ℝ) <
          NField.Alignment.DedekindFourierMoment.circularDistance k n.val := by
        exact_mod_cast NField.Alignment.DedekindFourierMoment.circularDistance_pos
          (ZMod.val_pos.mpr hn) n.val_lt
      unfold weight
      rw [if_neg hn]
      calc
        ‖intervalFourier k length (-n)‖ *
            ‖ZMod.dft (residueDedekindFunction β) n‖ ≤
          ((k : ℝ) / (2 *
            (NField.Alignment.DedekindFourierMoment.circularDistance
              k n.val : ℝ))) * ((k : ℝ) * U) := by
                exact mul_le_mul hinter hfreq (norm_nonneg _)
                  (by positivity)
        _ = A * (1 /
            (NField.Alignment.DedekindFourierMoment.circularDistance
              k n.val : ℝ)) := by
              dsimp [A]
              field_simp [hdist.ne']
  rw [residueDedekindInterval_fourier β start length]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ n : ZMod k,
          ZMod.stdAddChar (n * (start : ZMod k)) *
            intervalFourier k length (-n) *
              ZMod.dft (residueDedekindFunction β) n‖ ≤
        A * (2 * (harmonic k : ℝ)) := by
    calc
      ‖∑ n : ZMod k,
          ZMod.stdAddChar (n * (start : ZMod k)) *
            intervalFourier k length (-n) *
              ZMod.dft (residueDedekindFunction β) n‖ ≤
        ∑ n : ZMod k,
          ‖ZMod.stdAddChar (n * (start : ZMod k)) *
            intervalFourier k length (-n) *
              ZMod.dft (residueDedekindFunction β) n‖ := norm_sum_le _ _
      _ ≤ ∑ n : ZMod k, A * weight n :=
        Finset.sum_le_sum fun n _hn => hterm n
      _ = A * ∑ n : ZMod k, weight n := by rw [Finset.mul_sum]
      _ ≤ A * (2 * (harmonic k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        simpa [weight] using sum_nonzero_circular_reciprocal_le hkpos
  calc
    (k : ℝ)⁻¹ *
        ‖∑ n : ZMod k,
          ZMod.stdAddChar (n * (start : ZMod k)) *
            intervalFourier k length (-n) *
              ZMod.dft (residueDedekindFunction β) n‖ ≤
      (k : ℝ)⁻¹ * (A * (2 * (harmonic k : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hkR.le)
    _ = (k : ℝ) * U * (harmonic k : ℝ) := by
      dsimp [A]
      field_simp [hkR.ne']

/-- The finite Fourier prefix bound inserted into the exact Abel lemma gives
the manuscript's one-carrier estimate before logarithms are simplified. -/
theorem norm_floorWeighted_residueDedekindSequence_le_of_transform
    {k b : ℕ} [NeZero k] (hk : 2 ≤ k) (hkb : k < b)
    (β : (ZMod k)ˣ) {U : ℝ} (hU : 0 ≤ U)
    (htransform : ∀ t,
      ‖unitDedekindTransform k t‖ / (k : ℝ) ≤ U) :
    ‖∑ a ∈ Finset.Ico (k + 1) b,
        (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      2 * (((b - 1) / (k + 1) : ℕ) : ℝ) *
        ((k : ℝ) * U * (harmonic k : ℝ)) := by
  have hM : 0 ≤ (k : ℝ) * U * (harmonic k : ℝ) := by
    have hH : (0 : ℝ) ≤ (harmonic k : ℝ) := by
      exact_mod_cast (show (0 : ℚ) ≤ harmonic k by
        unfold harmonic
        positivity)
    positivity
  apply norm_floorWeighted_residueDedekindSequence_le_of_prefix
    hkb β ((k : ℝ) * U * (harmonic k : ℝ)) hM
  intro start length
  rw [Finset.sum_Ico_eq_sum_range]
  simpa using norm_residueDedekindSequence_interval_le_of_transform
    hk β hU htransform start length

end NField.Alignment.DedekindCarrierFourierBound
