/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBoundaryTesting
import NField.Alignment.CollisionAmplitudeEnclosure
import NField.Alignment.CollisionDivisibilityCovariance

/-!
# Certified finite Haar test pairings

The finite approximation retains the full constant term and truncates only
the divisor forcing. Its error is bounded by the omitted unit mass times
the test norm. Finite residue tables provide computable test functions.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHaarTestEnclosure

open scoped BigOperators Classical
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionResetIntegrability CollisionPotentialCoboundary CollisionBoundaryTesting
open CollisionIntegerSingularity CollisionAmplitudeEnclosure
open CollisionDivisibilityCovariance
open ProfinitePeriodicTesting
open CollisionPotentialConvergence

def resetPair (φ : LocallyConstant Phase ℝ) (k : ℕ) : ℝ :=
  ∫ x, resetTerm k x*φ x ∂phaseHaar

theorem resetPair_norm_bound (φ : LocallyConstant Phase ℝ) (k : ℕ) :
    ‖resetPair φ k‖ ≤ ‖(φ : C(Phase, ℝ))‖*collisionWeight k :=
  (norm_integral_le_integral_norm _).trans (resetTest_integral_norm_bound k φ)

theorem resetPair_summable (φ : LocallyConstant Phase ℝ) : Summable (resetPair φ) :=
  (collisionWeight_summable.mul_left ‖(φ : C(Phase, ℝ))‖).of_norm_bounded
    (resetPair_norm_bound φ)

def omittedPair (φ : LocallyConstant Phase ℝ) (M : ℕ) : ℝ :=
  ∑' j : ℕ, resetPair φ (j+(M+1))

theorem omittedPair_norm_bound (φ : LocallyConstant Phase ℝ) (M : ℕ) :
    ‖omittedPair φ M‖ ≤ ‖(φ : C(Phase, ℝ))‖*tailMass M := by
  have hinj : Function.Injective (fun j : ℕ => j+(M+1)) := fun _ _ h => Nat.add_right_cancel h
  have hs := (resetPair_summable φ).norm.comp_injective hinj
  calc
    _ ≤ ∑' j : ℕ, ‖resetPair φ (j+(M+1))‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, ‖(φ : C(Phase, ℝ))‖*collisionWeight (j+(M+1)) :=
      hs.tsum_le_tsum (fun j => resetPair_norm_bound φ (j+(M+1)))
        ((collisionWeight_summable.comp_injective hinj).mul_left _)
    _ = _ := by rw [tsum_mul_left]; rfl

def finiteHaarPair (φ : LocallyConstant Phase ℝ) (M : ℕ) : ℝ :=
  (2/3 : ℝ)*((∫ x, φ x ∂phaseHaar)-∑ k ∈ Finset.range (M+1), resetPair φ k)

theorem finiteHaarPair_error_identity (φ : LocallyConstant Phase ℝ) (M : ℕ) :
    (∫ x, increment x*φ x ∂phaseHaar)-finiteHaarPair φ M = -(2/3 : ℝ)*omittedPair φ M := by
  have hs := (resetPair_summable φ).sum_add_tsum_nat_add (M+1)
  change (∑ k ∈ Finset.range (M+1), resetPair φ k)+omittedPair φ M=∑' k, resetPair φ k at hs
  rw [increment_test_integral, finiteHaarPair, resetFunction_test_integral]
  change (2/3 : ℝ)*((∫ x, φ x ∂phaseHaar)-∑' k, resetPair φ k)-
    (2/3 : ℝ)*((∫ x, φ x ∂phaseHaar)-∑ k ∈ Finset.range (M+1), resetPair φ k) = _
  linarith

theorem finiteHaarPair_error_bound (φ : LocallyConstant Phase ℝ) (M : ℕ) :
    ‖(∫ x, increment x*φ x ∂phaseHaar)-finiteHaarPair φ M‖ ≤
      (2/3 : ℝ)*‖(φ : C(Phase, ℝ))‖*tailMass M := by
  rw [finiteHaarPair_error_identity, norm_mul]
  norm_num only [Real.norm_eq_abs, abs_neg, abs_div]
  have h := mul_le_mul_of_nonneg_left (omittedPair_norm_bound φ M) (by norm_num : (0 : ℝ)≤2/3)
  simpa only [mul_assoc, Real.norm_eq_abs] using h

theorem finiteHaarPair_enclosure (φ : LocallyConstant Phase ℝ) (M : ℕ) (B : ℝ)
    (hB : ‖(φ : C(Phase, ℝ))‖≤B) :
    (∫ x, increment x*φ x ∂phaseHaar) ∈ Set.Icc
      (finiteHaarPair φ M-(2/3 : ℝ)*B*(1-∑ k ∈ Finset.Icc 2 M, collisionWeight k))
      (finiteHaarPair φ M+(2/3 : ℝ)*B*(1-∑ k ∈ Finset.Icc 2 M, collisionWeight k)) := by
  have hb := (finiteHaarPair_error_bound φ M).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num)) (tailMass_nonneg M))
  rw [tailMass_eq_complement, Real.norm_eq_abs] at hb
  obtain ⟨hlo,hhi⟩ := abs_le.mp hb
  constructor <;> linarith

theorem finiteHaarPair_tendsto (φ : LocallyConstant Phase ℝ) :
    Tendsto (finiteHaarPair φ) atTop (nhds (∫ x, increment x*φ x ∂phaseHaar)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun M => norm_nonneg _)
    (fun M => (norm_sub_rev _ _).trans_le (finiteHaarPair_error_bound φ M)) ?_
  simpa only [mul_zero] using tailMass_tendsto_zero.const_mul ((2/3 : ℝ)*‖(φ : C(Phase, ℝ))‖)

def residueTableTest (L : ℕ) [NeZero L] (v : ℕ → ℝ) : LocallyConstant Phase ℝ :=
  ⟨fun x => v (residueHom L x).toAdd.val,
    (IsLocallyConstant.of_discrete (fun r : Multiplicative (ZMod L) => v r.toAdd.val)).comp_continuous
      (residueHom L).continuous_toFun⟩

theorem residueTableTest_integer (L : ℕ) [NeZero L] (v : ℕ → ℝ) (n : ℕ) :
    residueTableTest L v (integerPhase n)=v (n%L) := by
  simp only [residueTableTest, LocallyConstant.coe_mk, residue_integer, Int.cast_natCast,
    ZMod.val_natCast]

theorem residueTableTest_mean (L : ℕ) [NeZero L] (v : ℕ → ℝ) :
    (∫ x, residueTableTest L v x ∂phaseHaar)=(∑ j ∈ Finset.range L, v j)/(L : ℝ) :=
  integral_residue L v

theorem residueTableTest_norm_le (L : ℕ) [NeZero L] (v : ℕ → ℝ) {B : ℝ}
    (hB : 0≤B) (hv : ∀ j<L, |v j|≤B) : ‖(residueTableTest L v : C(Phase, ℝ))‖≤B := by
  apply (ContinuousMap.norm_le _ hB).mpr
  intro x
  exact hv _ (ZMod.val_lt _)

theorem residueTableTest_eq_sum (L : ℕ) [NeZero L] (v : ℕ → ℝ) (x : Phase) :
    residueTableTest L v x = ∑ j ∈ Finset.range L,
      v j*(residueEvent L j).indicator (fun _ => (1 : ℝ)) x := by
  have he (j : ℕ) (hj : j ∈ Finset.range L) :
      x ∈ residueEvent L j ↔ j=(residueHom L x).toAdd.val := by
    rw [mem_residueEvent_via (dvd_refl L)]
    exact ⟨fun h => (h.eq_of_lt_of_lt (ZMod.val_lt _) (Finset.mem_range.mp hj)).symm,
      fun h => h ▸ Nat.ModEq.refl _⟩
  calc
    _ = ∑ j ∈ Finset.range L,
        if j=(residueHom L x).toAdd.val then v j else 0 := by
      simp [residueTableTest, ZMod.val_lt]
    _ = _ := Finset.sum_congr rfl (fun j hj => by simp [Set.indicator_apply, he j hj])

theorem residuePair_integrable (k L j : ℕ) :
    Integrable (fun x => (residueEvent k 0).indicator (fun _ => (1 : ℝ)) x *
      (residueEvent L j).indicator (fun _ => (1 : ℝ)) x) phaseHaar := by
  convert! (continuous_phase_integrable (1 : C(Phase, ℝ))).indicator
    ((residueEvent_measurable k 0).inter (residueEvent_measurable L j)) using 1
  funext x
  by_cases hk : x ∈ residueEvent k 0 <;> by_cases hL : x ∈ residueEvent L j <;>
    simp [hk, hL]

/-- The finite formula uses the generalized CRT, so noncoprime periods
and incompatible residue classes are retained exactly. -/
theorem resetPair_residueTable {k L : ℕ} (hk : 0<k) (hL : 0<L)
    [NeZero L] (v : ℕ → ℝ) :
    resetPair (residueTableTest L v) k =
      ((k : ℝ)*collisionWeight k)/(k.lcm L : ℝ) *
        ∑ j ∈ Finset.range L, if k.gcd L ∣ j then v j else 0 := by
  have he (x : Phase) : resetTerm k x*residueTableTest L v x =
      ((k : ℝ)*collisionWeight k)*∑ j ∈ Finset.range L,
        v j*((residueEvent k 0).indicator (fun _ => (1 : ℝ)) x *
          (residueEvent L j).indicator (fun _ => (1 : ℝ)) x) := by
    rw [resetTerm_indicator, resetEvent_eq, residueTableTest_eq_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold resetPair
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _
    (fun j _ => (residuePair_integrable k L j).const_mul (v j))]
  simp_rw [integral_const_mul, residueEvent_pair_integral hk hL]
  have hi (j : ℕ) : Nat.ModEq (k.gcd L) 0 j ↔ k.gcd L ∣ j :=
    ⟨fun h => Nat.modEq_zero_iff_dvd.mp h.symm,
      fun h => (Nat.modEq_zero_iff_dvd.mpr h).symm⟩
  simp_rw [hi]
  rw [div_mul_eq_mul_div, mul_div_assoc, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem boundaryIncrement_divisor_formula {n : ℕ} (hn : 0<n) :
    boundaryIncrement n=(2/3 : ℝ)*(1-∑ k ∈ n.divisors, (k : ℝ)*collisionWeight k) := by
  rw [boundaryIncrement_integer hn, increment, resetFunction_integer hn]

theorem finiteHaarPair_residueTable (L M : ℕ) [NeZero L] (v : ℕ → ℝ) :
    finiteHaarPair (residueTableTest L v) M = (2/3 : ℝ)*
      ((∑ j ∈ Finset.range L, v j)/(L : ℝ)-∑ k ∈ Finset.Icc 2 M,
        ((k : ℝ)*collisionWeight k)/(k.lcm L : ℝ)*
          ∑ j ∈ Finset.range L, if k.gcd L ∣ j then v j else 0) := by
  have hs : (∑ k ∈ Finset.Icc 2 M, resetPair (residueTableTest L v) k) =
      ∑ k ∈ Finset.range (M+1), resetPair (residueTableTest L v) k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    · intro k hk hnot
      have hsmall : k<2 := by
        simp only [Finset.mem_Icc, Finset.mem_range] at *
        omega
      interval_cases k <;> simp [resetPair]
  rw [finiteHaarPair, residueTableTest_mean, ← hs]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  exact resetPair_residueTable (by have := (Finset.mem_Icc.mp hk).1; omega)
    (Nat.pos_of_ne_zero (NeZero.ne L)) v

theorem residueTable_boundary_average (N L : ℕ) [NeZero L] (v : ℕ → ℝ) :
    orbitAverage N (fun n => boundaryIncrement n*residueTableTest L v (integerPhase n)) =
      (∑ n ∈ Finset.range N, ((2/3 : ℝ)*(1-∑ k ∈ (n+1).divisors,
        (k : ℝ)*collisionWeight k))*v ((n+1)%L))/(N : ℝ) := by
  unfold orbitAverage
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  change boundaryIncrement (n+1)*residueTableTest L v (integerPhase (n+1 : ℕ))=_
  rw [boundaryIncrement_divisor_formula (Nat.succ_pos n), residueTableTest_integer]

def complexResidueTableTest (L : ℕ) [NeZero L] (vr vi : ℕ → ℝ) : LocallyConstant Phase ℂ :=
  ⟨fun x => (vr (residueHom L x).toAdd.val : ℂ)+(vi (residueHom L x).toAdd.val : ℂ)*Complex.I,
    (IsLocallyConstant.of_discrete (fun r : Multiplicative (ZMod L) =>
      (vr r.toAdd.val : ℂ)+(vi r.toAdd.val : ℂ)*Complex.I)).comp_continuous
      (residueHom L).continuous_toFun⟩

@[simp] theorem complexResidueTableTest_real (L : ℕ) [NeZero L] (vr vi : ℕ → ℝ) :
    realPartTest (complexResidueTableTest L vr vi)=residueTableTest L vr := by
  ext x
  simp [realPartTest, complexResidueTableTest, residueTableTest,
    LocallyConstant.map_apply]

@[simp] theorem complexResidueTableTest_imag (L : ℕ) [NeZero L] (vr vi : ℕ → ℝ) :
    imagPartTest (complexResidueTableTest L vr vi)=residueTableTest L vi := by
  ext x
  simp [imagPartTest, complexResidueTableTest, residueTableTest,
    LocallyConstant.map_apply]

def boundaryHaarPair (φ : LocallyConstant Phase ℂ) : ℂ :=
  ∫ x, ((collisionPotential x-
    collisionPotential (CollisionPotentialCoboundary.translate (-1) x)) : ℂ)*star (φ x) ∂phaseHaar

theorem boundaryHaarPair_split (φ : LocallyConstant Phase ℂ) :
    boundaryHaarPair φ =
      ((∫ x, increment x*realPartTest φ x ∂phaseHaar : ℝ) : ℂ)-
        ((∫ x, increment x*imagPartTest φ x ∂phaseHaar : ℝ) : ℂ)*Complex.I := by
  have he (ψ : LocallyConstant Phase ℝ) :
      (∫ x, (collisionPotential x-collisionPotential (CollisionPotentialCoboundary.translate (-1) x))*ψ x ∂phaseHaar) =
        ∫ x, increment x*ψ x ∂phaseHaar := by
    apply integral_congr_ae
    filter_upwards [increment_coboundary_ae] with x hx
    rw [hx]
  rw [boundaryHaarPair, complex_test_integral_split, he, he]

def finiteComplexHaarPair (φ : LocallyConstant Phase ℂ) (M : ℕ) : ℂ :=
  (finiteHaarPair (realPartTest φ) M : ℂ)-(finiteHaarPair (imagPartTest φ) M : ℂ)*Complex.I

theorem complexHaarPair_component_error (φ : LocallyConstant Phase ℂ) (M : ℕ) :
    |(boundaryHaarPair φ-finiteComplexHaarPair φ M).re| ≤
      (2/3 : ℝ)*‖(realPartTest φ : C(Phase, ℝ))‖*tailMass M ∧
    |(boundaryHaarPair φ-finiteComplexHaarPair φ M).im| ≤
      (2/3 : ℝ)*‖(imagPartTest φ : C(Phase, ℝ))‖*tailMass M := by
  rw [boundaryHaarPair_split, finiteComplexHaarPair]
  constructor
  · simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_sub, Real.norm_eq_abs]
      using finiteHaarPair_error_bound (realPartTest φ) M
  · have h := finiteHaarPair_error_bound (imagPartTest φ) M
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, zero_sub, add_zero]
    have he : -(∫ x, increment x*imagPartTest φ x ∂phaseHaar)-
        -(finiteHaarPair (imagPartTest φ) M) =
      -((∫ x, increment x*imagPartTest φ x ∂phaseHaar)-finiteHaarPair (imagPartTest φ) M) := by ring
    rw [he, abs_neg]
    simpa only [Real.norm_eq_abs] using h

theorem complexResidueTable_enclosure (L M : ℕ) [NeZero L] (vr vi : ℕ → ℝ)
    {Br Bi : ℝ} (hBr : 0≤Br) (hBi : 0≤Bi)
    (hr : ∀ j<L, |vr j|≤Br) (hi : ∀ j<L, |vi j|≤Bi) :
    |(boundaryHaarPair (complexResidueTableTest L vr vi)-
      finiteComplexHaarPair (complexResidueTableTest L vr vi) M).re| ≤
      (2/3 : ℝ)*Br*(1-∑ k ∈ Finset.Icc 2 M, collisionWeight k) ∧
    |(boundaryHaarPair (complexResidueTableTest L vr vi)-
      finiteComplexHaarPair (complexResidueTableTest L vr vi) M).im| ≤
      (2/3 : ℝ)*Bi*(1-∑ k ∈ Finset.Icc 2 M, collisionWeight k) := by
  have h := complexHaarPair_component_error (complexResidueTableTest L vr vi) M
  simp only [complexResidueTableTest_real, complexResidueTableTest_imag] at h
  rw [← tailMass_eq_complement]
  constructor
  · exact h.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (residueTableTest_norm_le L vr hBr hr) (by norm_num))
      (tailMass_nonneg M))
  · exact h.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (residueTableTest_norm_le L vi hBi hi) (by norm_num))
      (tailMass_nonneg M))

theorem finiteComplexHaarPair_tendsto (φ : LocallyConstant Phase ℂ) :
    Tendsto (finiteComplexHaarPair φ) atTop (nhds (boundaryHaarPair φ)) := by
  rw [boundaryHaarPair_split]
  have hr := (Complex.continuous_ofReal.tendsto _).comp (finiteHaarPair_tendsto (realPartTest φ))
  have hi := (Complex.continuous_ofReal.tendsto _).comp (finiteHaarPair_tendsto (imagPartTest φ))
  exact hr.sub (hi.mul_const Complex.I)

end NField.Alignment.CollisionHaarTestEnclosure
