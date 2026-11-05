/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionTranslationSubspace
import NField.Alignment.CollisionSpectralSupport

/-!
# Simple rational eigenspaces of the actual odometer

A real cosine/sine eigenpair, viewed as one complex-valued function, becomes
translation invariant after division by its unit character. Actual Haar
ergodicity therefore makes that quotient constant.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCharacterEigenvectors

open scoped BigOperators ComplexConjugate
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCoboundary ProfiniteOdometerErgodic
open CollisionRamanujan CollisionTranslationSubspace

def characterMap (q a : ℕ) [NeZero q] : C(Phase,ℂ) :=
  ⟨fun x => ZMod.stdAddChar ((a : ZMod q)*(residueHom q x).toAdd),
    (show Continuous (fun r : Multiplicative (ZMod q) =>
      ZMod.stdAddChar ((a : ZMod q)*r.toAdd)) from continuous_of_discreteTopology).comp
        (residueHom q).continuous_toFun⟩

def characterRoot (q a : ℕ) [NeZero q] : ℂ := ZMod.stdAddChar (a : ZMod q)

theorem characterMap_phase (q a : ℕ) [NeZero q] (x : Phase) :
    characterMap q a x=phase q ((residueHom q x).toAdd.val : ℤ) a := by
  rw [phase_std (Nat.pos_of_ne_zero (NeZero.ne q))]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val, characterMap, ContinuousMap.coe_mk]
  congr 1
  ring

theorem characterMap_norm (q a : ℕ) [NeZero q] (x : Phase) : ‖characterMap q a x‖=1 := by
  rw [characterMap_phase, phase_norm]

theorem characterRoot_phase (q a : ℕ) [NeZero q] : characterRoot q a=phase q 1 a := by
  rw [phase_std (Nat.pos_of_ne_zero (NeZero.ne q))]
  simp [characterRoot]

theorem characterRoot_norm (q a : ℕ) [NeZero q] : ‖characterRoot q a‖=1 := by
  rw [characterRoot_phase, phase_norm]

theorem characterMap_translate (q a : ℕ) [NeZero q] (x : Phase) :
    characterMap q a (translate 1 x)=characterRoot q a*characterMap q a x := by
  change ZMod.stdAddChar ((a : ZMod q)*(residueHom q (translate 1 x)).toAdd)=_
  rw [residue_translate]
  simp only [Int.cast_one, mul_add, mul_one, AddChar.map_add_eq_mul]
  rfl

def characterReMap (q a : ℕ) [NeZero q] : C(Phase,ℝ) :=
  ⟨fun x => (characterMap q a x).re, Complex.continuous_re.comp (characterMap q a).continuous⟩

def characterImMap (q a : ℕ) [NeZero q] : C(Phase,ℝ) :=
  ⟨fun x => (characterMap q a x).im, Complex.continuous_im.comp (characterMap q a).continuous⟩

def characterReVector (q a : ℕ) [NeZero q] : HaarL2 :=
  ContinuousMap.toLp 2 phaseHaar ℝ (characterReMap q a)

def characterImVector (q a : ℕ) [NeZero q] : HaarL2 :=
  ContinuousMap.toLp 2 phaseHaar ℝ (characterImMap q a)

def translationMap (h : ℤ) : C(Phase,Phase) :=
  ⟨translate h, continuous_const.mul continuous_id⟩

theorem shift_toLp (h : ℤ) (f : C(Phase,ℝ)) :
    shift h (ContinuousMap.toLp 2 phaseHaar ℝ f)=
      ContinuousMap.toLp 2 phaseHaar ℝ (f.comp (translationMap h)) := by
  apply Lp.ext
  have hf := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar f
  have hft := (translate_measurePreserving h).quasiMeasurePreserving.ae hf
  have hc := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar
    (f.comp (translationMap h))
  filter_upwards [shift_coe h (ContinuousMap.toLp 2 phaseHaar ℝ f), hft, hc]
    with x hx htx hcx
  exact hx.trans (htx.trans hcx.symm)

theorem characterReVector_shift (q a : ℕ) [NeZero q] :
    shift 1 (characterReVector q a) =
      (characterRoot q a).re • characterReVector q a-
      (characterRoot q a).im • characterImVector q a := by
  have hm : (characterReMap q a).comp (translationMap 1)=
      (characterRoot q a).re • characterReMap q a-
      (characterRoot q a).im • characterImMap q a := by
    ext x
    exact congrArg Complex.re (characterMap_translate q a x)
  simp only [characterReVector, characterImVector, shift_toLp, hm, map_sub, map_smul]

theorem characterImVector_shift (q a : ℕ) [NeZero q] :
    shift 1 (characterImVector q a) =
      (characterRoot q a).im • characterReVector q a+
      (characterRoot q a).re • characterImVector q a := by
  have hm : (characterImMap q a).comp (translationMap 1)=
      (characterRoot q a).im • characterReMap q a+
      (characterRoot q a).re • characterImMap q a := by
    ext x
    change (characterMap q a (translate 1 x)).im =
      (characterRoot q a).im*(characterMap q a x).re+
      (characterRoot q a).re*(characterMap q a x).im
    rw [characterMap_translate, Complex.mul_im, add_comm]
  simp only [characterReVector, characterImVector, shift_toLp, hm, map_add, map_smul]

theorem complex_pair_translate (U W : HaarL2) (z : ℂ)
    (hU : shift 1 U=z.re • U-z.im • W)
    (hW : shift 1 W=z.im • U+z.re • W) :
    (fun x => (U (translate 1 x) : ℂ)+Complex.I*(W (translate 1 x) : ℂ)) =ᵐ[phaseHaar]
      (fun x => z*((U x : ℂ)+Complex.I*(W x : ℂ))) := by
  have hu := shift_coe 1 U
  have hw := shift_coe 1 W
  rw [hU] at hu
  rw [hW] at hw
  filter_upwards [hu, hw, Lp.coeFn_sub (z.re • U) (z.im • W),
    Lp.coeFn_add (z.im • U) (z.re • W), Lp.coeFn_smul z.re U,
    Lp.coeFn_smul z.im W, Lp.coeFn_smul z.im U, Lp.coeFn_smul z.re W]
    with x hux hwx hsub hadd hru hiw hiu hrw
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [hsub, hru, hiw] at hux
  rw [hadd, hiu, hrw] at hwx
  rw [← hux, ← hwx]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, add_comm]

theorem character_eigenpair_simple (q a : ℕ) [NeZero q] (U W : HaarL2)
    (hU : shift 1 U=(characterRoot q a).re • U-(characterRoot q a).im • W)
    (hW : shift 1 W=(characterRoot q a).im • U+(characterRoot q a).re • W) :
    ∃ c : ℂ, (fun x => (U x : ℂ)+Complex.I*(W x : ℂ)) =ᵐ[phaseHaar]
      (fun x => c*characterMap q a x) := by
  let F : Phase → ℂ := fun x => ((U x : ℂ)+Complex.I*(W x : ℂ))*conj (characterMap q a x)
  have hUm : AEStronglyMeasurable (fun x => (U x : ℂ)) phaseHaar :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)
  have hWm : AEStronglyMeasurable (fun x => (W x : ℂ)) phaseHaar :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable W)
  have hFm : AEStronglyMeasurable F phaseHaar :=
    (hUm.add (hWm.const_mul Complex.I)).mul
      ((Complex.continuous_conj.comp (characterMap q a).continuous).aestronglyMeasurable)
  have hFinv : F ∘ translate 1 =ᵐ[phaseHaar] F := by
    filter_upwards [complex_pair_translate U W _ hU hW] with x hx
    change ((U (translate 1 x) : ℂ)+Complex.I*(W (translate 1 x) : ℂ))*
      conj (characterMap q a (translate 1 x))=F x
    rw [hx, characterMap_translate, map_mul]
    have hz : characterRoot q a*conj (characterRoot q a)=1 := by
      rw [Complex.mul_conj', characterRoot_norm]
      norm_num
    dsimp [F]
    linear_combination (((U x : ℂ)+Complex.I*(W x : ℂ))*conj (characterMap q a x))*hz
  obtain ⟨c,hc⟩ := odometer_ergodic.ae_eq_const_of_ae_eq_comp_ae hFm hFinv
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  have hz : conj (characterMap q a x)*characterMap q a x=1 := by
    rw [Complex.conj_mul', characterMap_norm]
    norm_num
  change ((U x : ℂ)+Complex.I*(W x : ℂ))*conj (characterMap q a x)=c at hx
  calc
    _ = ((U x : ℂ)+Complex.I*(W x : ℂ))*
      (conj (characterMap q a x)*characterMap q a x) := by rw [hz, mul_one]
    _ = c*characterMap q a x := by rw [← mul_assoc, hx]

end NField.Alignment.CollisionCharacterEigenvectors
