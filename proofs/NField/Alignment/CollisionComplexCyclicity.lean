/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionIncrementCyclicity

/-!
# Complex Haar cyclicity from the proved real translation span

Real and imaginary parts are continuous maps of the actual complex Haar
L2 space. Their real cyclic approximations lift to complex approximations,
so the complex closed span has precisely the same mean-zero description.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionComplexCyclicity

open scoped BigOperators
open MeasureTheory ProfiniteRemainderMeasure CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionPotentialCoboundary CollisionOdometerRecurrence
open CollisionTranslationSubspace CollisionIncrementCyclicity

abbrev ComplexHaarL2 := Lp ℂ 2 phaseHaar

def complexLift : HaarL2 →L[ℝ] ComplexHaarL2 := Complex.ofRealCLM.compLpL 2 phaseHaar
def realPart : ComplexHaarL2 →L[ℝ] HaarL2 := Complex.reCLM.compLpL 2 phaseHaar
def imagPart : ComplexHaarL2 →L[ℝ] HaarL2 := Complex.imCLM.compLpL 2 phaseHaar

theorem complexLift_coe (V : HaarL2) :
    (fun x => complexLift V x) =ᵐ[phaseHaar] (fun x => (V x : ℂ)) :=
  Complex.ofRealCLM.coeFn_compLpL V

theorem realPart_coe (V : ComplexHaarL2) :
    (fun x => realPart V x) =ᵐ[phaseHaar] (fun x => (V x).re) :=
  Complex.reCLM.coeFn_compLpL V

theorem imagPart_coe (V : ComplexHaarL2) :
    (fun x => imagPart V x) =ᵐ[phaseHaar] (fun x => (V x).im) :=
  Complex.imCLM.coeFn_compLpL V

theorem complex_parts (V : ComplexHaarL2) :
    complexLift (realPart V)+Complex.I • complexLift (imagPart V)=V := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (complexLift (realPart V)) (Complex.I • complexLift (imagPart V)),
    Lp.coeFn_smul Complex.I (complexLift (imagPart V)), complexLift_coe (realPart V),
    complexLift_coe (imagPart V), realPart_coe V, imagPart_coe V]
    with x hx hix hr hi hrx hix'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hix
  rw [hx, hix, hr, hi, hrx, hix']
  rw [mul_comm Complex.I]
  exact Complex.re_add_im (V x)

def complexShift (h : ℤ) : ComplexHaarL2 →ₗᵢ[ℂ] ComplexHaarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (translate h) (translate_measurePreserving h)

theorem complexShift_coe (h : ℤ) (V : ComplexHaarL2) :
    (fun x => complexShift h V x) =ᵐ[phaseHaar] (fun x => V (translate h x)) :=
  Lp.coeFn_compMeasurePreserving V (translate_measurePreserving h)

theorem complexLift_shift (h : ℤ) (V : HaarL2) :
    complexLift (shift h V)=complexShift h (complexLift V) := by
  apply Lp.ext
  have ht := (translate_measurePreserving h).quasiMeasurePreserving.ae (complexLift_coe V)
  filter_upwards [complexLift_coe (shift h V), shift_coe h V,
    complexShift_coe h (complexLift V), ht] with x hx hxr hxs hxt
  rw [hx, hxr, hxs, hxt]

def complexCyclicSpace : Submodule ℂ ComplexHaarL2 :=
  (Submodule.span ℂ (Set.range (fun h : ℤ => complexShift h (complexLift incrementVector)))).topologicalClosure

def complexOne : ComplexHaarL2 := ContinuousMap.toLp 2 phaseHaar ℂ (1 : C(Phase,ℂ))

theorem complex_mean_inner (V : ComplexHaarL2) :
    inner ℂ complexOne V=∫ x, V x ∂phaseHaar := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have ho : (fun x => complexOne x)=ᵐ[phaseHaar] (fun _ => (1 : ℂ)) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) phaseHaar (1 : C(Phase,ℂ))
  filter_upwards [ho] with x hx
  rw [hx]
  simp

def complexMeanZeroSpace : Submodule ℂ ComplexHaarL2 := (innerSL ℂ complexOne).ker

theorem mem_complexMeanZeroSpace (V : ComplexHaarL2) :
    V ∈ complexMeanZeroSpace ↔ (∫ x, V x ∂phaseHaar)=0 := by
  change inner ℂ complexOne V=0 ↔ _
  rw [complex_mean_inner]

theorem complexCyclicSpace_mean_zero : complexCyclicSpace ≤ complexMeanZeroSpace := by
  apply Submodule.topologicalClosure_minimal _ _ (innerSL ℂ complexOne).isClosed_ker
  apply Submodule.span_le.mpr
  rintro _ ⟨h,rfl⟩
  change complexShift h (complexLift incrementVector) ∈ complexMeanZeroSpace
  rw [mem_complexMeanZeroSpace, ← complexLift_shift,
    integral_congr_ae (complexLift_coe (shift h incrementVector)), integral_complex_ofReal,
    ← mean_inner_eq_integral, shift_mean_inner, incrementVector_mean_inner, Complex.ofReal_zero]

theorem complexLift_mem_cyclic {V : HaarL2} (hV : V ∈ cyclicSpace incrementVector) :
    complexLift V ∈ complexCyclicSpace := by
  let T := (complexCyclicSpace.restrictScalars ℝ).comap complexLift.toLinearMap
  have hs : Submodule.span ℝ (Set.range (fun h : ℤ => shift h incrementVector)) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h,rfl⟩
    change complexLift (shift h incrementVector) ∈ complexCyclicSpace
    rw [complexLift_shift]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self h))
  have hc : IsClosed (T : Set HaarL2) :=
    (Submodule.isClosed_topologicalClosure _).preimage complexLift.continuous
  exact Submodule.topologicalClosure_minimal _ hs hc hV

theorem complexCyclicSpace_eq_meanZeroSpace : complexCyclicSpace=complexMeanZeroSpace := by
  apply le_antisymm complexCyclicSpace_mean_zero
  intro V hV
  have hmean := (mem_complexMeanZeroSpace V).mp hV
  have hint : Integrable V phaseHaar := (Lp.memLp V).integrable (by norm_num)
  have hR : (∫ x, realPart V x ∂phaseHaar)=0 := by
    rw [integral_congr_ae (realPart_coe V)]
    have he := integral_re hint
    change (∫ x, (V x).re ∂phaseHaar)=(∫ x, V x ∂phaseHaar).re at he
    rw [he, hmean]
    rfl
  have hI : (∫ x, imagPart V x ∂phaseHaar)=0 := by
    rw [integral_congr_ae (imagPart_coe V)]
    have he := integral_im hint
    change (∫ x, (V x).im ∂phaseHaar)=(∫ x, V x ∂phaseHaar).im at he
    rw [he, hmean]
    rfl
  have hr := complexLift_mem_cyclic ((literal_increment_cyclic_span _).mpr hR)
  have hi := complexLift_mem_cyclic ((literal_increment_cyclic_span _).mpr hI)
  have hsum := complexCyclicSpace.add_mem hr (complexCyclicSpace.smul_mem Complex.I hi)
  rwa [complex_parts] at hsum

theorem literal_complex_increment_cyclic_span (V : ComplexHaarL2) :
    V ∈ complexCyclicSpace ↔ (∫ x, V x ∂phaseHaar)=0 := by
  rw [complexCyclicSpace_eq_meanZeroSpace, mem_complexMeanZeroSpace]

end NField.Alignment.CollisionComplexCyclicity
