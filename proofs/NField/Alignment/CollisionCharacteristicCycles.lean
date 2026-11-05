/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCharacteristicLaw
import NField.Alignment.CollisionCylinderOne

/-!
# Literal finite-cycle characteristic averages

The period is lcm(1,...,M). Each finite cutoff depends only on that
residue, whose Haar law is proved uniform. Complex integration retains
both components of the actual imaginary exponential.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCharacteristicCycles

open scoped Classical ENNReal
open MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionOdometerRecurrence CollisionCylinderOne CollisionCharacteristicLaw

theorem finite_haar_complex_integral {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Fintype G] [MeasurableSingletonClass G] (f : G → ℂ) :
    (∫ x, f x ∂probabilityHaar G)=(∑ x, f x)/(Fintype.card G : ℂ) := by
  apply Complex.ext
  · have hr : (∫ x, (f x).re ∂probabilityHaar G)=(∫ x, f x ∂probabilityHaar G).re :=
      integral_re (Integrable.of_finite : Integrable f (probabilityHaar G))
    rw [← hr,finite_haar_integral]
    simp
  · have hi : (∫ x, (f x).im ∂probabilityHaar G)=(∫ x, f x ∂probabilityHaar G).im :=
      integral_im (Integrable.of_finite : Integrable f (probabilityHaar G))
    rw [← hi,finite_haar_integral]
    simp

theorem sum_zmod_val_complex (n : ℕ) [NeZero n] (F : ℕ → ℂ) :
    (∑ j : ZMod n, F j.val)=∑ j ∈ Finset.range n, F j := by
  have h := Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun j => F j.val)
  simp only [RingEquiv.toEquiv_eq_coe,EquivLike.coe_coe,val_finEquiv] at h
  exact h.symm.trans (Fin.sum_univ_eq_sum_range F n)

theorem integral_residue_complex (n : ℕ) [NeZero n] (F : ℕ → ℂ) :
    (∫ x, F (residueHom n x).toAdd.val ∂phaseHaar)=
      (∑ j ∈ Finset.range n, F j)/(n : ℂ) := by
  have hm := residue_measurePreserving n
  have hi := integral_map_of_stronglyMeasurable (μ := phaseHaar) hm.measurable
    (f := fun r : Multiplicative (ZMod n) => F r.toAdd.val)
    continuous_of_discreteTopology.stronglyMeasurable
  rw [hm.map_eq] at hi
  rw [← hi,finite_haar_complex_integral]
  have hc : Fintype.card (Multiplicative (ZMod n))=n := by simp
  rw [hc]
  have hs := Equiv.sum_comp (@Multiplicative.toAdd (ZMod n)) (fun j => F j.val)
  rw [hs,sum_zmod_val_complex]

theorem potentialMap_via_cutoff_residue (v : ℕ → ℝ) (M : ℕ)
    [NeZero (cutoffPeriod M)] (x : Phase) :
    potentialMap v M x=finiteAge v M (residueHom (cutoffPeriod M) x).toAdd.val := by
  simp only [potentialMap,ContinuousMap.smul_apply,ContinuousMap.sum_apply,
    remainderMap,ContinuousMap.coe_mk,smul_eq_mul,finiteAge]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  letI : NeZero k := ⟨by omega⟩
  rw [centered_via_residue (dvd_cutoffPeriod (by omega) hk'.2)]

def cutoffCharacteristic (M : ℕ) (t : ℝ) : ℂ :=
  (1/(cutoffPeriod M : ℂ))*∑ a ∈ Finset.range (cutoffPeriod M),
    Complex.exp (((t*finiteAge collisionWeight M a : ℝ) : ℂ)*Complex.I)

theorem cutoffCharacteristic_integral (M : ℕ) (t : ℝ) :
    cutoffCharacteristic M t=
      ∫ x, Complex.exp (((t*potentialMap collisionWeight M x : ℝ) : ℂ)*Complex.I) ∂phaseHaar := by
  letI : NeZero (cutoffPeriod M) := ⟨(cutoffPeriod_pos M).ne'⟩
  have he (x : Phase) := potentialMap_via_cutoff_residue collisionWeight M x
  simp_rw [he]
  rw [integral_residue_complex (cutoffPeriod M)
    (fun a => Complex.exp (((t*finiteAge collisionWeight M a : ℝ) : ℂ)*Complex.I))]
  unfold cutoffCharacteristic
  ring

end NField.Alignment.CollisionCharacteristicCycles
