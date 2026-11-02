/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialConvergence

/-!
# Reflection symmetry of the Haar collision potential

Reflection is an actual measure-preserving map of the profinite group.
The finite pointwise identities pass to the constructed L² limit.
-/

noncomputable section

namespace NField.Alignment.CollisionPotentialReflection

open scoped BigOperators
open Filter MeasureTheory Measure
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence

def reflection (x : Phase) : Phase := integerPhase (-1) / x

theorem reflection_measurePreserving : MeasurePreserving reflection phaseHaar phaseHaar :=
  measurePreserving_div_left phaseHaar (integerPhase (-1))

theorem residue_reflection (k : ℕ) [NeZero k] (x : Phase) :
    (residueHom k (reflection x)).toAdd = -1 - (residueHom k x).toAdd := by
  unfold reflection
  rw [map_div]
  change (residueHom k (integerPhase (-1))).toAdd - (residueHom k x).toAdd = _
  rw [residue_integer]
  simp

theorem centered_reflection (k : ℕ) (x : Phase) : centered k (reflection x) = -centered k x := by
  cases k with
  | zero => simp [centered]
  | succ k =>
      have hv : (residueHom (k + 1) x).toAdd.val ≤ k := by
        have h := ZMod.val_lt (residueHom (k + 1) x).toAdd
        omega
      have hsub : (residueHom (k + 1) x).toAdd.val ≤ (-1 : ZMod (k + 1)).val := by
        simpa only [ZMod.val_neg_one] using hv
      rw [centered_eq, centered_eq, residue_reflection, ZMod.val_sub hsub,
        ZMod.val_neg_one, Nat.cast_sub hv]
      push_cast
      ring

theorem potentialMap_reflection (v : ℕ → ℝ) (M : ℕ) (x : Phase) :
    potentialMap v M (reflection x) = -potentialMap v M x := by
  simp only [potentialMap, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    remainderMap, ContinuousMap.coe_mk, smul_eq_mul, centered_reflection,
    mul_neg, Finset.sum_neg_distrib]

def reflectL2 : HaarL2 →+ HaarL2 := Lp.compMeasurePreserving reflection reflection_measurePreserving

theorem finitePotential_reflection (v : ℕ → ℝ) (M : ℕ) :
    reflectL2 (finitePotential v M) = -finitePotential v M := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving (finitePotential v M) reflection_measurePreserving
  have hfinite := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (potentialMap v M)
  rw [← finitePotential_toLp] at hfinite
  have htranslated := reflection_measurePreserving.quasiMeasurePreserving.ae hfinite
  have hneg := Lp.coeFn_neg (finitePotential v M)
  filter_upwards [hcomp, htranslated, hfinite, hneg] with x hc ht hf hn
  rw [show (reflectL2 (finitePotential v M)) x = finitePotential v M (reflection x) from hc,
    ht, potentialMap_reflection, hn]
  change -(potentialMap v M x) = -(finitePotential v M x)
  rw [hf]

theorem collisionPotential_reflection : reflectL2 collisionPotential = -collisionPotential := by
  have hcont : Continuous reflectL2 :=
    (Lp.isometry_compMeasurePreserving (E := ℝ) (p := 2) reflection_measurePreserving).continuous
  have hleft := hcont.tendsto collisionPotential |>.comp tendsto_collisionPotential
  have hright := tendsto_collisionPotential.neg
  have he : (fun M => reflectL2 (finitePotential collisionWeight M)) =
      (fun M => -finitePotential collisionWeight M) := by
    funext M
    exact finitePotential_reflection collisionWeight M
  change Tendsto (fun M => reflectL2 (finitePotential collisionWeight M)) _ _ at hleft
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem collisionPotential_reflection_ae :
    (fun x => collisionPotential (reflection x)) =ᵐ[phaseHaar] (fun x => -collisionPotential x) := by
  have hc := Lp.coeFn_compMeasurePreserving collisionPotential reflection_measurePreserving
  have hn := Lp.coeFn_neg collisionPotential
  change reflectL2 collisionPotential =ᵐ[phaseHaar] (fun x => collisionPotential (reflection x)) at hc
  rw [collisionPotential_reflection] at hc
  exact hc.symm.trans hn

theorem collisionPotential_law_symmetric :
    Measure.map (fun x => -collisionPotential x) phaseHaar =
      Measure.map collisionPotential phaseHaar := by
  have hY : AEMeasurable collisionPotential (Measure.map reflection phaseHaar) := by
    rw [reflection_measurePreserving.map_eq]
    exact (Lp.aestronglyMeasurable collisionPotential).aemeasurable
  calc
    _ = Measure.map (fun x => collisionPotential (reflection x)) phaseHaar :=
      Measure.map_congr collisionPotential_reflection_ae.symm
    _ = (Measure.map reflection phaseHaar).map collisionPotential :=
      (hY.map_map_of_aemeasurable reflection_measurePreserving.aemeasurable).symm
    _ = _ := by rw [reflection_measurePreserving.map_eq]

end NField.Alignment.CollisionPotentialReflection
