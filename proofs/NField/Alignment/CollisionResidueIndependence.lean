/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionJointCRT
import Mathlib.Probability.Independence.Basic

/-!
# Independence of actual coprime Haar residue coordinates

The joint residue map is surjective by the general CRT. Haar uniqueness
identifies its pushforward with the product probability, so independence
is a proved property of the actual phase space.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionResidueIndependence

open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory ProfiniteRemainderMeasure CollisionJointCRT

variable {ι : Type*} [Fintype ι]

def residueTuple (k : ι → ℕ) [∀ i, NeZero (k i)] :
    Phase →ₜ* (∀ i, Multiplicative (ZMod (k i))) where
  toFun x i := residueHom (k i) x
  map_one' := by ext i; exact map_one (residueHom (k i))
  map_mul' := by intro x y; ext i; exact map_mul (residueHom (k i)) x y
  continuous_toFun := continuous_pi (fun i => (residueHom (k i)).continuous_toFun)

theorem coprime_residues_compatible (k a : ι → ℕ)
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) :
    Compatible Finset.univ k a := by
  intro i _ j _
  by_cases he : i=j
  · subst j
    exact Nat.ModEq.refl _
  · rw [(hc he).gcd_eq_one]
    exact Nat.modEq_one

theorem residueTuple_surjective (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) :
    Function.Surjective (residueTuple k) := by
  intro r
  obtain ⟨n,_,hn⟩ := joint_crt_exists Finset.univ k (fun i => (r i).toAdd.val)
    (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (k i)))
    (coprime_residues_compatible k _ hc)
  refine ⟨integerPhase (n : ℤ),?_⟩
  funext i
  apply Multiplicative.toAdd.injective
  change (residueHom (k i) (integerPhase (n : ℤ))).toAdd=(r i).toAdd
  rw [residue_integer]
  apply ZMod.val_injective
  simpa only [Int.cast_natCast,ZMod.val_natCast,Nat.ModEq,
    Nat.mod_eq_of_lt (ZMod.val_lt (r i).toAdd)] using hn i (Finset.mem_univ i)

theorem residueTuple_measurePreserving (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) :
    MeasurePreserving (residueTuple k) phaseHaar
      (Measure.pi (fun i => probabilityHaar (Multiplicative (ZMod (k i))))) :=
  (residueTuple k).toMonoidHom.measurePreserving (residueTuple k).continuous_toFun
    (residueTuple_surjective k hc) (by simp)

theorem coprime_residue_independence (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) :
    iIndepFun (fun i => residueHom (k i)) phaseHaar := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (residueHom (k i)).continuous_toFun.measurable.aemeasurable)).mpr
  calc
    _ = Measure.pi (fun i => probabilityHaar (Multiplicative (ZMod (k i)))) :=
      (residueTuple_measurePreserving k hc).map_eq
    _ = _ := by
      congr 1
      funext i
      exact (residue_measurePreserving (k i)).map_eq.symm

end NField.Alignment.CollisionResidueIndependence
