/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionActivationArithmetic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-!
# Finite CRT coordinates for divisor activation

The actual cutoff factors through a complete finite residue quotient.
Changing one prime-power coordinate preserves every cutoff modulus prime
to that prime. The representative is an actual integer phase.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionActivationCRT

open scoped BigOperators Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionResidueIndependence
open CollisionJointCRT CollisionActivationArithmetic

variable {ι : Type*} [Fintype ι]

def representative (k : ι → ℕ) (hc : Pairwise (fun i j => (k i).Coprime (k j)))
    (r : ∀ i, Multiplicative (ZMod (k i))) : ℕ :=
  ((ZMod.prodEquivPi k hc).symm (fun i => (r i).toAdd)).val

def representativePhase (k : ι → ℕ) (hc : Pairwise (fun i j => (k i).Coprime (k j)))
    (r : ∀ i, Multiplicative (ZMod (k i))) : Phase :=
  integerPhase (representative k hc r : ℤ)

theorem representative_coordinate (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j)))
    (r : ∀ i, Multiplicative (ZMod (k i))) (i : ι) :
    (residueHom (k i) (representativePhase k hc r)).toAdd=(r i).toAdd := by
  letI : NeZero (∏ i, k i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (k i))⟩
  rw [representativePhase,residue_integer]
  have he := congrFun ((ZMod.prodEquivPi k hc).apply_symm_apply (fun i => (r i).toAdd)) i
  rw [ZMod.prodEquivPi_apply,ZMod.castHom_apply,ZMod.cast_eq_val] at he
  simpa only [representative,Int.cast_natCast] using he

theorem coordinates_determine_product (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (x y : Phase)
    (hxy : ∀ i, (residueHom (k i) x).toAdd=(residueHom (k i) y).toAdd) :
    letI : NeZero (∏ i, k i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (k i))⟩
    (residueHom (∏ i, k i) x).toAdd=(residueHom (∏ i, k i) y).toAdd := by
  letI : NeZero (∏ i, k i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (k i))⟩
  apply (ZMod.prodEquivPi k hc).injective
  funext i
  rw [ZMod.prodEquivPi_apply,ZMod.prodEquivPi_apply,
    ← residue_compatible (Finset.dvd_prod_of_mem k (Finset.mem_univ i)),
    ← residue_compatible (Finset.dvd_prod_of_mem k (Finset.mem_univ i))]
  exact hxy i

theorem representative_residue (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) {d : ℕ} [NeZero d]
    (hd : d∣∏ i, k i) (x : Phase) :
    (residueHom d (representativePhase k hc (residueTuple k x))).toAdd=(residueHom d x).toAdd := by
  letI : NeZero (∏ i, k i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (k i))⟩
  have ht := coordinates_determine_product k hc (representativePhase k hc (residueTuple k x)) x
    (fun i => representative_coordinate k hc _ i)
  rw [residue_compatible hd,ht,← residue_compatible hd]

theorem forcingCutoff_factors (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (h M : ℕ)
    (hM : ∀ d, 0<d → d≤M → d∣∏ i, k i) (x : Phase) :
    forcingCutoff h M (representativePhase k hc (residueTuple k x))=forcingCutoff h M x := by
  unfold forcingCutoff forcingTermBlock
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd0 : d=0
  · simp [hd0]
  · letI : NeZero d := ⟨hd0⟩
    exact resetTerm_eq_of_residue (representative_residue k hc
      (hM d (Nat.pos_of_ne_zero hd0) (by have := Finset.mem_range.mp hd; omega)) x) j.val

theorem representative_modEq (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j)))
    (r s : ∀ i, Multiplicative (ZMod (k i))) (i : ι) (he : r i=s i) :
    Nat.ModEq (k i) (representative k hc r) (representative k hc s) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have ht := (representative_coordinate k hc r i).trans
    ((congrArg Multiplicative.toAdd he).trans (representative_coordinate k hc s i).symm)
  simpa only [representativePhase,residue_integer,Int.cast_natCast] using ht

theorem representative_agrees_away (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (i : ι) {p e M : ℕ}
    (hp : p.Prime) (hki : k i=p^e) (hM : ∀ d, 0<d → d≤M → d∣∏ j, k j)
    (r s : ∀ j, Multiplicative (ZMod (k j))) (he : ∀ j, j≠i → r j=s j) :
    agreesAwayBelow p M (representativePhase k hc r) (representativePhase k hc s) := by
  intro d hdM hd0 hdP
  letI : NeZero d := ⟨hd0.ne'⟩
  have hdc : d.Coprime (k i) := by
    rw [hki]
    exact ((hp.coprime_iff_not_dvd.mpr hdP).symm).pow_right e
  have hprod : d∣∏ j∈Finset.univ.erase i, k j := by
    apply hdc.dvd_of_dvd_mul_left
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact hM d hd0 hdM
  have hm := modEq_finset_lcm (Finset.univ.erase i) k
    (fun j hj => representative_modEq k hc r s j (he j (Finset.ne_of_mem_erase hj)))
  rw [Finset.lcm_eq_prod (fun j _ l _ hjl => hc hjl)] at hm
  have hd := hm.of_dvd hprod
  rw [representativePhase,representativePhase,residue_integer,residue_integer]
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hd


theorem residueTuple_integral (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j)))
    (F : (∀ i, Multiplicative (ZMod (k i))) → ℝ) :
    (∫ x, F (residueTuple k x) ∂phaseHaar)=
      (∑ r, F r)/(Fintype.card (∀ i, Multiplicative (ZMod (k i))) : ℝ) := by
  have hm : MeasurePreserving (residueTuple k) phaseHaar
      (probabilityHaar (∀ i, Multiplicative (ZMod (k i)))) :=
    (residueTuple k).toMonoidHom.measurePreserving (residueTuple k).continuous_toFun
      (residueTuple_surjective k hc) (by simp)
  have hi := integral_map_of_stronglyMeasurable (μ := phaseHaar) hm.measurable
    (f := F) continuous_of_discreteTopology.stronglyMeasurable
  rw [hm.map_eq] at hi
  exact hi.symm.trans (finite_haar_integral F)

theorem forcingCutoff_crt_integral (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (h M : ℕ)
    (hM : ∀ d, 0<d → d≤M → d∣∏ i, k i) (G : ℝ → ℝ) :
    (∫ x, G (forcingCutoff h M x) ∂phaseHaar)=
      (∑ r, G (forcingCutoff h M (representativePhase k hc r)))/
        (Fintype.card (∀ i, Multiplicative (ZMod (k i))) : ℝ) := by
  calc
    _ = ∫ x, G (forcingCutoff h M (representativePhase k hc (residueTuple k x))) ∂phaseHaar :=
      integral_congr_ae (Filter.Eventually.of_forall
        (fun x => congrArg G (forcingCutoff_factors k hc h M hM x).symm))
    _ = _ := residueTuple_integral k hc (fun r => G (forcingCutoff h M (representativePhase k hc r)))

theorem forcingCutoff_continuous_via_crt (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (h M : ℕ)
    (hM : ∀ d, 0<d → d≤M → d∣∏ i, k i) : Continuous (forcingCutoff h M) := by
  have ht : Continuous (fun x => forcingCutoff h M (representativePhase k hc (residueTuple k x))) :=
    (continuous_of_discreteTopology (f := fun r : ∀ i, Multiplicative (ZMod (k i)) =>
      forcingCutoff h M (representativePhase k hc r))).comp (residueTuple k).continuous_toFun
  simpa only [forcingCutoff_factors k hc h M hM] using ht

theorem forcingCutoff_crt_probability (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (h M : ℕ)
    (hM : ∀ d, 0<d → d≤M → d∣∏ i, k i) (u v : ℝ) :
    phaseHaar.real {x | forcingCutoff h M x∈Set.Icc u v}=
      (∑ r, if forcingCutoff h M (representativePhase k hc r)∈Set.Icc u v then (1 : ℝ) else 0)/
        (Fintype.card (∀ i, Multiplicative (ZMod (k i))) : ℝ) := by
  have hm : MeasurableSet {x | forcingCutoff h M x∈Set.Icc u v} :=
    measurableSet_Icc.preimage (forcingCutoff_continuous_via_crt k hc h M hM).measurable
  rw [← integral_indicator_one hm]
  simpa only [Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] using
    forcingCutoff_crt_integral k hc h M hM (fun y => if y∈Set.Icc u v then 1 else 0)

end NField.Alignment.CollisionActivationCRT
