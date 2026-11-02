/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRemainderCovariance
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Instances.ZMod

/-!
# Haar remainder coordinates on the profinite completion of the integers

The compact phase group is the actual inverse limit of finite quotients of
the integer group. Haar probability and the finite residue projections are
constructed, rather than assumed as covariance hypotheses.
-/

noncomputable section

open CategoryTheory MeasureTheory Measure TopologicalSpace
open scoped BigOperators
open ProfiniteGrp

namespace NField.Alignment.ProfiniteRemainderMeasure

def probabilityHaar (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure G :=
  haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)

instance probabilityHaar_isHaar (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    (probabilityHaar G).IsHaarMeasure := by
  unfold probabilityHaar
  infer_instance

instance probabilityHaar_isProbability (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsProbabilityMeasure (probabilityHaar G) where
  measure_univ := haarMeasure_self

def phaseGroup : ProfiniteGrp := ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

abbrev Phase : Type := phaseGroup

instance phaseCommGroup : CommGroup Phase := {
  (inferInstance : Group Phase) with
  mul_comm := by
    intro x y
    apply Subtype.ext
    funext H
    change (x.val H : (Multiplicative ℤ) ⧸ H.toSubgroup) * y.val H =
      y.val H * x.val H
    exact mul_comm (G := (Multiplicative ℤ) ⧸ H.toSubgroup) (x.val H) (y.val H) }

instance phaseMeasurableSpace : MeasurableSpace Phase := borel Phase
instance phaseBorelSpace : BorelSpace Phase := ⟨rfl⟩

instance cyclicMeasurableSpace (n : ℕ) : MeasurableSpace (Multiplicative (ZMod n)) :=
  borel (Multiplicative (ZMod n))
instance cyclicBorelSpace (n : ℕ) : BorelSpace (Multiplicative (ZMod n)) := ⟨rfl⟩

def phaseHaar : Measure Phase := probabilityHaar Phase

instance : phaseHaar.IsHaarMeasure := probabilityHaar_isHaar Phase
instance : IsProbabilityMeasure phaseHaar := probabilityHaar_isProbability Phase

def integerPhase (z : ℤ) : Phase :=
  ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ)) (Multiplicative.ofAdd z)

def residueMorphism (n : ℕ) [NeZero n] :
    phaseGroup ⟶ ProfiniteGrp.of (Multiplicative (ZMod n)) := by
  let f : Multiplicative ℤ →* Multiplicative (ZMod n) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))
  exact ProfiniteCompletion.lift (GrpCat.ofHom f)

def residueHom (n : ℕ) [NeZero n] : Phase →ₜ* Multiplicative (ZMod n) :=
  (residueMorphism n).hom

theorem residue_integer (n : ℕ) [NeZero n] (z : ℤ) :
    (residueHom n (integerPhase z)).toAdd = (z : ZMod n) := by
  let f : Multiplicative ℤ →* Multiplicative (ZMod n) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))
  have he := ProfiniteCompletion.lift_eta
    (G := GrpCat.of (Multiplicative ℤ))
    (P := ProfiniteGrp.of (Multiplicative (ZMod n))) (GrpCat.ofHom f)
  have hf := congrArg (fun h => h (Multiplicative.ofAdd z)) he
  exact congrArg Multiplicative.toAdd hf

theorem residue_surjective (n : ℕ) [NeZero n] : Function.Surjective (residueHom n) := by
  intro a
  refine ⟨integerPhase (a.toAdd.val : ℤ), ?_⟩
  have he := residue_integer n (a.toAdd.val : ℤ)
  simpa using congrArg Multiplicative.ofAdd he

theorem finite_haar_integral {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Fintype G] [MeasurableSingletonClass G] (f : G → ℝ) :
    (∫ x, f x ∂probabilityHaar G) = (∑ x, f x) / Fintype.card G := by
  have hc (x : G) : (probabilityHaar G).real {x} = (probabilityHaar G).real {1} := by
    exact congrArg ENNReal.toReal (haar_singleton (probabilityHaar G) x)
  have hnorm := integral_fintype (μ := probabilityHaar G)
    (f := fun _ : G => (1 : ℝ)) Integrable.of_finite
  simp only [integral_const, probReal_univ, hc,
    smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hnorm
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  rw [integral_fintype (Integrable.of_finite : Integrable f (probabilityHaar G))]
  simp only [hc, smul_eq_mul, ← Finset.mul_sum]
  field_simp
  calc
    _ = ((Fintype.card G : ℝ) * (probabilityHaar G).real {1}) * ∑ x, f x := by ring
    _ = _ := by rw [← hnorm, one_mul]

theorem residue_measurePreserving (n : ℕ) [NeZero n] :
    MeasurePreserving (residueHom n) phaseHaar
      (probabilityHaar (Multiplicative (ZMod n))) := by
  exact (residueHom n).toMonoidHom.measurePreserving
    (residueHom n).continuous_toFun (residue_surjective n) (by simp)

theorem val_finEquiv (n : ℕ) [NeZero n] (j : Fin n) :
    ((ZMod.finEquiv n) j).val = j.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem sum_zmod_val (n : ℕ) [NeZero n] (F : ℕ → ℝ) :
    (∑ j : ZMod n, F j.val) = ∑ j ∈ Finset.range n, F j := by
  have h := Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun j => F j.val)
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, val_finEquiv] at h
  exact h.symm.trans (Fin.sum_univ_eq_sum_range F n)

/-- Every finite residue projection of Haar probability is uniform. -/
theorem integral_residue (n : ℕ) [NeZero n] (F : ℕ → ℝ) :
    (∫ x, F (residueHom n x).toAdd.val ∂phaseHaar) =
      (∑ j ∈ Finset.range n, F j) / (n : ℝ) := by
  have hm := residue_measurePreserving n
  have hi := integral_map_of_stronglyMeasurable (μ := phaseHaar) hm.measurable
    (f := fun r : Multiplicative (ZMod n) => F r.toAdd.val)
    (continuous_of_discreteTopology.stronglyMeasurable)
  rw [hm.map_eq] at hi
  rw [← hi, finite_haar_integral]
  have hc : Fintype.card (Multiplicative (ZMod n)) = n := by simp
  rw [hc]
  have hs := Equiv.sum_comp (@Multiplicative.toAdd (ZMod n)) (fun j => F j.val)
  rw [hs, sum_zmod_val]

/-- Compatibility of the finite coordinates follows from density of the
ordinary integer image and equality of the two reductions there. -/
theorem residue_compatible {k m : ℕ} [NeZero k] [NeZero m] (hkm : k ∣ m)
    (x : Phase) :
    (residueHom k x).toAdd =
      ZMod.castHom hkm (ZMod k) (residueHom m x).toAdd := by
  have hleft : Continuous (fun x : Phase => (residueHom k x).toAdd) :=
    (continuous_of_discreteTopology).comp (residueHom k).continuous_toFun
  have hright : Continuous (fun x : Phase =>
      ZMod.castHom hkm (ZMod k) (residueHom m x).toAdd) :=
    (continuous_of_discreteTopology).comp (residueHom m).continuous_toFun
  have he := (ProfiniteCompletion.denseRange (GrpCat.of (Multiplicative ℤ))).equalizer
    hleft hright
  apply congrFun (he ?_) x
  funext z
  change (residueHom k (integerPhase z.toAdd)).toAdd =
    ZMod.castHom hkm (ZMod k) (residueHom m (integerPhase z.toAdd)).toAdd
  rw [residue_integer, residue_integer]
  simp

def centered (k : ℕ) (x : Phase) : ℝ :=
  if hk : 0 < k then
    letI : NeZero k := ⟨hk.ne'⟩
    ((residueHom k x).toAdd.val : ℝ) - ((k : ℝ) - 1) / 2
  else 0

theorem centered_eq (k : ℕ) [NeZero k] (x : Phase) :
    centered k x = ((residueHom k x).toAdd.val : ℝ) - ((k : ℝ) - 1) / 2 := by
  simp [centered, Nat.pos_of_ne_zero (NeZero.ne k)]

theorem centered_integer {k : ℕ} (hk : 0 < k) (n : ℕ) :
    centered k (integerPhase (n : ℤ)) =
      CollisionRemainderDynamics.centeredRemainder k n := by
  letI : NeZero k := ⟨hk.ne'⟩
  rw [centered_eq, residue_integer]
  simp [CollisionRemainderDynamics.centeredRemainder]

theorem centered_via_residue {k m : ℕ} [NeZero k] [NeZero m]
    (hkm : k ∣ m) (x : Phase) :
    centered k x = CollisionRemainderDynamics.centeredRemainder k
      (residueHom m x).toAdd.val := by
  rw [centered_eq, residue_compatible hkm]
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
    CollisionRemainderDynamics.centeredRemainder]

/-- The paper's exact Haar covariance for every positive pair of periods. -/
theorem haar_remainder_covariance {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    (∫ x, centered k x * centered l x ∂phaseHaar) =
      ((k.gcd l : ℝ) ^ 2 - 1) / 12 := by
  letI : NeZero k := ⟨hk.ne'⟩
  letI : NeZero l := ⟨hl.ne'⟩
  letI : NeZero (k.lcm l) := ⟨(Nat.lcm_pos hk hl).ne'⟩
  calc
    _ = ∫ x, CollisionRemainderDynamics.centeredRemainder k
          (residueHom (k.lcm l) x).toAdd.val *
        CollisionRemainderDynamics.centeredRemainder l
          (residueHom (k.lcm l) x).toAdd.val ∂phaseHaar := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [centered_via_residue (Nat.dvd_lcm_left k l),
        centered_via_residue (Nat.dvd_lcm_right k l)]
    _ = (∑ n ∈ Finset.range (k.lcm l),
          CollisionRemainderDynamics.centeredRemainder k n *
          CollisionRemainderDynamics.centeredRemainder l n) / (k.lcm l : ℝ) :=
      integral_residue (k.lcm l) (fun n =>
        CollisionRemainderDynamics.centeredRemainder k n *
          CollisionRemainderDynamics.centeredRemainder l n)
    _ = _ := CollisionRemainderCovariance.remainder_covariance hk hl

theorem haar_centered_mean {k : ℕ} (hk : 0 < k) :
    (∫ x, centered k x ∂phaseHaar) = 0 := by
  letI : NeZero k := ⟨hk.ne'⟩
  have hfun : (fun x => centered k x) =
      (fun x => CollisionRemainderDynamics.centeredRemainder k
        (residueHom k x).toAdd.val) := by
    funext x
    exact centered_via_residue (dvd_refl k) x
  rw [hfun, integral_residue, CollisionRemainderDynamics.centered_cycle_sum hk, zero_div]

theorem haar_centered_variance {k : ℕ} (hk : 0 < k) :
    (∫ x, centered k x ^ 2 ∂phaseHaar) = ((k : ℝ) ^ 2 - 1) / 12 := by
  simpa only [pow_two, Nat.gcd_self] using haar_remainder_covariance hk hk

theorem continuous_centered (k : ℕ) : Continuous (centered k) := by
  by_cases hk : 0 < k
  · letI : NeZero k := ⟨hk.ne'⟩
    have he : centered k = fun x : Phase =>
        ((residueHom k x).toAdd.val : ℝ) - ((k : ℝ) - 1) / 2 := by
      funext x
      exact centered_eq k x
    rw [he]
    exact (continuous_of_discreteTopology : Continuous
      (fun r : Multiplicative (ZMod k) => (r.toAdd.val : ℝ) - ((k : ℝ) - 1) / 2)).comp
      (residueHom k).continuous_toFun
  · have he : centered k = fun _ : Phase => 0 := by
      funext x
      simp [centered, hk]
    rw [he]
    exact continuous_const

end NField.Alignment.ProfiniteRemainderMeasure
