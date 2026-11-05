/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteFamilyFourier
import NField.Alignment.FiniteFamilyProbability

/-! # Finite-family transversality on the actual joint unit group -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FiniteFamilyCRT
open scoped BigOperators ComplexConjugate Classical
open CollisionCharacterStructure CenteredCollisionSum DoubleTransversality
open FiniteFamilyTransversality FiniteFamilyEnergy FiniteFamilyFourier
open FiniteFamilyProbability MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : Pairwise fun i j => Nat.Coprime (m i) (m j))

def crtLift (f : ∀ i, UnitClass (m i) → ℂ) (i : ι) (a : UnitClass (∏ i, m i)) : ℂ :=
  f i (unitPiEquiv m hm a i)

variable [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]

theorem crt_sum_zero (f : ∀ i, UnitClass (m i) → ℂ)
    (hf : ∀ i, ∑ a, f i a = 0) (i : ι) : ∑ a, crtLift m hm f i a = 0 := by
  unfold crtLift
  calc
    _ = ∑ x : ∀ j, UnitClass (m j), f i (x i) :=
      Equiv.sum_comp (unitPiEquiv m hm).toEquiv (fun x => f i (x i))
    _ = 0 := coordinate_sum_zero (α := fun j => UnitClass (m j)) i (f i) (hf i)

theorem crt_orthogonal (f : ∀ i, UnitClass (m i) → ℂ)
    (hf : ∀ i, ∑ a, f i a = 0) {i j : ι} (hij : i ≠ j) :
    finiteInner (crtLift m hm f i) (crtLift m hm f j) = 0 :=
  (finiteInner_equiv (unitPiEquiv m hm).toEquiv
    (fun x => f i (x i)) (fun x => f j (x j))).trans
    (coordinate_orthogonal (α := fun j => UnitClass (m j)) hij (f i) (f j) (hf i) (hf j))

theorem crt_energy (f : ∀ i, UnitClass (m i) → ℂ) (i : ι) :
    finiteEnergy (crtLift m hm f i) = finiteEnergy (f i) :=
  (finiteEnergy_equiv (unitPiEquiv m hm).toEquiv
    (fun x => f i (x i))).trans (coordinate_energy (α := fun j => UnitClass (m j)) i (f i))

theorem crt_weighted_energy (f : ∀ i, UnitClass (m i) → ℂ)
    (hf : ∀ i, ∑ a, f i a = 0) (w : ι → ℂ) :
    finiteEnergy (fun a => ∑ i, w i * crtLift m hm f i a) =
      ∑ i, (w i * star (w i)) * finiteEnergy (f i) :=
  (finiteEnergy_equiv (unitPiEquiv m hm).toEquiv
    (fun x => ∑ i, w i * f i (x i))).trans (coordinate_weighted_energy f hf w)

omit [∀ i, NeZero (m i)] [NeZero (∏ i, m i)] in
theorem crt_character_factorization (χ : UnitClass (∏ i, m i) →* ℂ) :
    ∃! ψ : ∀ i, UnitClass (m i) →* ℂ,
      ∀ a, χ a = ∏ i, ψ i (unitPiEquiv m hm a i) := by
  let e := unitPiEquiv m hm
  obtain ⟨ψ, hψ, huniq⟩ := character_factorization (χ.comp e.symm.toMonoidHom)
  refine ⟨ψ, ?_, ?_⟩
  · intro a
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      using hψ (e a)
  · intro φ hφ
    apply huniq φ
    intro x
    have hh := hφ (e.symm x)
    change χ (e.symm x) = ∏ i, φ i (e (e.symm x) i) at hh
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      using hh

theorem crt_coefficient (f : ∀ i, UnitClass (m i) → ℂ) (i : ι)
    (χ : ∀ i, UnitClass (m i) →* ℂ) :
    finiteCoefficient (crtLift m hm f i) (fun a => ∏ j, χ j (unitPiEquiv m hm a j)) =
      finiteCoefficient (f i) (χ i) *
        ∏ j : {j // j ≠ i}, finiteMean (fun a => star (χ j a)) :=
  (finiteInner_equiv (unitPiEquiv m hm).toEquiv
    (fun x => f i (x i)) (fun x => ∏ j, χ j (x j))).trans
    (coordinate_coefficient (α := fun j => UnitClass (m j)) i (f i) (fun j => χ j))

theorem crt_disjoint_support (f : ∀ i, UnitClass (m i) → ℂ)
    (hf : ∀ i, ∑ a, f i a = 0) {i j : ι} (hij : i ≠ j)
    (χ : ∀ i, UnitClass (m i) →* ℂ) :
    finiteCoefficient (crtLift m hm f i) (fun a => ∏ k, χ k (unitPiEquiv m hm a k)) = 0 ∨
      finiteCoefficient (crtLift m hm f j) (fun a => ∏ k, χ k (unitPiEquiv m hm a k)) = 0 := by
  obtain h | h := disjoint_coordinate_support hij (f i) (f j) (hf i) χ
  · exact Or.inl ((finiteInner_equiv (unitPiEquiv m hm).toEquiv
      (fun x => f i (x i)) (fun x => ∏ k, χ k (x k))).trans h)
  · exact Or.inr ((finiteInner_equiv (unitPiEquiv m hm).toEquiv
      (fun x => f j (x j)) (fun x => ∏ k, χ k (x k))).trans h)

omit [NeZero (∏ i, m i)] in
theorem crt_recover_coordinate (f : ∀ i, UnitClass (m i) → ℂ)
    (hf : ∀ i, ∑ a, f i a = 0) (w : ι → ℂ) (i : ι) (a : UnitClass (m i)) :
    finiteMean (fun y : ∀ j : {j // j ≠ i}, UnitClass (m j) =>
      ∑ j, w j * crtLift m hm f j ((unitPiEquiv m hm).symm
        ((Equiv.piSplitAt i (fun j => UnitClass (m j))).symm (a, y)))) = w i * f i a := by
  simp only [crtLift, MulEquiv.apply_symm_apply]
  exact recover_coordinate f hf w i a

/- Uniform counting uses the discrete sigma algebra on each finite unit group. -/
local instance unitMeasurableSpace (n : ℕ) : MeasurableSpace (UnitClass n) := ⊤
local instance unitMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (UnitClass n) :=
  ⟨fun _ => trivial⟩

theorem crt_uniform_coordinates :
    (uniformMeasure (UnitClass (∏ i, m i))).map (unitPiEquiv m hm) =
      Measure.pi (fun i => uniformMeasure (UnitClass (m i))) :=
  (uniformMeasure_map_equiv (unitPiEquiv m hm).toEquiv).trans uniformMeasure_pi

theorem crt_independent_signals (f : ∀ i, UnitClass (m i) → ℂ) :
    iIndepFun (crtLift m hm f) (uniformMeasure (UnitClass (∏ i, m i))) :=
  independent_signals_equiv (unitPiEquiv m hm).toEquiv f

end NField.Alignment.FiniteFamilyCRT
