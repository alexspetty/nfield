/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionJointCRT
import NField.Alignment.CollisionBoundaryTesting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The full joint Haar moment expansion

Finite generalized-CRT probabilities are summed only after the positive
series and the integrability of the full product have been justified.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionJointMoments

open scoped BigOperators Classical ENNReal
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionResetIntegrability CollisionPotentialCoboundary CollisionBoundaryTesting
open CollisionJointCRT ProfinitePeriodicTesting

theorem hasSum_nonneg_fin_product (r : ℕ) (f : Fin r → ℕ → ℝ) (v : Fin r → ℝ)
    (hn : ∀ i k, 0≤f i k) (hs : ∀ i, HasSum (f i) (v i)) :
    HasSum (fun k : Fin r → ℕ => ∏ i, f i (k i)) (∏ i, v i) := by
  induction r with
  | zero =>
    letI : Fintype (Fin 0 → ℕ) := Fintype.ofFinite _
    simp
  | succ r ih =>
    have ht := ih (fun i => f i.succ) (fun i => v i.succ)
      (fun i k => hn i.succ k) (fun i => hs i.succ)
    have hnn : ∀ k : Fin r → ℕ, 0≤∏ i : Fin r, f i.succ (k i) :=
      fun k => Finset.prod_nonneg (fun i _ => hn i.succ (k i))
    have hsum := (hs 0).summable.mul_of_nonneg ht.summable (hn 0) hnn
    have hm := (hs 0).mul ht hsum
    apply (Fin.consEquiv (fun _ : Fin (r+1) => ℕ)).hasSum_iff.mp
    convert! hm using 1
    · funext p
      simp [Fin.prod_univ_succ, Fin.consEquiv]
    · exact Fin.prod_univ_succ v

theorem resetTerm_summable_ae :
    ∀ᵐ x ∂phaseHaar, Summable (fun k => resetTerm k x) := by
  have he : (∑' k, ‖resetVector 1 k‖ₑ)≠∞ := by
    simpa only [ofReal_norm] using
      (resetVector_norm_summable 1 le_rfl (by norm_num)).tsum_ofReal_ne_top
  have hs := Lp.hasSum_coeFn_tsum (f := resetVector 1) he
  filter_upwards [hs, ae_all_iff.mpr (resetVector_coe 1)] with x hx hc
  exact hx.summable.congr (fun k => hc k)

theorem resetTerm_from_two_hasSum_ae :
    ∀ᵐ x ∂phaseHaar, HasSum (fun k : ℕ => resetTerm (k+2) x) (resetFunction x) := by
  filter_upwards [resetTerm_summable_ae] with x hx
  have ht := hx.comp_injective (fun _ _ h => Nat.add_right_cancel h :
    Function.Injective (fun k : ℕ => k+2))
  have he := hx.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, resetTerm_zero,
    resetTerm_one, Pi.zero_apply, zero_add] at he
  rw [show resetFunction x=∑' k, resetTerm (k+2) x from he.symm]
  exact ht.hasSum

theorem reset_joint_integrable (r : ℕ) (h : Fin r → ℕ) :
    Integrable (fun x => ∏ i, resetFunction
      (CollisionPotentialCoboundary.translate (h i : ℤ) x)) phaseHaar := by
  by_cases hr : r=0
  · subst r
    simp
  have hp : (1 : ℝ≥0∞)≤r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hm := MemLp.prod' (s := Finset.univ) (p := fun _ : Fin r => (r : ℝ≥0∞))
    (fun i _ => (resetFunction_memLp r hp (by simp)).comp_measurePreserving
      (translate_measurePreserving (h i : ℤ)))
  have hexp : (∑ _i : Fin r, (r : ℝ≥0∞)⁻¹)⁻¹=1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by exact_mod_cast hr) (by simp), inv_one]
  rw [hexp] at hm
  exact memLp_one_iff_integrable.mp hm

def jointResetTerm (r : ℕ) (h : Fin r → ℕ) (k : Fin r → ℕ) (x : Phase) : ℝ :=
  ∏ i, resetTerm (k i+2) (CollisionPotentialCoboundary.translate (h i : ℤ) x)

theorem jointResetTerm_nonneg (r : ℕ) (h k : Fin r → ℕ) (x : Phase) :
    0≤jointResetTerm r h k x := Finset.prod_nonneg (fun _ _ => resetTerm_nonneg _ _)

theorem jointResetTerm_continuous (r : ℕ) (h k : Fin r → ℕ) :
    Continuous (jointResetTerm r h k) := by
  apply continuous_finsetProd
  intro i _
  exact (resetTerm_locallyConstant (k i+2)).continuous.comp
    (continuous_const.mul continuous_id)

theorem shifted_resetTerm_from_two_hasSum_ae (z : ℤ) :
    ∀ᵐ x ∂phaseHaar, HasSum (fun k : ℕ => resetTerm (k+2)
      (CollisionPotentialCoboundary.translate z x))
      (resetFunction (CollisionPotentialCoboundary.translate z x)) := by
  have hs := (translate_measurePreserving z).quasiMeasurePreserving.ae
    (p := fun x => HasSum (fun k : ℕ => resetTerm (k+2) x) (resetFunction x))
    resetTerm_from_two_hasSum_ae
  convert! hs using 1

theorem jointResetTerm_hasSum_ae (r : ℕ) (h : Fin r → ℕ) :
    ∀ᵐ x ∂phaseHaar, HasSum (fun k => jointResetTerm r h k x)
      (∏ i, resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x)) := by
  have hs : ∀ i : Fin r, ∀ᵐ x ∂phaseHaar,
      HasSum (fun k : ℕ => resetTerm (k+2)
        (CollisionPotentialCoboundary.translate (h i : ℤ) x))
        (resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x)) :=
    fun i => shifted_resetTerm_from_two_hasSum_ae (h i : ℤ)
  filter_upwards [ae_all_iff.mpr hs] with x hx
  unfold jointResetTerm
  exact hasSum_nonneg_fin_product r
    (fun (i : Fin r) (k : ℕ) => resetTerm (k+2)
      (CollisionPotentialCoboundary.translate (h i : ℤ) x))
    (fun i : Fin r => resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x))
    (fun i k => resetTerm_nonneg (k+2) (CollisionPotentialCoboundary.translate (h i : ℤ) x)) hx

theorem jointResetTerm_integral_hasSum (r : ℕ) (h : Fin r → ℕ) :
    HasSum (fun k : Fin r → ℕ => ∫ x, jointResetTerm r h k x ∂phaseHaar)
      (∫ x, ∏ i, resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar) := by
  have hs := jointResetTerm_hasSum_ae r h
  have hi : Integrable (fun x => ∑' k, jointResetTerm r h k x) phaseHaar := by
    apply (reset_joint_integrable r h).congr
    filter_upwards [hs] with x hx
    exact hx.tsum_eq.symm
  exact hasSum_integral_of_dominated_convergence (jointResetTerm r h)
    (fun k => (jointResetTerm_continuous r h k).aestronglyMeasurable)
    (fun k => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (jointResetTerm_nonneg r h k x)]))
    (hs.mono (fun _ hx => hx.summable)) hi hs

def jointCRTTerm (r : ℕ) (h k : Fin r → ℕ) : ℝ :=
  (∏ i, ((k i+2 : ℕ) : ℝ)*collisionWeight (k i+2))*
    (if ∀ i j : Fin r, ((k i+2).gcd (k j+2) : ℤ) ∣ (h i : ℤ)-(h j : ℤ)
      then 1/((Finset.univ.lcm (fun i : Fin r => k i+2) : ℕ) : ℝ) else 0)

theorem jointCRTTerm_integral (r : ℕ) (h k : Fin r → ℕ) :
    (∫ x, jointResetTerm r h k x ∂phaseHaar)=jointCRTTerm r h k := by
  have he := joint_reset_integral Finset.univ (fun i : Fin r => k i+2) h
    (fun _ _ => by omega)
  simpa only [Finset.mem_univ, forall_true_left, jointResetTerm, jointCRTTerm] using he

theorem joint_moment_CRT_hasSum (r : ℕ) (h : Fin r → ℕ) :
    HasSum (jointCRTTerm r h)
      (∫ x, ∏ i, resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar) := by
  simpa only [jointCRTTerm_integral] using jointResetTerm_integral_hasSum r h

theorem joint_moment_CRT (r : ℕ) (h : Fin r → ℕ) :
    (∫ x, ∏ i, resetFunction (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar) =
      ∑' k : Fin r → ℕ, jointCRTTerm r h k := (joint_moment_CRT_hasSum r h).tsum_eq.symm

end NField.Alignment.CollisionJointMoments
