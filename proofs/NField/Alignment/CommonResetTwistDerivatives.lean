/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSecondDerivative
import NField.Alignment.CommonResetGridDistances

/-! # Derivative estimates for the actual linear Fourier twists -/

noncomputable section

namespace NField.Alignment.CommonResetTwistDerivatives

open scoped BigOperators
open Set CommonResetDerivativeFirst CommonResetDerivativeSmooth CommonResetDerivativeIntervals
open CommonResetSecondDerivative CommonResetCircleDistance

def linearTwistSum (f : ℝ → ℝ) (a : ℝ) (N u h : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (N+1), phase (f (a+i)+(h : ℝ)/u*(a+i))

theorem strip_of_positive_arc_distance {A B x : ℝ} (hAB : A ≤ B)
    (hd : 0 < arcDistance (-B) (-A) x) :
    ∃ m : ℤ, ∀ y ∈ Icc A B,
      (m : ℝ)+arcDistance (-B) (-A) x ≤ y+x ∧
        y+x ≤ (m : ℝ)+1-arcDistance (-B) (-A) x := by
  let m : ℤ := ⌊A+x⌋
  have hmlo : (m : ℝ) ≤ A+x := Int.floor_le _
  have hmhi : A+x < (m : ℝ)+1 := Int.lt_floor_add_one _
  have hneg : -B ≤ -A := by linarith
  have hcross : B+x < (m : ℝ)+1 := by
    by_contra h
    have hz : arcDistance (-B) (-A) x ≤ 0 := by
      apply (arcDistance_le_iff hneg le_rfl).mpr
      refine ⟨m+1, ?_, ?_⟩ <;> push_cast <;> linarith
    linarith
  have hl : arcDistance (-B) (-A) x ≤ A+x-m := by
    apply (arcDistance_le_iff hneg (by linarith)).mpr
    exact ⟨m, by linarith, by linarith⟩
  have hh : arcDistance (-B) (-A) x ≤ (m : ℝ)+1-(B+x) := by
    apply (arcDistance_le_iff hneg (by linarith)).mpr
    refine ⟨m+1, ?_, ?_⟩ <;> push_cast <;> linarith
  refine ⟨m, ?_⟩
  intro y hy
  constructor <;> linarith [hy.1, hy.2]

set_option backward.isDefEq.respectTransparency false in
/-- Title: `Every Fourier twist away from the derivative arc has the first-derivative bound`. -/
theorem linear_twist_first_bound (f g : ℝ → ℝ) (a : ℝ) (N u h : ℕ)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : MonotoneOn g (Icc a (a+N)))
    (hd : 0 < arcDistance (-g (a+N)) (-g a) ((h : ℝ)/u)) :
    ‖linearTwistSum f a N u h‖ ≤ 2/arcDistance (-g (a+N)) (-g a) ((h : ℝ)/u) := by
  have hAB : g a ≤ g (a+N) := by
    simpa using hg (natural_sample_mem (Nat.zero_le N))
      (natural_sample_mem (le_refl N)) (by simp)
  obtain ⟨m, hm⟩ := strip_of_positive_arc_distance hAB hd
  have hf' : ContinuousOn (fun x : ℝ => f x+(h : ℝ)/u*x) (Icc a (a+N)) :=
    hf.add ((continuous_const.mul continuous_id).continuousOn)
  have hfg' : ∀ x ∈ Ioo a (a+N),
      HasDerivAt (fun x : ℝ => f x+(h : ℝ)/u*x) (g x+(h : ℝ)/u) x := by
    intro x hx
    exact (hfg x hx).fun_add (hasDerivAt_const_mul ((h : ℝ)/u))
  have hg' : MonotoneOn (fun x : ℝ => g x+(h : ℝ)/u) (Icc a (a+N)) := by
    intro x hx y hy hxy
    exact add_le_add (hg hx hy hxy) (le_refl _)
  have hstrip : ∀ x ∈ Ioo a (a+N),
      (m : ℝ)+arcDistance (-g (a+N)) (-g a) ((h : ℝ)/u) ≤ g x+(h : ℝ)/u ∧
        g x+(h : ℝ)/u ≤ (m : ℝ)+1-arcDistance (-g (a+N)) (-g a) ((h : ℝ)/u) := by
    intro x hx
    have hx' : x ∈ Icc a (a+N) := Ioo_subset_Icc_self hx
    apply hm (g x)
    constructor
    · exact hg (by simpa using natural_sample_mem (a := a) (Nat.zero_le N)) hx' hx.1.le
    · exact hg hx' (natural_sample_mem (le_refl N)) hx.2.le
  exact first_derivative_bound (fun x : ℝ => f x+(h : ℝ)/u*x)
    (fun x : ℝ => g x+(h : ℝ)/u) a N m _ hd
    (arcDistance_le_half (by linarith) _) hf' hfg' (Or.inl hg') hstrip

set_option backward.isDefEq.respectTransparency false in
/-- Title: `Every linear Fourier twist has the same actual second-derivative estimate`. -/
theorem linear_twist_second_bound (f g k : ℝ → ℝ) (a : ℝ) (N u h : ℕ)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hf : ContinuousOn f (Icc a (a+N)))
    (hfg : ∀ x ∈ Ioo a (a+N), HasDerivAt f (g x) x)
    (hg : ContinuousOn g (Icc a (a+N)))
    (hgk : ∀ x ∈ Ioo a (a+N), HasDerivAt g (k x) x)
    (hk : ∀ x ∈ Ioo a (a+N), lam ≤ k x ∧ k x ≤ A*lam) :
    ‖linearTwistSum f a N u h‖ ≤
      10*(A+1)*(((N : ℝ)+1)*Real.sqrt lam + 1/Real.sqrt lam) := by
  have hf' : ContinuousOn (fun x : ℝ => f x+(h : ℝ)/u*x) (Icc a (a+N)) :=
    hf.add ((continuous_const.mul continuous_id).continuousOn)
  have hfg' : ∀ x ∈ Ioo a (a+N),
      HasDerivAt (fun x : ℝ => f x+(h : ℝ)/u*x) (g x+(h : ℝ)/u) x := by
    intro x hx
    exact (hfg x hx).fun_add (hasDerivAt_const_mul ((h : ℝ)/u))
  have hg' : ContinuousOn (fun x : ℝ => g x+(h : ℝ)/u) (Icc a (a+N)) :=
    hg.add continuous_const.continuousOn
  have hgk' : ∀ x ∈ Ioo a (a+N), HasDerivAt (fun x : ℝ => g x+(h : ℝ)/u) (k x) x :=
    fun x hx => (hgk x hx).add_const _
  exact second_derivative_bound (fun x : ℝ => f x+(h : ℝ)/u*x)
    (fun x : ℝ => g x+(h : ℝ)/u) k a N hlam hA hf' hfg' hg' hgk' hk

end NField.Alignment.CommonResetTwistDerivatives
