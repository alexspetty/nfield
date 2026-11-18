/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.TorusMarginal
/-! # Divisor coordinates of every source in the complete cutoff space -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators Matrix
open MeasureTheory Module NField.Alignment CommonResetGram CollisionRampEnergy SourceMetrics

def divisorCoordinate (N : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, if d ∣ h then c h/(h : ℝ) else 0

theorem weighted_profile_scaled (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    weightedProfile N c x=∑ h ∈ Finset.Icc 1 N, (c h/(h : ℝ))*scaledSaw h x := by
  rw [weightedProfile, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hp : 0 < h := (Finset.mem_Icc.mp hh).1
  have hR : (h : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [scaledSaw]
  field_simp

theorem weighted_profile_mem_cutoff (N : ℕ) (c : ℕ → ℝ) :
    weightedProfile N c ∈ cutoffSpace N := by
  have he : weightedProfile N c=∑ h ∈ Finset.Icc 1 N, (c h/(h : ℝ)) • scaledSaw h := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using weighted_profile_scaled N c x
  rw [he]
  apply Submodule.sum_mem
  intro h hh
  exact Submodule.smul_mem _ _ (scaled_saw_mem_cutoff hh)

theorem weighted_primitive_work {n : ℕ} (hn : 0 < n) (N : ℕ) (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, weightedProfile N c x*primitiveField n x)=
      jordanMass n/3*divisorCoordinate N c n := by
  have he (x : ℝ) : weightedProfile N c x*primitiveField n x=
      ∑ h ∈ Finset.Icc 1 N, (c h/(h : ℝ))*(scaledSaw h x*primitiveField n x) := by
    rw [weighted_profile_scaled, Finset.sum_mul]
    simp only [mul_assoc]
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun h hh =>
    (scaled_primitive_integrable (Finset.mem_Icc.mp hh).1 n 0 1).const_mul (c h/(h : ℝ)))]
  simp only [intervalIntegral.integral_const_mul]
  rw [divisorCoordinate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [scaled_primitive_work (Finset.mem_Icc.mp hh).1 hn]
  by_cases hd : n ∣ h <;> simp [hd, mul_comm]

theorem weighted_profile_primitive_coordinates (N : ℕ) (c : ℕ → ℝ) :
    weightedProfile N c=
      primitiveCombination N (fun i => divisorCoordinate N c (i.val+1)) := by
  let v : cutoffSpace N := ⟨weightedProfile N c, weighted_profile_mem_cutoff N c⟩
  let b := primitiveBasis N
  have hexp : primitiveCombination N (fun i => b.repr v i)=weightedProfile N c := by
    have h := congrArg (fun u : cutoffSpace N => (u : ℝ → ℝ)) (b.sum_repr v)
    simpa only [b, Submodule.coe_sum, Submodule.coe_smul, primitiveCombination,
      primitive_basis_apply] using h
  have hc (i : Fin N) : b.repr v i=divisorCoordinate N c (i.val+1) := by
    have h := congrArg (fun f : ℝ → ℝ =>
      ∫ x in (0 : ℝ)..1, f x*primitiveField (i.val+1) x) hexp
    rw [primitive_combination_work, weighted_primitive_work (Nat.succ_pos i.val)] at h
    have hJ := (jordan_mass_pos (Nat.succ_pos i.val)).ne'
    apply (mul_right_cancel₀ hJ)
    linarith
  simpa only [hc] using hexp.symm

theorem primitive_source_coordinates {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    {d : ℕ} (hd : 0 < d) :
    divisorCoordinate N (primitiveSource n) d=if d=n then 1 else 0 := by
  have h := weighted_primitive_work hd N (primitiveSource n)
  simp_rw [primitive_field_source hn hnN] at h
  rw [primitive_field_gram hn hd] at h
  have hJ := (jordan_mass_pos hd).ne'
  by_cases he : d=n
  · subst d
    simp only [if_true] at h ⊢
    apply (mul_left_cancel₀ hJ)
    linarith
  · have hne : n ≠ d := Ne.symm he
    simp only [he, hne, if_false] at h ⊢
    apply (mul_left_cancel₀ hJ)
    linarith

theorem primitive_combination_energy (N : ℕ) (c : Fin N → ℝ) :
    (∫ x in (0 : ℝ)..1, primitiveCombination N c x^2)=
      (1/3 : ℝ)*∑ i : Fin N, jordanMass (i.val+1)*(c i)^2 := by
  have he (x : ℝ) : primitiveCombination N c x^2=
      ∑ i : Fin N, c i*(primitiveCombination N c x*primitiveField (i.val+1) x) := by
    conv_lhs => rw [pow_two]; arg 2; unfold primitiveCombination
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hint (i : Fin N) : IntervalIntegrable
      (fun x => c i*(primitiveCombination N c x*primitiveField (i.val+1) x)) volume 0 1 := by
    have hex (x : ℝ) : primitiveCombination N c x*primitiveField (i.val+1) x=
        ∑ j : Fin N, c j*(primitiveField (j.val+1) x*primitiveField (i.val+1) x) := by
      simp only [primitiveCombination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul, mul_assoc]
    simp_rw [hex]
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ (fun j _ =>
        (primitive_product_integrable (j.val+1) (i.val+1) 0 1).const_mul (c j))).const_mul (c i)
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  simp only [intervalIntegral.integral_const_mul, primitive_combination_work]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem continuous_divisor_coordinates (N : ℕ) (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, weightedProfile N c x^2)=
      (1/3 : ℝ)*∑ d ∈ Finset.Icc 1 N, jordanMass d*(divisorCoordinate N c d)^2 := by
  rw [weighted_profile_primitive_coordinates, primitive_combination_energy, sum_source_indices]

theorem continuous_gram_divisor_coordinates (N : ℕ) (c : Fin N → ℝ) :
    c ⬝ᵥ (continuousGram N *ᵥ c)=
      (1/3 : ℝ)*∑ d ∈ Finset.Icc 1 N,
        jordanMass d*(divisorCoordinate N (cutoffCoefficients N c) d)^2 := by
  have h := continuous_gram_quadratic N c
  simp only [star_trivial] at h
  rw [h, continuous_divisor_coordinates]

end NField.ResetForests.PrimitiveCoordinates
