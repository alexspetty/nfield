/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrimitiveWork
/-! # The primitive fields form a basis of the literal cutoff space -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators
open MeasureTheory Set Module NField.Alignment CollisionRampEnergy

def primitiveCombination (N : ℕ) (c : Fin N → ℝ) : ℝ → ℝ :=
  ∑ i : Fin N, c i • primitiveField (i.val+1)

theorem primitive_combination_work (N : ℕ) (c : Fin N → ℝ) (j : Fin N) :
    (∫ x in (0 : ℝ)..1, primitiveCombination N c x*primitiveField (j.val+1) x)=
      c j*jordanMass (j.val+1)/3 := by
  have hpair (i : Fin N) :
      (∫ x in (0 : ℝ)..1, primitiveField (i.val+1) x*primitiveField (j.val+1) x)=
        if i=j then jordanMass (j.val+1)/3 else 0 := by
    have h := primitive_field_gram (Nat.succ_pos i.val) (Nat.succ_pos j.val)
    by_cases he : i=j
    · simpa only [he,if_true] using h
    · have hne : i.val+1 ≠ j.val+1 := by
        intro hv
        apply he
        exact Fin.ext (by omega)
      simpa only [hne,he,if_false] using h
  simp only [primitiveCombination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (primitive_product_integrable (i.val+1) (j.val+1) 0 1).const_mul (c i))]
  simp only [intervalIntegral.integral_const_mul, hpair, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem primitive_fields_linearIndependent (N : ℕ) :
    LinearIndependent ℝ (fun i : Fin N => primitiveField (i.val+1)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  change primitiveCombination N c=0 at hc
  have h := primitive_combination_work N c j
  rw [hc] at h
  simp only [Pi.zero_apply, zero_mul, intervalIntegral.integral_zero] at h
  have hJ := (jordan_mass_pos (Nat.succ_pos j.val)).ne'
  have hz : c j*jordanMass (j.val+1)=0 := by nlinarith [h]
  exact (mul_eq_zero.mp hz).resolve_right hJ

def sawGenerator (N : ℕ) (i : Fin N) (x : ℝ) : ℝ :=
  2*midpointRow (i.val+1) x

def cutoffSpace (N : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (range (sawGenerator N))

theorem scaled_saw_mem_cutoff {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    scaledSaw n ∈ cutoffSpace N := by
  have hnB := Finset.mem_Icc.mp hn
  have hbase : (fun x => 2*midpointRow n x) ∈ cutoffSpace N := by
    apply Submodule.subset_span
    refine ⟨⟨n-1,by omega⟩,?_⟩
    funext x
    simp only [sawGenerator, Nat.sub_add_cancel hnB.1]
  have he : scaledSaw n=(n : ℝ) • (fun x => 2*midpointRow n x) := by
    funext x
    simp only [scaledSaw, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact Submodule.smul_mem _ _ hbase

theorem primitive_field_mem_cutoff {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    primitiveField n ∈ cutoffSpace N := by
  unfold primitiveField
  apply Submodule.sum_mem
  intro d hd
  rw [← Int.cast_smul_eq_zsmul ℝ]
  apply Submodule.smul_mem
  apply scaled_saw_mem_cutoff
  have hdiv := Nat.snd_mem_divisors_of_mem_antidiagonal hd
  have hp := Nat.pos_of_mem_divisors hdiv
  exact Finset.mem_Icc.mpr ⟨hp,(Nat.le_of_dvd (Finset.mem_Icc.mp hn).1
    (Nat.mem_divisors.mp hdiv).1).trans (Finset.mem_Icc.mp hn).2⟩

theorem cutoff_space_eq_primitive_span (N : ℕ) :
    cutoffSpace N=Submodule.span ℝ (range (fun i : Fin N => primitiveField (i.val+1))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    have hs : scaledSaw (i.val+1) ∈
        Submodule.span ℝ (range (fun i : Fin N => primitiveField (i.val+1))) := by
      rw [← scaled_saw_primitive_sum (Nat.succ_pos i.val)]
      apply Submodule.sum_mem
      intro d hd
      apply Submodule.subset_span
      have hdp := Nat.pos_of_mem_divisors hd
      have hdn := Nat.le_of_dvd (Nat.succ_pos i.val) (Nat.mem_divisors.mp hd).1
      refine ⟨⟨d-1,by omega⟩,?_⟩
      simp only [Nat.sub_add_cancel hdp]
    have he : sawGenerator N i=(((i.val+1 : ℕ) : ℝ))⁻¹ • scaledSaw (i.val+1) := by
      funext x
      simp only [sawGenerator, scaledSaw, Pi.smul_apply, smul_eq_mul]
      have hi : (((i.val+1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
    rw [he]
    exact Submodule.smul_mem _ _ hs
  · apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    exact primitive_field_mem_cutoff (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)

def primitiveBasis (N : ℕ) : Basis (Fin N) ℝ (cutoffSpace N) :=
  (Basis.span (primitive_fields_linearIndependent N)).map
    (LinearEquiv.ofEq _ _ (cutoff_space_eq_primitive_span N).symm)

theorem primitive_basis_apply (N : ℕ) (i : Fin N) :
    (primitiveBasis N i : ℝ → ℝ)=primitiveField (i.val+1) := by
  simp [primitiveBasis]

end NField.ResetForests.PrimitiveCoordinates
