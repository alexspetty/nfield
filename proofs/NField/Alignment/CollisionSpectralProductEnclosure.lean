/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralEuler
import NField.Alignment.CollisionDirichletRationalEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionSpectralProductEnclosure
open scoped BigOperators
open Filter CollisionSpectralArithmetic CollisionSpectralEuler CollisionDirichletRationalEnclosure
open CollisionDivisorSeries

def natEulerFactor (n : ℕ) : ℝ :=
  if n.Prime then 1+(localFactor n-1)/(n : ℝ) else 1

def productPrefix (P : ℕ) : ℝ := ∏ n ∈ Finset.range (P+1),natEulerFactor n

theorem natEulerFactor_bounds (n : ℕ) : 0 ≤ natEulerFactor n ∧ natEulerFactor n ≤ 1 := by
  by_cases hp : n.Prime
  · have hn := spectral_euler_factor_pos ⟨n,hp⟩
    have hl := localFactor_le_one hp
    simp only [natEulerFactor,if_pos hp]
    exact ⟨hn.le,by have h := div_nonpos_of_nonpos_of_nonneg (by linarith : localFactor n-1 ≤ 0) (Nat.cast_nonneg n); linarith⟩
  · simp [natEulerFactor,hp]

theorem natEulerFactor_defect (n : ℕ) :
    1-natEulerFactor n ≤ 2*zetaKernel 2 n := by
  by_cases hp : n.Prime
  · have h := primeAbsolute_bound n
    rw [primeAbsolute,if_pos hp,abs_of_nonpos (by linarith [localFactor_le_one hp])] at h
    have hk : CollisionZetaMoments.powerKernel 2 n=zetaKernel 2 n := by
      rw [zetaKernel_rpow (by norm_num : (2 : ℝ) ≠ 0),Real.rpow_neg (Nat.cast_nonneg n)]
      norm_num [CollisionZetaMoments.powerKernel]
    rw [hk] at h
    rw [neg_div] at h
    simp only [natEulerFactor,if_pos hp]
    linarith
  · simp only [natEulerFactor,if_neg hp,sub_self]
    exact mul_nonneg (by norm_num) (zetaKernel_nonneg 2 n)

theorem natEulerFactor_hasProd : HasProd natEulerFactor spectralConstant := by
  have h := spectralConstant_hasProd
  rw [← spectralConstant_hasProd.tprod_eq] at h
  have hi := (hasProd_subtype_iff_mulIndicator (s := {n : ℕ | n.Prime})
    (f := fun n : ℕ => 1+(localFactor n-1)/(n : ℝ))).mp h
  have he : ({n : ℕ | n.Prime}.mulIndicator
      (fun n : ℕ => 1+(localFactor n-1)/(n : ℝ)))=natEulerFactor := by
    funext n
    by_cases hp : n.Prime <;> simp [natEulerFactor,Set.mulIndicator,hp]
  rw [he] at hi
  exact hi

theorem finite_product_defect {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s,0 ≤ f a ∧ f a ≤ 1) :
    1-(∏ a ∈ s,f a) ≤ ∑ a ∈ s,(1-f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ b ∈ s,0 ≤ f b ∧ f b ≤ 1 := fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have haa := hf a (Finset.mem_insert_self _ _)
    have hh := ih hs
    have hp : 0 ≤ ∏ b ∈ s,f b := Finset.prod_nonneg (fun b hb => (hs b hb).1)
    have hu : ∏ b ∈ s,f b ≤ 1 := Finset.prod_le_one (fun b hb => (hs b hb).1) (fun b hb => (hs b hb).2)
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr haa.2) (sub_nonneg.mpr hu)]

theorem productPrefix_bounds (P : ℕ) : 0 ≤ productPrefix P ∧ productPrefix P ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun n _ => (natEulerFactor_bounds n).1),
    Finset.prod_le_one (fun n _ => (natEulerFactor_bounds n).1) (fun n _ => (natEulerFactor_bounds n).2)⟩

theorem prefix_product_difference (P M : ℕ) :
    0 ≤ productPrefix P-(∏ n ∈ Finset.range (P+1+M),natEulerFactor n) ∧
      productPrefix P-(∏ n ∈ Finset.range (P+1+M),natEulerFactor n) ≤
        ∑ n ∈ Finset.range M,(1-natEulerFactor (P+1+n)) := by
  have h := finite_product_defect (Finset.range M) (fun n => natEulerFactor (P+1+n))
    (fun n _ => natEulerFactor_bounds _)
  have ht : (∏ n ∈ Finset.range M,natEulerFactor (P+1+n)) ≤ 1 :=
    Finset.prod_le_one (fun n _ => (natEulerFactor_bounds _).1) (fun n _ => (natEulerFactor_bounds _).2)
  have hp := productPrefix_bounds P
  rw [Finset.prod_range_add]
  change 0 ≤ productPrefix P-productPrefix P*_ ∧ productPrefix P-productPrefix P*_ ≤ _
  constructor
  · nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr ht)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr ht)]

theorem finite_factor_tail_bound {P : ℕ} (hP : 1 ≤ P) (M : ℕ) :
    (∑ n ∈ Finset.range M,(1-natEulerFactor (P+1+n))) ≤ 2/(P : ℝ) := by
  have h1 : (∑ n ∈ Finset.range M,(1-natEulerFactor (P+1+n))) ≤
      2*∑ n ∈ Finset.range M,zetaKernel 2 (P+1+n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => natEulerFactor_defect _)
  have hs : Summable (fun n : ℕ => zetaKernel 2 (P+1+n)) :=
    (zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).comp_injective
      (fun a b h => by omega)
  have h2 := hs.sum_le_tsum (Finset.range M) (fun n _ => zetaKernel_nonneg 2 _)
  have h3 := zeta_tail_bound (by norm_num : (1 : ℝ) < 2) hP
  have he : (fun n : ℕ => zetaKernel 2 (n+P+1))=(fun n : ℕ => zetaKernel 2 (P+1+n)) := by
    funext n;congr 1;omega
  rw [he] at h3
  norm_num at h3
  rw [Real.rpow_neg_one] at h3
  have hh : 2/(P : ℝ)=2*(P : ℝ)⁻¹ := by ring
  rw [hh]
  linarith

theorem spectralConstant_product_enclosure {P : ℕ} (hP : 1 ≤ P) :
    max 0 (productPrefix P-2/(P : ℝ)) ≤ spectralConstant ∧
      spectralConstant ≤ productPrefix P := by
  have ht := natEulerFactor_hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat (P+1))
  have hlo : ∀ M : ℕ,productPrefix P-2/(P : ℝ) ≤ ∏ n ∈ Finset.range (M+(P+1)),natEulerFactor n := by
    intro M
    have h := (prefix_product_difference P M).2.trans (finite_factor_tail_bound hP M)
    rw [show P+1+M=M+(P+1) by omega] at h
    linarith
  have hhi : ∀ M : ℕ,(∏ n ∈ Finset.range (M+(P+1)),natEulerFactor n) ≤ productPrefix P := by
    intro M
    have h := (prefix_product_difference P M).1
    rw [show P+1+M=M+(P+1) by omega] at h
    linarith
  exact ⟨max_le spectralConstant_pos.le (ge_of_tendsto' ht hlo),le_of_tendsto' ht hhi⟩

end NField.Alignment.CollisionSpectralProductEnclosure
