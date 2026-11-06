/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetSmallSource
import NField.Alignment.CommonResetTailSource
import NField.Alignment.CommonResetBoxSource

/-! # The complete published frequency budget for the original signed source -/

noncomputable section

namespace NField.Alignment.CommonResetBudget

open scoped BigOperators
open CommonResetFrequencyPartition CommonResetConductorSelection CommonResetSampling
open CommonResetSmallSource CommonResetTailSource CommonResetBoxSource

def budgetScale (p V J : ℕ) : ℝ :=
  (p : ℝ)^(3/2 : ℝ)*(Real.sqrt ((J : ℝ)*V)+1)+(p : ℝ)^2/V+(p : ℝ)^2/J

theorem budgetScale_nonneg (p V J : ℕ) : 0 ≤ budgetScale p V J := by
  unfold budgetScale
  positivity

theorem abs_four_sum (a b c d : ℝ) : |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))) (le_refl _))

theorem complete_frequency_budget_half (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p V J : ℕ, p.Prime → 0 < V → V ≤ halfPrime p →
      0 < J → J ≤ halfPrime p →
      |interiorSource (p-1) (p^2)| ≤ C*(p : ℝ)^ε*budgetScale p V J := by
  obtain ⟨Cs, hCs, hs⟩ := small_source_small_power ε hε
  obtain ⟨Cl, hCl, hl⟩ := large_linear_source_small_power ε hε
  obtain ⟨Ce, hCe, he⟩ := large_endpoint_source_small_power ε hε
  obtain ⟨Cb, hCb, hb⟩ := large_box_source_small_power ε hε
  let C := Cs+Cl+Ce+Cb
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p V J hp hV hVP hJ hJP
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hP : halfPrime p ≤ p := (Nat.div_le_self _ _).trans (Nat.sub_le p 1)
  have hsmall := hs p hp
  have hlinear := hl p (quarterCutoff p) V hp hV
  have hend := he p (quarterCutoff p) V J hp hVP hJ
  have hbox := hb p V J hp (hVP.trans hP) (hJP.trans hP)
  rw [Real.rpow_add hpR] at hsmall hbox
  rw [Real.rpow_add hpR, Real.rpow_two] at hlinear hend
  let B : ℝ := (p : ℝ)^(3/2 : ℝ)*(Real.sqrt ((J : ℝ)*V)+1)
  let L : ℝ := (p : ℝ)^2/V
  let E : ℝ := (p : ℝ)^2/J
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hQ : 0 ≤ (p : ℝ)^ε := Real.rpow_nonneg hpR.le _
  have hsmallB : |smallSource p (quarterCutoff p)| ≤ Cs*(p : ℝ)^ε*B := by
    apply hsmall.trans
    dsimp [B]
    have hh : (p : ℝ)^(3/2 : ℝ) ≤ (p : ℝ)^(3/2 : ℝ)*(Real.sqrt ((J : ℝ)*V)+1) :=
      le_mul_of_one_le_right (Real.rpow_nonneg hpR.le _) (by linarith [Real.sqrt_nonneg ((J : ℝ)*V)])
    calc
      _ = Cs*(p : ℝ)^ε*(p : ℝ)^(3/2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
  have hlinearL : |largeLinearSource p (quarterCutoff p) V| ≤ Cl*(p : ℝ)^ε*L := by
    convert hlinear using 1 <;> dsimp [L] <;> ring
  have hendE : |largeEndpointSource p (quarterCutoff p) V J| ≤ Ce*(p : ℝ)^ε*E := by
    convert hend using 1 <;> dsimp [E] <;> ring
  have hboxB : |largeBoxSource p (quarterCutoff p) V J| ≤ Cb*(p : ℝ)^ε*B := by
    convert hbox using 1 <;> dsimp [B] <;> ring
  have hSC : Cs+Cb ≤ C := by dsimp [C]; linarith
  have hLC : Cl ≤ C := by dsimp [C]; linarith
  have hEC : Ce ≤ C := by dsimp [C]; linarith
  calc
    _ = |smallSource p (quarterCutoff p)+largeLinearSource p (quarterCutoff p) V+
        largeEndpointSource p (quarterCutoff p) V J+largeBoxSource p (quarterCutoff p) V J| := by
      rw [full_source_partition hp (quarterCutoff p) hVP hJP]
    _ ≤ |smallSource p (quarterCutoff p)|+|largeLinearSource p (quarterCutoff p) V|+
        |largeEndpointSource p (quarterCutoff p) V J|+|largeBoxSource p (quarterCutoff p) V J| := abs_four_sum _ _ _ _
    _ ≤ Cs*(p : ℝ)^ε*B+Cl*(p : ℝ)^ε*L+Ce*(p : ℝ)^ε*E+Cb*(p : ℝ)^ε*B :=
      add_le_add (add_le_add (add_le_add hsmallB hlinearL) hendE) hboxB
    _ = (Cs+Cb)*(p : ℝ)^ε*B+Cl*(p : ℝ)^ε*L+Ce*(p : ℝ)^ε*E := by ring
    _ ≤ C*(p : ℝ)^ε*B+C*(p : ℝ)^ε*L+C*(p : ℝ)^ε*E := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSC hQ) hB)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLC hQ) hL))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC hQ) hE)
    _ = _ := by dsimp [B, L, E, budgetScale]; ring

theorem halfPrime_clip_pos {p V : ℕ} (hp : 3 ≤ p) (hV : 0 < V) : 0 < min V (halfPrime p) := by
  unfold halfPrime
  omega

theorem halfPrime_clip_compare {p V : ℕ} (hp : 3 ≤ p) (hV : V ≤ p) : V ≤ 4*min V (halfPrime p) := by
  unfold halfPrime
  omega

theorem clipped_reciprocal {p V : ℕ} (hp : 3 ≤ p) (hV : 0 < V) (hVP : V ≤ p) :
    (p : ℝ)^2/(min V (halfPrime p) : ℕ) ≤ 4*((p : ℝ)^2/(V : ℝ)) := by
  have hVR : (0 : ℝ) < V := by exact_mod_cast hV
  have hCR : (0 : ℝ) < min V (halfPrime p) := by exact_mod_cast halfPrime_clip_pos hp hV
  have hcomp : (V : ℝ) ≤ 4*(min V (halfPrime p) : ℕ) := by exact_mod_cast halfPrime_clip_compare hp hVP
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hCR hVR).mpr
  nlinarith [mul_le_mul_of_nonneg_left hcomp (sq_nonneg (p : ℝ))]

theorem clipped_budget {p V J : ℕ} (hp : 3 ≤ p) (hV : 0 < V) (hVP : V ≤ p)
    (hJ : 0 < J) (hJP : J ≤ p) :
    budgetScale p (min V (halfPrime p)) (min J (halfPrime p)) ≤ 4*budgetScale p V J := by
  have hroot : Real.sqrt ((min J (halfPrime p) : ℕ)*(min V (halfPrime p) : ℕ) : ℝ) ≤
      Real.sqrt ((J : ℝ)*V) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (Nat.cast_le.mpr (min_le_left _ _)) (Nat.cast_le.mpr (min_le_left _ _))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hB : (p : ℝ)^(3/2 : ℝ)*(Real.sqrt ((min J (halfPrime p) : ℕ)*(min V (halfPrime p) : ℕ) : ℝ)+1) ≤
      4*((p : ℝ)^(3/2 : ℝ)*(Real.sqrt ((J : ℝ)*V)+1)) := by
    have hnonneg : 0 ≤ (p : ℝ)^(3/2 : ℝ)*(Real.sqrt ((J : ℝ)*V)+1) := by positivity
    have hh := mul_le_mul_of_nonneg_left (add_le_add hroot (le_refl 1)) (Real.rpow_nonneg (Nat.cast_nonneg p) (3/2 : ℝ))
    linarith
  unfold budgetScale
  calc
    _ ≤ 4*((p : ℝ)^(3/2 : ℝ)*(Real.sqrt ((J : ℝ)*V)+1))+
        4*((p : ℝ)^2/V)+4*((p : ℝ)^2/J) :=
      add_le_add (add_le_add hB (clipped_reciprocal hp hV hVP)) (clipped_reciprocal hp hJ hJP)
    _ = _ := by ring

/-- Title: `The original complete signed source satisfies the published two-cutoff frequency budget`. -/
theorem complete_frequency_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p V J : ℕ, p.Prime → 0 < V → V ≤ p → 0 < J → J ≤ p →
      |interiorSource (p-1) (p^2)| ≤ C*(p : ℝ)^ε*budgetScale p V J := by
  obtain ⟨C, hC, hc⟩ := complete_frequency_budget_half ε hε
  refine ⟨4*C, by positivity, ?_⟩
  intro p V J hp hV hVP hJ hJP
  by_cases hp2 : p=2
  · subst p
    norm_num only [interiorSource, Nat.reduceSub, Finset.Icc_eq_empty_of_lt (by norm_num : 1<2), Finset.sum_empty, abs_zero]
    exact mul_nonneg (by positivity) (budgetScale_nonneg 2 V J)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hb := hc p (min V (halfPrime p)) (min J (halfPrime p)) hp
    (halfPrime_clip_pos hp3 hV) (min_le_right _ _) (halfPrime_clip_pos hp3 hJ) (min_le_right _ _)
  calc
    _ ≤ C*(p : ℝ)^ε*budgetScale p (min V (halfPrime p)) (min J (halfPrime p)) := hb
    _ ≤ C*(p : ℝ)^ε*(4*budgetScale p V J) :=
      mul_le_mul_of_nonneg_left (clipped_budget hp3 hV hVP hJ hJP) (by positivity)
    _ = _ := by ring

end NField.Alignment.CommonResetBudget
