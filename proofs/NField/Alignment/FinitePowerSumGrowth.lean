/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Field

/-!
# Individual complex moduli from aggregate power-sum growth

Cesaro averages separate the copies of a maximal-modulus root from all
other normalized roots. Repeated roots are retained, and no individual
bound is assumed when estimating the aggregate.
-/

set_option autoImplicit false
namespace NField.Alignment.FinitePowerSumGrowth
open scoped BigOperators Topology Classical
open Filter Finset

/-- Partial geometric sums are bounded on the closed unit disk away from one. -/
theorem norm_geometric_sum_le (w : ℂ) (hw : ‖w‖≤1) (h1 : w≠1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, w^k‖ ≤ 2/‖w-1‖ := by
  rw [geom_sum_eq h1 n,norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖w^n-1‖ ≤ ‖w^n‖+‖(1:ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 := by
      rw [norm_pow,norm_one]
      have := pow_le_one₀ (n := n) (norm_nonneg w) hw
      linarith

/-- Cesaro averages of powers on the closed unit disk select exactly w=1. -/
theorem tendsto_cesaro_geometric (w : ℂ) (hw : ‖w‖≤1) :
    Tendsto (fun n : ℕ => (n⁻¹:ℝ) • ∑ k ∈ Finset.range n, w^k)
      atTop (𝓝 (if w=1 then 1 else 0)) := by
  by_cases h1 : w=1
  · subst w
    simpa only [if_true,one_pow] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1)).cesaro_smul
  · rw [if_neg h1]
    apply squeeze_zero_norm (a := fun n : ℕ => (n⁻¹:ℝ)*(2/‖w-1‖))
    · intro n
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      exact mul_le_mul_of_nonneg_left (norm_geometric_sum_le w hw h1 n)
        (inv_nonneg.mpr (Nat.cast_nonneg n))
    · simpa using (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)).mul_const
          (2/‖w-1‖)

/-- Normalize a power-sum growth bound by any strictly larger modulus. -/
theorem normalized_power_sum_tendsto_zero {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (R C : ℝ) (hR : 0<R) (v : ℂ) (hv : R<‖v‖)
    (h : ∀ᶠ n : ℕ in atTop, ‖∑ i, z i^n‖ ≤ C*R^n) :
    Tendsto (fun n : ℕ => ∑ i, (z i/v)^n) atTop (𝓝 0) := by
  have hvp : 0<‖v‖ := hR.trans hv
  have hratio : R/‖v‖<1 := (div_lt_one hvp).mpr hv
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one
    (le_of_lt (div_pos hR hvp)) hratio
  apply squeeze_zero_norm' (a := fun n : ℕ => C*(R/‖v‖)^n)
  · filter_upwards [h] with n hn
    simp_rw [div_pow]
    rw [← Finset.sum_div,norm_div,norm_pow]
    calc
      ‖∑ i, z i^n‖/‖v‖^n ≤ (C*R^n)/‖v‖^n :=
        div_le_div_of_nonneg_right hn (pow_nonneg (norm_nonneg _) _)
      _ = C*(R^n/‖v‖^n) := by ring
  · simpa using tendsto_const_nhds.mul hgeom

/-- Aggregate exponential growth bounds each root separately. The bound
is only required eventually, and the finite family may have repetitions. -/
theorem norm_le_of_power_sum_growth {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (R C : ℝ) (hR : 0<R)
    (h : ∀ᶠ n : ℕ in atTop, ‖∑ i, z i^n‖ ≤ C*R^n) :
    ∀ i, ‖z i‖≤R := by
  intro i
  by_contra! hi
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun k => ‖z k‖)
    ⟨i,Finset.mem_univ i⟩
  have hjR : R<‖z j‖ := hi.trans_le (hj i (Finset.mem_univ i))
  have hjp : 0<‖z j‖ := hR.trans hjR
  have hj0 : z j≠0 := norm_pos_iff.mp hjp
  have hw : ∀ k, ‖z k/z j‖≤1 := by
    intro k
    rw [norm_div,div_le_one hjp]
    exact hj k (Finset.mem_univ k)
  have hz := (normalized_power_sum_tendsto_zero z R C hR (z j) hjR h).cesaro_smul
  have hc := tendsto_finsetSum Finset.univ
    (fun k _ => tendsto_cesaro_geometric (z k/z j) (hw k))
  have hc' : Tendsto
      (fun n : ℕ => (n⁻¹:ℝ) • ∑ k ∈ Finset.range n, ∑ l, (z l/z j)^k)
      atTop (𝓝 (∑ l, if z l/z j=1 then (1:ℂ) else 0)) := by
    convert hc using 1
    ext n
    rw [Finset.sum_comm,Finset.smul_sum]
  have he : (0:ℂ)=∑ l, if z l/z j=1 then (1:ℂ) else 0 :=
    tendsto_nhds_unique hz hc'
  have hs : (∑ l, if z l/z j=1 then (1:ℂ) else 0) =
      ((Finset.univ.filter (fun l => z l/z j=1)).card : ℂ) := by
    simp
  rw [hs] at he
  have hcard : 0<(Finset.univ.filter (fun l => z l/z j=1)).card := by
    apply Finset.card_pos.mpr
    exact ⟨j,by simp [hj0]⟩
  have : (Finset.univ.filter (fun l => z l/z j=1)).card=0 := by
    exact_mod_cast he.symm
  omega

end NField.Alignment.FinitePowerSumGrowth
