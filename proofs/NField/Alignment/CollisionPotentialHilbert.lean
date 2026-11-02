/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ProfiniteRemainderMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Finite collision potentials in the Haar Hilbert space

The vectors below are the actual continuous remainder functions embedded
in Haar L². Their Gram formula therefore controls the same observable as
the manuscript, rather than a separately postulated kernel.
-/

noncomputable section

namespace NField.Alignment.CollisionPotentialHilbert

open scoped BigOperators
open MeasureTheory
open NField.Alignment.ProfiniteRemainderMeasure

abbrev HaarL2 := Lp ℝ 2 phaseHaar

def remainderMap (k : ℕ) : C(Phase, ℝ) := ⟨centered k, continuous_centered k⟩

def remainderVector (k : ℕ) : HaarL2 :=
  ContinuousMap.toLp 2 phaseHaar ℝ (remainderMap k)

theorem remainder_inner {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    inner ℝ (remainderVector k) (remainderVector l) =
      ((k.gcd l : ℝ) ^ 2 - 1) / 12 := by
  rw [remainderVector, remainderVector, ContinuousMap.inner_toLp]
  simpa only [remainderMap, ContinuousMap.coe_mk, conj_trivial, mul_comm]
    using haar_remainder_covariance hk hl

theorem remainder_inner_nonneg {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    0 ≤ inner ℝ (remainderVector k) (remainderVector l) := by
  rw [remainder_inner hk hl]
  have hd : (1 : ℝ) ≤ (k.gcd l : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left l hk
  exact div_nonneg (by nlinarith) (by norm_num)

def potentialMap (v : ℕ → ℝ) (M : ℕ) : C(Phase, ℝ) :=
  (2 / 3 : ℝ) • ∑ k ∈ Finset.Icc 2 M, v k • remainderMap k

def finitePotential (v : ℕ → ℝ) (M : ℕ) : HaarL2 :=
  (2 / 3 : ℝ) • ∑ k ∈ Finset.Icc 2 M, v k • remainderVector k

theorem finitePotential_toLp (v : ℕ → ℝ) (M : ℕ) :
    finitePotential v M = ContinuousMap.toLp 2 phaseHaar ℝ (potentialMap v M) := by
  simp [finitePotential, potentialMap, remainderVector]

theorem potentialMap_integer (v : ℕ → ℝ) (M n : ℕ) :
    potentialMap v M (integerPhase (n : ℤ)) =
      CollisionRemainderDynamics.finiteAge v M n := by
  simp only [potentialMap, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    remainderMap, ContinuousMap.coe_mk, smul_eq_mul,
    CollisionRemainderDynamics.finiteAge]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [centered_integer (by have := (Finset.mem_Icc.mp hk).1; omega)]

theorem finite_potential_norm_sq (v : ℕ → ℝ) (M : ℕ) :
    ‖finitePotential v M‖ ^ 2 =
      (1 / 27 : ℝ) * ∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M,
        v k * v l * ((k.gcd l : ℝ) ^ 2 - 1) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold finitePotential
  simp only [inner_smul_left, inner_smul_right, conj_trivial]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
  have he : (∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M,
      v k * (v l * inner ℝ (remainderVector k) (remainderVector l))) =
      (1 / 12 : ℝ) * ∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M,
        v k * v l * ((k.gcd l : ℝ) ^ 2 - 1) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [remainder_inner (by have := (Finset.mem_Icc.mp hk).1; omega)
      (by have := (Finset.mem_Icc.mp hl).1; omega)]
    ring
  rw [he]
  ring

section PositiveGram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Nonnegative pairwise inner products prevent cancellation from concealing
the energy of a tail. This is a Hilbert-space statement, not an assumption
that the remainder variables are independent. -/
theorem positive_gram_tail_bound (v : ℕ → E)
    (hv : ∀ i j, 0 ≤ inner ℝ (v i) (v j)) {m n : ℕ} (hmn : m ≤ n) :
    ‖(∑ i ∈ Finset.range n, v i) - ∑ i ∈ Finset.range m, v i‖^2 ≤
      ‖∑ i ∈ Finset.range n, v i‖^2 - ‖∑ i ∈ Finset.range m, v i‖^2 := by
  have hsplit := Finset.sum_range_add_sum_Ico v hmn
  have hcross : 0 ≤ inner ℝ (∑ i ∈ Finset.range m, v i) (∑ i ∈ Finset.Ico m n, v i) := by
    simp_rw [sum_inner, inner_sum]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hv i j))
  rw [← hsplit]
  simp only [add_sub_cancel_left]
  rw [norm_add_sq_real]
  linarith

theorem positive_gram_norm_monotone (v : ℕ → E)
    (hv : ∀ i j, 0 ≤ inner ℝ (v i) (v j)) :
    Monotone (fun n => ‖∑ i ∈ Finset.range n, v i‖^2) := by
  intro m n hmn
  have h := positive_gram_tail_bound v hv hmn
  nlinarith [sq_nonneg ‖(∑ i ∈ Finset.range n, v i) - ∑ i ∈ Finset.range m, v i‖]

theorem positive_gram_cauchy_of_bounded (v : ℕ → E)
    (hv : ∀ i j, 0 ≤ inner ℝ (v i) (v j))
    (hb : BddAbove (Set.range (fun n => ‖∑ i ∈ Finset.range n, v i‖^2))) :
    CauchySeq (fun n => ∑ i ∈ Finset.range n, v i) := by
  have ht := tendsto_atTop_ciSup (positive_gram_norm_monotone v hv) hb
  have hc := Metric.cauchySeq_iff.mp ht.cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn N (le_refl N)
  have htail := positive_gram_tail_bound v hv hn
  rw [Real.dist_eq] at hd
  rw [abs_of_nonneg (sub_nonneg.mpr (positive_gram_norm_monotone v hv hn))] at hd
  rw [dist_eq_norm]
  nlinarith [norm_nonneg ((∑ i ∈ Finset.range n, v i) - ∑ i ∈ Finset.range N, v i)]

theorem positive_gram_converges_iff_bounded [CompleteSpace E] (v : ℕ → E)
    (hv : ∀ i j, 0 ≤ inner ℝ (v i) (v j)) :
    (∃ y : E, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, v i) Filter.atTop (nhds y)) ↔
      BddAbove (Set.range (fun n => ‖∑ i ∈ Finset.range n, v i‖^2)) := by
  constructor
  · rintro ⟨y, hy⟩
    exact hy.norm.pow 2 |>.isBoundedUnder_le.bddAbove_range
  · intro hb
    exact cauchySeq_tendsto_of_complete (positive_gram_cauchy_of_bounded v hv hb)

end PositiveGram

end NField.Alignment.CollisionPotentialHilbert
