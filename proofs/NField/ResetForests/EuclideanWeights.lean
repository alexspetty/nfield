/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.EuclideanInverse
/-! # Arbitrary denominator weights and both signed transport commutators -/

set_option autoImplicit false
noncomputable section

namespace NField.ResetForests.EuclideanFold

def clockWeightMap (N : ℕ) (β : ℕ → ℝ) : Module.End ℝ (FoldSource N) :=
  Finsupp.linearCombination ℝ (fun s => β (clockDenominator s) • clockBasis s)

theorem weight_basis {N : ℕ} (β : ℕ → ℝ) (s : FoldClock N) :
    clockWeightMap N β (clockBasis s) = β (clockDenominator s) • clockBasis s := by
  simp [clockWeightMap, clockBasis]

theorem weight_commutator_nonterminal {N : ℕ} (β : ℕ → ℝ)
    (s : FoldClock N) (hs : Nonterminal s) :
    (clockTransport N * clockWeightMap N β - clockWeightMap N β * clockTransport N)
        (clockBasis s) =
      (clockSign s * (β (clockDenominator s) - β (clockAddress s))) •
        clockBasis (successorClock s hs) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, weight_basis,
    transport_nonterminal s hs, map_smul, weight_basis,
    (successor_coordinates s hs).1, smul_smul]
  rw [← sub_smul]
  congr 1
  ring

theorem weight_commutator_terminal {N : ℕ} (β : ℕ → ℝ)
    (s : FoldClock N) (hs : ¬Nonterminal s) :
    (clockTransport N * clockWeightMap N β - clockWeightMap N β * clockTransport N)
      (clockBasis s) = 0 := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, weight_basis,
    map_smul, transport_terminal s hs, smul_zero, map_zero, sub_self]

theorem inverse_weight_commutator (N : ℕ) (β : ℕ → ℝ) :
    foldInverse N * clockWeightMap N β - clockWeightMap N β * foldInverse N =
      -(foldInverse N) *
        (clockTransport N * clockWeightMap N β - clockWeightMap N β * clockTransport N) *
          foldInverse N := by
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun f : Module.End ℝ (FoldSource N) => f x) (inverse_fold_left N)
  have hx' : foldInverse N x + clockTransport N (foldInverse N x) = x := hx
  have hwork := congrArg (fun y => foldInverse N (clockWeightMap N β y)) hx'
  simp only [map_add] at hwork
  have hcost := congrArg
    (fun f : Module.End ℝ (FoldSource N) => f (clockWeightMap N β (foldInverse N x)))
    (inverse_fold_right N)
  have hcost' : foldInverse N (clockWeightMap N β (foldInverse N x)) +
      foldInverse N (clockTransport N (clockWeightMap N β (foldInverse N x))) =
      clockWeightMap N β (foldInverse N x) := by
    simpa only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, map_add] using hcost
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply]
  calc
    _ = (foldInverse N (clockWeightMap N β (foldInverse N x)) +
          foldInverse N (clockWeightMap N β (clockTransport N (foldInverse N x)))) -
        (foldInverse N (clockWeightMap N β (foldInverse N x)) +
          foldInverse N (clockTransport N (clockWeightMap N β (foldInverse N x)))) := by
      rw [hwork, hcost']
    _ = -(foldInverse N (clockTransport N (clockWeightMap N β (foldInverse N x))) -
        foldInverse N (clockWeightMap N β (clockTransport N (foldInverse N x)))) := by abel
    _ = _ := by rw [map_sub]

end NField.ResetForests.EuclideanFold
