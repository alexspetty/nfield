/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimitiveSquareTree

/-!
# The exact harmonic bound on the square-tree frontier

For each first coordinate a, exactly a partners leave the square. The
outgoing potential is bounded before dropping the coprimality restriction.
Reflection gives the other half of the literal manuscript error bound.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimitiveSquareBoundary

open scoped BigOperators Classical
open CollisionPrimitiveSquareTree CollisionPrimitiveMassDisplays CollisionMassReadout

def leftSquareBoundary (M : ℕ) : ℝ :=
  ∑ p ∈ (primitiveSquare M).filter (fun p => M < p.1+p.2),
    pairTreePotential p.1 (p.1+p.2)

theorem pairTreePotential_nonneg (a b : ℕ) : 0 ≤ pairTreePotential a b := by
  unfold pairTreePotential
  positivity

theorem pairTreePotential_symm (a b : ℕ) : pairTreePotential a b=pairTreePotential b a := by
  unfold pairTreePotential
  ring

theorem left_child_frontier_bound {M a b : ℕ} (hM : 0 < M) (ha : 0 < a)
    (hs : M < a+b) :
    pairTreePotential a (a+b) ≤ 1/((a : ℝ)^2*(M : ℝ))+1/((a : ℝ)*(M : ℝ)^2) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hsR : (a : ℝ)+(b : ℝ) ≠ 0 := by positivity
  have hm : (M : ℝ) ≤ (a : ℝ)+(b : ℝ) := by exact_mod_cast hs.le
  calc
    _ = 1/((a : ℝ)^2*((a : ℝ)+(b : ℝ)))+
        1/((a : ℝ)*((a : ℝ)+(b : ℝ))^2) := by
      unfold pairTreePotential
      push_cast
      field_simp
      ring
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hm (sq_nonneg _)))
      (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm 2) (Nat.cast_nonneg a)))

theorem squareTreeBoundary_twice_left (M : ℕ) :
    squareTreeBoundary M=2*leftSquareBoundary M := by
  have hs : (∑ p ∈ (primitiveSquare M).filter (fun p => M < p.1+p.2),
      pairTreePotential (p.1+p.2) p.2)=leftSquareBoundary M := by
    unfold leftSquareBoundary
    apply Finset.sum_bij (fun p _ => p.swap)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hs⟩
      rcases primitiveSquare_mem.mp hp with ⟨ha,haM,hb,hbM,hcop⟩
      exact Finset.mem_filter.mpr
        ⟨primitiveSquare_mem.mpr ⟨hb,hbM,ha,haM,hcop.symm⟩,by dsimp; omega⟩
    · intro p hp q hq he
      exact Prod.swap_injective he
    · intro p hp
      refine ⟨p.swap,?_,by simp⟩
      rcases Finset.mem_filter.mp hp with ⟨hp,hs⟩
      rcases primitiveSquare_mem.mp hp with ⟨ha,haM,hb,hbM,hcop⟩
      exact Finset.mem_filter.mpr
        ⟨primitiveSquare_mem.mpr ⟨hb,hbM,ha,haM,hcop.symm⟩,by dsimp; omega⟩
    · intro p hp
      dsimp
      rw [pairTreePotential_symm,add_comm p.1 p.2]
  unfold squareTreeBoundary
  rw [Finset.sum_add_distrib,hs]
  change leftSquareBoundary M+leftSquareBoundary M=2*leftSquareBoundary M
  ring

theorem square_boundary_partner_set {M a : ℕ} (_ha : 0 < a) (haM : a ≤ M) :
    (Finset.Icc 1 M).filter (fun b => M < a+b)=Finset.Icc (M-a+1) M := by
  ext b
  simp only [Finset.mem_filter,Finset.mem_Icc]
  omega

theorem square_boundary_partner_count {M a : ℕ} (ha : 0 < a) (haM : a ≤ M) :
    ((Finset.Icc 1 M).filter (fun b => M < a+b)).card=a := by
  rw [square_boundary_partner_set ha haM,Nat.card_Icc]
  omega

theorem full_square_left_majorant {M : ℕ} (hM : 0 < M) :
    (∑ p ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun p => M < p.1+p.2),
      (1/((p.1 : ℝ)^2*(M : ℝ))+1/((p.1 : ℝ)*(M : ℝ)^2)))=
      ((harmonic M : ℝ)+1)/(M : ℝ) := by
  rw [Finset.sum_filter,Finset.sum_product]
  have hrow : ∀ a ∈ Finset.Icc 1 M,
      (∑ b ∈ Finset.Icc 1 M,
        if M < a+b then 1/((a : ℝ)^2*(M : ℝ))+1/((a : ℝ)*(M : ℝ)^2) else 0)=
      (a : ℝ)⁻¹/(M : ℝ)+1/(M : ℝ)^2 := by
    intro a ha
    rcases Finset.mem_Icc.mp ha with ⟨ha,haM⟩
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [← Finset.sum_filter,Finset.sum_const,square_boundary_partner_count ha haM,nsmul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl hrow,Finset.sum_add_distrib,← Finset.sum_div,
    ← harmonic_real_sum,Finset.sum_const,Nat.card_Icc]
  simp only [Nat.add_sub_cancel,nsmul_eq_mul]
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem leftSquareBoundary_bound {M : ℕ} (hM : 0 < M) :
    leftSquareBoundary M ≤ ((harmonic M : ℝ)+1)/(M : ℝ) := by
  calc
    _ ≤ ∑ p ∈ (primitiveSquare M).filter (fun p => M < p.1+p.2),
        (1/((p.1 : ℝ)^2*(M : ℝ))+1/((p.1 : ℝ)*(M : ℝ)^2)) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hs⟩
      exact left_child_frontier_bound hM (primitiveSquare_mem.mp hp).1 hs
    _ ≤ ∑ p ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun p => M < p.1+p.2),
        (1/((p.1 : ℝ)^2*(M : ℝ))+1/((p.1 : ℝ)*(M : ℝ)^2)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp,hs⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,hs⟩
      · intro p hp hn
        positivity
    _ = _ := full_square_left_majorant hM

theorem squareTreeBoundary_bounds {M : ℕ} (hM : 0 < M) :
    0 ≤ squareTreeBoundary M ∧ squareTreeBoundary M ≤ 2*((harmonic M : ℝ)+1)/(M : ℝ) := by
  constructor
  · unfold squareTreeBoundary
    exact Finset.sum_nonneg (fun p _ => add_nonneg (pairTreePotential_nonneg _ _)
      (pairTreePotential_nonneg _ _))
  · rw [squareTreeBoundary_twice_left]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (leftSquareBoundary_bound hM)
      (by norm_num : (0 : ℝ) ≤ 2)

theorem literal_primitive_square_frontier {M : ℕ} (hM : 0 < M) :
    (∑ p ∈ primitiveSquare M, 1/((p.1 : ℝ)*(p.2 : ℝ)*((p.1+p.2 : ℕ) : ℝ)))=
      2-squareTreeBoundary M ∧
    0 ≤ squareTreeBoundary M ∧ squareTreeBoundary M ≤ 2*((harmonic M : ℝ)+1)/(M : ℝ) :=
  ⟨primitive_square_tree_identity hM,squareTreeBoundary_bounds hM⟩

end NField.Alignment.CollisionPrimitiveSquareBoundary
