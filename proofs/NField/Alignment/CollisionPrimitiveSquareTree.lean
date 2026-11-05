/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimitiveMassDisplays

/-!
# Finite primitive square-tree cancellation

Every non-root primitive pair in the positive square has one internal
parent. The two child maps identify the strict upper and lower triangles.
Only outgoing child potentials remain after finite cancellation.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimitiveSquareTree

open scoped BigOperators Classical
open CollisionPrimitiveMassDisplays

def primitiveSquare (M : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun p => p.1.Coprime p.2)

def squareTreeBoundary (M : ℕ) : ℝ :=
  ∑ p ∈ (primitiveSquare M).filter (fun p => M < p.1+p.2),
    (pairTreePotential p.1 (p.1+p.2)+pairTreePotential (p.1+p.2) p.2)

theorem primitiveSquare_mem {M : ℕ} {p : ℕ×ℕ} : p ∈ primitiveSquare M ↔
    0 < p.1 ∧ p.1 ≤ M ∧ 0 < p.2 ∧ p.2 ≤ M ∧ p.1.Coprime p.2 := by
  simp [primitiveSquare,Finset.mem_product,Nat.succ_le_iff,and_assoc]

theorem primitiveSquare_root {M : ℕ} (hM : 0 < M) : (1,1) ∈ primitiveSquare M := by
  simp [primitiveSquare_mem,hM,Nat.succ_le_iff]

theorem square_left_child_sum (M : ℕ) :
    (∑ p ∈ (primitiveSquare M).filter (fun p => p.1+p.2 ≤ M),
      pairTreePotential p.1 (p.1+p.2))=
    ∑ p ∈ (primitiveSquare M).filter (fun p => p.1 < p.2),
      pairTreePotential p.1 p.2 := by
  apply Finset.sum_bij (fun p _ => (p.1,p.1+p.2))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hs⟩
    rcases primitiveSquare_mem.mp hp with ⟨ha,haM,hb,hbM,hcop⟩
    apply Finset.mem_filter.mpr
    refine ⟨primitiveSquare_mem.mpr ⟨ha,haM,by omega,hs,?_⟩,by dsimp; omega⟩
    simpa only [Nat.coprime_self_add_right] using hcop
  · intro p hp q hq he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> dsimp at * <;> omega
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hab⟩
    rcases primitiveSquare_mem.mp hp with ⟨ha,haM,hb,hbM,hcop⟩
    refine ⟨(p.1,p.2-p.1),?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨primitiveSquare_mem.mpr ⟨ha,haM,by omega,by omega,?_⟩,by dsimp; omega⟩
      exact (Nat.coprime_sub_self_right hab.le).mpr hcop
    · apply Prod.ext <;> dsimp
      omega
  · intro p hp
    rfl

theorem square_right_child_sum (M : ℕ) :
    (∑ p ∈ (primitiveSquare M).filter (fun p => p.1+p.2 ≤ M),
      pairTreePotential (p.1+p.2) p.2)=
    ∑ p ∈ (primitiveSquare M).filter (fun p => p.2 < p.1),
      pairTreePotential p.1 p.2 := by
  apply Finset.sum_bij (fun p _ => (p.1+p.2,p.2))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hs⟩
    rcases primitiveSquare_mem.mp hp with ⟨ha,haM,hb,hbM,hcop⟩
    apply Finset.mem_filter.mpr
    refine ⟨primitiveSquare_mem.mpr ⟨by omega,hs,hb,hbM,?_⟩,by dsimp; omega⟩
    exact Nat.coprime_add_self_left.mpr hcop
  · intro p hp q hq he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> dsimp at * <;> omega
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hba⟩
    rcases primitiveSquare_mem.mp hp with ⟨ha,haM,hb,hbM,hcop⟩
    refine ⟨(p.1-p.2,p.2),?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨primitiveSquare_mem.mpr ⟨by omega,by omega,hb,hbM,?_⟩,by dsimp; omega⟩
      exact (Nat.coprime_sub_self_left hba.le).mpr hcop
    · apply Prod.ext <;> dsimp
      omega
  · intro p hp
    rfl

theorem primitiveSquare_diagonal_root {M : ℕ} {p : ℕ×ℕ}
    (hp : p ∈ primitiveSquare M) (he : p.1=p.2) : p=(1,1) := by
  have hc := (primitiveSquare_mem.mp hp).2.2.2.2
  rw [he,Nat.coprime_self] at hc
  exact Prod.ext (he.trans hc) hc

theorem square_potential_root_split {M : ℕ} (hM : 0 < M) :
    (∑ p ∈ primitiveSquare M, pairTreePotential p.1 p.2)=2+
      (∑ p ∈ (primitiveSquare M).filter (fun p => p.1 < p.2), pairTreePotential p.1 p.2)+
      (∑ p ∈ (primitiveSquare M).filter (fun p => p.2 < p.1), pairTreePotential p.1 p.2) := by
  have hpoint : ∀ p ∈ primitiveSquare M, pairTreePotential p.1 p.2=
      (if p=(1,1) then (2 : ℝ) else 0)+
      (if p.1 < p.2 then pairTreePotential p.1 p.2 else 0)+
      (if p.2 < p.1 then pairTreePotential p.1 p.2 else 0) := by
    intro p hp
    rcases lt_trichotomy p.1 p.2 with hl|he|hr
    · have hn : p ≠ (1,1) := by intro h; subst p; simp at hl
      simp [hn,hl,not_lt_of_ge hl.le]
    · have hroot := primitiveSquare_diagonal_root hp he
      subst p
      norm_num [pairTreePotential]
    · have hn : p ≠ (1,1) := by intro h; subst p; simp at hr
      simp [hn,hr,not_lt_of_ge hr.le]
  rw [Finset.sum_congr rfl hpoint]
  simp [Finset.sum_add_distrib,Finset.sum_filter,primitiveSquare_root hM]

theorem primitive_square_tree_identity {M : ℕ} (hM : 0 < M) :
    (∑ p ∈ primitiveSquare M, 1/((p.1 : ℝ)*(p.2 : ℝ)*((p.1+p.2 : ℕ) : ℝ)))=
      2-squareTreeBoundary M := by
  have hmass : (∑ p ∈ primitiveSquare M,
      1/((p.1 : ℝ)*(p.2 : ℝ)*((p.1+p.2 : ℕ) : ℝ)))=
      (∑ p ∈ primitiveSquare M, pairTreePotential p.1 p.2)-
      (∑ p ∈ primitiveSquare M,
        (pairTreePotential p.1 (p.1+p.2)+pairTreePotential (p.1+p.2) p.2)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rcases primitiveSquare_mem.mp hp with ⟨ha,haM,hb,hbM,hcop⟩
    rw [← pairTreePotential_conservation ha hb]
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not (primitiveSquare M)
    (fun p : ℕ×ℕ => p.1+p.2 ≤ M)
    (fun p => pairTreePotential p.1 (p.1+p.2)+pairTreePotential (p.1+p.2) p.2)
  simp only [not_le] at hsplit
  rw [Finset.sum_add_distrib,square_left_child_sum,square_right_child_sum] at hsplit
  rw [hmass,square_potential_root_split hM,← hsplit]
  unfold squareTreeBoundary
  ring

end NField.Alignment.CollisionPrimitiveSquareTree
