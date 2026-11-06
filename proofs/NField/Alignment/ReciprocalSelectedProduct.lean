/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalCoefficientBands

/-! # The selected reciprocal degrees yield a quadratic total saving -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalSelectedProduct
open scoped BigOperators
open RealKernelSaving ReciprocalPolynomialCoefficients ReciprocalCoefficientBands

def degreeEmbedding {m n : ℕ} (hm : 1 ≤ m) (hn : 4*m ≤ n) : Fin (2*m) ↪ Fin n where
  toFun i := ⟨2*m+i.val-1,by omega⟩
  inj' i j h := by
    have h' := congrArg Fin.val h
    apply Fin.ext
    dsimp at h'
    omega

def selected {m n : ℕ} (hm : 1 ≤ m) (hn : 4*m ≤ n) : Finset (Fin n) :=
  Finset.univ.map (degreeEmbedding hm hn)

theorem selected_degree_bounds {m n : ℕ} (hm : 1 ≤ m) (hn : 4*m ≤ n)
    (j : Fin n) (hj : j ∈ selected hm hn) : 2*m ≤ j.val+1 ∧ j.val+1 ≤ 4*m := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hj
  dsimp [degreeEmbedding]
  have := i.isLt
  omega

theorem selected_weight {m n : ℕ} (hm : 1 ≤ m) (hn : 4*m ≤ n) :
    4*(m:ℝ)^2 ≤ ∑ j ∈ selected hm hn, ((j.val:ℝ)+1) := by
  calc
    _ = ∑ _j ∈ selected hm hn, (2*(m:ℝ)) := by
      simp only [Finset.sum_const, selected, Finset.card_map, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,Nat.cast_ofNat]
      ring
    _ ≤ _ := Finset.sum_le_sum fun j hj => by
      exact_mod_cast (selected_degree_bounds hm hn j hj).1

theorem product_bound_of_selected {n : ℕ} (β : Fin n → ℝ) (K : Fin n → ℕ)
    (S : Finset (Fin n)) (L W : ℝ) (hL : 0 ≤ L)
    (hW : W ≤ ∑ j ∈ S, ((j.val:ℝ)+1))
    (hsel : ∀ j ∈ S, saving (β j) (K j) ≤ Real.exp (-((j.val:ℝ)+1)*L/512)) :
    (∏ j : Fin n, saving (β j) (K j)) ≤ Real.exp (-W*L/512) := by
  calc
    _ ≤ ∏ j ∈ S, saving (β j) (K j) :=
      Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _)
        (fun j _ => saving_nonneg _ _) (fun j _ _ => saving_le_one _ _)
    _ ≤ ∏ j ∈ S, Real.exp (-((j.val:ℝ)+1)*L/512) :=
      Finset.prod_le_prod (fun j _ => saving_nonneg _ _) hsel
    _ = Real.exp (-(∑ j ∈ S, ((j.val:ℝ)+1))*L/512) := by
      rw [← Real.exp_sum]
      rw [← Finset.sum_div, ← Finset.sum_mul, Finset.sum_neg_distrib]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem reciprocal_saving_product (Q x L ρ : ℝ) (hQ : 0 < Q) (hx : 0 < x)
    (hL : 0 ≤ L) (hρ : 3/2 ≤ ρ) (m : ℕ) (hm : 1 ≤ m)
    (hm0 : ρ ≤ m) (hm1 : (m:ℝ) ≤ ρ+1)
    (hQlog : Real.log Q = ρ*L)
    (hX0 : L ≤ Real.log x) (hX1 : Real.log x ≤ L+L/512)
    (hscale : Real.log 3 ≤ L/512)
    (s H n : ℕ) (hs : 1 ≤ s) (hH : 1 ≤ H) (hn : 4*m ≤ n)
    (hHlog : 123*L/256 ≤ Real.log (H:ℝ)) :
    (∏ j : Fin n, saving (coefficient Q x j) (s*H^(j.val+1))) ≤
      Real.exp (-(m:ℝ)^2*L/128) := by
  have h := product_bound_of_selected (coefficient Q x (n:=n))
    (fun j => s*H^(j.val+1)) (selected hm hn) L (4*(m:ℝ)^2) hL
    (selected_weight hm hn) (fun j hj =>
      coefficient_selected_saving Q x L ρ m hQ hx hL hρ hm0 hm1 hQlog hX0 hX1 hscale
        s H hs hH hHlog j
        (by exact_mod_cast (selected_degree_bounds hm hn j hj).1)
        (by exact_mod_cast (selected_degree_bounds hm hn j hj).2))
  convert h using 1 <;> congr 1 <;> ring

end NField.Alignment.ReciprocalSelectedProduct
