/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalPolynomialCoefficients
import NField.Alignment.FiniteShiftAveraging

/-! # Exact product-shift approximation of the real reciprocal phase -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalBilinearApproximation
open scoped BigOperators
open RealPolynomialMomentBox RealReciprocalTaylor ReciprocalPolynomialCoefficients
  FiniteShiftAveraging

abbrev ShiftIndex (H : ℕ) := {a // a ∈ Finset.Icc 1 (H:ℤ)}

theorem shiftIndex_card (H : ℕ) : Fintype.card (ShiftIndex H) = H := by
  simp only [ShiftIndex,Fintype.card_coe,Int.card_Icc,add_sub_cancel_right,Int.toNat_natCast]

theorem shiftProduct_bounds (H : ℕ) (a b : ShiftIndex H) :
    0 ≤ a.val*b.val ∧ a.val*b.val ≤ (H:ℤ)^2 := by
  have ha := Finset.mem_Icc.mp a.property
  have hb := Finset.mem_Icc.mp b.property
  exact ⟨mul_nonneg (by omega) (by omega), by nlinarith⟩

def reciprocalBilinear (Q x : ℝ) (H : ℕ) : ℂ :=
  ∑ a : ShiftIndex H, ∑ b : ShiftIndex H,
    realCharacter (Q/(x+((a.val*b.val:ℤ):ℝ)))

theorem reciprocal_bilinear_approximation (Q x : ℝ) (hQ : 0 ≤ Q) (hx : 0 < x)
    (H n : ℕ) :
    ‖reciprocalBilinear Q x H‖ ≤
      ‖polynomialBilinear (coefficient Q x (n:=n)) H‖+
        (H:ℝ)^2*(2*Real.pi*(Q/x*((H:ℝ)^2/x)^(n+1))) := by
  let T := ∑ a : ShiftIndex H, ∑ b : ShiftIndex H,
    realCharacter (reciprocalTaylor Q x ((a.val*b.val:ℤ):ℝ) n)
  have herr (a b : ShiftIndex H) :
      ‖realCharacter (Q/(x+((a.val*b.val:ℤ):ℝ)))-
        realCharacter (reciprocalTaylor Q x ((a.val*b.val:ℤ):ℝ) n)‖ ≤
      2*Real.pi*(Q/x*((H:ℝ)^2/x)^(n+1)) := by
    obtain ⟨hz0,hz⟩ := shiftProduct_bounds H a b
    have hz0R : (0:ℝ) ≤ ((a.val*b.val:ℤ):ℝ) := by exact_mod_cast hz0
    have hzR : (((a.val*b.val:ℤ):ℝ)) ≤ (H:ℝ)^2 := by exact_mod_cast hz
    apply (reciprocal_phase_taylor_bound Q x _ hQ hx hz0R n).trans
    gcongr
  have herror : ‖reciprocalBilinear Q x H-T‖ ≤
      (H:ℝ)^2*(2*Real.pi*(Q/x*((H:ℝ)^2/x)^(n+1))) := by
    simp only [reciprocalBilinear,T,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ a : ShiftIndex H, ∑ b : ShiftIndex H,
          ‖realCharacter (Q/(x+((a.val*b.val:ℤ):ℝ)))-
            realCharacter (reciprocalTaylor Q x ((a.val*b.val:ℤ):ℝ) n)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : ShiftIndex H, ∑ _b : ShiftIndex H,
          2*Real.pi*(Q/x*((H:ℝ)^2/x)^(n+1)) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => herr a b
      _ = _ := by simp [shiftIndex_card]; ring
  have he : ‖T‖ = ‖polynomialBilinear (coefficient Q x (n:=n)) H‖ :=
    taylor_bilinear_norm Q x H n
  have h := norm_le_norm_add_norm_sub T (reciprocalBilinear Q x H)
  rw [norm_sub_rev] at herror
  exact (h.trans (add_le_add (le_refl _) herror)).trans_eq (by rw [he])

theorem reciprocal_prefix_product_shifts (p M H : ℕ) (Q : ℝ) :
    (H:ℝ)^2*‖ReciprocalWeightedBlocks.reciprocalPrefix p M Q‖ ≤
      ‖∑ i ∈ Finset.range M, reciprocalBilinear Q ((p:ℝ)+i+1) H‖+2*(H:ℝ)^4 := by
  let f := fun i : ℕ => realCharacter (Q/((p:ℝ)+i+1))
  have hf (i : ℕ) : ‖f i‖ ≤ 1 := (realCharacter_norm _).le
  let h := fun a : ShiftIndex H × ShiftIndex H => (a.1.val*a.2.val).toNat
  have hh (a : ShiftIndex H × ShiftIndex H) : (h a:ℝ) ≤ (H:ℝ)^2 := by
    have hz := shiftProduct_bounds H a.1 a.2
    have he : ((h a:ℕ):ℤ) = a.1.val*a.2.val := Int.toNat_of_nonneg hz.1
    exact_mod_cast he ▸ hz.2
  have hav := average_shift_bound f hf M h ((H:ℝ)^2) hh
  have hcard : Fintype.card (ShiftIndex H × ShiftIndex H) = H^2 := by
    rw [Fintype.card_prod,shiftIndex_card]
    ring
  rw [hcard] at hav
  have hfS : (∑ i ∈ Finset.range M, f i) =
      ReciprocalWeightedBlocks.reciprocalPrefix p M Q := by
    unfold ReciprocalWeightedBlocks.reciprocalPrefix
      ReciprocalWeightedBlocks.reciprocalPhase
    simp only [f,realCharacter,AddChar.coe_mk,Nat.cast_add,Nat.cast_one]
  rw [hfS] at hav
  have hs (i : ℕ) : (∑ a : ShiftIndex H × ShiftIndex H, f (i+h a)) =
      reciprocalBilinear Q ((p:ℝ)+i+1) H := by
    rw [Fintype.sum_prod_type]
    unfold reciprocalBilinear
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have he : (((a.val*b.val).toNat:ℕ):ℝ) = ((a.val*b.val:ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (shiftProduct_bounds H a b).1
    dsimp [f,h]
    push_cast
    rw [he]
    push_cast
    congr 2
    ring
  simp_rw [hs] at hav
  push_cast at hav
  convert hav using 1 <;> ring

end NField.Alignment.ReciprocalBilinearApproximation
