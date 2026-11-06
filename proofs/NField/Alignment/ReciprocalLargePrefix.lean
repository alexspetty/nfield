/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReciprocalPolynomialDecay
import NField.Alignment.ReciprocalTaylorDecay
import NField.Alignment.ReciprocalBilinearApproximation

/-! # Unconditional reciprocal-prefix cancellation for large block logarithms -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalLargePrefix
open scoped BigOperators
open ReciprocalWeightedBlocks ReciprocalPolynomialDecay ReciprocalTaylorDecay
  ReciprocalParameterChoice ReciprocalMomentDeficit ReciprocalBilinearApproximation

theorem large_log_prefix_decay :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p M : ℕ) (Q ρ : ℝ),
      1 ≤ p → M ≤ p → 0 < Q → 4096 ≤ Real.log (p:ℝ) →
      3/2 ≤ ρ → Real.log Q = ρ*Real.log (p:ℝ) →
      ‖reciprocalPrefix p M Q‖ ≤ C*(p:ℝ)*
        Real.exp (-decayConstant*Real.log (p:ℝ)/(degreeScale ρ:ℝ)^2) := by
  obtain ⟨C,hC,hpoly⟩ := reciprocal_polynomial_decay
  refine ⟨C+10,by linarith,?_⟩
  intro p M Q ρ hp hM hQ hL hρ hlogQ
  let L := Real.log (p:ℝ)
  let H := shiftLength L
  let m := degreeScale ρ
  let D := Real.exp (-decayConstant*L/(m:ℝ)^2)
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  obtain ⟨hm,_,_⟩ := degreeScale_bounds ρ hρ
  obtain ⟨hH,_,_⟩ := shiftLength_bounds L hL
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hD0 : 0 < D := Real.exp_pos _
  have herr := small_error_decay L hL0 m hm
  have hpoint (i : ℕ) (hi : i ∈ Finset.range M) :
      ‖reciprocalBilinear Q ((p:ℝ)+i+1) H‖ ≤ (H:ℝ)^2*(C+8)*D := by
    have hi' : i < M := Finset.mem_range.mp hi
    have hxp : (p:ℝ) ≤ (p:ℝ)+i+1 := by linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    have hx3 : (p:ℝ)+i+1 ≤ 3*p := by
      have hiR : (i:ℝ)+1 ≤ p := by exact_mod_cast (show i+1 ≤ p by omega)
      linarith
    have hx0 : 0 < (p:ℝ)+i+1 := by positivity
    have hb := reciprocal_bilinear_approximation Q ((p:ℝ)+i+1) hQ.le hx0 H (degree m)
    have hpb := hpoly p Q ((p:ℝ)+i+1) L ρ hp0 hQ hL rfl hρ hlogQ hxp hx3
    have hr := reciprocal_remainder_decay p Q ((p:ℝ)+i+1) L ρ hp0 hQ hL rfl hlogQ hρ hxp
    have he : 2*Real.pi*(Q/((p:ℝ)+i+1)*((H:ℝ)^2/((p:ℝ)+i+1))^(degree m+1)) ≤ 8*D := by
      have ht := mul_le_mul_of_nonneg_left (hr.trans herr.1) (show 0 ≤ 2*Real.pi by positivity)
      have hp8 : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
      exact ht.trans (mul_le_mul_of_nonneg_right hp8 hD0.le)
    calc
      _ ≤ ‖RealPolynomialMomentBox.polynomialBilinear
          (ReciprocalPolynomialCoefficients.coefficient Q ((p:ℝ)+i+1) (n:=degree m)) H‖+
          (H:ℝ)^2*(2*Real.pi*(Q/((p:ℝ)+i+1)*((H:ℝ)^2/((p:ℝ)+i+1))^(degree m+1))) := hb
      _ ≤ (H:ℝ)^2*C*D+(H:ℝ)^2*(8*D) :=
        add_le_add hpb (mul_le_mul_of_nonneg_left he (sq_nonneg _))
      _ = _ := by ring
  have hsum : ‖∑ i ∈ Finset.range M, reciprocalBilinear Q ((p:ℝ)+i+1) H‖ ≤
      (p:ℝ)*(H:ℝ)^2*(C+8)*D := by
    calc
      _ ≤ ∑ i ∈ Finset.range M, ‖reciprocalBilinear Q ((p:ℝ)+i+1) H‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range M, (H:ℝ)^2*(C+8)*D := Finset.sum_le_sum hpoint
      _ = (M:ℝ)*((H:ℝ)^2*(C+8)*D) := by simp
      _ ≤ (p:ℝ)*((H:ℝ)^2*(C+8)*D) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hM)
        positivity
      _ = _ := by ring
  have hshift : (H:ℝ)^2 ≤ (p:ℝ)*D := by
    have hb := (shift_ratio_bound p L hp0 hL rfl).trans herr.2
    have h := (div_le_iff₀ hp0).mp hb
    simpa only [mul_comm] using h
  have hav := reciprocal_prefix_product_shifts p M H Q
  have hbound : (H:ℝ)^2*‖reciprocalPrefix p M Q‖ ≤
      (H:ℝ)^2*((C+10)*(p:ℝ)*D) := by
    calc
      _ ≤ ‖∑ i ∈ Finset.range M, reciprocalBilinear Q ((p:ℝ)+i+1) H‖+2*(H:ℝ)^4 := hav
      _ ≤ (p:ℝ)*(H:ℝ)^2*(C+8)*D+2*(H:ℝ)^4 := add_le_add hsum (le_refl _)
      _ ≤ (p:ℝ)*(H:ℝ)^2*(C+8)*D+2*(H:ℝ)^2*((p:ℝ)*D) := by
        have hh := mul_le_mul_of_nonneg_left hshift (show 0 ≤ 2*(H:ℝ)^2 by positivity)
        nlinarith
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hH0)).mp (by
    simpa only [mul_comm ((H:ℝ)^2)] using hbound)

end NField.Alignment.ReciprocalLargePrefix
