/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLimitingPrimeLogSum

/-!
# Log-square asymptotics and uniformly bounded remainders

These transfer lemmas retain an explicit additive error and its cutoff.
They will be applied to the actual reset and alignment Euler identities.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLogSquareAsymptotic

open Filter Asymptotics CollisionLimitingPrimeLogSum

theorem constant_isLittleO_log_square_nat (c : ℝ) :
    (fun _ : ℕ => c) =o[atTop] (fun m : ℕ => (Real.log m)^2) := by
  have h := ((constant_isLittleO_log 1).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).pow (by norm_num : 0 < (2 : ℕ))
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun m : ℕ => (Real.log m)^2) := by simpa using h
  simpa only [mul_one] using h1.const_mul_left c

theorem asymptotic_of_uniform_log_square_error {f g : ℕ → ℝ} {c B : ℝ} (hc : c ≠ 0)
    (hg : g ~[atTop] (fun m : ℕ => c*(Real.log m)^2))
    (herr : ∀ m, 1 ≤ m → |f m-g m| ≤ B) :
    f ~[atTop] (fun m : ℕ => c*(Real.log m)^2) := by
  have hO : (fun m : ℕ => f m-g m) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply isBigO_iff.mpr
    refine ⟨B,?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    simpa only [Real.norm_eq_abs,abs_one,mul_one] using herr m hm
  have he : (fun m : ℕ => f m-g m) =o[atTop] (fun m : ℕ => c*(Real.log m)^2) :=
    hO.trans_isLittleO ((constant_isLittleO_log_square_nat 1).const_mul_right hc)
  have h := hg.add_isLittleO he
  convert! h using 1
  funext m
  dsimp only [Pi.add_apply]
  ring

theorem euler_main_log_square_asymptotic {P S : ℕ → ℝ} {c : ℝ}
    (hP : P ~[atTop] (fun m : ℕ => c*Real.log m))
    (hS : S ~[atTop] (fun m : ℕ => Real.log m)) :
    (fun m : ℕ => P m*(Real.eulerMascheroniConstant+S m)) ~[atTop]
      (fun m : ℕ => c*(Real.log m)^2) := by
  have hgamma := (constant_isLittleO_log Real.eulerMascheroniConstant).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hS' : (fun m : ℕ => Real.eulerMascheroniConstant+S m) ~[atTop]
      (fun m : ℕ => Real.log m) := by
    have h := hS.add_isLittleO hgamma
    convert! h using 1
    funext m
    dsimp only [Pi.add_apply,Function.comp_apply]
    ring
  have h := hP.mul hS'
  convert! h using 1
  funext m
  dsimp only [Pi.mul_apply]
  ring

theorem shifted_uniform_error_bound {x a g B : ℝ} (h : |x-(a-g)| ≤ B) :
    |x-a| ≤ B+|g| := by
  have ht := abs_sub_le x (a-g) a
  have he : |(a-g)-a|=|g| := by rw [show (a-g)-a=-g by ring,abs_neg]
  rw [he] at ht
  linarith

theorem scaled_alignment_error_bound {C a g B : ℝ} (h : |3*C+1-(a-g)| ≤ B) :
    |C-a/3| ≤ (B+|g+1|)/3 := by
  have he : C-a/3=((3*C+1-(a-g))-(g+1))/3 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have ht : |(3*C+1-(a-g))-(g+1)| ≤ |3*C+1-(a-g)|+|g+1| := abs_sub _ _
  exact div_le_div_of_nonneg_right (ht.trans (add_le_add h le_rfl)) (by norm_num)

end NField.Alignment.CollisionLogSquareAsymptotic
