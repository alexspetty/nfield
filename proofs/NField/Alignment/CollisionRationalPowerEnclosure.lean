/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRationalLogKernel
import NField.Alignment.CollisionFourierEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionRationalPowerEnclosure
open scoped BigOperators
open CollisionRationalFourierKernel CollisionFourierEnclosure

def realExpPolynomial (x : ℝ) : ℝ := ∑ m ∈ Finset.range 24, x^m/(m.factorial : ℝ)

theorem realExpPolynomial_complex (x : ℝ) :
    (realExpPolynomial x : ℂ)=expPolynomial (x : ℂ) := by
  simp [realExpPolynomial,expPolynomial]

theorem realExpPolynomial_error {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x-realExpPolynomial x| ≤ taylorError := by
  have h := expPolynomial_error (z := (x : ℂ)) (by simpa using hx)
  rw [← realExpPolynomial_complex,← Complex.ofReal_exp,← Complex.ofReal_sub] at h
  simpa only [Complex.norm_real,Real.norm_eq_abs] using h

theorem small_exp_enclosure {x a b : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) :
    max 1 (realExpPolynomial a-taylorError) ≤ Real.exp x ∧
      Real.exp x ≤ realExpPolynomial b+taylorError := by
  have hab := hx.1.trans hx.2
  have hal := abs_le.mpr (show -1 ≤ a ∧ a ≤ 1 by constructor <;> linarith)
  have hbl := abs_le.mpr (show -1 ≤ b ∧ b ≤ 1 by constructor <;> linarith)
  have he1 := abs_le.mp (realExpPolynomial_error hal)
  have he2 := abs_le.mp (realExpPolynomial_error hbl)
  have hl := Real.exp_le_exp.mpr hx.1
  have hu := Real.exp_le_exp.mpr hx.2
  constructor
  · exact max_le ((Real.one_le_exp_iff).mpr (ha0.trans hx.1)) (by linarith)
  · linarith

theorem gridLower_nonneg {x grid : ℝ} (hx : 0 ≤ x) (hg : 0 < grid) :
    0 ≤ gridLower x grid := by
  unfold gridLower
  apply div_nonneg _ hg.le
  exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg hg.le hx))

theorem rounded_exp_enclosure {x a b grid : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hg : 0 < grid) :
    gridLower (max 1 (realExpPolynomial a-taylorError)) grid ≤ Real.exp x ∧
      Real.exp x ≤ gridUpper (realExpPolynomial b+taylorError) grid := by
  have h := small_exp_enclosure hx ha0 hb1
  exact ⟨(grid_outward hg).1.trans h.1,h.2.trans (grid_outward hg).2⟩

theorem square_exp_enclosure {x l u : ℝ} (hl : 0 ≤ l)
    (hx : l ≤ Real.exp x ∧ Real.exp x ≤ u) :
    l^2 ≤ Real.exp (2*x) ∧ Real.exp (2*x) ≤ u^2 := by
  rw [show Real.exp (2*x)=(Real.exp x)^2 by
    simpa using Real.exp_nat_mul x 2]
  exact ⟨(sq_le_sq₀ hl (Real.exp_pos x).le).mpr hx.1,
    (sq_le_sq₀ (Real.exp_pos x).le ((Real.exp_pos x).le.trans hx.2)).mpr hx.2⟩

theorem rounded_square_exp_enclosure {x l u grid : ℝ} (hl : 0 ≤ l)
    (hx : l ≤ Real.exp x ∧ Real.exp x ≤ u) (hg : 0 < grid) :
    gridLower (l^2) grid ≤ Real.exp (2*x) ∧
      Real.exp (2*x) ≤ gridUpper (u^2) grid := by
  have h := square_exp_enclosure hl hx
  exact ⟨(grid_outward hg).1.trans h.1,h.2.trans (grid_outward hg).2⟩

theorem negative_power_exp {n s : ℝ} (hn : 0 < n) :
    n^(-s)=1/Real.exp (s*Real.log n) := by
  rw [Real.rpow_neg hn.le,Real.rpow_def_of_pos hn,mul_comm,one_div]

theorem negative_nat_power {n : ℝ} (hn : 0 < n) (k : ℕ) :
    n^(-(k : ℝ))=1/n^k := by
  rw [Real.rpow_neg hn.le,Real.rpow_natCast,one_div]

theorem negative_power_enclosure {n s l u : ℝ} (hn : 0 < n) (hl : 0 < l)
    (hx : l ≤ Real.exp (s*Real.log n) ∧ Real.exp (s*Real.log n) ≤ u) :
    1/u ≤ n^(-s) ∧ n^(-s) ≤ 1/l := by
  rw [negative_power_exp hn]
  exact reciprocal_interval hl hx

def expLower (a grid : ℝ) : ℕ → ℝ
  | 0 => max 1 (gridLower (max 1 (realExpPolynomial a-taylorError)) grid)
  | k+1 => max 1 (gridLower ((expLower a grid k)^2) grid)

def expUpper (b grid : ℝ) : ℕ → ℝ
  | 0 => gridUpper (realExpPolynomial b+taylorError) grid
  | k+1 => gridUpper ((expUpper b grid k)^2) grid

theorem expLower_one_le (a grid : ℝ) (k : ℕ) : 1 ≤ expLower a grid k := by
  cases k <;> exact le_max_left _ _

theorem iterated_exp_enclosure {x a b grid : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hg : 0 < grid) (k : ℕ) :
    expLower a grid k ≤ Real.exp ((2 : ℝ)^k*x) ∧
      Real.exp ((2 : ℝ)^k*x) ≤ expUpper b grid k := by
  induction k with
  | zero =>
    have h := rounded_exp_enclosure hx ha0 hb1 hg
    simp only [pow_zero,one_mul,expLower,expUpper]
    exact ⟨max_le (Real.one_le_exp_iff.mpr (ha0.trans hx.1)) h.1,h.2⟩
  | succ k ih =>
    have hl : 0 ≤ expLower a grid k := (by norm_num : (0 : ℝ) ≤ 1).trans
      (expLower_one_le a grid k)
    have h := rounded_square_exp_enclosure hl ih hg
    have hx0 : 0 ≤ (2 : ℝ)^(k+1)*x := mul_nonneg (by positivity) (ha0.trans hx.1)
    have he : (2 : ℝ)^(k+1)*x=2*((2 : ℝ)^k*x) := by rw [pow_succ]; ring
    simp only [expLower,expUpper]
    rw [← he] at h
    exact ⟨max_le (Real.one_le_exp_iff.mpr hx0) h.1,h.2⟩

theorem logarithmic_power_enclosure {n s ll lh grid : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hll : 0 ≤ ll)
    (hlog : ll ≤ Real.log n ∧ Real.log n ≤ lh)
    (hscale : s*lh ≤ 128) (hg : 0 < grid) :
    1/expUpper (s*lh/128) grid 7 ≤ n^(-s) ∧
      n^(-s) ≤ 1/expLower (s*ll/128) grid 7 := by
  have hx : s*ll/128 ≤ s*Real.log n/128 ∧ s*Real.log n/128 ≤ s*lh/128 :=
    ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog.1 hs) (by norm_num),
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog.2 hs) (by norm_num)⟩
  have h := iterated_exp_enclosure hx (by positivity)
    (by linarith : s*lh/128 ≤ 1) hg 7
  have he : (2 : ℝ)^7*(s*Real.log n/128)=s*Real.log n := by norm_num; ring
  rw [he] at h
  exact negative_power_enclosure hn
    ((by norm_num : (0 : ℝ) < 1).trans_le (expLower_one_le _ _ _)) h

theorem logarithmic_power_rounded_enclosure {n s ll lh grid outputGrid : ℝ}
    (hn : 0 < n) (hs : 0 ≤ s) (hll : 0 ≤ ll)
    (hlog : ll ≤ Real.log n ∧ Real.log n ≤ lh)
    (hscale : s*lh ≤ 128) (hg : 0 < grid) (ho : 0 < outputGrid) :
    gridLower (1/expUpper (s*lh/128) grid 7) outputGrid ≤ n^(-s) ∧
      n^(-s) ≤ gridUpper (1/expLower (s*ll/128) grid 7) outputGrid := by
  have h := logarithmic_power_enclosure hn hs hll hlog hscale hg
  exact ⟨(grid_outward ho).1.trans h.1,h.2.trans (grid_outward ho).2⟩

end NField.Alignment.CollisionRationalPowerEnclosure
