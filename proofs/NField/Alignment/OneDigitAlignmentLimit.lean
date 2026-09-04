/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Golden.Threshold

/-!
# Monotonicity and limit of the one-digit alignment profile
-/

namespace NField.Alignment

open Filter NField.Golden

/-- Real interpolation of the exact one-digit alignment formula. -/
noncomputable def oneDigitAlignmentProfile (p : ℕ) (x : ℝ) : ℝ :=
  (x * 2 - 1) / (x * (p : ℝ) - 1)

theorem oneDigitAlignmentProfile_three_deriv_eq {x : ℝ}
    (hden : 3 * x - 1 ≠ 0) :
    deriv (oneDigitAlignmentProfile 3) x =
      1 / (3 * x - 1) ^ 2 := by
  change deriv ((fun y : ℝ => (y * 2 - 1) / (y * 3 - 1))) x =
    1 / (3 * x - 1) ^ 2
  have hden' : x * 3 - 1 ≠ 0 := by simpa [mul_comm] using hden
  have hraw := (((hasDerivAt_id x).mul_const 2).sub_const 1).div
    (((hasDerivAt_id x).mul_const 3).sub_const 1) hden'
  have hderiv :
      (2 * (x * 3 - 1) - (x * 2 - 1) * 3) /
          (x * 3 - 1) ^ 2 = 1 / (3 * x - 1) ^ 2 := by
    field_simp [hden, hden']
    ring
  simp only [id_eq, one_mul] at hraw
  rw [hderiv] at hraw
  have hderivative := hraw.deriv
  exact hderivative

/-- The derivative displayed in the manuscript is strictly positive on the
positive-resolution domain. -/
theorem oneDigitAlignmentProfile_three_deriv_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < deriv (oneDigitAlignmentProfile 3) x := by
  have hden : 3 * x - 1 ≠ 0 := by nlinarith
  rw [oneDigitAlignmentProfile_three_deriv_eq hden]
  positivity

/-- The integer alignment values for prime three are strictly increasing. -/
theorem alignmentFormulaReal_three_strictMonoOn :
    StrictMonoOn (alignmentFormulaReal 3) (Set.Ici 1) := by
  intro m hm n hn hmn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hmden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  have hnden : 0 < (3 : ℝ) * n - 1 := by nlinarith
  rw [alignmentFormulaReal]
  apply (div_lt_div_iff₀ hmden hnden).2
  nlinarith

theorem alignmentFormulaReal_three_below_limit {m : ℕ} (hm : 1 ≤ m) :
    alignmentFormulaReal 3 m < (2 : ℝ) / 3 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  rw [alignmentFormulaReal]
  apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 3)).2
  nlinarith

theorem alignmentFormulaReal_three_correction (m : ℕ) :
    alignmentFormulaReal 3 m =
      (2 : ℝ) / 3 - 1 / (3 * (3 * (m : ℝ) - 1)) := by
  cases m with
  | zero => norm_num [alignmentFormulaReal]
  | succ m =>
      let x : ℝ := (m.succ : ℕ)
      have hm : (1 : ℝ) ≤ x := by
        dsimp [x]
        exact_mod_cast m.succ_pos
      have hden : 3 * x - 1 ≠ 0 := by nlinarith
      have hden' : -1 + x * 3 ≠ 0 := by nlinarith
      change (2 * x - 1) / (3 * x - 1) =
        (2 : ℝ) / 3 - 1 / (3 * (3 * x - 1))
      apply (div_eq_iff hden).2
      field_simp [hden, hden']
      have hinverse : (-1 + x * 3)⁻¹ * (-1 + x * 3) = 1 :=
        inv_mul_cancel₀ hden'
      ring_nf at hinverse ⊢
      nlinarith

/-- The exact alignment tends to `2/3` as the supported resolution grows.
The unrestricted natural-number limit is stronger than the manuscript's
restriction to any unbounded supported subsequence. -/
theorem alignmentFormulaReal_three_tendsto :
    Tendsto (alignmentFormulaReal 3) atTop (nhds ((2 : ℝ) / 3)) := by
  have hlinear : Tendsto (fun m : ℕ => (3 : ℝ) * (m : ℝ) - 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1)
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hden : Tendsto (fun m : ℕ => (3 : ℝ) * (3 * (m : ℝ) - 1))
      atTop atTop := hlinear.const_mul_atTop (by norm_num)
  have hcorrection : Tendsto
      (fun m : ℕ => (1 : ℝ) / (3 * (3 * (m : ℝ) - 1)))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hconstant : Tendsto (fun _ : ℕ => (2 : ℝ) / 3)
      atTop (nhds ((2 : ℝ) / 3)) := tendsto_const_nhds
  have hlimit : Tendsto
      (fun m : ℕ => (2 : ℝ) / 3 - 1 / (3 * (3 * (m : ℝ) - 1)))
      atTop (nhds ((2 : ℝ) / 3)) := by
    simpa using hconstant.sub hcorrection
  exact hlimit.congr' (Filter.Eventually.of_forall fun m =>
    (alignmentFormulaReal_three_correction m).symm)

/-- The manuscript's literal decimal-supported subsequence already tends to
`2/3`; every term uses the supported denominator `10^D`. -/
theorem alignmentFormulaReal_three_tendsto_along_decimal_powers :
    Tendsto (fun D : ℕ => alignmentFormulaReal 3 (10 ^ D)) atTop
      (nhds ((2 : ℝ) / 3)) :=
  alignmentFormulaReal_three_tendsto.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (10 : ℕ)))

end NField.Alignment
