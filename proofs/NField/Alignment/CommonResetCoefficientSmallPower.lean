/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTripleGcd
import NField.Alignment.CommonResetNegativeCurvature

/-! # The printed small-power Fourier coefficient bound at signed integer indices -/

noncomputable section

namespace NField.Alignment.CommonResetCoefficientSmallPower

open CommonResetTripleGcd CommonResetNegativeCurvature InverseAdditiveCompletion

theorem integer_joint_gcd {q : ℕ} [NeZero q] (h n : ℤ) :
    jointGcd q (-(h : ZMod q)) (n : ZMod q) = (h.natAbs.gcd n.natAbs).gcd q := by
  rw [jointGcd, gcd_neg_val, integer_frequency_gcd, integer_frequency_gcd, gcd_pair_modulus]

/-- Title: `The literal Fourier coefficient has the printed epsilon bound with the gcd of both signed frequencies`. -/
theorem reciprocal_coefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (n h : ℤ),
      ‖(q : ℂ)⁻¹*ZMod.dft (inversePhase 1 (n : ZMod q)) (h : ZMod q)‖ ≤
        C*(q : ℝ)^(-1/2+ε)*Real.sqrt ((h.natAbs.gcd n.natAbs).gcd q : ℝ) := by
  obtain ⟨D, hD, hd⟩ := DivisorSmallPowerBound.divisor_count_small_power ε hε
  refine ⟨4*D, by positivity, ?_⟩
  intro q inst n h
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hs : Real.sqrt (q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hqR).ne'
  have hb := reciprocal_coefficient_joint_bound (n : ZMod q) (h : ZMod q)
  rw [integer_joint_gcd] at hb
  calc
    _ ≤ (4*Real.sqrt (q : ℝ)*q.divisors.card*
        Real.sqrt ((h.natAbs.gcd n.natAbs).gcd q : ℝ))/(q : ℝ) := hb
    _ ≤ (4*Real.sqrt (q : ℝ)*(D*(q : ℝ)^ε)*
        Real.sqrt ((h.natAbs.gcd n.natAbs).gcd q : ℝ))/(q : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hd q (NeZero.pos q)) (by positivity))
          (Real.sqrt_nonneg _)) hqR.le
    _ = _ := by
      rw [show (-1/2+ε : ℝ)=ε-1/2 by ring, Real.rpow_sub hqR, ← Real.sqrt_eq_rpow]
      have he := Real.sq_sqrt hqR.le
      field_simp
      rw [he]
      ring

theorem triple_gcd_root_le (q : ℕ) [NeZero q] (h n : ℤ) :
    Real.sqrt ((h.natAbs.gcd n.natAbs).gcd q : ℝ) ≤ Real.sqrt (n.natAbs.gcd q : ℝ) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_right n.natAbs (NeZero.pos q))
    (Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)) (Nat.gcd_dvd_right _ _))

end NField.Alignment.CommonResetCoefficientSmallPower
