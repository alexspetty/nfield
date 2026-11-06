/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetCompletedDerivative
import NField.Alignment.CommonResetFrequencies

/-! # Exact inverse reciprocity with arbitrary signed integer phase numerator -/

noncomputable section

namespace NField.Alignment.CommonResetInverseReciprocity

open scoped BigOperators
open CommonResetDerivativeFirst CommonResetCompletedDerivative DedekindInverseResidueTransform
open InverseAdditiveCompletion

theorem inverse_residue_mul {n q : ℕ} (hq : 0 < q) (hn : n.Coprime q) :
    (n : ZMod q)*(inverseResidue n q : ZMod q) = 1 := by
  letI : NeZero q := ⟨hq.ne'⟩
  unfold inverseResidue
  rw [dif_neg hq.ne', dif_pos hn]
  simp [ZMod.coe_unitOfCoprime]

theorem coprime_integer_product_dvd {u t : ℕ} (hut : u.Coprime t) {D : ℤ}
    (huD : (u : ℤ) ∣ D) (htD : (t : ℤ) ∣ D) : (u : ℤ)*(t : ℤ) ∣ D := by
  have hu : u ∣ D.natAbs := by exact_mod_cast Int.dvd_natAbs.mpr huD
  have ht : t ∣ D.natAbs := by exact_mod_cast Int.dvd_natAbs.mpr htD
  have hh := hut.mul_dvd_of_dvd_of_dvd hu ht
  have hi : (u : ℤ)*(t : ℤ) ∣ (D.natAbs : ℤ) := by exact_mod_cast hh
  exact Int.dvd_natAbs.mp hi

theorem inverse_reciprocity_integer {u t : ℕ} (hu : 0 < u) (ht : 0 < t)
    (hut : u.Coprime t) :
    ∃ k : ℤ, (u : ℤ)*inverseResidue u t+(t : ℤ)*inverseResidue t u-1 = (u : ℤ)*t*k := by
  let D : ℤ := (u : ℤ)*inverseResidue u t+(t : ℤ)*inverseResidue t u-1
  have hdT : (t : ℤ) ∣ D := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd D t).mp
    dsimp [D]
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, inverse_residue_mul ht hut, sub_self]
  have hdU : (u : ℤ) ∣ D := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd D u).mp
    dsimp [D]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add, inverse_residue_mul hu hut.symm, sub_self]
  exact coprime_integer_product_dvd hut hdU hdT

/-- Title: `Inverse reciprocity preserves the full reciprocal phase including modulus one`. -/
theorem inverse_phase_reciprocity {u t : ℕ} (hu : 0 < u) (ht : 0 < t)
    (hut : u.Coprime t) (n : ℤ) (shift : ℝ) :
    phase ((n : ℝ)*inverseResidue u t/(t : ℝ)+shift/t) =
      phase (-(n : ℝ)*inverseResidue t u/(u : ℝ)+((n : ℝ)/u+shift)/t) := by
  obtain ⟨k, hk⟩ := inverse_reciprocity_integer hu ht hut
  have hkR : (u : ℝ)*inverseResidue u t+(t : ℝ)*inverseResidue t u-1 = (u : ℝ)*t*k := by
    exact_mod_cast hk
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have he : (n : ℝ)*inverseResidue u t/(t : ℝ)+shift/t =
      (-(n : ℝ)*inverseResidue t u/(u : ℝ)+((n : ℝ)/u+shift)/t) + ((n*k : ℤ) : ℝ) := by
    push_cast
    field_simp
    linear_combination (n : ℝ)*hkR
  rw [he, phase_add, phase_int, mul_one]

theorem inversePhase_nat_eq_phase {u t : ℕ} [NeZero u] (htu : t.Coprime u) (n : ℤ) :
    inversePhase 1 (-n : ZMod u) (t : ZMod u) =
      phase (-(n : ℝ)*inverseResidue t u/(u : ℝ)) := by
  rw [inverse_phase_natCast, dif_pos htu]
  simp only [Nat.cast_one, one_mul]
  have he : (ZMod.unitOfCoprime t htu)⁻¹.val = (inverseResidue t u : ZMod u) := by
    unfold inverseResidue
    rw [dif_neg (NeZero.ne u), dif_pos htu, ZMod.natCast_zmod_val]
  rw [he]
  have harg : (-n : ZMod u)*(inverseResidue t u : ZMod u) =
      ((-n*(inverseResidue t u : ℤ) : ℤ) : ZMod u) := by push_cast; rfl
  rw [harg, integer_character_phase]
  congr 1
  push_cast
  ring

/-- Title: `The original inverse phase is exactly the completed reciprocal factor times its smooth phase`. -/
theorem inverse_reciprocity_completion {u t : ℕ} [NeZero u] (ht : 0 < t)
    (hut : u.Coprime t) (n : ℤ) (shift : ℝ) :
    phase ((n : ℝ)*inverseResidue u t/(t : ℝ)+shift/t) =
      inversePhase 1 (-n : ZMod u) (t : ZMod u)*phase (((n : ℝ)/u+shift)/t) := by
  rw [inverse_phase_reciprocity (NeZero.pos u) ht hut, phase_add,
    inversePhase_nat_eq_phase hut.symm]

theorem phase_im (x : ℝ) : (phase x).im = Real.sin (2*Real.pi*x) := by
  rw [phase_exp, Complex.exp_ofReal_mul_I_im]

end NField.Alignment.CommonResetInverseReciprocity
