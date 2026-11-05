/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicRemainder
import NField.Alignment.CollisionZetaMoments

/-!
# Uniform harmonic-seed expansion with its strict remainder

The harmonic error is summed over positive multiples. Absolute convergence
and the exact zeta-four bound precede the expansion of the infinite seed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicSeedExpansion

open scoped BigOperators Classical
open CollisionAmplitudeArithmetic CollisionHarmonicSeed CollisionZetaMoments
open CollisionHarmonicRemainder

def seedErrorTerm (q m : ℕ) : ℝ :=
  harmonicError (q*(m+1))/((q*(m+1) : ℕ) : ℝ)^2
def seedError (q : ℕ) : ℝ := ∑' m, seedErrorTerm q m

theorem seedErrorTerm_bounds {q : ℕ} (hq : 0<q) (m : ℕ) :
    -(powerKernel 4 (q*(m+1))/12)<seedErrorTerm q m ∧ seedErrorTerm q m<0 := by
  have hk : 1≤q*(m+1) := Nat.mul_pos hq (Nat.succ_pos m)
  have hkR : 0<((q*(m+1) : ℕ) : ℝ) := by exact_mod_cast hk
  have he := harmonicError_bounds hk
  constructor
  · have hh := div_lt_div_of_pos_right he.1 (sq_pos_of_pos hkR)
    unfold seedErrorTerm
    convert! hh using 1
    unfold powerKernel
    field_simp
  · exact div_neg_of_neg_of_pos he.2 (sq_pos_of_pos hkR)

theorem seedErrorTerm_norm_bound {q : ℕ} (hq : 0<q) (m : ℕ) :
    ‖seedErrorTerm q m‖<powerKernel 4 (q*(m+1))/12 := by
  have he := seedErrorTerm_bounds hq m
  rw [Real.norm_eq_abs,abs_of_neg he.2]
  linarith

theorem seedErrorTerm_summable {q : ℕ} (hq : 0<q) : Summable (seedErrorTerm q) :=
  Summable.of_norm_bounded
    ((powerKernel_positive_multiple_hasSum (by norm_num : 1<(4 : ℕ)) q).summable.div_const 12)
    (fun m => (seedErrorTerm_norm_bound hq m).le)

theorem seedError_bounds {q : ℕ} (hq : 0<q) :
    -(zetaNat 4/(12*(q : ℝ)^4))<seedError q ∧ seedError q<0 := by
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hs := seedErrorTerm_summable hq
  have hb := ((powerKernel_positive_multiple_hasSum (by norm_num : 1<(4 : ℕ)) q).div_const 12).neg
  have hl := Summable.tsum_lt_tsum
    (fun m => (seedErrorTerm_bounds hq m).1.le) (seedErrorTerm_bounds hq 0).1 hb.summable hs
  have hu := Summable.tsum_lt_tsum
    (fun m => (seedErrorTerm_bounds hq m).2.le) (seedErrorTerm_bounds hq 0).2 hs summable_zero
  rw [hb.tsum_eq] at hl
  constructor
  · convert! hl using 1
    field_simp
  · simp only [tsum_zero] at hu
    convert! hu using 1

theorem logSquareTerm_positive_hasSum :
    HasSum (fun m => logSquareTerm (m+1)) logSquareMoment := by
  have hs := logSquareTerm_summable
  have he := hs.sum_add_tsum_nat_add 1
  have ht : (∑' m, logSquareTerm (m+1))=logSquareMoment := by
    simpa [logSquareTerm,logSquareMoment] using he
  rw [← ht]
  exact (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)).hasSum

theorem harmonicKernel_expansion {q : ℕ} (hq : 0<q) (m : ℕ) :
    harmonicKernel (q*(m+1))=
      ((Real.log q+Real.eulerMascheroniConstant)/(q : ℝ)^2)*powerKernel 2 (m+1)+
      (1/(q : ℝ)^2)*logSquareTerm (m+1)-
      (1/(2*(q : ℝ)^3))*powerKernel 3 (m+1)+seedErrorTerm q m := by
  have hk : 1≤q*(m+1) := Nat.mul_pos hq (Nat.succ_pos m)
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hmR : ((m+1 : ℕ) : ℝ)≠0 := by positivity
  have he := (strict_harmonic_remainder hk).1
  unfold harmonicKernel seedErrorTerm powerKernel logSquareTerm
  rw [he]
  push_cast
  rw [Real.log_mul hqR (by positivity : (m : ℝ)+1≠0)]
  field_simp
  ring

theorem harmonicSeed_expansion {q : ℕ} (hq : 0<q) :
    harmonicSeed q=zetaNat 2*(Real.log q+kappaZero)/(q : ℝ)^2-
      zetaThree/(2*(q : ℝ)^3)+seedError q := by
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hz : zetaNat 2≠0 := (zetaNat_pos (by norm_num : 1<(2 : ℕ))).ne'
  have h2 := (powerKernel_positive_hasSum (by norm_num : 1<(2 : ℕ))).mul_left
    ((Real.log q+Real.eulerMascheroniConstant)/(q : ℝ)^2)
  have hl := logSquareTerm_positive_hasSum.mul_left (1/(q : ℝ)^2)
  have h3 := (powerKernel_positive_hasSum (by norm_num : 1<(3 : ℕ))).mul_left (1/(2*(q : ℝ)^3))
  have hs := ((h2.add hl).sub h3).add (seedErrorTerm_summable hq).hasSum
  have hf : HasSum (fun m => harmonicKernel (q*(m+1)))
      (((Real.log q+Real.eulerMascheroniConstant)/(q : ℝ)^2)*zetaNat 2+
      (1/(q : ℝ)^2)*logSquareMoment-
      (1/(2*(q : ℝ)^3))*zetaNat 3+seedError q) := by
    convert! hs using 1
    funext m
    exact harmonicKernel_expansion hq m
  have he := hf.tsum_eq
  have ht : (∑' m, harmonicKernel (q*(m+1)))=harmonicSeed q :=
    (harmonicSeed_positive_series hq).symm
  rw [ht] at he
  rw [he,kappaZero,zetaNat_three]
  field_simp
  ring

theorem strict_harmonicSeed_expansion {q : ℕ} (hq : 1≤q) :
    harmonicSeed q=zetaNat 2*(Real.log q+kappaZero)/(q : ℝ)^2-
      zetaThree/(2*(q : ℝ)^3)+seedError q ∧
    -(zetaNat 4/(12*(q : ℝ)^4))<seedError q ∧ seedError q<0 :=
  ⟨harmonicSeed_expansion hq,seedError_bounds hq⟩

end NField.Alignment.CollisionHarmonicSeedExpansion
