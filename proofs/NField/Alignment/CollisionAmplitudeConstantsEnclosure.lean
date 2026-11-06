/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPositiveConstants
import NField.Alignment.CollisionHarmonicRemainder
import NField.Alignment.CollisionZetaMoments
import NField.Alignment.CollisionInverseRationalBound

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionAmplitudeConstantsEnclosure
open scoped BigOperators
open CollisionHarmonicRemainder CollisionZetaMoments CollisionPositiveLogTail
open CollisionInverseRationalBound CollisionVarianceEnclosure CollisionInverseRemainder

theorem gamma_enclosure {N : ℕ} (hN : 1 ≤ N) {l u : ℝ}
    (hl : l ≤ Real.log N) (hu : Real.log N ≤ u) :
    (harmonic (N-1) : ℝ)-u+1/(2*(N : ℝ))  ≤  Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant  ≤  (harmonic (N-1) : ℝ)-l+1/(2*(N : ℝ))+
      1/(12*(N : ℝ)^2) := by
  have h := strict_harmonic_remainder hN
  constructor <;> linarith [h.1,h.2.1,h.2.2]

def logMomentPrefix (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N+1), logSquareTerm n

theorem logSquareTerm_nonneg (n : ℕ) : 0 ≤ logSquareTerm n := by
  exact div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)

theorem logSquareTerm_le_positiveLog (n : ℕ) : logSquareTerm n ≤ positiveLogKernel n := by
  unfold logSquareTerm positiveLogKernel
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  linarith

theorem logMoment_tail_split (N : ℕ) :
    logSquareMoment-logMomentPrefix N=∑' n,logSquareTerm (n+N+1) := by
  have h := logSquareTerm_summable.sum_add_tsum_nat_add (N+1)
  change logMomentPrefix N+(∑' n,logSquareTerm (n+(N+1)))=logSquareMoment at h
  simp only [← Nat.add_assoc] at h
  linarith

theorem logMoment_binary_tail {N b : ℕ} (hN : 1 ≤ N) (hb : 2*N ≤ 2^b) :
    0 ≤ logSquareMoment-logMomentPrefix N ∧
    logSquareMoment-logMomentPrefix N ≤ (2*(b : ℝ)+3)/(N : ℝ) := by
  rw [logMoment_tail_split]
  constructor
  · exact tsum_nonneg (fun n => logSquareTerm_nonneg _)
  have hs : Summable (fun n : ℕ => logSquareTerm (n+N+1)) :=
    logSquareTerm_summable.comp_injective (fun a b h => by omega)
  have ht := hs.tsum_le_tsum (fun n => logSquareTerm_le_positiveLog (n+N+1))
    (positiveLog_shift_summable hN)
  apply (ht.trans (positiveLog_shift_bound hN)).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hl := log_le_binary_bound hN hb
  linarith


theorem positive_division_enclosure {x y xl xh yl yh : ℝ}
    (hxl : 0 ≤ xl) (hyl : 0<yl) (hx : xl ≤ x ∧ x ≤ xh) (hy : yl ≤ y ∧ y ≤ yh) :
    xl/yh ≤ x/y ∧ x/y ≤ xh/yl := by
  have hy0 : 0<y := hyl.trans_le hy.1
  constructor
  · exact (div_le_div_of_nonneg_left hxl hy0 hy.2).trans
      (div_le_div_of_nonneg_right hx.1 hy0.le)
  · exact (div_le_div_of_nonneg_left (hxl.trans hx.1) hyl hy.1).trans
      (div_le_div_of_nonneg_right hx.2 hyl.le)

theorem zetaNat_eq_realZeta {p : ℕ} (hp : 0<p) :
    zetaNat p=CollisionDivisorSeries.realZeta p := by
  unfold zetaNat CollisionDivisorSeries.realZeta
  apply tsum_congr
  intro n
  exact (CollisionPositiveConstants.zetaKernel_nat hp n).symm

theorem zetaNat_two_pi : zetaNat 2=Real.pi^2/6 := by
  rw [zetaNat_eq_realZeta (by norm_num : 0<(2 : ℕ))]
  exact CollisionPositiveConstants.realZeta_two

theorem zetaNat_four_pi : zetaNat 4=Real.pi^4/90 := by
  rw [zetaNat_eq_realZeta (by norm_num : 0<(4 : ℕ))]
  exact CollisionPositiveConstants.realZeta_four

theorem zeta_even_enclosures {l u : ℝ} (hl : 0 ≤ l)
    (hp : l ≤ Real.pi ∧ Real.pi ≤ u) :
    l^2/6 ≤ zetaNat 2 ∧ zetaNat 2 ≤ u^2/6 ∧
    l^4/90 ≤ zetaNat 4 ∧ zetaNat 4 ≤ u^4/90 := by
  rw [zetaNat_two_pi,zetaNat_four_pi]
  exact ⟨div_le_div_of_nonneg_right (pow_le_pow_left₀ hl hp.1 2) (by norm_num),
    div_le_div_of_nonneg_right (pow_le_pow_left₀ Real.pi_pos.le hp.2 2) (by norm_num),
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hl hp.1 4) (by norm_num),
    div_le_div_of_nonneg_right (pow_le_pow_left₀ Real.pi_pos.le hp.2 4) (by norm_num)⟩

theorem log_moment_enclosure {N b : ℕ} (hN : 1 ≤ N) (hb : 2*N ≤ 2^b)
    (L U : ℕ → ℝ)
    (hlog : ∀ n∈Finset.range (N+1), L n ≤ Real.log n ∧ Real.log n ≤ U n) :
    (∑ n∈Finset.range (N+1), L n/(n : ℝ)^2) ≤ logSquareMoment ∧
    logSquareMoment ≤ (∑ n∈Finset.range (N+1), U n/(n : ℝ)^2)+(2*(b : ℝ)+3)/(N : ℝ) := by
  have hl : (∑ n∈Finset.range (N+1), L n/(n : ℝ)^2) ≤ logMomentPrefix N := by
    apply Finset.sum_le_sum
    intro n hn
    exact div_le_div_of_nonneg_right (hlog n hn).1 (sq_nonneg _)
  have hu : logMomentPrefix N ≤ (∑ n∈Finset.range (N+1), U n/(n : ℝ)^2) := by
    apply Finset.sum_le_sum
    intro n hn
    exact div_le_div_of_nonneg_right (hlog n hn).2 (sq_nonneg _)
  have ht := logMoment_binary_tail hN hb
  constructor <;> linarith [ht.1,ht.2]

theorem kappa_enclosure {gl gh ml mh zl zh : ℝ} (hml : 0 ≤ ml) (hzl : 0<zl)
    (hg : gl ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ gh)
    (hm : ml ≤ logSquareMoment ∧ logSquareMoment ≤ mh)
    (hz : zl ≤ zetaNat 2 ∧ zetaNat 2 ≤ zh) :
    gl+ml/zh ≤ kappaZero ∧ kappaZero ≤ gh+mh/zl := by
  have h := positive_division_enclosure hml hzl hm hz
  exact ⟨add_le_add hg.1 h.1,add_le_add hg.2 h.2⟩

theorem amplitude_leading_enclosure {zl zh tl th : ℝ} (hzl : 0 ≤ zl) (htl : 0<tl)
    (hz : zl ≤ zetaNat 2 ∧ zetaNat 2 ≤ zh)
    (ht : tl ≤ CollisionHarmonicSeed.zetaThree ∧ CollisionHarmonicSeed.zetaThree ≤ th) :
    zl/th ≤ amplitudeLeading ∧ amplitudeLeading ≤ zh/tl :=
  positive_division_enclosure hzl htl hz ht

end NField.Alignment.CollisionAmplitudeConstantsEnclosure
