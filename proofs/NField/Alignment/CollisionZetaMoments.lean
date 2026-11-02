/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicSeed
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Actual zeta constants and the logarithmic square moment

All constants are convergent real series with explicit identifications
with the Riemann zeta function and its complex derivative at two.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionZetaMoments

open scoped BigOperators Classical
open Filter CollisionHarmonicSeed

def powerKernel (p n : ℕ) : ℝ := 1/(n : ℝ)^p
def zetaNat (p : ℕ) : ℝ := ∑' n, powerKernel p n
def logSquareTerm (n : ℕ) : ℝ := Real.log n/(n : ℝ)^2
def logSquareMoment : ℝ := ∑' n, logSquareTerm n
def kappaZero : ℝ := Real.eulerMascheroniConstant+logSquareMoment/zetaNat 2
def amplitudeLeading : ℝ := zetaNat 2/zetaThree

theorem powerKernel_nonneg (p n : ℕ) : 0≤powerKernel p n := by
  unfold powerKernel
  positivity

theorem powerKernel_summable {p : ℕ} (hp : 1<p) : Summable (powerKernel p) := by
  unfold powerKernel
  simp only [one_div]
  exact Real.summable_nat_pow_inv.mpr hp

theorem zetaNat_pos {p : ℕ} (hp : 1<p) : 0<zetaNat p := by
  have he := (powerKernel_summable hp).le_tsum 1 (fun n _ => powerKernel_nonneg p n)
  have h1 : powerKernel p 1=1 := by simp [powerKernel]
  rw [h1] at he
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) he

theorem zetaNat_eq_riemannZeta {p : ℕ} (hp : 1<p) :
    (zetaNat p : ℂ)=riemannZeta p := by
  rw [zetaNat, Complex.ofReal_tsum, zeta_nat_eq_tsum_of_gt_one hp]
  apply tsum_congr
  intro n
  simp [powerKernel]

theorem zetaNat_three : zetaNat 3=zetaThree := rfl

theorem powerKernel_mul (p q m : ℕ) :
    powerKernel p (q*m)=powerKernel p q*powerKernel p m := by
  simp [powerKernel,Nat.cast_mul,mul_pow,one_div,mul_inv_rev,mul_comm]

theorem powerKernel_positive_hasSum {p : ℕ} (hp : 1<p) :
    HasSum (fun n => powerKernel p (n+1)) (zetaNat p) := by
  have hs := powerKernel_summable hp
  have he := hs.sum_add_tsum_nat_add 1
  have h0 : powerKernel p 0=0 := by
    simp only [powerKernel,Nat.cast_zero,zero_pow (by omega : p≠0),div_zero]
  have ht : (∑' n, powerKernel p (n+1))=zetaNat p := by simpa [h0,zetaNat] using he
  rw [← ht]
  exact (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)).hasSum

theorem powerKernel_positive_multiple_hasSum {p : ℕ} (hp : 1<p) (q : ℕ) :
    HasSum (fun n => powerKernel p (q*(n+1))) (zetaNat p/(q : ℝ)^p) := by
  have hs := (powerKernel_positive_hasSum hp).mul_left (powerKernel p q)
  convert! hs using 1
  · funext n
    exact powerKernel_mul p q (n+1)
  · unfold powerKernel
    ring

theorem logSquareTerm_complex (n : ℕ) :
    (logSquareTerm n : ℂ)=LSeries.term (LSeries.logMul 1) 2 n := by
  by_cases hn : n=0
  · simp [hn,logSquareTerm,LSeries.term]
  unfold logSquareTerm LSeries.term LSeries.logMul
  rw [if_neg hn]
  push_cast
  simp only [Pi.one_apply,mul_one,Complex.cpow_two]

theorem logSquareTerm_summable : Summable logSquareTerm := by
  have hh : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ)<(2 : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    change (1 : EReal)<((2 : ℝ) : EReal)
    exact_mod_cast (by norm_num : (1 : ℝ)<2)
  have hs := LSeriesSummable_logMul_of_lt_re hh
  change Summable (fun n => LSeries.term (LSeries.logMul 1) 2 n) at hs
  apply Complex.summable_ofReal.mp
  simpa only [logSquareTerm_complex] using hs

theorem logSquareMoment_eq_LSeries :
    (logSquareMoment : ℂ)=LSeries (LSeries.logMul 1) 2 := by
  rw [logSquareMoment,Complex.ofReal_tsum]
  exact tsum_congr logSquareTerm_complex

theorem zeta_derivative_two : deriv riemannZeta 2=-(logSquareMoment : ℂ) := by
  have hh : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ)<(2 : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    change (1 : EReal)<((2 : ℝ) : EReal)
    exact_mod_cast (by norm_num : (1 : ℝ)<2)
  have he : deriv (LSeries (1 : ℕ → ℂ)) 2=deriv riemannZeta 2 := by
    apply Filter.EventuallyEq.deriv_eq
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨{z : ℂ | 1<z.re}, ?_, fun _ h => LSeries_one_eq_riemannZeta h⟩
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  rw [← he,LSeries_deriv hh,← logSquareMoment_eq_LSeries]

theorem kappaZero_eq_zeta_derivative :
    (kappaZero : ℂ)=(Real.eulerMascheroniConstant : ℂ)-deriv riemannZeta 2/riemannZeta 2 := by
  rw [kappaZero,zeta_derivative_two]
  push_cast
  have hz := zetaNat_eq_riemannZeta (by norm_num : 1<(2 : ℕ))
  norm_num only [Nat.cast_ofNat] at hz
  rw [hz]
  ring

theorem amplitudeLeading_eq_zeta_ratio :
    (amplitudeLeading : ℂ)=riemannZeta 2/riemannZeta 3 := by
  rw [amplitudeLeading]
  push_cast
  have hz := zetaNat_eq_riemannZeta (by norm_num : 1<(2 : ℕ))
  norm_num only [Nat.cast_ofNat] at hz
  rw [hz,zetaThree_eq_riemannZeta]

end NField.Alignment.CollisionZetaMoments
