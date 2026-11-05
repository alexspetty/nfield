/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicCoefficients
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The harmonic power-series derivative in the open disk

The logarithm square is obtained from the absolutely convergent Cauchy
product of its actual Taylor series. Differentiation uses a geometric
majorant on each smaller disk, retaining the original harmonic series.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicInterior

open scoped BigOperators Topology
open Filter Finset
open CollisionHarmonicCoefficients CollisionHarmonicRootSeries CollisionAmplitudeArithmetic

def logPowerTerm (z : ℂ) (n : ℕ) : ℂ := z^(n+1)/(n+1 : ℕ)

def harmonicFirstPowerTerm (z : ℂ) (n : ℕ) : ℂ :=
  (shiftedHarmonicFirst n : ℂ)*z^(n+2)

def harmonicDerivativeTerm (z : ℂ) (n : ℕ) : ℂ :=
  (shiftedHarmonicFirst n : ℂ)*z^(n+1)

theorem logPowerTerm_hasSum {z : ℂ} (hz : ‖z‖<1) :
    HasSum (logPowerTerm z) (-Complex.log (1-z)) := by
  change HasSum (fun n : ℕ => z^(n+1)/((n+1 : ℕ) : ℂ)) _
  apply (hasSum_nat_add_iff (f := fun n : ℕ => z^n/(n : ℂ)) 1).2
  simpa using Complex.hasSum_taylorSeries_neg_log hz

theorem logPowerTerm_convolution (z : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), logPowerTerm z k*logPowerTerm z (n-k))=
      2*harmonicFirstPowerTerm z n := by
  have hterm (k : ℕ) (hk : k∈Finset.range (n+1)) :
      logPowerTerm z k*logPowerTerm z (n-k)=
        (1/(((k+1 : ℕ) : ℂ)*((n-k+1 : ℕ) : ℂ)))*z^(n+2) := by
    have hkn : k≤n := by simpa using Finset.mem_range.mp hk
    unfold logPowerTerm
    rw [div_mul_div_comm,← pow_add,show (k+1)+(n-k+1)=n+2 by omega]
    ring
  rw [Finset.sum_congr rfl hterm,← Finset.sum_mul]
  have hc : (∑ k ∈ Finset.range (n+1),
      1/(((k+1 : ℕ) : ℂ)*((n-k+1 : ℕ) : ℂ)))=2*(shiftedHarmonicFirst n : ℂ) := by
    have h := congrArg Complex.ofReal (reciprocal_convolution n)
    simpa only [Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat] using h
  rw [hc,harmonicFirstPowerTerm]
  ring

theorem harmonicFirstPowerTerm_hasSum {z : ℂ} (hz : ‖z‖<1) :
    HasSum (harmonicFirstPowerTerm z) (Complex.log (1-z)^2/2) := by
  have hl := logPowerTerm_hasSum hz
  have hp := hasSum_sum_range_mul_of_summable_norm hl.summable.norm hl.summable.norm
  rw [hl.tsum_eq] at hp
  have hp' : HasSum (fun n => 2*harmonicFirstPowerTerm z n) (Complex.log (1-z)^2) := by
    simpa only [logPowerTerm_convolution,neg_mul_neg,pow_two] using hp
  have hhalf := hp'.div_const 2
  convert! hhalf using 1
  ext n
  ring

theorem harmonicDerivativeTerm_hasSum {z : ℂ} (hz : ‖z‖<1) :
    HasSum (harmonicDerivativeTerm z) (Complex.log (1-z)^2/(2*z)) := by
  by_cases hz0 : z=0
  · subst z
    change HasSum (fun n => harmonicDerivativeTerm 0 n) _
    simp [harmonicDerivativeTerm]
  · have hdiv := (harmonicFirstPowerTerm_hasSum hz).div_const z
    convert! hdiv using 1
    · ext n
      unfold harmonicDerivativeTerm harmonicFirstPowerTerm
      rw [show n+2=(n+1)+1 by omega,pow_succ]
      field_simp
      ring
    · field_simp

theorem harmonicPowerTerm_succ_succ_hasDerivAt (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w => harmonicPowerTerm w (n+2)) (harmonicDerivativeTerm z n) z := by
  convert! (hasDerivAt_pow (n+2) z).const_mul (harmonicKernel (n+2) : ℂ) using 1
  simp only [harmonicDerivativeTerm,shiftedHarmonicFirst_eq,harmonicFirstKernel_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_natCast,show n+2-1=n+1 by omega]
  ring

theorem harmonicDerivativeTerm_bound {r : ℝ} (_hr : 0≤r) {z : ℂ}
    (hz : ‖z‖≤r) (n : ℕ) : ‖harmonicDerivativeTerm z n‖≤r^(n+1) := by
  rw [harmonicDerivativeTerm,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (shiftedHarmonicFirst_nonneg n),norm_pow]
  have hc : shiftedHarmonicFirst n≤1 := by
    rw [shiftedHarmonicFirst_eq]
    exact harmonicFirstKernel_le_one _
  calc
    shiftedHarmonicFirst n*‖z‖^(n+1) ≤ 1*r^(n+1) :=
      mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg z) hz _)
        (by positivity) (by norm_num)
    _ = r^(n+1) := one_mul _

theorem harmonicPolylog_eq_shift {z : ℂ} (hz : ‖z‖≤1) :
    harmonicPolylog z=∑' n, harmonicPowerTerm z (n+2) := by
  have hs : HasSum (fun n => harmonicPowerTerm z (n+2)) (harmonicPolylog z) := by
    apply (hasSum_nat_add_iff (f := harmonicPowerTerm z) 2).2
    simpa [harmonicPowerTerm,harmonicKernel,Finset.sum_range_succ,harmonicPolylog]
      using! (harmonicPowerTerm_summable hz).hasSum
  exact hs.tsum_eq.symm

theorem literal_harmonic_polylog_derivative {z : ℂ} (hz : ‖z‖<1) :
    HasDerivAt harmonicPolylog (Complex.log (1-z)^2/(2*z)) z := by
  obtain ⟨r,hzr,hr1⟩ := exists_between hz
  have hr0 : 0<r := lt_of_le_of_lt (norm_nonneg z) hzr
  have hu : Summable (fun n : ℕ => r^(n+1)) :=
    (summable_geometric_of_lt_one hr0.le hr1).comp_injective Nat.succ_injective
  have hbase : Summable (fun n => harmonicPowerTerm 0 (n+2)) := by
    simp [harmonicPowerTerm]
  have hd := hasDerivAt_tsum_of_isPreconnected hu
    (t := Metric.ball (0 : ℂ) r) Metric.isOpen_ball Metric.isPreconnected_ball
    (fun n w _ => harmonicPowerTerm_succ_succ_hasDerivAt n w)
    (fun n w hw => harmonicDerivativeTerm_bound hr0.le
      (by simpa using (Metric.mem_ball.mp hw).le) n)
    (by simpa using hr0 : (0 : ℂ)∈Metric.ball 0 r) hbase
    (by simpa using hzr : z∈Metric.ball 0 r)
  rw [(harmonicDerivativeTerm_hasSum hz).tsum_eq] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hzr : z∈Metric.ball 0 r)] with w hw
  exact harmonicPolylog_eq_shift (le_trans (by simpa using (Metric.mem_ball.mp hw).le) hr1.le)

end NField.Alignment.CollisionHarmonicInterior
