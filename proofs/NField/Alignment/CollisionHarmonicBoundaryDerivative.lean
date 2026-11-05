/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicAbelBoundary
import NField.Alignment.CollisionClausenDerivative
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Differentiating the actual harmonic boundary series

Uniform ordered derivative convergence on neighborhoods separated from
the trivial root combines with absolute convergence of the original
series. The resulting derivative has the exact principal-log square.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicBoundaryDerivative

open scoped BigOperators Topology
open Filter Finset
open CollisionDirichletBoundary CollisionHarmonicCoefficients CollisionHarmonicInterior
open CollisionHarmonicRootSeries CollisionHarmonicAbelBoundary CollisionHarmonicLogBoundary
open CollisionAmplitudeArithmetic

def harmonicBoundaryPartial (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, harmonicPowerTerm (Complex.exp ((θ : ℂ)*Complex.I)) (k+2)

def harmonicBoundaryDerivativePartial (n : ℕ) (θ : ℝ) : ℂ :=
  Complex.I*Complex.exp ((θ : ℂ)*Complex.I)*
    dirichletPartial shiftedHarmonicFirst n (Complex.exp ((θ : ℂ)*Complex.I))

theorem circle_exp_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ)*Complex.I))
      (Complex.exp ((θ : ℂ)*Complex.I)*Complex.I) θ := by
  simpa using ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp

theorem harmonicBoundaryTerm_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => harmonicPowerTerm (Complex.exp ((t : ℂ)*Complex.I)) (n+2))
      (Complex.I*Complex.exp ((θ : ℂ)*Complex.I)*
        harmonicDerivativeTerm (Complex.exp ((θ : ℂ)*Complex.I)) n) θ := by
  convert! ((circle_exp_hasDerivAt θ).pow (n+2)).const_mul (harmonicKernel (n+2) : ℂ) using 1
  simp only [harmonicDerivativeTerm,shiftedHarmonicFirst_eq,harmonicFirstKernel_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_natCast,show n+2-1=n+1 by omega]
  ring

theorem harmonicBoundaryPartial_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (harmonicBoundaryPartial n) (harmonicBoundaryDerivativePartial n θ) θ := by
  have h := HasDerivAt.fun_sum (u := Finset.range n) fun k _ =>
    harmonicBoundaryTerm_hasDerivAt k θ
  simpa only [harmonicBoundaryPartial,harmonicBoundaryDerivativePartial,dirichletPartial,
    harmonicDerivativeTerm,← Finset.mul_sum] using! h

theorem harmonicBoundaryPartial_tendsto (θ : ℝ) :
    Tendsto (fun n => harmonicBoundaryPartial n θ) atTop (𝓝 (harmonicBoundary θ)) := by
  have hs := (harmonicPowerTerm_summable (circle_exp_norm θ).le).comp_injective
    (fun i j h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n+2))
  have ht := hs.hasSum.tendsto_sum_nat
  simp only [Function.comp_def] at ht
  rw [← harmonicPolylog_eq_shift (circle_exp_norm θ).le] at ht
  exact ht

theorem harmonicBoundary_hasDerivAt_log {θ : ℝ}
    (hθ : Complex.exp ((θ : ℂ)*Complex.I)≠1) :
    HasDerivAt harmonicBoundary
      (Complex.I*Complex.log (1-Complex.exp ((θ : ℂ)*Complex.I))^2/2) θ := by
  let δ : ℝ := ‖Complex.exp ((θ : ℂ)*Complex.I)-1‖/2
  let s : Set ℝ := {t | δ<‖Complex.exp ((t : ℂ)*Complex.I)-1‖}
  have hnormpos : 0<‖Complex.exp ((θ : ℂ)*Complex.I)-1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hθ)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hsopen : IsOpen s := by
    apply isOpen_lt continuous_const
    fun_prop
  have hθs : θ∈s := by dsimp [s,δ]; linarith
  have hsep (t : ℝ) (ht : t∈s) : δ≤‖Complex.exp ((t : ℂ)*Complex.I)-1‖ := ht.le
  have hpoint (t : ℝ) (ht : t∈s) :
      Tendsto (fun n => dirichletPartial shiftedHarmonicFirst n
        (Complex.exp ((t : ℂ)*Complex.I))) atTop
        (𝓝 (Complex.log (1-Complex.exp ((t : ℂ)*Complex.I))^2/
          (2*Complex.exp ((t : ℂ)*Complex.I)))) := by
    apply harmonic_dirichlet_tendsto (circle_exp_norm t)
    intro heq
    have hb := hsep t ht
    rw [heq,sub_self,norm_zero] at hb
    linarith
  have hu := dirichlet_tendstoUniformlyOn shiftedHarmonicFirst_nonneg
    shiftedHarmonicFirst_antitone shiftedHarmonicFirst_tendsto_zero hδ
    (fun t _ => circle_exp_norm t) hsep hpoint
  have hderiv : TendstoUniformlyOn harmonicBoundaryDerivativePartial
      (fun t => Complex.I*Complex.log (1-Complex.exp ((t : ℂ)*Complex.I))^2/2) atTop s := by
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu ε hε] with n hn t ht
    have hscale : Complex.I*Complex.log (1-Complex.exp ((t : ℂ)*Complex.I))^2/2=
        (Complex.I*Complex.exp ((t : ℂ)*Complex.I))*
          (Complex.log (1-Complex.exp ((t : ℂ)*Complex.I))^2/
            (2*Complex.exp ((t : ℂ)*Complex.I))) := by
      field_simp
    rw [hscale,harmonicBoundaryDerivativePartial,dist_eq_norm,← mul_sub,
      norm_mul,norm_mul,Complex.norm_I,circle_exp_norm,one_mul,one_mul]
    simpa only [dist_eq_norm] using hn t ht
  exact hasDerivAt_of_tendstoUniformlyOn hsopen hderiv
    (Eventually.of_forall fun n t _ => harmonicBoundaryPartial_hasDerivAt n t)
    (fun t _ => harmonicBoundaryPartial_tendsto t) hθs

theorem harmonicBoundary_re_hasDerivAt {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    HasDerivAt (fun t => (harmonicBoundary t).re)
      (-(θ-Real.pi)*Real.log (2*Real.sin (θ/2))/2) θ := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ
    (harmonicBoundary_hasDerivAt_log (circle_exp_ne_one hθ0 hθ2))
  convert! h using 1
  simp only [Complex.reCLM_apply,Complex.div_ofNat_re,pow_two,Complex.mul_re,
    Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,
    log_one_sub_circle_exp_re hθ0 hθ2,log_one_sub_circle_exp_im hθ0 hθ2]
  ring

end NField.Alignment.CollisionHarmonicBoundaryDerivative
