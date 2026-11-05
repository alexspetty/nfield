/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDirichletBoundary
import NField.Alignment.CollisionHarmonicLogBoundary
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# The actual Clausen derivative on the open arc

The derivative is a conditionally convergent cosine series. Uniform
Dirichlet tails on a neighborhood of each nontrivial root justify
differentiating the original absolutely convergent quadratic sine series.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionClausenDerivative

open scoped BigOperators Topology
open Filter Finset
open CollisionDirichletBoundary CollisionHarmonicRootSeries CollisionHarmonicLogBoundary

def inverseLinear (n : ℕ) : ℝ := 1/(n+1 : ℕ)

def clausenPartial (n : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, quadraticSineTerm θ (k+1)

def clausenDerivativePartial (n : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.cos ((k+1 : ℕ)*θ)/(k+1 : ℕ)

theorem inverseLinear_nonneg (n : ℕ) : 0 ≤ inverseLinear n := by
  unfold inverseLinear
  positivity

theorem inverseLinear_antitone : Antitone inverseLinear := by
  intro m n hmn
  unfold inverseLinear
  gcongr

theorem inverseLinear_tendsto_zero : Tendsto inverseLinear atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [inverseLinear,Nat.cast_add,Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem inverseLinear_dirichlet_tendsto {z : ℂ} (hzNorm : ‖z‖=1) (hz : z≠1) :
    Tendsto (fun n => dirichletPartial inverseLinear n z) atTop
      (𝓝 (-Complex.log (1-z))) := by
  simpa [dirichletPartial,inverseLinear,div_eq_mul_inv,mul_comm] using
    SawtoothLValue.tendsto_harmonic_geometric hzNorm hz

theorem circle_power_re (θ : ℝ) (n : ℕ) :
    (Complex.exp ((θ : ℂ)*Complex.I)^n).re=Real.cos ((n : ℝ)*θ) := by
  rw [← Complex.exp_nat_mul]
  simp [Complex.exp_re]

theorem clausenDerivativePartial_eq_re (n : ℕ) (θ : ℝ) :
    clausenDerivativePartial n θ=
      (dirichletPartial inverseLinear n (Complex.exp ((θ : ℂ)*Complex.I))).re := by
  simp only [clausenDerivativePartial,dirichletPartial,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    inverseLinear,circle_power_re]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem quadraticSineTerm_succ_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun t => quadraticSineTerm t (n+1))
      (Real.cos ((n+1 : ℕ)*θ)/(n+1 : ℕ)) θ := by
  convert! (((hasDerivAt_id θ).const_mul ((n+1 : ℕ) : ℝ)).sin).div_const
    (((n+1 : ℕ) : ℝ)^2) using 1
  simp only [mul_one,id_eq]
  field_simp

theorem clausenPartial_hasDerivAt (n : ℕ) (θ : ℝ) :
    HasDerivAt (clausenPartial n) (clausenDerivativePartial n θ) θ := by
  exact HasDerivAt.fun_sum fun k _ => quadraticSineTerm_succ_hasDerivAt k θ

theorem clausenPartial_tendsto (θ : ℝ) :
    Tendsto (fun n => clausenPartial n θ) atTop (𝓝 (quadraticSine θ)) := by
  have hs : HasSum (fun k => quadraticSineTerm θ (k+1)) (quadraticSine θ) := by
    apply (hasSum_nat_add_iff 1).2
    simpa [quadraticSine,quadraticSineTerm] using! (quadraticSineTerm_summable θ).hasSum
  exact hs.tendsto_sum_nat

theorem quadraticSine_hasDerivAt_log {θ : ℝ}
    (hθ : Complex.exp ((θ : ℂ)*Complex.I)≠1) :
    HasDerivAt quadraticSine
      (-(Complex.log (1-Complex.exp ((θ : ℂ)*Complex.I))).re) θ := by
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
      Tendsto (fun n => dirichletPartial inverseLinear n
        (Complex.exp ((t : ℂ)*Complex.I))) atTop
        (𝓝 (-Complex.log (1-Complex.exp ((t : ℂ)*Complex.I)))) := by
    apply inverseLinear_dirichlet_tendsto (circle_exp_norm t)
    intro heq
    have hb := hsep t ht
    rw [heq,sub_self,norm_zero] at hb
    linarith
  have hu := dirichlet_tendstoUniformlyOn inverseLinear_nonneg inverseLinear_antitone
    inverseLinear_tendsto_zero hδ (fun t _ => circle_exp_norm t) hsep hpoint
  have hur := Complex.uniformContinuous_re.comp_tendstoUniformlyOn hu
  have hreal : TendstoUniformlyOn clausenDerivativePartial
      (fun t => -(Complex.log (1-Complex.exp ((t : ℂ)*Complex.I))).re) atTop s := by
    simpa only [Function.comp_def,Complex.neg_re,← clausenDerivativePartial_eq_re] using hur
  exact hasDerivAt_of_tendstoUniformlyOn hsopen hreal
    (Eventually.of_forall fun n t _ => clausenPartial_hasDerivAt n t)
    (fun t _ => clausenPartial_tendsto t) hθs

theorem literal_clausen_derivative {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    HasDerivAt quadraticSine (-Real.log (2*Real.sin (θ/2))) θ := by
  simpa only [log_one_sub_circle_exp_re hθ0 hθ2] using
    quadraticSine_hasDerivAt_log (circle_exp_ne_one hθ0 hθ2)

end NField.Alignment.CollisionClausenDerivative
