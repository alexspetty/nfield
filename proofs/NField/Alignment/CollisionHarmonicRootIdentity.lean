/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicBoundaryDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The literal harmonic-root identity, including its endpoints

The two sides have the same derivative on the open arc. Their difference
is constant there; continuity extends that constant to the closed arc,
and the independently proved value at zero determines it.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicRootIdentity

open scoped Topology
open CollisionHarmonicRootSeries CollisionHarmonicBoundaryDerivative
open CollisionClausenDerivative CollisionHarmonicSeed

theorem literal_harmonic_series_hasSum {z : ℂ} (hz : ‖z‖≤1) :
    HasSum (fun n : ℕ => (harmonic n : ℂ)/((n+1 : ℕ) : ℂ)^2*z^(n+1))
      (harmonicPolylog z) := by
  have hs : HasSum (fun n => harmonicPowerTerm z (n+1)) (harmonicPolylog z) := by
    apply (hasSum_nat_add_iff (f := harmonicPowerTerm z) 1).2
    simpa [harmonicPolylog,harmonicPowerTerm,CollisionAmplitudeArithmetic.harmonicKernel]
      using! (harmonicPowerTerm_summable hz).hasSum
  convert! hs using 1
  funext n
  simp [harmonicPowerTerm,CollisionAmplitudeArithmetic.harmonicKernel]

theorem literal_cubic_cosine_hasSum (θ : ℝ) :
    HasSum (fun n : ℕ => Real.cos (((n+1 : ℕ) : ℝ)*θ)/((n+1 : ℕ) : ℝ)^3)
      (cubicCosine θ) := by
  apply (hasSum_nat_add_iff (f := cubicCosineTerm θ) 1).2
  simpa [cubicCosine,cubicCosineTerm] using! (cubicCosineTerm_summable θ).hasSum

theorem literal_quadratic_sine_hasSum (θ : ℝ) :
    HasSum (fun n : ℕ => Real.sin (((n+1 : ℕ) : ℝ)*θ)/((n+1 : ℕ) : ℝ)^2)
      (quadraticSine θ) := by
  apply (hasSum_nat_add_iff (f := quadraticSineTerm θ) 1).2
  simpa [quadraticSine,quadraticSineTerm] using! (quadraticSineTerm_summable θ).hasSum

theorem literal_absolute_series {z : ℂ} (hz : ‖z‖≤1) (θ : ℝ) :
    Summable (fun n : ℕ => ‖(harmonic n : ℂ)/((n+1 : ℕ) : ℂ)^2*z^(n+1)‖) ∧
    Summable (fun n : ℕ => ‖Real.cos (((n+1 : ℕ) : ℝ)*θ)/((n+1 : ℕ) : ℝ)^3‖) ∧
    Summable (fun n : ℕ => ‖Real.sin (((n+1 : ℕ) : ℝ)*θ)/((n+1 : ℕ) : ℝ)^2‖) :=
  ⟨(literal_harmonic_series_hasSum hz).summable.norm,
    (literal_cubic_cosine_hasSum θ).summable.norm,
    (literal_quadratic_sine_hasSum θ).summable.norm⟩

def harmonicRootExpression (θ : ℝ) : ℝ :=
  (zetaThree+cubicCosine θ)/2+(θ-Real.pi)/2*quadraticSine θ

def harmonicRootDifference (θ : ℝ) : ℝ :=
  (harmonicBoundary θ).re-harmonicRootExpression θ

theorem harmonicRootExpression_continuous : Continuous harmonicRootExpression := by
  exact ((continuous_const.add cubicCosine_continuous).div_const 2).add
    (((continuous_id.sub continuous_const).div_const 2).mul quadraticSine_continuous)

theorem harmonicRootDifference_continuous : Continuous harmonicRootDifference :=
  (Complex.continuous_re.comp harmonicBoundary_continuous).sub harmonicRootExpression_continuous

theorem harmonicRootExpression_hasDerivAt {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    HasDerivAt harmonicRootExpression
      (-(θ-Real.pi)*Real.log (2*Real.sin (θ/2))/2) θ := by
  have h := (((cubicCosine_hasDerivAt θ).const_add zetaThree).div_const 2).add
    ((((hasDerivAt_id θ).sub_const Real.pi).div_const 2).mul
      (literal_clausen_derivative hθ0 hθ2))
  convert! h using 1
  simp only [id_eq]
  ring

theorem harmonicRootDifference_hasDerivAt_zero {θ : ℝ} (hθ0 : 0<θ) (hθ2 : θ<2*Real.pi) :
    HasDerivAt harmonicRootDifference 0 θ := by
  have h := (harmonicBoundary_re_hasDerivAt hθ0 hθ2).sub
    (harmonicRootExpression_hasDerivAt hθ0 hθ2)
  simpa only [sub_self,harmonicRootDifference] using! h

theorem harmonicRootDifference_zero : harmonicRootDifference 0=0 := by
  simp [harmonicRootDifference,harmonicRootExpression,harmonicBoundary_zero,
    cubicCosine_zero,quadraticSine_zero]

theorem literal_harmonic_root_identity {θ : ℝ} (hθ0 : 0≤θ) (hθ2 : θ≤2*Real.pi) :
    (harmonicPolylog (Complex.exp ((θ : ℂ)*Complex.I))).re=
      (zetaThree+cubicCosine θ)/2+(θ-Real.pi)/2*quadraticSine θ := by
  have hderiv (t : ℝ) (ht : t∈Set.Ioo 0 (2*Real.pi)) :
      HasDerivAt harmonicRootDifference 0 t :=
    harmonicRootDifference_hasDerivAt_zero ht.1 ht.2
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo (0 : ℝ) (2*Real.pi)).isPreconnected
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hderiv t ht).deriv)
  have heq : Set.EqOn harmonicRootDifference (fun _ => c) (Set.Ioo 0 (2*Real.pi)) := hc
  have hclosure := heq.closure harmonicRootDifference_continuous continuous_const
  rw [closure_Ioo (by positivity : (0 : ℝ)≠2*Real.pi)] at hclosure
  have hc0 : c=0 := by
    have h := hclosure (show (0 : ℝ)∈Set.Icc 0 (2*Real.pi) by constructor <;> positivity)
    simpa [harmonicRootDifference_zero] using h.symm
  have hθ := hclosure ⟨hθ0,hθ2⟩
  rw [hc0] at hθ
  exact sub_eq_zero.mp hθ

end NField.Alignment.CollisionHarmonicRootIdentity
