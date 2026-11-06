/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRationalFourierKernel
import NField.Alignment.CollisionPrimitiveFourier
import NField.Alignment.CollisionFiniteSineTransform
import NField.Alignment.CollisionSpectralWeights

/-! Exact interval operations for the primitive additive Fourier readout.
The finite endpoint inequalities are separate from the universal analytic
containment theorem. Signed amplitude intervals are admitted. -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionFourierEnclosure
open CollisionRationalFourierKernel

def productLower (al ah bl bh : ℝ) : ℝ := min (min (al*bl) (al*bh)) (min (ah*bl) (ah*bh))
def productUpper (al ah bl bh : ℝ) : ℝ := max (max (al*bl) (al*bh)) (max (ah*bl) (ah*bh))
def squareLower (l u : ℝ) : ℝ := if l ≤ 0 ∧ 0 ≤ u then 0 else min (l^2) (u^2)
def squareUpper (l u : ℝ) : ℝ := max (l^2) (u^2)

theorem scale_between {x l u c L U : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hll : L ≤ c*l) (hlu : L ≤ c*u) (hul : c*l ≤ U) (huu : c*u ≤ U) :
    L ≤ c*x ∧ c*x ≤ U := by
  by_cases hc : 0 ≤ c
  · exact ⟨hll.trans (mul_le_mul_of_nonneg_left hx.1 hc),
      (mul_le_mul_of_nonneg_left hx.2 hc).trans huu⟩
  · have hn : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact ⟨hlu.trans (mul_le_mul_of_nonpos_left hx.2 hn),
      (mul_le_mul_of_nonpos_left hx.1 hn).trans hul⟩

theorem product_interval {x y al ah bl bh : ℝ}
    (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    productLower al ah bl bh ≤ x*y ∧ x*y ≤ productUpper al ah bl bh := by
  let L := productLower al ah bl bh
  let U := productUpper al ah bl bh
  have ha : L ≤ al*y ∧ al*y ≤ U := scale_between hy
    ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _))
    ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
  have hb : L ≤ ah*y ∧ ah*y ≤ U := scale_between hy
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _))
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
  have h := scale_between (c := y) hx
    (by simpa only [mul_comm] using ha.1) (by simpa only [mul_comm] using hb.1)
    (by simpa only [mul_comm] using ha.2) (by simpa only [mul_comm] using hb.2)
  simpa only [mul_comm] using h

theorem square_interval {x l u : ℝ} (hx : l ≤ x ∧ x ≤ u) :
    squareLower l u ≤ x^2 ∧ x^2 ≤ squareUpper l u := by
  have hu : x^2 ≤ squareUpper l u := by
    by_cases hn : 0 ≤ x
    · exact ((sq_le_sq₀ hn (hn.trans hx.2)).mpr hx.2).trans (le_max_right _ _)
    · have hl : l ≤ 0 := by linarith
      have hm := mul_nonneg (sub_nonneg.mpr hx.1) (show 0 ≤ -l-x by linarith)
      exact (show x^2 ≤ l^2 by nlinarith).trans (le_max_left _ _)
  refine ⟨?_,hu⟩
  unfold squareLower
  split_ifs with hc
  · positivity
  · by_cases hl : 0 < l
    · exact (min_le_left _ _).trans ((sq_le_sq₀ hl.le (hl.le.trans hx.1)).mpr hx.1)
    · have hu0 : u < 0 := by by_contra hn; exact hc ⟨le_of_not_gt hl,le_of_not_gt hn⟩
      have hm := mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ -u-x by linarith)
      exact (min_le_right _ _).trans (show u^2 ≤ x^2 by nlinarith)

theorem reciprocal_interval {x l u : ℝ} (hl : 0 < l) (hx : l ≤ x ∧ x ≤ u) :
    1/u ≤ 1/x ∧ 1/x ≤ 1/l := by
  exact ⟨one_div_le_one_div_of_le (hl.trans_le hx.1) hx.2,
    one_div_le_one_div_of_le hl hx.1⟩

theorem reciprocal_square_interval {x l u : ℝ} (hl : 0 < l) (hx : l ≤ x ∧ x ≤ u) :
    (1/u)^2 ≤ (1/x)^2 ∧ (1/x)^2 ≤ (1/l)^2 := by
  have h := reciprocal_interval hl hx
  have hx0 : 0 < x := hl.trans_le hx.1
  have hu0 : 0 < u := hx0.trans_le hx.2
  exact ⟨(sq_le_sq₀ (by positivity) (by positivity)).mpr h.1,
    (sq_le_sq₀ (by positivity) (by positivity)).mpr h.2⟩

theorem sin_rounded_enclosure {r l u : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hl : l ≤ (anglePolynomial (piMidpoint*r)).im-trigRadius)
    (hu : (anglePolynomial (piMidpoint*r)).im+trigRadius ≤ u) :
    l ≤ Real.sin (Real.pi*r) ∧ Real.sin (Real.pi*r) ≤ u := by
  have h := abs_le.mp (sin_ratio_enclosure hr0 hr1)
  constructor <;> linarith

theorem cos_rounded_enclosure {r l u : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hl : l ≤ (anglePolynomial (piMidpoint*r)).re-trigRadius)
    (hu : (anglePolynomial (piMidpoint*r)).re+trigRadius ≤ u) :
    l ≤ Real.cos (Real.pi*r) ∧ Real.cos (Real.pi*r) ≤ u := by
  have h := abs_le.mp (cos_ratio_enclosure hr0 hr1)
  constructor <;> linarith

theorem trig_half_exact : Real.sin (Real.pi*(1/2))=1 ∧ Real.cos (Real.pi*(1/2))=0 := by
  simpa only [mul_one_div] using And.intro Real.sin_pi_div_two Real.cos_pi_div_two

theorem cot_interval {r sl sh cl ch : ℝ} (hs0 : 0 < sl)
    (hs : sl ≤ Real.sin (Real.pi*r) ∧ Real.sin (Real.pi*r) ≤ sh)
    (hc : cl ≤ Real.cos (Real.pi*r) ∧ Real.cos (Real.pi*r) ≤ ch) :
    productLower cl ch (1/sh) (1/sl) ≤ Real.cot (Real.pi*r) ∧
    Real.cot (Real.pi*r) ≤ productUpper cl ch (1/sh) (1/sl) := by
  simpa only [Real.cot_eq_cos_div_sin,div_eq_mul_inv,one_mul] using
    product_interval hc (reciprocal_interval hs0 hs)

def gridLower (x grid : ℝ) : ℝ := (⌊grid*x⌋ : ℝ)/grid
def gridUpper (x grid : ℝ) : ℝ := (⌈grid*x⌉ : ℝ)/grid

theorem grid_outward {x grid : ℝ} (hg : 0 < grid) :
    gridLower x grid ≤ x ∧ x ≤ gridUpper x grid := by
  constructor
  · apply (div_le_iff₀ hg).mpr
    simpa only [mul_comm] using Int.floor_le (grid*x)
  · apply (le_div_iff₀ hg).mpr
    simpa only [mul_comm] using Int.le_ceil (grid*x)

theorem squareLower_nonneg (l u : ℝ) : 0 ≤ squareLower l u := by
  unfold squareLower
  split_ifs <;> positivity

open DedekindFourierMoment DedekindInverseResidueTransform CollisionPrimitiveFourier
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionJordanVariance
open CollisionConductorRows

theorem primitive_coefficient_cotangent {q a : ℕ}
    (hq : 0 < q) (ha : 0 < a) (haq : a < q) :
    (-1 : ℂ)/(1-negativeRoot q a) =
      -1/2+Complex.I/2*(Real.cot (Real.pi*(a : ℝ)/(q : ℝ)) : ℂ) := by
  have hc : Complex.cot ((Real.pi : ℂ)*((a : ℂ)/(q : ℂ)))=
      (Real.cot (Real.pi*(a : ℝ)/(q : ℝ)) : ℂ) := by
    rw [Complex.ofReal_cot]
    congr 1
    push_cast
    ring
  have h := sawtoothFourier_eq_cotangent hq ha haq
  rw [sawtoothFourier_eq_root_ratio hq ha haq,hc] at h
  have hz := sub_ne_zero.mpr (negativeRoot_ne_one hq ha haq).symm
  calc
    _ = -1/2+(-(1+negativeRoot q a)/(2*(1-negativeRoot q a))) := by
      field_simp [hz]
      ring
    _ = _ := by rw [h]

def potentialCoefficient (v c : ℝ) : ℂ := ((-v/3 : ℝ) : ℂ)+((v*c/3 : ℝ) : ℂ)*Complex.I

theorem finitePotential_fourier_cotangent {q a : ℕ}
    (hq : 2 ≤ q) (ha : 0 < a) (haq : a < q) (hcop : a.Coprime q)
    (v : ℕ → ℝ) (M : ℕ) :
    fourierFunctional q a (finitePotential v M) =
      potentialCoefficient (finiteAmplitude v q M) (Real.cot (Real.pi*(a : ℝ)/(q : ℝ))) := by
  rw [finitePotential_fourier hq hcop,primitive_coefficient_cotangent (by omega) ha haq]
  unfold potentialCoefficient
  push_cast
  ring

theorem collisionPotential_fourier_cotangent {q a : ℕ}
    (hq : 2 ≤ q) (ha : 0 < a) (haq : a < q) (hcop : a.Coprime q) :
    fourierFunctional q a collisionPotential =
      potentialCoefficient (amplitude q) (Real.cot (Real.pi*(a : ℝ)/(q : ℝ))) := by
  rw [collisionPotential_fourier hq hcop]
  have he : -2*(amplitude q : ℂ)/(3*(1-negativeRoot q a))=
      (2/3 : ℂ)*(amplitude q : ℂ)*(-1/(1-negativeRoot q a)) := by
    have hz := sub_ne_zero.mpr (negativeRoot_primitive_ne_one hq hcop).symm
    field_simp [hz]
  rw [he,primitive_coefficient_cotangent (by omega) ha haq]
  unfold potentialCoefficient
  push_cast
  ring

theorem potential_coefficient_interval {v l u c cl ch : ℝ}
    (hv : l ≤ v ∧ v ≤ u) (hc : cl ≤ c ∧ c ≤ ch) :
    -u/3 ≤ (potentialCoefficient v c).re ∧
    (potentialCoefficient v c).re ≤ -l/3 ∧
    productLower l u cl ch/3 ≤ (potentialCoefficient v c).im ∧
    (potentialCoefficient v c).im ≤ productUpper l u cl ch/3 := by
  have hp := product_interval hv hc
  simp only [potentialCoefficient,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,add_zero,zero_add,sub_zero]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem increment_coefficient_interval {v l u : ℝ} (hv : l ≤ v ∧ v ≤ u) :
    -2*u/3 ≤ -2*v/3 ∧ -2*v/3 ≤ -2*l/3 := by
  constructor <;> linarith

theorem increment_mass_interval {v l u : ℝ} (hv : l ≤ v ∧ v ≤ u) :
    4*squareLower l u/9 ≤ 4*v^2/9 ∧ 4*v^2/9 ≤ 4*squareUpper l u/9 := by
  have h := square_interval hv
  constructor <;> linarith

theorem potential_mass_interval {v l u s sl sh : ℝ}
    (hv : l ≤ v ∧ v ≤ u) (hs0 : 0 < sl) (hs : sl ≤ s ∧ s ≤ sh) :
    (squareLower l u/9)*(1/sh)^2 ≤ (v^2/9)*(1/s)^2 ∧
    (v^2/9)*(1/s)^2 ≤ (squareUpper l u/9)*(1/sl)^2 := by
  have ha := square_interval hv
  have hb := reciprocal_square_interval hs0 hs
  have hla : 0 ≤ squareLower l u := squareLower_nonneg l u
  have hua : 0 ≤ squareUpper l u := (sq_nonneg v).trans ha.2
  constructor
  · apply (mul_le_mul_of_nonneg_right (show squareLower l u/9 ≤ v^2/9 by linarith)
      (sq_nonneg (1/sh))).trans
    exact mul_le_mul_of_nonneg_left hb.1 (by positivity)
  · apply (mul_le_mul_of_nonneg_right (show v^2/9 ≤ squareUpper l u/9 by linarith)
      (sq_nonneg (1/s))).trans
    exact mul_le_mul_of_nonneg_left hb.2 (by positivity)

theorem full_spectral_mass_enclosure {i : CollisionSpectralWeights.SpectralAddress}
    {l u sl sh : ℝ} (hv : l ≤ amplitude i.1 ∧ amplitude i.1 ≤ u) (hs0 : 0 < sl)
    (hs : sl ≤ Real.sin (Real.pi*(i.2.1 : ℝ)/(i.1 : ℝ)) ∧
      Real.sin (Real.pi*(i.2.1 : ℝ)/(i.1 : ℝ)) ≤ sh) :
    4*squareLower l u/9 ≤ CollisionSpectralWeights.incrementMass i ∧
    CollisionSpectralWeights.incrementMass i ≤ 4*squareUpper l u/9 ∧
    (squareLower l u/9)*(1/sh)^2 ≤ CollisionSpectralWeights.potentialMass i ∧
    CollisionSpectralWeights.potentialMass i ≤ (squareUpper l u/9)*(1/sl)^2 := by
  have hg := increment_mass_interval hv
  have hy := potential_mass_interval hv hs0 hs
  rw [CollisionSpectralWeights.potentialMass_literal]
  have he : (1/9 : ℝ)*(amplitude i.1)^2*
      (Real.sin (Real.pi*(i.2.1 : ℝ)/(i.1 : ℝ))^2)⁻¹ =
      ((amplitude i.1)^2/9)*(1/Real.sin (Real.pi*(i.2.1 : ℝ)/(i.1 : ℝ)))^2 := by
    simp only [one_div,inv_pow]
    ring
  rw [he]
  simp only [CollisionSpectralWeights.incrementMass]
  exact ⟨by nlinarith [hg.1],by nlinarith [hg.2],hy.1,hy.2⟩

end NField.Alignment.CollisionFourierEnclosure
