/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFourierEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionComplexPhaseEnclosure
open CollisionFourierEnclosure

def phase (r : ℝ) : ℂ := Complex.exp (((2*(Real.pi*r) : ℝ) : ℂ)*Complex.I)

def rectangleContains (z : ℂ) (rl ru il iu : ℝ) : Prop :=
  rl ≤ z.re ∧ z.re ≤ ru ∧ il ≤ z.im ∧ z.im ≤ iu

theorem phase_coordinates (r : ℝ) :
    (phase r).re=Real.cos (2*(Real.pi*r)) ∧ (phase r).im=Real.sin (2*(Real.pi*r)) := by
  exact ⟨Complex.exp_ofReal_mul_I_re _,Complex.exp_ofReal_mul_I_im _⟩

theorem phase_zero : rectangleContains (phase 0) 1 1 0 0 := by
  simp [rectangleContains,phase]

theorem phase_half : rectangleContains (phase (1/2)) (-1) (-1) 0 0 := by
  rw [rectangleContains,(phase_coordinates (1/2)).1,(phase_coordinates (1/2)).2]
  have h : 2*(Real.pi*(1/2))=Real.pi := by ring
  rw [h]
  simp

theorem double_angle_enclosure {r sl su cl cu : ℝ}
    (hs : sl ≤ Real.sin (Real.pi*r) ∧ Real.sin (Real.pi*r) ≤ su)
    (hc : cl ≤ Real.cos (Real.pi*r) ∧ Real.cos (Real.pi*r) ≤ cu) :
    rectangleContains (phase r)
      (squareLower cl cu-squareUpper sl su) (squareUpper cl cu-squareLower sl su)
      (2*productLower sl su cl cu) (2*productUpper sl su cl cu) := by
  have hc2 := square_interval hc
  have hs2 := square_interval hs
  have hp := product_interval hs hc
  rw [rectangleContains,(phase_coordinates r).1,(phase_coordinates r).2,
    Real.cos_two_mul',Real.sin_two_mul]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [hc2.1,hc2.2,hs2.1,hs2.2,hp.1,hp.2]

theorem conjugate_enclosure {z : ℂ} {rl ru il iu : ℝ}
    (h : rectangleContains z rl ru il iu) : rectangleContains (star z) rl ru (-iu) (-il) := by
  rcases h with ⟨h1,h2,h3,h4⟩
  simp only [rectangleContains,Complex.star_def,Complex.conj_re,Complex.conj_im]
  exact ⟨h1,h2,by linarith,by linarith⟩

theorem product_enclosure {z w : ℂ} {arl aru ail aiu brl bru bil biu : ℝ}
    (hz : rectangleContains z arl aru ail aiu) (hw : rectangleContains w brl bru bil biu) :
    rectangleContains (z*w)
      (productLower arl aru brl bru-productUpper ail aiu bil biu)
      (productUpper arl aru brl bru-productLower ail aiu bil biu)
      (productLower arl aru bil biu+productLower ail aiu brl bru)
      (productUpper arl aru bil biu+productUpper ail aiu brl bru) := by
  rcases hz with ⟨zr1,zr2,zi1,zi2⟩
  rcases hw with ⟨wr1,wr2,wi1,wi2⟩
  have hrr := product_interval ⟨zr1,zr2⟩ ⟨wr1,wr2⟩
  have hii := product_interval ⟨zi1,zi2⟩ ⟨wi1,wi2⟩
  have hri := product_interval ⟨zr1,zr2⟩ ⟨wi1,wi2⟩
  have hir := product_interval ⟨zi1,zi2⟩ ⟨wr1,wr2⟩
  simp only [rectangleContains,Complex.mul_re,Complex.mul_im]
  exact ⟨by linarith [hrr.1,hii.2],by linarith [hrr.2,hii.1],
    by linarith [hri.1,hir.1],by linarith [hri.2,hir.2]⟩

theorem sum_enclosure {α : Type*} (s : Finset α) (z : α → ℂ) (rl ru il iu : α → ℝ)
    (h : ∀ a ∈ s,rectangleContains (z a) (rl a) (ru a) (il a) (iu a)) :
    rectangleContains (∑ a ∈ s,z a) (∑ a ∈ s,rl a) (∑ a ∈ s,ru a)
      (∑ a ∈ s,il a) (∑ a ∈ s,iu a) := by
  simp only [rectangleContains,Complex.re_sum,Complex.im_sum]
  exact ⟨Finset.sum_le_sum (fun a ha => (h a ha).1),
    Finset.sum_le_sum (fun a ha => (h a ha).2.1),
    Finset.sum_le_sum (fun a ha => (h a ha).2.2.1),
    Finset.sum_le_sum (fun a ha => (h a ha).2.2.2)⟩

end NField.Alignment.CollisionComplexPhaseEnclosure
