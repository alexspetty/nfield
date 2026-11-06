/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicSeriesEnclosure
import NField.Alignment.CollisionMixedMomentEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionRootIdentityEnclosure
open scoped BigOperators
open CollisionComplexPhaseEnclosure CollisionFourierEnclosure CollisionHarmonicRootSeries
open CollisionHarmonicRootIdentity CollisionHarmonicRootAverage CollisionHarmonicSeed
open CollisionFiniteSineTransform

theorem phase_ratio_ramanujan (q a : ℕ) :
    phase ((a : ℝ)/(q : ℝ))=CollisionRamanujan.phase q 1 a := by
  unfold phase CollisionRamanujan.phase
  push_cast
  congr 1
  ring

theorem phase_product_mod {q : ℕ} (hq : 0<q) (a n : ℕ) :
    phase (((a*n%q : ℕ) : ℝ)/(q : ℝ))=CollisionRamanujan.phase q (n : ℤ) a := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [phase_ratio_ramanujan,CollisionRamanujan.phase_std hq,CollisionRamanujan.phase_std hq]
  simp [Nat.cast_mul,mul_comm]

theorem root_power_reduced_phase {q : ℕ} (hq : 0<q) (a n : ℕ) :
    Complex.exp ((rootAngle q a : ℂ)*Complex.I)^n=
      phase (((a*n%q : ℕ) : ℝ)/(q : ℝ)) := by
  rw [root_power_eq_phase,phase_product_mod hq]

theorem root_identity_enclosure {θ zl zu cl cu sl su wl wu : ℝ}
    (hθ0 : 0≤θ) (hθ2 : θ≤2*Real.pi)
    (hz : zl≤zetaThree ∧ zetaThree≤zu)
    (hc : cl≤cubicCosine θ ∧ cubicCosine θ≤cu)
    (hs : sl ≤ quadraticSine θ ∧ quadraticSine θ ≤ su)
    (hw : wl≤(θ-Real.pi)/2 ∧ (θ-Real.pi)/2≤wu) :
    (zl+cl)/2+productLower wl wu sl su ≤ (harmonicBoundary θ).re ∧
    (harmonicBoundary θ).re ≤ (zu+cu)/2+productUpper wl wu sl su := by
  rw [harmonicBoundary,literal_harmonic_root_identity hθ0 hθ2]
  have h := product_interval hw hs
  constructor <;> linarith [hz.1,hz.2,hc.1,hc.2,h.1,h.2]

theorem root_angle_weight_enclosure (q a : ℕ) {pl pu : ℝ}
    (hp : pl≤Real.pi ∧ Real.pi≤pu) :
    productLower pl pu (((a : ℝ)/(q : ℝ))-1/2) (((a : ℝ)/(q : ℝ))-1/2) ≤
      (rootAngle q a-Real.pi)/2 ∧
    (rootAngle q a-Real.pi)/2 ≤
      productUpper pl pu (((a : ℝ)/(q : ℝ))-1/2) (((a : ℝ)/(q : ℝ))-1/2) := by
  rw [rootAngle_weight]
  exact product_interval hp ⟨le_rfl,le_rfl⟩

theorem sine_transform_phase_sum {q : ℕ} (hq : 0<q) (n : ℕ) :
    finiteSineTransform q n=∑ a∈Finset.Ico 1 q,
      ((a : ℝ)/(q : ℝ)-1/2)*(phase (((a*n%q : ℕ) : ℝ)/(q : ℝ))).im := by
  unfold finiteSineTransform
  apply Finset.sum_congr rfl
  intro a _
  rw [phase_product_mod hq]
  unfold CollisionRamanujan.phase
  have he : 2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(a : ℂ)/(q : ℂ)=
      ((2*Real.pi*(a : ℝ)*(n : ℝ)/(q : ℝ) : ℝ) : ℂ)*Complex.I := by push_cast; ring
  push_cast
  rw [he,Complex.exp_ofReal_mul_I_im]

theorem sine_transform_cotangent_enclosure {q : ℕ} (hq : 0<q) (n : ℕ)
    (hn : ¬q∣n) {l u : ℝ}
    (hc : l≤Real.cot (Real.pi*(n : ℝ)/(q : ℝ)) ∧
      Real.cot (Real.pi*(n : ℝ)/(q : ℝ))≤u) :
    -u/2≤finiteSineTransform q n ∧ finiteSineTransform q n≤-l/2 := by
  rw [literal_finite_sine_transform hq,if_neg hn]
  constructor <;> linarith [hc.1,hc.2]

theorem sine_transform_multiple_exact {q : ℕ} (hq : 0<q) (n : ℕ) (hn : q∣n) :
    finiteSineTransform q n=0 := by
  simp [literal_finite_sine_transform hq,hn]

theorem closed_disk_of_coordinates (z : ℂ) (h : z.re^2+z.im^2≤1) : ‖z‖≤1 := by
  have he := Complex.normSq_eq_norm_sq z
  rw [Complex.normSq_apply] at he
  nlinarith [norm_nonneg z]

theorem phase_integer_residue {q : ℕ} (hq : 0<q) (a : ℕ) (n : ℤ) :
    letI : NeZero q := ⟨hq.ne'⟩
    phase (((a*(n : ZMod q).val%q : ℕ) : ℝ)/(q : ℝ))=CollisionRamanujan.phase q n a := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [phase_product_mod hq,CollisionRamanujan.phase_std hq,CollisionRamanujan.phase_std hq]
  simp

def integerSineTransform (q : ℕ) (n : ℤ) : ℝ :=
  ∑ a∈Finset.Ico 1 q,((a : ℝ)/(q : ℝ)-1/2)*
    Real.sin (2*Real.pi*(a : ℝ)*(n : ℝ)/(q : ℝ))

theorem integer_sine_transform_reduced {q : ℕ} (hq : 0<q) (n : ℤ) :
    letI : NeZero q := ⟨hq.ne'⟩
    integerSineTransform q n=finiteSineTransform q (n : ZMod q).val := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [sine_transform_phase_sum hq,integerSineTransform]
  apply Finset.sum_congr rfl
  intro a _
  rw [phase_integer_residue hq]
  unfold CollisionRamanujan.phase
  have he : 2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(a : ℂ)/(q : ℂ)=
      ((2*Real.pi*(a : ℝ)*(n : ℝ)/(q : ℝ) : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I_im]

end NField.Alignment.CollisionRootIdentityEnclosure
