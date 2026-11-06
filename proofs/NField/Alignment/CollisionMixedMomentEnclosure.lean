/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCotangentSeriesEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionMixedMomentEnclosure
open scoped BigOperators Classical
open CollisionComplexPhaseEnclosure CollisionCotangentMixedMoment CollisionAmplitudeCotangent
open CollisionHarmonicSeed CollisionAmplitudeArithmetic CollisionFourierEnclosure
open CollisionJordanVariance

def oddCharacterSum {q : ℕ} [NeZero q] (f : DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,if χ.Odd then f χ else 0

theorem mixed_moment_enclosure {q : ℕ} [NeZero q]
    (rl ru il iu : DirichletCharacter ℂ q → ℝ)
    (h : ∀ χ : DirichletCharacter ℂ q,χ.Odd →
      rectangleContains (DirichletCharacter.LFunction χ⁻¹ 1*DirichletCharacter.LFunction χ 2)
        (rl χ) (ru χ) (il χ) (iu χ)) :
    rectangleContains (cotangentCharacterMoment q)
      (oddCharacterSum rl) (oddCharacterSum ru) (oddCharacterSum il) (oddCharacterSum iu) := by
  apply sum_enclosure Finset.univ
  intro χ _
  by_cases hχ : χ.Odd
  · simpa only [if_pos hχ] using h χ hχ
  · simp [hχ,rectangleContains]

theorem amplitude_real_mixed_moment {q : ℕ} [NeZero q] (hq : 2≤q) :
    amplitude q=1/2-(cotangentCharacterMoment q).re/
      (zetaThree*deltaThree q*(q.totient : ℝ)) := by
  have hm : cotangentCharacterMoment q=((cotangentCharacterMoment q).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using cotangentCharacterMoment_real hq
  have h := literal_original_amplitude_mixed_moment hq
  rw [hm] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem mixed_amplitude_enclosure {q : ℕ} [NeZero q] (hq : 2≤q)
    {ml mu zl zu : ℝ} (hz0 : 0<zl)
    (hm : ml ≤ (cotangentCharacterMoment q).re ∧ (cotangentCharacterMoment q).re ≤ mu)
    (hz : zl ≤ zetaThree ∧ zetaThree ≤ zu) :
    1/2-productUpper ml mu (1/(zu*deltaThree q*(q.totient : ℝ)))
      (1/(zl*deltaThree q*(q.totient : ℝ))) ≤ amplitude q ∧
    amplitude q ≤ 1/2-productLower ml mu (1/(zu*deltaThree q*(q.totient : ℝ)))
      (1/(zl*deltaThree q*(q.totient : ℝ))) := by
  have hd := deltaThree_pos q
  have hp : (0 : ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hden : zl*deltaThree q*(q.totient : ℝ) ≤ zetaThree*deltaThree q*(q.totient : ℝ) ∧
      zetaThree*deltaThree q*(q.totient : ℝ) ≤ zu*deltaThree q*(q.totient : ℝ) :=
    ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz.1 hd.le) hp.le,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz.2 hd.le) hp.le⟩
  have hi := reciprocal_interval (show 0<zl*deltaThree q*(q.totient : ℝ) by positivity) hden
  have he := product_interval hm hi
  rw [amplitude_real_mixed_moment hq]
  simp only [mul_one_div] at he
  constructor <;> linarith [he.1,he.2]

theorem intersect_amplitude_enclosures {q : ℕ} {l u a b : ℝ}
    (h : l ≤ amplitude q ∧ amplitude q ≤ u) (hp : a ≤ amplitude q ∧ amplitude q ≤ b) :
    max l a ≤ amplitude q ∧ amplitude q ≤ min u b :=
  ⟨max_le h.1 hp.1,le_min h.2 hp.2⟩

end NField.Alignment.CollisionMixedMomentEnclosure
