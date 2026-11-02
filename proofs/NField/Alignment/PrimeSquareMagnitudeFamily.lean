/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FiniteMagnitudeDecorrelation
import NField.Papers.TheCollisionSpectrum

/-!
# The concrete prime-square magnitude family

The sample includes every primitive odd character, with both members of each
conjugate pair. Its short sum, generalized Bernoulli magnitude and analytic
L-value are actual functions, not unconstrained scalar stand-ins.

The primitive kernel and Bernoulli-to-L relation reuse existing proofs.
The concrete short-sum second moment is assembled in
PrimeSquareMagnitudeShortMoment. The Bernoulli and L-value marginal is
assembled in PrimeSquareMagnitudeBernoulliMoment. The twisted and mixed
moments and analytic estimates still require the ledgered formalization.
-/

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators Topology
open Filter
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.SpectralRepulsion
open NField.Alignment.FiniteMagnitudeDecorrelation

abbrev PrimitiveOddFamily (b : ℕ) :=
  {χ : Character (b ^ 2) // χ.IsPrimitive ∧ χ.Odd}

noncomputable instance familyFintype (b : ℕ) : Fintype (PrimitiveOddFamily b) :=
  Fintype.ofFinite _

theorem family_card_eq_count (b : ℕ) :
    Fintype.card (PrimitiveOddFamily b) = primitiveOddCharacterCount (b ^ 2) := by
  classical
  simp [PrimitiveOddFamily, primitiveOddCharacterCount, Fintype.card_subtype]

theorem family_population {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    (Fintype.card (PrimitiveOddFamily b) : ℝ) =
      (((b - 1) ^ 2 : ℕ) : ℝ) / 2 := by
  rw [family_card_eq_count]
  exact NField.Papers.TheCollisionSpectrum.exact_primitive_odd_population hb hbodd

theorem family_nonempty {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) : Nonempty (PrimitiveOddFamily b) := by
  have hc := family_population hb hbodd
  have hb1 : 1 < b := hb.one_lt
  have hstep : 0 < b - 1 := by omega
  have hp : 0 < (Fintype.card (PrimitiveOddFamily b) : ℝ) := by
    rw [hc]
    positivity
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hp)

noncomputable def shortSum (b : ℕ) (χ : PrimitiveOddFamily b) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (b - 1), star (χ.val (k : ZMod (b ^ 2)))

noncomputable def bernoulliSum (b : ℕ) [NeZero (b ^ 2)] (χ : PrimitiveOddFamily b) : ℂ :=
  generalizedBernoulliOne χ.val⁻¹

noncomputable def shortMagnitude (b : ℕ) (χ : PrimitiveOddFamily b) : ℝ :=
  ‖shortSum b χ‖ / Real.sqrt b

noncomputable def lMagnitude (b : ℕ) [NeZero (b ^ 2)] (χ : PrimitiveOddFamily b) : ℝ :=
  ‖DirichletCharacter.LFunction χ.val 1‖

noncomputable def familyCorrelation (b : ℕ) [NeZero (b ^ 2)] : ℝ :=
  magnitudeCorrelation (shortMagnitude b) (lMagnitude b)

theorem short_magnitude_nonneg (b : ℕ) (χ : PrimitiveOddFamily b) :
    0 ≤ shortMagnitude b χ :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem l_magnitude_nonneg (b : ℕ) [NeZero (b ^ 2)] (χ : PrimitiveOddFamily b) :
    0 ≤ lMagnitude b χ := norm_nonneg _

theorem bernoulli_l_magnitude_sq {b : ℕ} [NeZero (b ^ 2)]
    (hb : b.Prime) (χ : PrimitiveOddFamily b) :
    Complex.normSq (bernoulliSum b χ) =
      ((b ^ 2 : ℕ) : ℝ) / Real.pi ^ 2 *
        Complex.normSq (DirichletCharacter.LFunction χ.val 1) :=
  NField.Papers.TheCollisionSpectrum.exact_bernoulli_l_value_magnitude
    hb χ.property.1 χ.property.2

/-- The actual sample has an eventual zero correlation if its explicit
fractional moment tends to zero and its stated L-magnitude bounds hold.
Those arithmetic and analytic inputs are visible in the theorem type. -/
theorem correlation_limit_from_character_moments
    {α : Type*} {l : Filter α} (base : α → ℕ)
    [∀ a, NeZero (base a ^ 2)]
    [∀ a, Nonempty (PrimitiveOddFamily (base a))]
    (V M v : ℝ) (hv : 0 < v)
    (hXsecond : ∀ a, uniformAverage
      (fun χ => shortMagnitude (base a) χ ^ 2) = 1)
    (hYsecond : ∀ a, uniformAverage
      (fun χ => lMagnitude (base a) χ ^ 2) ≤ V)
    (hthird : ∀ a, magnitudeMoment 3 (lMagnitude (base a)) ≤ M)
    (hvariance : ∀ a, v ≤ uniformVariance (lMagnitude (base a)))
    (hHarper : Tendsto
      (fun a => magnitudeMoment (3/2) (shortMagnitude (base a))) l (𝓝 0)) :
    Tendsto (fun a => familyCorrelation (base a)) l (𝓝 0) :=
  correlation_limit_from_moments
    (fun a => shortMagnitude (base a)) (fun a => lMagnitude (base a))
    (fun a => short_magnitude_nonneg (base a))
    (fun a => l_magnitude_nonneg (base a))
    V M v hv hXsecond hYsecond hthird hvariance hHarper

end NField.Alignment.PrimeSquareMagnitudeFamily
