/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareShortMoment
import NField.Alignment.PrimeSquareMagnitudeFamily
import NField.Alignment.PrimeCarrySpectralBridge

/-!
# The exact short-sum marginal for prime-square magnitudes

This assembles the first clause of Proposition 3 in Magnitude Decorrelation
in the Collision Spectrum for its actual short character sum and complete
primitive odd sample. Orthogonality gives the full odd moment; every lifted
odd character contributes zero. Conjugation and indexing agree with shortSum.

The normalized average square is one for every odd prime, including base
three. The manuscript only needs bases at least five. The Bernoulli marginal,
twisted moments and analytic estimates remain separate proof obligations.
-/

set_option autoImplicit false

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod Topology
open Filter
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.PrimeCarrySpectralBridge
open NField.Alignment.SpectralRepulsion
open NField.Alignment.FiniteMagnitudeDecorrelation

attribute [local instance] Classical.propDecidable

alias firstWindowUnit_neg_ne := NField.Alignment.PrimeSquareShortMoment.firstWindowUnit_neg_ne

alias odd_packet_second_moment := NField.Alignment.PrimeSquareShortMoment.odd_packet_second_moment

alias odd_shortWindow_second_moment := NField.Alignment.PrimeSquareShortMoment.odd_shortWindow_second_moment

alias primitive_odd_shortWindow_second_moment := NField.Alignment.PrimeSquareShortMoment.primitive_odd_shortWindow_second_moment

theorem shortSum_eq_conj_window {b : ℕ} (hb : b.Prime)
    (χ : PrimitiveOddFamily b) : shortSum b χ = star (shortWindowSum hb χ.val) := by
  classical
  unfold shortSum shortWindowSum firstWindowUnit
  simp only [ZMod.coe_unitOfCoprime, star_sum]
  change (∑ k ∈ Finset.Icc 1 (b - 1), star (χ.val (k : ZMod (b ^ 2)))) =
    ∑ i : Fin (b - 1), star (χ.val ((i.val + 1 : ℕ) : ZMod (b ^ 2)))
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => star (χ.val ((k + 1 : ℕ) : ZMod (b ^ 2)))) (b - 1)]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.sub_add_cancel hb.one_lt.le, Nat.add_comm]

/-- Exact total of the squared magnitudes over every primitive odd character.
The theorem includes both members of each conjugate pair. -/
theorem shortSum_second_moment_total {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) :
    (∑ χ : PrimitiveOddFamily b, ‖shortSum b χ‖ ^ 2) =
      (b : ℝ) * ((b - 1 : ℕ) : ℝ) ^ 2 / 2 := by
  classical
  have h := primitive_odd_shortWindow_second_moment hb
  rw [Finset.sum_subtype (p := fun χ : Character (b ^ 2) => χ.IsPrimitive ∧ χ.Odd)
    (F := familyFintype b) _ (by simp) (fun χ =>
    (Complex.normSq (shortWindowSum hb χ) : ℂ))] at h
  have hreal :
      (∑ χ : PrimitiveOddFamily b, Complex.normSq (shortWindowSum hb χ.val)) =
        (1 / 2 : ℝ) * ((b ^ 2).totient : ℝ) * (b - 1 : ℕ) := by
    apply Complex.ofReal_injective
    push_cast
    exact h
  have hnorm : ∀ χ : PrimitiveOddFamily b,
      ‖shortSum b χ‖ ^ 2 = Complex.normSq (shortWindowSum hb χ.val) := by
    intro χ
    rw [shortSum_eq_conj_window hb, norm_star, Complex.sq_norm]
  simp_rw [hnorm]
  rw [hreal, Nat.totient_prime_pow hb (by omega : 0 < 2)]
  norm_num
  ring

/-- The first marginal identity in equation `eq:marginals`: the uniform
average of `shortMagnitude` squared equals one. This does not assert the
second identity there for the L-value magnitude. -/
theorem short_magnitude_second_moment {b : ℕ} [NeZero b] [NeZero (b ^ 2)]
    (hb : b.Prime) (hbodd : b ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily b => shortMagnitude b χ ^ 2) = 1 := by
  classical
  unfold uniformAverage shortMagnitude
  simp_rw [div_pow]
  rw [← Finset.sum_div, shortSum_second_moment_total hb,
    Real.sq_sqrt (Nat.cast_nonneg b), family_population hb hbodd]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne_zero
  have hb2 := hb.two_le
  have hb1 : ((b - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : b - 1 ≠ 0)
  push_cast
  field_simp

/-- The exact short-sum second moment is proved here, so it is no longer an
input to this limit deduction. The L-magnitude bounds, positive variance and
vanishing short fractional moment remain explicit hypotheses. -/
theorem correlation_limit_from_remaining_inputs
    {α : Type*} {l : Filter α} (base : α → ℕ)
    [∀ a, NeZero (base a ^ 2)]
    (hprime : ∀ a, (base a).Prime) (hodd : ∀ a, base a ≠ 2)
    (V M v : ℝ) (hv : 0 < v)
    (hYsecond : ∀ a, uniformAverage
      (fun χ => lMagnitude (base a) χ ^ 2) ≤ V)
    (hthird : ∀ a, magnitudeMoment 3 (lMagnitude (base a)) ≤ M)
    (hvariance : ∀ a, v ≤ uniformVariance (lMagnitude (base a)))
    (hHarper : Tendsto
      (fun a => magnitudeMoment (3/2) (shortMagnitude (base a))) l (𝓝 0)) :
    Tendsto (fun a => familyCorrelation (base a)) l (𝓝 0) := by
  letI : ∀ a, NeZero (base a) := fun a => ⟨(hprime a).ne_zero⟩
  letI : ∀ a, Nonempty (PrimitiveOddFamily (base a)) :=
    fun a => family_nonempty (hprime a) (hodd a)
  exact correlation_limit_from_character_moments base V M v hv
    (fun a => short_magnitude_second_moment (hprime a) (hodd a))
    hYsecond hthird hvariance hHarper

end NField.Alignment.PrimeSquareMagnitudeFamily
