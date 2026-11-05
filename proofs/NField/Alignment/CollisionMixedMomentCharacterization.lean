/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCotangentPositivity
import NField.Alignment.CollisionMassInverse

/-!
# The complete mixed-moment characterization

The formula is for the original collision amplitudes. Any nonnegative
summable mass with the same amplitudes has the original mass, by absolute
Mobius inversion. The displayed formula itself supplies the required
energy summability, so the selector does not assume it separately.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMixedMomentCharacterization

open CollisionGeneralWeightCriterion CollisionMassInverse CollisionJordanVariance
open CollisionRemainderDynamics CollisionMassReadout CollisionAmplitudeArithmetic CollisionHarmonicSeed
open CollisionAmplitudeCotangent CollisionCotangentMixedMoment CollisionCotangentPositivity

def HasMixedMomentAmplitudes (v : ℕ → ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], 2≤q → (generalAmplitude v q : ℂ)=
    1/2-cotangentCharacterMoment q/((zetaThree : ℂ)*(deltaThree q : ℂ)*(q.totient : ℂ))

theorem original_mass_has_mixed_moment_amplitudes : HasMixedMomentAmplitudes collisionWeight := by
  intro q _ hq
  exact literal_original_amplitude_mixed_moment hq

theorem mass_eq_collision_of_amplitudes (v : ℕ → ℝ) (hv : ∀ n, 0≤v n)
    (h0 : v 0=0) (h1 : v 1=0) (hs : Summable v)
    (ha : ∀ q, 2≤q → generalAmplitude v q=amplitude q) : v=collisionWeight := by
  have heq : generalEnergy v=conductorEnergy := by
    funext q
    unfold generalEnergy conductorEnergy
    split_ifs with hq
    · rw [ha q hq]
    · rfl
  have he : Summable (generalEnergy v) := by rw [heq]; exact conductorEnergy_summable
  have hw : Summable (generalEnergy collisionWeight) := conductorEnergy_summable
  funext k
  by_cases hk : 2≤k
  · rw [mass_moebius_inverse v hv h0 hs he (by omega : 0<k),
      mass_moebius_inverse collisionWeight collisionWeight_nonneg collisionWeight_zero
        collisionWeight_summable hw (by omega : 0<k)]
    apply tsum_congr
    intro j
    by_cases hj : j=0
    · simp [hj]
    · have hkj : 2≤k*j := hk.trans (Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hj))
      rw [ha (k*j) hkj]
      rfl
  · interval_cases k <;> simp_all

theorem mixed_moment_mass_selector (v : ℕ → ℝ) (hv : ∀ n, 0≤v n)
    (h0 : v 0=0) (h1 : v 1=0) (hs : Summable v) :
    HasMixedMomentAmplitudes v ↔ v=collisionWeight := by
  constructor
  · intro hformula
    apply mass_eq_collision_of_amplitudes v hv h0 h1 hs
    intro q hq
    letI : NeZero q := ⟨by omega⟩
    apply Complex.ofReal_injective
    exact (hformula q hq).trans (literal_original_amplitude_mixed_moment hq).symm
  · rintro rfl
    exact original_mass_has_mixed_moment_amplitudes

theorem literal_mixed_moment_characterization :
    (∀ (q : ℕ) [NeZero q], 2≤q → (amplitude q : ℂ)=
      1/2-cotangentCharacterMoment q/((zetaThree : ℂ)*(deltaThree q : ℂ)*(q.totient : ℂ))) ∧
    (∀ (q : ℕ) [NeZero q], 2≤q → (cotangentCharacterMoment q).im=0) ∧
    amplitude 2=1/2 ∧
    (∀ q : ℕ, 2<q → 0<amplitude q ∧ amplitude q<1/2) ∧
    (∀ v : ℕ → ℝ, (∀ n, 0≤v n) → v 0=0 → v 1=0 → HasSum v 1 →
      (HasMixedMomentAmplitudes v ↔ v=collisionWeight)) := by
  refine ⟨fun q _ hq => literal_original_amplitude_mixed_moment hq,
    fun q _ hq => cotangentCharacterMoment_real hq,original_amplitude_two,
    fun q hq => original_amplitude_strict_bounds hq,?_⟩
  intro v hv h0 h1 hs
  exact mixed_moment_mass_selector v hv h0 h1 hs.summable

end NField.Alignment.CollisionMixedMomentCharacterization
