/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryLocalizationUnconditional
import NField.Alignment.DedekindCarrierFourierBound

/-! # The open signed-damping hypothesis on literal integer intervals -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerSignedDamping
open scoped BigOperators Classical
open LiveCarrierDamping DedekindCarrierFourierBound DedekindAbelRemainder
  DedekindCollisionKernel CarryBoundarySpectra PrimeSecondaryCoefficient PrimeCarryEnergyBridge
  SecondaryCapacityLedger

def integerIntervalSum {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) (start : ℤ) (length : ℕ) : ℂ :=
  ∑ j ∈ Finset.range length,residueDedekindFunction β ((start : ZMod k)+(j : ZMod k))

/-- This is a proposition, not an asserted theorem: it is the paper's open problem. -/
def IntegerSignedCarrierDamping : Prop :=
  ∃ C : ℝ,0 ≤ C ∧ ∀ (k : ℕ) [NeZero k],2 ≤ k → ∀ β : (ZMod k)ˣ,
    ∀ start : ℤ,∀ length : ℕ,‖integerIntervalSum β start length‖ ≤
      C*(k : ℝ)*Real.log (2*(k : ℝ))

theorem interval_nat {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) (start length : ℕ) :
    integerIntervalSum β (start : ℤ) length=signedDedekindIntervalSum k β start length := by
  unfold integerIntervalSum signedDedekindIntervalSum
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← residueDedekindFunction_natCast]
  simp [Nat.add_comm]

theorem interval_mod_start {k : ℕ} [NeZero k] (β : (ZMod k)ˣ) (start : ℤ) (length : ℕ) :
    integerIntervalSum β start length=integerIntervalSum β (((start : ZMod k).val : ℕ) : ℤ) length := by
  unfold integerIntervalSum
  simp

theorem dedekind_modulus_one (u : (ZMod 1)ˣ) : dedekindSum u=0 := by
  unfold dedekindSum
  apply Finset.sum_eq_zero
  intro x hx
  rw [show x=(0 : ZMod 1) by exact Subsingleton.elim _ _]
  simp [centeredSawtooth]

theorem interval_modulus_one (β : (ZMod 1)ˣ) (start length : ℕ) :
    signedDedekindIntervalSum 1 β start length=0 := by
  unfold signedDedekindIntervalSum
  apply Finset.sum_eq_zero
  intro a ha
  unfold residueDedekindSequence
  split_ifs
  · exact dedekind_modulus_one _
  · rfl

/-- Title: `The signed-damping hypothesis is unchanged on integer intervals`. -/
theorem signed_damping_iff_integer_intervals :
    SignedDedekindCarrierDamping ↔ IntegerSignedCarrierDamping := by
  constructor
  · rintro ⟨C,hC,hb⟩
    refine ⟨C,hC,?_⟩
    intro k inst hk β start length
    rw [interval_mod_start,interval_nat]
    exact hb k inst β (start : ZMod k).val length
  · rintro ⟨C,hC,hb⟩
    refine ⟨C,hC,?_⟩
    intro k inst β start length
    by_cases hk : 2 ≤ k
    · rw [← interval_nat]
      exact hb k hk β start length
    · have hk1 : k=1 := by have := NeZero.ne k; omega
      subst k
      rw [interval_modulus_one,norm_zero]
      positivity

/-- Title: `Sampling under the literal integer signed-damping hypothesis`. -/
theorem sampling_under_integer_signed_damping (h : IntegerSignedCarrierDamping) :
    PrimeCarrierDamping.PrimeUniformBound primeSamplingDefect (fun p => Real.log p) :=
  sampling_conditional_on_signed_damping (signed_damping_iff_integer_intervals.mpr h)

/-- Title: `The stronger secondary coefficient remains conditional on signed damping`. -/
theorem secondary_under_integer_signed_damping (h : IntegerSignedCarrierDamping) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ)^2*primeContinuousScale p) :=
  SecondaryLocalizationUnconditional.finite_secondary_coefficient_under_signed_damping
    (signed_damping_iff_integer_intervals.mpr h)

/-- Title: `A separately sharpened capacity remainder transfers under signed damping`. -/
theorem secondary_under_sharp_capacity_and_integer_signed_damping
    (hcapacity : EventualErrorBound continuousCapacity continuousCapacityMain (fun N => Real.log N))
    (h : IntegerSignedCarrierDamping) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ)^2*Real.log p) :=
  finite_secondary_coefficient_under_log_capacity_and_sampling hcapacity
    (sampling_under_integer_signed_damping h)

end NField.Alignment.IntegerSignedDamping
