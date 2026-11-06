/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConstructiveFluctuationPrimeIdentity
import NField.Alignment.PrimeResidualCutoffs

/-! # Literal prime congruence channels at the harmonic boundary -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.PrimePeriodicLimits
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.GeneralNeutrality
open NField.Alignment.NeutralityTheorem

theorem unitReduction_nat_unit {n m p : ℕ} [NeZero n] [NeZero m]
    (hd : n ∣ m) (hm : IsUnit (p : ZMod m)) (hn : IsUnit (p : ZMod n)) :
    unitReduction hd hm.unit = hn.unit := by
  apply Units.ext
  change (ZMod.unitsMap hd hm.unit : ZMod n) = (hn.unit : ZMod n)
  rw [ZMod.unitsMap_val, hm.unit_spec, ZMod.cast_natCast hd p, hn.unit_spec]

theorem restricted_unitExtension_at_prime {m Q p : ℕ}
    [NeZero m] [NeZero Q] [NeZero (Nat.lcm m Q)]
    (f : UnitClass m → ℂ) (r : UnitClass Q) (hp : p.Prime) (hlt : Nat.lcm m Q < p) :
    unitExtension (restrictedUnitSignal
      (fun A : UnitClass (Nat.lcm m Q) => f (unitReduction (Nat.dvd_lcm_left m Q) A))
      (fun A => unitReduction (Nat.dvd_lcm_right m Q) A = r)) p =
      if (p : ZMod Q) = r then unitExtension f p else 0 := by
  classical
  have hmM : m ≤ Nat.lcm m Q := Nat.le_of_dvd (NeZero.pos _) (Nat.dvd_lcm_left m Q)
  have hQM : Q ≤ Nat.lcm m Q := Nat.le_of_dvd (NeZero.pos _) (Nat.dvd_lcm_right m Q)
  have hM := prime_unit_of_modulus_lt hp hlt
  have hm := prime_unit_of_modulus_lt hp (hmM.trans_lt hlt)
  have hQ := prime_unit_of_modulus_lt hp (hQM.trans_lt hlt)
  have hl := unitReduction_nat_unit (Nat.dvd_lcm_left m Q) hM hm
  have hr := unitReduction_nat_unit (Nat.dvd_lcm_right m Q) hM hQ
  have hc : hQ.unit = r ↔ (p : ZMod Q) = r := by
    rw [Units.ext_iff, hQ.unit_spec]
  simp only [unitExtension, dif_pos hM, dif_pos hm, restrictedUnitSignal, hl, hr, hc]

/-- Title: `Every squarefree true prime channel has its own harmonic limit`.
The channel tests the prime itself, with the literal lcm cutoff. -/
theorem squarefree_literal_true_channel_limit
    {b ell Q : ℕ} [NeZero b] [NeZero Q] [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) Q)]
    [NeZero (Nat.gcd (allLagModulus b ell) Q)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (hQ : Squarefree Q) (r : UnitClass Q) :
    ∃ L : ℂ, Tendsto (fun x : ℝ =>
      ∑ p ∈ Finset.Ioc (Nat.lcm (allLagModulus b ell) Q) ⌊x⌋₊,
        if p.Prime ∧ (p : ZMod Q) = r then
          directCenteredCollisionValue b ell p / (p : ℂ) else 0) atTop (𝓝 L) := by
  classical
  let M := Nat.lcm (allLagModulus b ell) Q
  let F : UnitClass M → ℂ := restrictedUnitSignal
    (fun A => centeredCollisionTransform b ell
      (unitReduction (Nat.dvd_lcm_left (allLagModulus b ell) Q) A))
    (fun A => unitReduction (Nat.dvd_lcm_right (allLagModulus b ell) Q) A = r)
  obtain ⟨L, hL⟩ := squarefree_true_channel_prime_limit (b := b) (ell := ell) hQ r
  have hfull : Tendsto (weightedPrimeReciprocalSum F) atTop (𝓝 L) := hL
  have htail := sum_Ioc_cutoff_limit
    (fun p => if p.Prime then unitExtension F p / (p : ℂ) else 0) M hfull
  refine ⟨_, htail.congr' (Filter.Eventually.of_forall ?_)⟩
  intro x
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · have heq := restricted_unitExtension_at_prime (centeredCollisionTransform b ell) r
      hprime (Finset.mem_Ioc.mp hp).1
    change unitExtension F p = _ at heq
    rw [if_pos hprime, heq]
    rw [← directCenteredCollisionValue_eq_unitExtension hb hell]
    by_cases hc : (p : ZMod Q) = r <;> simp [hprime, hc]
  · simp [hprime]

/-- Title: `Real convergence in each squarefree prime channel`. -/
theorem squarefree_real_true_channel_limit
    {b ell Q : ℕ} [NeZero b] [NeZero Q] [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) Q)]
    [NeZero (Nat.gcd (allLagModulus b ell) Q)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) (hQ : Squarefree Q) (r : UnitClass Q) :
    ∃ L : ℝ, Tendsto (fun x : ℝ =>
      ∑ p ∈ Finset.Ioc (Nat.lcm (allLagModulus b ell) Q) ⌊x⌋₊,
        if p.Prime ∧ (p : ZMod Q) = r then
          realDirectCenteredCollisionValue b ell p / (p : ℝ) else 0) atTop (𝓝 L) := by
  classical
  obtain ⟨L, hL⟩ := squarefree_literal_true_channel_limit hb hell hQ r
  have h := Complex.continuous_re.continuousAt.tendsto.comp hL
  refine ⟨L.re, h.congr' (Filter.Eventually.of_forall ?_)⟩
  intro x
  have heq : ((∑ p ∈ Finset.Ioc (Nat.lcm (allLagModulus b ell) Q) ⌊x⌋₊,
      if p.Prime ∧ (p : ZMod Q) = r then
        realDirectCenteredCollisionValue b ell p / (p : ℝ) else 0 : ℝ) : ℂ) =
      ∑ p ∈ Finset.Ioc (Nat.lcm (allLagModulus b ell) Q) ⌊x⌋₊,
        if p.Prime ∧ (p : ZMod Q) = r then
          directCenteredCollisionValue b ell p / (p : ℂ) else 0 := by
    simp only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, Complex.ofReal_div,
      ofReal_realDirectCenteredCollisionValue, Complex.ofReal_natCast]
  change (∑ p ∈ Finset.Ioc (Nat.lcm (allLagModulus b ell) Q) ⌊x⌋₊,
    if p.Prime ∧ (p : ZMod Q) = r then directCenteredCollisionValue b ell p / (p : ℂ)
      else 0).re = _
  rw [← heq, Complex.ofReal_re]

end NField.Alignment.CollisionPrimeLimits
