/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeManuscriptConsequences

/-! # The exact half-sum decomposition for the actual prime packets -/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.NeutralityTheorem
open NField.Alignment.CenteredCollisionSum

def primePacket {K : Type*} [AddCommMonoid K]
    (w : ℕ → K) (c : ℕ) (x : ℝ) : K :=
  ∑ p ∈ Ioc c ⌊x⌋₊, if p.Prime then w p else 0

def residueThreePrimeChannel {K : Type*} [AddCommMonoid K]
    (w : ℕ → K) (r c : ℕ) (x : ℝ) : K :=
  ∑ p ∈ Ioc c ⌊x⌋₊, if p.Prime ∧ p % 3 = r then w p else 0

theorem prime_above_three_residue {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hlt := Nat.mod_lt p (by decide : 0 < 3)
  have hne : p % 3 ≠ 0 := by
    intro hz
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hz) with h | h <;> omega
  omega

/-- Title: `Each actual prime channel is an exact half sum or half difference`. -/
theorem actual_prime_channel_half_split {K : Type*} [Field K] [CharZero K]
    (w : ℕ → K) {r c : ℕ} (hc : 3 ≤ c) (hr : r = 1 ∨ r = 2) (x : ℝ) :
    residueThreePrimeChannel w r c x =
      (1 / 2 : K) * (primePacket w c x +
        (modThreeSign r : K) * primePacket (fun p => (modThreeSign p : K) * w p) c x) := by
  classical
  let S := (Ioc c ⌊x⌋₊).filter Nat.Prime
  have hresidue (p : S) : (p : ℕ) % 3 = 1 ∨ (p : ℕ) % 3 = 2 := by
    have hp := mem_filter.mp p.property
    exact prime_above_three_residue hp.2 (hc.trans_lt (mem_Ioc.mp hp.1).1)
  have h := exact_finite_channel_split (fun p : S => (p : ℕ))
    (fun p : S => w p) hresidue hr
  rw [Finset.sum_coe_sort S (fun p => if p % 3 = r then w p else 0),
    Finset.sum_coe_sort S (fun p => (modThreeSign p : K) * w p)] at h
  simpa only [Finset.sum_coe_sort, S, Finset.sum_filter, ← ite_and,
    primePacket, residueThreePrimeChannel] using h

/-- Title: `The total prime packet is the sum of its two residue three channels`. -/
theorem actual_prime_packet_channel_sum {K : Type*} [Field K] [CharZero K]
    (w : ℕ → K) {c : ℕ} (hc : 3 ≤ c) (x : ℝ) :
    primePacket w c x =
      residueThreePrimeChannel w 1 c x + residueThreePrimeChannel w 2 c x := by
  have h1 := actual_prime_channel_half_split w hc (Or.inl rfl : 1 = 1 ∨ 1 = 2) x
  have h2 := actual_prime_channel_half_split w hc (Or.inr rfl : 2 = 1 ∨ 2 = 2) x
  rw [modThreeSign_eq_one (by decide : 1 % 3 = 1), Int.cast_one, one_mul] at h1
  rw [modThreeSign_eq_neg_one (by decide : 2 % 3 = 2), Int.cast_neg, Int.cast_one,
    neg_one_mul] at h2
  linear_combination -h1 - h2

/-- Title: `The twisted prime packet is the difference of the two channels`. -/
theorem actual_twisted_prime_packet_channel_difference {K : Type*} [Field K] [CharZero K]
    (w : ℕ → K) {c : ℕ} (hc : 3 ≤ c) (x : ℝ) :
    primePacket (fun p => (modThreeSign p : K) * w p) c x =
      residueThreePrimeChannel w 1 c x - residueThreePrimeChannel w 2 c x := by
  have h1 := actual_prime_channel_half_split w hc (Or.inl rfl : 1 = 1 ∨ 1 = 2) x
  have h2 := actual_prime_channel_half_split w hc (Or.inr rfl : 2 = 1 ∨ 2 = 2) x
  rw [modThreeSign_eq_one (by decide : 1 % 3 = 1), Int.cast_one, one_mul] at h1
  rw [modThreeSign_eq_neg_one (by decide : 2 % 3 = 2), Int.cast_neg, Int.cast_one,
    neg_one_mul] at h2
  linear_combination -h1 + h2

/-- Title: `Both literal residue three prime classes have harmonic limits`. -/
theorem residue_three_channel_nat_limit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) 3)]
    [NeZero (Nat.gcd (allLagModulus b ell) 3)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) {r : ℕ} (hr : r = 1 ∨ r = 2) :
    ∃ L : ℝ, Tendsto
      (residueThreePrimeChannel (fun p => realDirectCenteredCollisionValue b ell p / p)
        r (Nat.lcm (allLagModulus b ell) 3)) atTop (𝓝 L) := by
  rcases hr with rfl | rfl
  · obtain ⟨L, hL⟩ := residue_three_real_prime_channel_limit hb hell (1 : (ZMod 3)ˣ)
    refine ⟨L, hL.congr' (Filter.Eventually.of_forall ?_)⟩
    intro x
    apply Finset.sum_congr rfl
    intro p _
    have hcast : (p : ZMod 3) = (1 : (ZMod 3)ˣ) ↔ p % 3 = 1 := by
      change (p : ZMod 3) = ((1 : ℕ) : ZMod 3) ↔ _
      simpa using ZMod.natCast_eq_natCast_iff' p 1 3
    simp only [hcast]
  · obtain ⟨L, hL⟩ := residue_three_real_prime_channel_limit hb hell (-1 : (ZMod 3)ˣ)
    refine ⟨L, hL.congr' (Filter.Eventually.of_forall ?_)⟩
    intro x
    apply Finset.sum_congr rfl
    intro p _
    have hcast : (p : ZMod 3) = (-1 : (ZMod 3)ˣ) ↔ p % 3 = 2 := by
      have htwo : ((-1 : (ZMod 3)ˣ) : ZMod 3) = (2 : ℕ) := by decide +kernel
      rw [htwo]
      simpa using ZMod.natCast_eq_natCast_iff' p 2 3
    simp only [hcast]

/-- Title: `The total and twisted harmonic prime packets both converge`. -/
theorem residue_three_total_and_twisted_limits
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) 3)]
    [NeZero (Nat.gcd (allLagModulus b ell) 3)]
    (hb : 2 ≤ b) (hell : 1 ≤ ell) :
    ∃ L D : ℝ,
      Tendsto (primePacket (fun p => realDirectCenteredCollisionValue b ell p / p)
        (Nat.lcm (allLagModulus b ell) 3)) atTop (𝓝 L) ∧
      Tendsto (primePacket (fun p => (modThreeSign p : ℝ) *
          (realDirectCenteredCollisionValue b ell p / p))
        (Nat.lcm (allLagModulus b ell) 3)) atTop (𝓝 D) := by
  obtain ⟨L1, h1⟩ := residue_three_channel_nat_limit hb hell (Or.inl rfl : 1 = 1 ∨ 1 = 2)
  obtain ⟨L2, h2⟩ := residue_three_channel_nat_limit hb hell (Or.inr rfl : 2 = 1 ∨ 2 = 2)
  have hc : 3 ≤ Nat.lcm (allLagModulus b ell) 3 :=
    Nat.le_of_dvd (NeZero.pos _) (Nat.dvd_lcm_right _ _)
  refine ⟨L1 + L2, L1 - L2, ?_, ?_⟩
  · exact (h1.add h2).congr' (Filter.Eventually.of_forall fun x =>
      (actual_prime_packet_channel_sum _ hc x).symm)
  · exact (h1.sub h2).congr' (Filter.Eventually.of_forall fun x =>
      (actual_twisted_prime_packet_channel_difference _ hc x).symm)

end NField.Alignment.CollisionPrimeLimits
