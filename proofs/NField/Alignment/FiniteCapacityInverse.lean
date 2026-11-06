/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResolutionLaw
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Exact finite inversion of the capacity readout

The scalar-capacity clause of Theorem 14 in *Finite Generation of Collision
Capacity*. The inverse uses Mathlib's finite Möbius inversion. It needs no
positivity, summability, smoothness, or infinite-limit assumption.
-/

noncomputable section

namespace NField.Alignment.FiniteCapacityInverse

open scoped BigOperators ArithmeticFunction
open CollisionResolutionLaw

/-- The paper's scaled capacity after removing its diagonal term. -/
def scaledCapacity (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  (3 / 2 : ℝ) * (completedCapacity v N - (N : ℝ) / 3)

@[simp] theorem scaled_capacity_zero (v : ℕ → ℝ) : scaledCapacity v 0 = 0 := by
  simp [scaledCapacity, completedCapacity]

/-- Title: `Scaled capacity as a finite weighted floor sum`. -/
theorem scaled_capacity_floor_sum (v : ℕ → ℝ) (hv1 : v 1 = 0) (N : ℕ) :
    scaledCapacity v N =
      ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * v k * ((N / k : ℕ) : ℝ) := by
  have hs : (∑ k ∈ Finset.Icc 2 N, v k * (k : ℝ) * ((N / k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc 1 N, v k * (k : ℝ) * ((N / k : ℕ) : ℝ) := by
    apply Finset.sum_subset
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩
    · intro k hk hnot
      have hk1 : k = 1 := by
        simp only [Finset.mem_Icc] at hk hnot
        omega
      simp [hk1, hv1]
  unfold scaledCapacity completedCapacity
  rw [hs]
  have hcomm : (∑ k ∈ Finset.Icc 1 N, v k * (k : ℝ) * ((N / k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * v k * ((N / k : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hcomm]
  ring

theorem floor_quotient_step (n k : ℕ) :
    (((n + 1) / k : ℕ) : ℝ) - ((n / k : ℕ) : ℝ) =
      if k ∣ n + 1 then 1 else 0 := by
  rw [Nat.succ_div]
  split_ifs <;> simp

theorem divisors_as_interval_filter {n : ℕ} (hn : 0 < n) :
    n.divisors = (Finset.Icc 1 n).filter (fun k => k ∣ n) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hk
    exact ⟨⟨Nat.pos_of_mem_divisors hk,
      Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hk)⟩, Nat.dvd_of_mem_divisors hk⟩
  · rintro ⟨_, hkn⟩
    exact Nat.mem_divisors.mpr ⟨hkn, hn.ne'⟩

/-- Successive scaled capacities expose the divisor sum of the period masses. -/
theorem scaled_capacity_difference (v : ℕ → ℝ) (hv1 : v 1 = 0) (n : ℕ) :
    scaledCapacity v (n + 1) - scaledCapacity v n =
      ∑ k ∈ (n + 1).divisors, (k : ℝ) * v k := by
  rw [scaled_capacity_floor_sum v hv1, scaled_capacity_floor_sum v hv1]
  have hext : (∑ k ∈ Finset.Icc 1 (n + 1),
      (k : ℝ) * v k * ((n / k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * v k * ((n / k : ℕ) : ℝ) := by
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp [Nat.div_eq_of_lt (Nat.lt_succ_self n)]
  rw [← hext, ← Finset.sum_sub_distrib,
    divisors_as_interval_filter (Nat.succ_pos n), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_sub, floor_quotient_step]
  split_ifs <;> simp

/-- Title: `Successive capacities recover the divisor sum of period masses`. -/
theorem scaled_capacity_difference_pred (v : ℕ → ℝ) (hv1 : v 1 = 0)
    {n : ℕ} (hn : 0 < n) :
    scaledCapacity v n - scaledCapacity v (n - 1) =
      ∑ k ∈ n.divisors, (k : ℝ) * v k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using scaled_capacity_difference v hv1 m

/-- Title: `Period masses recovered from scalar capacities`.

 The literal divisor inverse in the manuscript, for every positive address. -/
theorem mass_from_capacity (v : ℕ → ℝ) (hv1 : v 1 = 0)
    {n : ℕ} (hn : 0 < n) :
    v n = (1 / (n : ℝ)) *
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) *
        (scaledCapacity v d - scaledCapacity v (d - 1)) := by
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun k => (k : ℝ) * v k)
    (g := fun k => scaledCapacity v k - scaledCapacity v (k - 1))).mp
      (fun k hk => (scaled_capacity_difference_pred v hv1 hk).symm) n hn
  rw [Nat.sum_divisorsAntidiagonal'
    (fun a b => (ArithmeticFunction.moebius a : ℝ) *
      (scaledCapacity v b - scaledCapacity v (b - 1)))] at hi
  rw [hi]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Title: `A finite capacity prefix determines its positive mass prefix`.

 A finite capacity prefix determines precisely the positive mass prefix. -/
theorem capacity_prefix_determines_mass (v u : ℕ → ℝ)
    (hv1 : v 1 = 0) (hu1 : u 1 = 0) (N : ℕ)
    (hc : ∀ j, j ≤ N → completedCapacity v j = completedCapacity u j)
    {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) : v n = u n := by
  rw [mass_from_capacity v hv1 hn, mass_from_capacity u hu1 hn]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdN : d ≤ N := (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)).trans hnN
  have hpredN : d - 1 ≤ N := (Nat.sub_le d 1).trans hdN
  simp only [scaledCapacity, hc d hdN, hc (d - 1) hpredN]

/-- Title: `A finite mass prefix determines its capacity prefix`. -/
theorem mass_prefix_determines_capacity (v u : ℕ → ℝ) (N : ℕ)
    (hm : ∀ k, 1 ≤ k → k ≤ N → v k = u k)
    {j : ℕ} (hjN : j ≤ N) : completedCapacity v j = completedCapacity u j := by
  unfold completedCapacity
  have hs : (∑ k ∈ Finset.Icc 2 j, v k * (k : ℝ) * ((j / k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc 2 j, u k * (k : ℝ) * ((j / k : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    rw [hm k (by omega) (hk'.2.trans hjN)]
  rw [hs]

/-- Title: `Equality of capacity prefixes is equivalent to equality of mass prefixes`. -/
theorem capacity_prefix_iff_mass_prefix (v u : ℕ → ℝ)
    (hv1 : v 1 = 0) (hu1 : u 1 = 0) (N : ℕ) :
    (∀ j, j ≤ N → completedCapacity v j = completedCapacity u j) ↔
      ∀ k, 1 ≤ k → k ≤ N → v k = u k := by
  constructor
  · intro hc k hk hkN
    exact capacity_prefix_determines_mass v u hv1 hu1 N hc hk hkN
  · intro hm j hjN
    exact mass_prefix_determines_capacity v u N hm hjN

/-- Title: `The complete capacity sequence determines exactly the positive-address masses`.

 The readout ignores address zero; equality of all positive masses is exact. -/
theorem all_capacities_iff_positive_masses (v u : ℕ → ℝ)
    (hv1 : v 1 = 0) (hu1 : u 1 = 0) :
    (∀ N, completedCapacity v N = completedCapacity u N) ↔
      ∀ k, 1 ≤ k → v k = u k := by
  constructor
  · intro hc k hk
    exact capacity_prefix_determines_mass v u hv1 hu1 k (fun j _ => hc j) hk le_rfl
  · intro hm N
    exact mass_prefix_determines_capacity v u N (fun k hk _ => hm k hk) le_rfl

end NField.Alignment.FiniteCapacityInverse
