/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevAllowedEulerProduct
import NField.Alignment.KorolevQuotientSieve

/-!
# Counting actual integers missing selected prime factors

The canonical smooth/rough decomposition maps each nonsmooth integer
avoiding S into an allowed smooth factor and a nontrivial rough factor.
The product recovers the integer, so the map is injective. Combine the
quotient-uniform sieve with the finite allowed-prime Euler product.
The estimate is uniform in every finite S contained in the primes up to Q.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevMissingPrimeCount
open scoped BigOperators Topology Classical
open Filter CollisionMertensInput HarperSmoothDivisor HarperSmoothRough
  HarperIntervalSieve KorolevFirstExclusion KorolevQuotientSieve KorolevAllowedEulerProduct

def avoidSet (x : ℝ) (S : Finset ℕ) : Finset ℕ :=
  (intervalSupport 0 x).filter (fun n => ∀ p ∈ S, ¬p ∣ n)

def nonsmoothAvoidSet (x Q : ℝ) (S : Finset ℕ) : Finset ℕ :=
  (avoidSet x S).filter (fun n => n ∉ smoothIntegers Q)

def allowedSmoothSet (x Q : ℝ) (S : Finset ℕ) : Finset ℕ :=
  (intervalSupport 0 x).filter (fun w => w ∈ Nat.factoredNumbers (primesUpTo Q \ S))

theorem avoidSet_mem {x : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) (n : ℕ) :
    n ∈ avoidSet x S ↔ 0 < n ∧ (n : ℝ) ≤ x ∧ ∀ p ∈ S, ¬p ∣ n := by
  rw [avoidSet, Finset.mem_filter, intervalSupport_mem (by norm_num) hx]
  simp only [Nat.cast_pos, and_assoc]

theorem allowedSmoothSet_mem {x Q : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) (w : ℕ) :
    w ∈ allowedSmoothSet x Q S ↔ 0 < w ∧ (w : ℝ) ≤ x ∧
      w ∈ Nat.factoredNumbers (primesUpTo Q \ S) := by
  rw [allowedSmoothSet, Finset.mem_filter, intervalSupport_mem (by norm_num) hx]
  simp only [Nat.cast_pos, and_assoc]

theorem canonical_allowed_factor {x Q : ℝ} (hx : 0 ≤ x) {S : Finset ℕ} {n : ℕ}
    (hn : n ∈ avoidSet x S) : supportedPart (primeBase Q) n ∈ allowedSmoothSet x Q S := by
  obtain ⟨hn0, hnx, havoid⟩ := (avoidSet_mem hx S n).mp hn
  have hw := supportedPart_pos (b := primeBase Q) hn0
  have hwd := supportedPart_dvd (b := primeBase Q) hn0
  apply (allowedSmoothSet_mem hx S _).mpr
  refine ⟨hw, (show (supportedPart (primeBase Q) n : ℝ) ≤ n by
    exact_mod_cast Nat.le_of_dvd hn0 hwd).trans hnx, ?_⟩
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  refine ⟨hw.ne', ?_⟩
  intro p hp
  obtain ⟨hpp, hpw, _⟩ := Nat.mem_primeFactors.mp hp
  have hpQ := (smoothIntegers_mem.mp (canonical_smooth_part (P := Q) hn0)).2 p hpp hpw
  exact Finset.mem_sdiff.mpr ⟨primesUpTo_mem.mpr ⟨hpp, hpQ⟩,
    fun hpS => havoid p hpS (hpw.trans hwd)⟩

theorem canonical_nontrivial_rough {x Q : ℝ} (hx : 0 ≤ x) {S : Finset ℕ} {n : ℕ}
    (hn : n ∈ nonsmoothAvoidSet x Q S) :
    roughPart (primeBase Q) n ∈
      nontrivialRoughSet (x / (supportedPart (primeBase Q) n : ℝ)) Q := by
  obtain ⟨hn, hns⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn0, hnx, _⟩ := (avoidSet_mem hx S n).mp hn
  have hw : (0 : ℝ) < supportedPart (primeBase Q) n := by
    exact_mod_cast supportedPart_pos (b := primeBase Q) hn0
  have hv := roughPart_pos (b := primeBase Q) hn0
  have hv1 : roughPart (primeBase Q) n ≠ 1 := by
    intro he
    exact hns ((supported_iff_smooth hn0).mp ((roughPart_eq_one_iff_supported hn0).mp he))
  apply Finset.mem_filter.mpr
  refine ⟨(roughSet_mem (div_nonneg hx hw.le) _).mpr ⟨hv, ?_, ?_⟩, by omega⟩
  · apply (le_div_iff₀ hw).mpr
    have he : (roughPart (primeBase Q) n : ℝ) * supportedPart (primeBase Q) n = n := by
      exact_mod_cast roughPart_mul_supportedPart (b := primeBase Q) hn0
    rw [he]
    exact hnx
  · intro p hpp hpv
    exact canonical_rough_primes hn0 hpp hpv

/-- Literal finite-set count, using the already proved canonical factors. -/
theorem nonsmooth_avoid_count_le_factor_sum {x Q : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    (nonsmoothAvoidSet x Q S).card ≤
      ∑ w ∈ allowedSmoothSet x Q S, (nontrivialRoughSet (x / (w : ℝ)) Q).card := by
  let f : ℕ → Σ _ : ℕ, ℕ := fun n => ⟨supportedPart (primeBase Q) n, roughPart (primeBase Q) n⟩
  have hmap : Set.MapsTo f (nonsmoothAvoidSet x Q S)
      ((allowedSmoothSet x Q S).sigma (fun w => nontrivialRoughSet (x / (w : ℝ)) Q)) := by
    intro n hn
    exact Finset.mem_sigma.mpr ⟨canonical_allowed_factor hx (Finset.mem_filter.mp hn).1,
      canonical_nontrivial_rough hx hn⟩
  have hinj : Set.InjOn f (nonsmoothAvoidSet x Q S) := by
    intro n hn m hm he
    have hn0 := ((avoidSet_mem hx S n).mp (Finset.mem_filter.mp hn).1).1
    have hm0 := ((avoidSet_mem hx S m).mp (Finset.mem_filter.mp hm).1).1
    have h := congrArg (fun z : Σ _ : ℕ, ℕ => z.2 * z.1) he
    change roughPart (primeBase Q) n * supportedPart (primeBase Q) n =
      roughPart (primeBase Q) m * supportedPart (primeBase Q) m at h
    simpa only [roughPart_mul_supportedPart hn0, roughPart_mul_supportedPart hm0] using h
  simpa only [Finset.card_sigma] using Finset.card_le_card_of_injOn f hmap hinj

theorem eventual_nonsmooth_count_euler : ∀ᶠ Q : ℝ in atTop,
    ∀ x : ℝ, Q ≤ x → ∀ S : Finset ℕ, S ⊆ primesUpTo Q →
      ((nonsmoothAvoidSet x Q S).card : ℝ) ≤
        (17 * x * Real.log x / (Real.log Q)^2) * inversePrimeProduct Q *
          Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) := by
  filter_upwards [eventual_factor_sum_bound, eventually_ge_atTop (2 : ℝ)]
    with Q hQ hQ2 x hQx S hS
  have hx : 0 ≤ x := by linarith
  have hW : ∀ w ∈ allowedSmoothSet x Q S, 0 < w :=
    fun w hw => ((allowedSmoothSet_mem hx S w).mp hw).1
  have hb := hQ x hQx 1 (by omega) (allowedSmoothSet x Q S) hW
  norm_num only [Nat.cast_one, one_pow, one_mul] at hb
  have hc : ((nonsmoothAvoidSet x Q S).card : ℝ) ≤
      ∑ w ∈ allowedSmoothSet x Q S, ((nontrivialRoughSet (x / (w : ℝ)) Q).card : ℝ) := by
    exact_mod_cast nonsmooth_avoid_count_le_factor_sum hx S
  have he := allowed_reciprocal_bound hS
    (fun w hw => ((allowedSmoothSet_mem hx S w).mp hw).2.2)
  have hnonneg : 0 ≤ 17 * x * Real.log x / (Real.log Q)^2 :=
    div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith))) (sq_nonneg _)
  calc
    _ ≤ _ := (hc.trans hb).trans (mul_le_mul_of_nonneg_left he hnonneg)
    _ = _ := by ring

theorem eventual_nonsmooth_count_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℝ in atTop,
    ∀ x : ℝ, Q ≤ x → ∀ S : Finset ℕ, S ⊆ primesUpTo Q →
      ((nonsmoothAvoidSet x Q S).card : ℝ) ≤
        C * (x * Real.log x / Real.log Q) * Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) := by
  obtain ⟨C, hC, hprod⟩ := uniform_smooth_divisor_estimate
  refine ⟨17 * C, by positivity, ?_⟩
  filter_upwards [eventual_nonsmooth_count_euler, hprod, eventually_ge_atTop (2 : ℝ)]
    with Q hQ hp hQ2 x hQx S hS
  have hp' : inversePrimeProduct Q ≤ C * Real.log Q := by simpa using (hp 1 (by norm_num)).2
  have hlQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ _ := hQ x hQx S hS
    _ ≤ (17 * x * Real.log x / (Real.log Q)^2) * (C * Real.log Q) *
        Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) := by gcongr
    _ = _ := by field_simp

end NField.Alignment.KorolevMissingPrimeCount
