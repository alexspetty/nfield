/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperIntervalSieve
import NField.Alignment.SelbergWeights
import NField.Alignment.SquarefreeHarmonic

/-!
# Uniform rough-number interval bound

Explicit truncated Selberg weights, their unit divisor-count remainders,
and the proved squarefree harmonic lower bound give
`count(a<n<=b, coprime(n, primeBase P)) <= 2*(b-a)/log(P)+P^4`.
The bound is uniform in the endpoints and uses the full prime base.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace NField.Alignment.HarperSieveBound

open HarperSmoothRough HarperIntervalSieve CollisionMertensInput

theorem squarefree_dvd_primeBase {P : ℝ} {d : ℕ} (hd : Squarefree d)
    (hdP : (d : ℝ) ≤ P) : d ∣ primeBase P := by
  rw [← Nat.prod_primeFactors_of_squarefree hd,
    Nat.prod_primeFactors_dvd_iff (primeBase_pos P).ne']
  intro r hr
  apply Nat.mem_primeFactors.mpr
  have hrd := Nat.dvd_of_mem_primeFactors hr
  have hrp := Nat.prime_of_mem_primeFactors hr
  refine ⟨hrp, (prime_dvd_primeBase hrp).mpr ?_, (primeBase_pos P).ne'⟩
  exact primesUpTo_mem.mpr ⟨hrp,
    (show (r : ℝ) ≤ d by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) hrd).trans hdP⟩

theorem density_le_selbergTerms (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.nu d ≤ s.selbergTerms d := by
  rw [s.selbergTerms_apply]
  calc
    s.nu d = s.nu d * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_prod fun p hp => by
      have hpN : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hd
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      exact (one_le_inv₀ (sub_pos.mpr (s.nu_lt_one_of_prime p hpPrime hpN))).mpr
        (sub_le_self _ (s.nu_pos_of_prime p hpPrime hpN).le))
      (s.nu_pos_of_dvd_prodPrimes hd).le

theorem squarefreeSum_le_normalizer (a b P : ℝ) (hP : 0 ≤ P) :
    SquarefreeHarmonic.reciprocalSum ⌊P⌋₊ ≤
      SelbergWeights.normalizer (roughIntervalSieve a b P) P := by
  let D := (primeBase P).divisors.filter (fun d : ℕ => (d : ℝ) ≤ P)
  have hsub : SquarefreeHarmonic.squarefreeRange ⌊P⌋₊ ⊆ D := by
    intro d hd
    rcases mem_filter.mp hd with ⟨hdI, hsf⟩
    have hdP : (d : ℝ) ≤ P := (Nat.le_floor_iff hP).mp (mem_Icc.mp hdI).2
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨squarefree_dvd_primeBase hsf hdP, (primeBase_pos P).ne'⟩, hdP⟩
  calc
    SquarefreeHarmonic.reciprocalSum ⌊P⌋₊ ≤ ∑ d ∈ D, (d : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ d ∈ D, (roughIntervalSieve a b P).selbergTerms d := by
      apply sum_le_sum
      intro d hd
      exact density_le_selbergTerms (roughIntervalSieve a b P)
        (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ = SelbergWeights.normalizer (roughIntervalSieve a b P) P := by
      dsimp only [D]
      rw [sum_filter]
      rfl

theorem log_le_twice_normalizer (a b P : ℝ) (hP : 0 ≤ P) :
    Real.log P ≤ 2 * SelbergWeights.normalizer (roughIntervalSieve a b P) P :=
  (SquarefreeHarmonic.log_le_twice hP).trans
    (mul_le_mul_of_nonneg_left (squarefreeSum_le_normalizer a b P hP) (by norm_num))

/-- Uniform interval bound with the full prime base and an explicit error. -/
theorem rough_interval_bound {a b P : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hP : 2 ≤ P) :
    (((intervalSupport a b).filter (fun n => n.Coprime (primeBase P))).card : ℝ) ≤
      2 * (b-a) / Real.log P + P^4 := by
  let s := roughIntervalSieve a b P
  have hz : 1 ≤ P := by linarith
  have hnu : ∀ d, d ∣ s.prodPrimes → (s.nu d)⁻¹ ≤ (d : ℝ) := by
    intro d _
    simp [s, roughIntervalSieve, reciprocalDensity]
  have hr : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ 1 := by
    intro d hd
    exact roughIntervalSieve_remainder ha hab P
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd))
  have hbnd := SelbergWeights.siftedSum_le s hz hnu hr
  rw [roughIntervalSieve_siftedSum] at hbnd
  refine hbnd.trans (add_le_add ?_ le_rfl)
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hG := SelbergWeights.normalizer_pos s hz
  have hlogG := log_le_twice_normalizer a b P (by linarith)
  change (b-a) / SelbergWeights.normalizer s P ≤ 2*(b-a)/Real.log P
  apply (div_le_div_iff₀ hG hlog).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab)
    (show 0 ≤ 2*SelbergWeights.normalizer s P - Real.log P from sub_nonneg.mpr hlogG)]

end NField.Alignment.HarperSieveBound
