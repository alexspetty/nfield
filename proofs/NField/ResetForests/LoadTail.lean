/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.RawClock
/-! # The complete reset-load tail

The divisor sum is evaluated on the complete cutoff and bounded by a
telescoping reciprocal-square sum. Every chosen clock is then included
by its actual integer load.
-/

noncomputable section

namespace NField.ResetForests.PhasePopulations

open scoped BigOperators
open NField.Alignment

def reciprocalSquareH (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K, 1/(j : ℝ)^2

theorem divisor_sum_ratio_reciprocals {k : ℕ} (hk : 0 < k) :
    (divisorSumOne k : ℝ)/(k : ℝ) = ∑ d ∈ k.divisors, 1/(d : ℝ) := by
  have hswap : (∑ d ∈ k.divisors, 1/((k/d : ℕ) : ℝ)) =
      ∑ d ∈ k.divisors, 1/(d : ℝ) := by
    exact (Nat.sum_divisorsAntidiagonal (fun _ b : ℕ => 1/(b : ℝ))).symm.trans
      (Nat.sum_divisorsAntidiagonal' (fun _ b : ℕ => 1/(b : ℝ)))
  calc
    _ = ∑ d ∈ k.divisors, (d : ℝ)/(k : ℝ) := by
      unfold divisorSumOne
      push_cast
      rw [Finset.sum_div]
    _ = ∑ d ∈ k.divisors, 1/((k/d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdk := Nat.dvd_of_mem_divisors hd
      have hq0 : 0 < k/d := Nat.div_pos (Nat.le_of_dvd hk hdk) hd0
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      have hqR : ((k/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      field_simp
      exact_mod_cast Nat.mul_div_cancel' hdk
    _ = _ := hswap

theorem summatory_divisor_ratio (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (divisorSumOne k : ℝ)/(k : ℝ)) ≤
      (K : ℝ)*reciprocalSquareH K := by
  have hcolumns := CommonResetDedekind.sum_divisor_columns K (fun d : ℕ => 1/(d : ℚ))
  calc
    _ = ∑ k ∈ Finset.Icc 1 K, ∑ d ∈ k.divisors, 1/(d : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact divisor_sum_ratio_reciprocals (Finset.mem_Icc.mp hk).1
    _ = ∑ d ∈ Finset.Icc 1 K, ((K/d : ℕ) : ℝ)*(1/(d : ℝ)) := by
      have hc := congrArg (fun q : ℚ => (q : ℝ)) hcolumns
      push_cast at hc
      exact hc
    _ ≤ ∑ d ∈ Finset.Icc 1 K, (K : ℝ)/(d : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hdiv : ((K/d : ℕ) : ℝ) ≤ (K : ℝ)/(d : ℝ) := by
        apply (le_div_iff₀ hdR).mpr
        exact_mod_cast Nat.div_mul_le_self K d
      calc
        _ ≤ ((K : ℝ)/(d : ℝ))*(1/(d : ℝ)) := mul_le_mul_of_nonneg_right hdiv (by positivity)
        _ = _ := by ring
    _ = _ := by
      unfold reciprocalSquareH
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

theorem reciprocal_square_step {x : ℝ} (hx : 1 ≤ x) :
    1/x^2 ≤ 2/x-2/(x+1) := by
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ 2/(x*(x+1)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < x^2) (by positivity : 0 < x*(x+1))).mpr
      nlinarith
    _ = _ := by field_simp; ring

theorem reciprocal_square_telescope (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, (2/(j : ℝ)-2/((j : ℝ)+1))) =
      2-2/((K : ℝ)+1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K+1), ih]
    push_cast
    ring

theorem reciprocal_square_sum_le_two (K : ℕ) : reciprocalSquareH K ≤ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 K, (2/(j : ℝ)-2/((j : ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact reciprocal_square_step (by exact_mod_cast (Finset.mem_Icc.mp hj).1)
    _ = 2-2/((K : ℝ)+1) := reciprocal_square_telescope K
    _ ≤ _ := by
      have ht : 0 ≤ 2/((K : ℝ)+1) := by positivity
      linarith

theorem clock_collection_cutoff_bound {p K : ℕ} (hp : p.Prime)
    (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k ∧ k ≤ p-1)
    (hcut : ∀ k ∈ S, k ≤ K) :
    (∑ k ∈ S, |4*Core.clockReading (p-1) (p^2) k|) ≤
      2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(K : ℝ)*reciprocalSquareH K := by
  have hsub : S ⊆ Finset.Icc 1 K := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨by have := (hS k hk).1; omega, hcut k hk⟩
  calc
    _ ≤ ∑ k ∈ S, (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*
        ((divisorSumOne k : ℝ)/(k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkp : k < p := lt_of_le_of_lt (hS k hk).2 (Nat.sub_lt hp.pos (by decide))
      calc
        _ ≤ 2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(divisorSumOne k : ℝ)/(k : ℝ) :=
          raw_clock_divisor_bound hp (hS k hk).1 hkp
        _ = _ := by ring
    _ = (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*
        (∑ k ∈ S, (divisorSumOne k : ℝ)/(k : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*
        (∑ k ∈ Finset.Icc 1 K, (divisorSumOne k : ℝ)/(k : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*((K : ℝ)*reciprocalSquareH K) :=
      mul_le_mul_of_nonneg_left (summatory_divisor_ratio _) (by positivity)
    _ = _ := by ring

theorem reset_load_tail {p M : ℕ} (hp : p.Prime) (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k ∧ k ≤ p-1)
    (hload : ∀ k ∈ S, M ≤ (p-1)/k) :
    (∑ k ∈ S, |4*Core.clockReading (p-1) (p^2) k|) ≤
      2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*
        (((p-1)/M : ℕ) : ℝ)*reciprocalSquareH ((p-1)/M) ∧
    2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*
        (((p-1)/M : ℕ) : ℝ)*reciprocalSquareH ((p-1)/M) ≤
      4*((p-1 : ℕ) : ℝ)^2*(harmonic (p-1) : ℝ)^2/(M : ℝ) := by
  have hsub : S ⊆ Finset.Icc 1 ((p-1)/M) := by
    intro k hk
    obtain ⟨hk2, hkN⟩ := hS k hk
    have hm := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp (hload k hk)
    exact Finset.mem_Icc.mpr ⟨by omega,
      (Nat.le_div_iff_mul_le hM).mpr (by simpa [mul_comm] using hm)⟩
  constructor
  · calc
      _ ≤ ∑ k ∈ S, (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*
          ((divisorSumOne k : ℝ)/(k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkp : k < p := by
          exact lt_of_le_of_lt (hS k hk).2 (Nat.sub_lt hp.pos (by decide))
        calc
          _ ≤ 2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(divisorSumOne k : ℝ)/(k : ℝ) :=
            raw_clock_divisor_bound hp (hS k hk).1 hkp
          _ = _ := by ring
      _ = (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*
          (∑ k ∈ S, (divisorSumOne k : ℝ)/(k : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*
          (∑ k ∈ Finset.Icc 1 ((p-1)/M), (divisorSumOne k : ℝ)/(k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ (2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2)*
          ((((p-1)/M : ℕ) : ℝ)*reciprocalSquareH ((p-1)/M)) :=
        mul_le_mul_of_nonneg_left (summatory_divisor_ratio _) (by positivity)
      _ = _ := by ring
  · have hmR : (0 : ℝ) < M := by exact_mod_cast hM
    have hK : (((p-1)/M : ℕ) : ℝ) ≤ ((p-1 : ℕ) : ℝ)/(M : ℝ) := by
      apply (le_div_iff₀ hmR).mpr
      exact_mod_cast Nat.div_mul_le_self (p-1) M
    calc
      _ ≤ 2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(((p-1)/M : ℕ) : ℝ)*2 :=
        mul_le_mul_of_nonneg_left (reciprocal_square_sum_le_two _) (by positivity)
      _ ≤ 2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(((p-1 : ℕ) : ℝ)/(M : ℝ))*2 := by
        gcongr
      _ = _ := by ring

/-- The complete printed tail bound also holds at every positive real load threshold. -/
theorem reset_load_tail_real {p : ℕ} {M : ℝ} (hp : p.Prime) (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k ∧ k ≤ p-1)
    (hload : ∀ k ∈ S, M ≤ (((p-1)/k : ℕ) : ℝ)) :
    let K := ⌊((p-1 : ℕ) : ℝ)/M⌋₊
    (∑ k ∈ S, |4*Core.clockReading (p-1) (p^2) k|) ≤
      2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(K : ℝ)*reciprocalSquareH K ∧
    2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(K : ℝ)*reciprocalSquareH K ≤
      4*((p-1 : ℕ) : ℝ)^2*(harmonic (p-1) : ℝ)^2/M := by
  let K := ⌊((p-1 : ℕ) : ℝ)/M⌋₊
  have hcut : ∀ k ∈ S, k ≤ K := by
    intro k hk
    have hkR : (0 : ℝ) < k := by
      have hk0 : 0 < k := by have hh := (hS k hk).1; omega
      exact_mod_cast hk0
    have hm : (((p-1)/k : ℕ) : ℝ) ≤ ((p-1 : ℕ) : ℝ)/(k : ℝ) := by
      apply (le_div_iff₀ hkR).mpr
      exact_mod_cast Nat.div_mul_le_self (p-1) k
    have hprod := (le_div_iff₀ hkR).mp ((hload k hk).trans hm)
    apply Nat.le_floor
    apply (le_div_iff₀ hM).mpr
    simpa only [mul_comm] using hprod
  refine ⟨clock_collection_cutoff_bound hp S hS hcut, ?_⟩
  have hK : (K : ℝ) ≤ ((p-1 : ℕ) : ℝ)/M := Nat.floor_le (by positivity)
  calc
    _ ≤ 2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(K : ℝ)*2 :=
      mul_le_mul_of_nonneg_left (reciprocal_square_sum_le_two K) (by positivity)
    _ ≤ 2*((p-1 : ℕ) : ℝ)*(harmonic (p-1) : ℝ)^2*(((p-1 : ℕ) : ℝ)/M)*2 := by
      gcongr
    _ = _ := by ring

end NField.ResetForests.PhasePopulations
