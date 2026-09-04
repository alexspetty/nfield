/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindReciprocity

/-!
# Carrier jump data

The exact block cancellation and terminal-prefix calculation at a reduced
rational jump of the straightened Bernoulli boundary.
-/

namespace NField.Alignment.CarrierJumpData

open scoped BigOperators
open NField.Alignment.DedekindReciprocity

def boundaryMidpoint (N a k : ℕ) : ℚ :=
  2 * ∑ r ∈ Finset.range N, rationalSawtooth ((r + 1) * a) k

def cyclicPrefixResponse (a k s : ℕ) : ℚ :=
  2 * ∑ r ∈ Finset.range s, rationalSawtooth ((r + 1) * a) k

theorem sum_range_shift_one (f : ℕ → ℚ) (n : ℕ) :
    (∑ r ∈ Finset.range n, f (r + 1)) + f 0 =
      ∑ r ∈ Finset.range (n + 1), f r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

theorem sum_rationalSawtooth_range {k : ℕ} (hk : 0 < k) :
    (∑ r ∈ Finset.range k, rationalSawtooth r k) = 0 := by
  rw [sum_range_eq_sum_Ico_one (fun r ↦ rationalSawtooth r k)
    hk (rationalSawtooth_zero k)]
  calc
    (∑ r ∈ Finset.Ico 1 k, rationalSawtooth r k) =
        ∑ r ∈ Finset.Ico 1 k, ((r : ℚ) / (k : ℚ) - 1 / 2) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact rationalSawtooth_of_lt
            (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2
    _ = 0 := by
      have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
      have hsum : (∑ r ∈ Finset.Ico 1 k, (r : ℚ)) =
          (k : ℚ) * ((k : ℚ) - 1) / 2 := by
        rw [show (∑ r ∈ Finset.Ico 1 k, (r : ℚ)) =
            ∑ r ∈ Finset.range k, (r : ℚ) by
              symm
              exact sum_range_eq_sum_Ico_one (fun r ↦ (r : ℚ)) hk (by simp)]
        exact NField.Alignment.DedekindReciprocity.rational_sum_range_id k
      rw [Finset.sum_sub_distrib]
      have hdiv : (∑ r ∈ Finset.Ico 1 k, (r : ℚ) / (k : ℚ)) =
          (∑ r ∈ Finset.Ico 1 k, (r : ℚ)) / (k : ℚ) := by
        rw [Finset.sum_div]
      rw [hdiv, hsum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Ico 1 k).card = k - 1 := by simp
      rw [hcard]
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      field_simp [hkQ]
      ring

theorem sum_rationalSawtooth_coprime_mul
    {a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) :
    (∑ r ∈ Finset.range k, rationalSawtooth (a * r) k) = 0 := by
  letI : NeZero k := ⟨hk.ne'⟩
  let e := coprimeResidueEquiv hcop
  calc
    (∑ r ∈ Finset.range k, rationalSawtooth (a * r) k) =
        ∑ r : Fin k, rationalSawtooth (a * r.val) k := by
          exact (Fin.sum_univ_eq_sum_range
            (fun r : ℕ ↦ rationalSawtooth (a * r) k) k).symm
    _ = ∑ r : Fin k, rationalSawtooth (e r).val k := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [coprimeResidueEquiv_val hcop]
          unfold rationalSawtooth
          rw [Nat.mod_mod]
    _ = ∑ r : Fin k, rationalSawtooth r.val k :=
      e.sum_comp (fun r : Fin k ↦ rationalSawtooth r.val k)
    _ = ∑ r ∈ Finset.range k, rationalSawtooth r k := by
          exact Fin.sum_univ_eq_sum_range
            (fun r : ℕ ↦ rationalSawtooth r k) k
    _ = 0 := sum_rationalSawtooth_range hk

theorem rationalSawtooth_add_period (a k r : ℕ) :
    rationalSawtooth ((r + k) * a) k = rationalSawtooth (r * a) k := by
  unfold rationalSawtooth
  simp [Nat.add_mul, Nat.add_mod]

theorem sum_periodic_blocks
    (f : ℕ → ℚ) {k : ℕ}
    (hperiod : ∀ r, f (r + k) = f r) (M s : ℕ) :
    (∑ r ∈ Finset.range (M * k + s), f r) =
      (M : ℚ) * (∑ r ∈ Finset.range k, f r) +
        ∑ r ∈ Finset.range s, f r := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Nat.succ_mul]
      have hlen : M * k + k + s = k + (M * k + s) := by omega
      rw [hlen]
      rw [Finset.sum_range_add]
      have htail :
          (∑ x ∈ Finset.range (M * k + s), f (k + x)) =
            ∑ x ∈ Finset.range (M * k + s), f x := by
        apply Finset.sum_congr rfl
        intro x _hx
        simpa [Nat.add_comm] using hperiod x
      rw [htail, ih]
      push_cast
      ring

/-- Complete blocks cancel and only the Euclidean terminal prefix remains. -/
theorem boundaryMidpoint_eq_cyclicPrefix
    {N a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) :
    boundaryMidpoint N a k = cyclicPrefixResponse a k (N % k) := by
  let f := fun r : ℕ ↦ rationalSawtooth ((r + 1) * a) k
  have hperiod : ∀ r, f (r + k) = f r := by
    intro r
    unfold f
    rw [show r + k + 1 = (r + 1) + k by omega]
    exact rationalSawtooth_add_period a k (r + 1)
  have hblock : (∑ r ∈ Finset.range k, f r) = 0 := by
    have hshift := sum_range_shift_one
      (fun r ↦ rationalSawtooth (r * a) k) k
    have hzero0 : rationalSawtooth (0 * a) k = 0 := by simp [rationalSawtooth]
    have hzerok : rationalSawtooth (k * a) k = 0 := by simp [rationalSawtooth]
    have hbase := sum_rationalSawtooth_coprime_mul hk hcop
    rw [hzero0, Finset.sum_range_succ, hzerok, add_zero] at hshift
    unfold f
    rw [hshift]
    simpa [Nat.mul_comm] using hbase
  have hdecomp : N / k * k + N % k = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N k
  unfold boundaryMidpoint cyclicPrefixResponse
  change 2 * (∑ r ∈ Finset.range N, f r) =
    2 * ∑ r ∈ Finset.range (N % k), f r
  have hsum := sum_periodic_blocks f hperiod (N / k) (N % k)
  rw [hdecomp] at hsum
  rw [hsum, hblock]
  ring

/-- The two square-jump formulas after the midpoint and multiplicity have
been identified. -/
theorem squared_jump_data
    {N a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) (L : ℚ) :
    boundaryMidpoint N a k = cyclicPrefixResponse a k (N % k) ∧
      let T := cyclicPrefixResponse a k (N % k)
      let M : ℚ := (N / k : ℕ)
      (T - M) ^ 2 - (T + M) ^ 2 = -4 * M * T ∧
        2 * L * (T - M) - 2 * L * (T + M) = -4 * L * M := by
  refine ⟨boundaryMidpoint_eq_cyclicPrefix hk hcop, ?_⟩
  dsimp only
  constructor <;> ring

end NField.Alignment.CarrierJumpData
