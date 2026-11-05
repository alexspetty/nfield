/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionTransformStrip
import NField.Alignment.PrimeCarryTableColumnLaw

/-! # Sharp base-power witnesses for the actual all-lag table -/

namespace NField.Alignment.BasePowerOptimality

open scoped BigOperators
open CollisionFluctuationSum CollisionPeriodicTable CenteredCollisionSum
  CollisionTransformStrip PrimeCarryTableColumnLaw

/-- Below the wrapping threshold the integer floor increment vanishes. -/
theorem floorJump_eq_zero_of_below {M a n : ℕ} (hM : 0 < M)
    (hbelow : n * a % M + a < M) : floorJump M a n = 0 := by
  have hdecomp := Nat.mod_add_div (n * a) M
  have hdiv : (n * a + a) / M = n * a / M := by
    calc
      (n * a + a) / M = (M * (n * a / M) + (n * a % M + a)) / M := by
        congr 1
        omega
      _ = n * a / M + (n * a % M + a) / M :=
        Nat.mul_add_div hM _ _
      _ = n * a / M := by rw [Nat.div_eq_of_lt hbelow, Nat.add_zero]
  unfold floorJump
  rw [Nat.add_mul, Nat.one_mul, hdiv]
  omega

theorem allLagTable_one {b ell : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    allLagTable b ell 1 = 0 := by
  have hM : 0 < allLagModulus b ell := pow_pos (by omega) _
  have hM2 : 1 < allLagModulus b ell := by
    exact one_lt_pow₀ (by omega) (by omega)
  have hsum : (∑ n ∈ allLagDiagonal b ell,
      floorJump (allLagModulus b ell) 1 n) = 1 := by
    rw [Finset.sum_eq_single (allLagModulus b ell - 1)]
    · exact floorJump_last_eq_one hM (by omega) hM2
    · intro n hn hne
      have hnlt := allLagDiagonal_index_lt hb2 hell hn
      apply floorJump_eq_zero_of_below hM
      simpa only [Nat.mul_one, Nat.mod_eq_of_lt hnlt] using
        (show n + 1 < allLagModulus b ell by omega)
    · intro hnot
      exact (hnot (allLagDiagonal_last_mem hb2 hell)).elim
  unfold allLagTable
  rw [hsum, Nat.div_eq_of_lt (by omega : 1 < b)]
  norm_num

theorem pow_predecessor {b ell : ℕ} (hell : 1 ≤ ell) :
    b ^ ell = b * b ^ (ell - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel hell]
  rw [pow_succ]
  ring

/-- The canonical residue calculation in the sharpness proof. -/
theorem sharp_witness_residue {b ell d k : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hd : d < b) (hk : k < b ^ (ell - 1)) :
    (((b ^ ell + 1) * d + b * k) * ((b - 1) * b ^ ell + 1)) %
      allLagModulus b ell = d + b * k := by
  have hpow := pow_predecessor (b := b) hell
  have hM : allLagModulus b ell = b * (b * b ^ (ell - 1)) := by
    unfold allLagModulus
    rw [pow_succ, hpow]
    ring
  have hb : b = (b - 1) + 1 := by omega
  have heq : ((b ^ ell + 1) * d + b * k) * ((b - 1) * b ^ ell + 1) =
      allLagModulus b ell * (((b - 1) * b ^ (ell - 1) + 1) * d +
        (b - 1) * k) + (d + b * k) := by
    rw [hM, hpow]
    generalize hK : b ^ (ell - 1) = K
    generalize hc : b - 1 = c at *
    rw [hb]
    ring
  have hres : d + b * k < b ^ ell := by
    rw [hpow]
    nlinarith
  have hlt : d + b * k < allLagModulus b ell := by
    rw [hM]
    have hpos : 0 < b * b ^ (ell - 1) := by positivity
    rw [hpow] at hres
    nlinarith
  rw [heq, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hlt]

theorem sharp_witness_eq_displayed {b ell : ℕ} (hb2 : 2 ≤ b) :
    (b - 1) * b ^ ell + 1 = allLagModulus b ell - b ^ ell + 1 := by
  have hb : b - 1 + 1 = b := by omega
  have hM : allLagModulus b ell = b * b ^ ell := by
    unfold allLagModulus
    rw [pow_succ]
    ring
  rw [hM, ← hb]
  simp [Nat.add_mul]

theorem sharp_witness_bounds {b ell : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    0 < (b - 1) * b ^ ell + 1 ∧
      (b - 1) * b ^ ell + 1 < allLagModulus b ell := by
  have hpow := pow_predecessor (b := b) hell
  have hK : 0 < b ^ (ell - 1) := pow_pos (by omega) _
  have hB : 1 < b ^ ell := by nlinarith
  have hM : allLagModulus b ell = b * b ^ ell := by
    unfold allLagModulus
    rw [pow_succ]
    ring
  rw [sharp_witness_eq_displayed hb2]
  constructor
  · omega
  · rw [hM]
    have := Nat.le_mul_of_pos_left (b ^ ell) (by omega : 0 < b)
    omega

theorem sharp_witness_coprime {b ell : ℕ} (hell : 1 ≤ ell) :
    ((b - 1) * b ^ ell + 1).Coprime (allLagModulus b ell) := by
  apply Nat.Coprime.pow_right
  rw [pow_predecessor hell,
    show (b - 1) * (b * b ^ (ell - 1)) + 1 =
      ((b - 1) * b ^ (ell - 1)) * b + 1 by ring]
  simp

theorem sharp_witness_quotient {b ell : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    ((b - 1) * b ^ ell + 1) / b = (b - 1) * b ^ (ell - 1) := by
  rw [pow_predecessor hell,
    show (b - 1) * (b * b ^ (ell - 1)) + 1 =
      b * ((b - 1) * b ^ (ell - 1)) + 1 by ring,
    Nat.mul_add_div (by omega : 0 < b), Nat.div_eq_of_lt (by omega : 1 < b)]
  omega

theorem allLagTable_sharp_witness {b ell : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    allLagTable b ell ((b - 1) * b ^ ell + 1) =
      -(((b - 1) * b ^ (ell - 1) : ℕ) : ℤ) := by
  have hM : 0 < allLagModulus b ell := pow_pos (by omega) _
  obtain ⟨ha, halt⟩ := sharp_witness_bounds hb2 hell
  have hsum : (∑ n ∈ allLagDiagonal b ell,
      floorJump (allLagModulus b ell) ((b - 1) * b ^ ell + 1) n) = 1 := by
    rw [Finset.sum_eq_single (allLagModulus b ell - 1)]
    · exact floorJump_last_eq_one hM ha halt
    · intro n hn hne
      obtain ⟨⟨d, k⟩, hdk, rfl⟩ := Finset.mem_image.mp hn
      have hd : d < b := Finset.mem_range.mp (Finset.mem_product.mp hdk).1
      have hk : k < b ^ (ell - 1) :=
        Finset.mem_range.mp (Finset.mem_product.mp hdk).2
      have hpow := pow_predecessor (b := b) hell
      have hK : 0 < b ^ (ell - 1) := pow_pos (by omega) _
      have hKpred : b ^ (ell - 1) - 1 + 1 = b ^ (ell - 1) := by omega
      have hBpred : b ^ ell - 1 + 1 = b ^ ell := by
        have : 0 < b ^ ell := pow_pos (by omega) _
        omega
      have hbpred : b - 1 + 1 = b := by omega
      have hbkmax : b * (b ^ (ell - 1) - 1) + b = b ^ ell := by
        nlinarith [congrArg (fun x => b * x) hKpred]
      have hbk : b * k ≤ b * (b ^ (ell - 1) - 1) :=
        Nat.mul_le_mul_left b (by omega)
      have hres : d + b * k < b ^ ell - 1 := by
        by_contra hnot
        have hdlast : d = b - 1 := by omega
        have hklast : k = b ^ (ell - 1) - 1 := by
          apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < b)
          omega
        apply hne
        change (b ^ ell + 1) * d + b * k = allLagModulus b ell - 1
        rw [hdlast, hklast]
        exact allLag_last_index_eq hb2 hell
      apply floorJump_eq_zero_of_below hM
      rw [sharp_witness_residue hb2 hell hd hk]
      have hw : ((b - 1) * b ^ ell + 1) + b ^ ell = allLagModulus b ell + 1 := by
        unfold allLagModulus
        rw [pow_succ]
        nlinarith [congrArg (fun x => x * b ^ ell) hbpred]
      omega
    · intro hnot
      exact (hnot (allLagDiagonal_last_mem hb2 hell)).elim
  unfold allLagTable
  rw [hsum, sharp_witness_quotient hb2 hell]
  omega

/-- The two witnesses agree at every lower base-power resolution. -/
theorem sharp_witness_lower_congruence {b ell k : ℕ} (hk : k ≤ ell) :
    1 ≡ (b - 1) * b ^ ell + 1 [MOD b ^ k] := by
  apply Nat.ModEq.of_dvd (pow_dvd_pow b hk)
  simp [Nat.ModEq, Nat.add_mod]

/-- The two literal unit representatives and their distinct table values. -/
theorem optimal_base_power_witnesses {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagModulus b ell - b ^ ell + 1).Coprime (allLagModulus b ell) ∧
    1 ≡ allLagModulus b ell - b ^ ell + 1 [MOD b ^ ell] ∧
    allLagTable b ell 1 = 0 ∧
    allLagTable b ell (allLagModulus b ell - b ^ ell + 1) =
      -(((b - 1) * b ^ (ell - 1) : ℕ) : ℤ) := by
  rw [← sharp_witness_eq_displayed (ell := ell) hb2]
  exact ⟨sharp_witness_coprime hell, sharp_witness_lower_congruence le_rfl,
    allLagTable_one hb2 hell, allLagTable_sharp_witness hb2 hell⟩

/-- No function of a lower base-power residue recovers the actual unit table. -/
theorem allLagTable_not_factor_lower_power {b ell k : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (hk : k ≤ ell) :
    ¬ ∃ f : ℕ → ℤ, ∀ a, 0 < a → a < allLagModulus b ell →
      a.Coprime (allLagModulus b ell) → allLagTable b ell a = f (a % b ^ k) := by
  rintro ⟨f, hf⟩
  have hM2 : 1 < allLagModulus b ell :=
    one_lt_pow₀ (by omega) (by omega)
  obtain ⟨ha, halt⟩ := sharp_witness_bounds hb2 hell
  have heq : allLagTable b ell 1 = allLagTable b ell ((b - 1) * b ^ ell + 1) := by
    rw [hf 1 (by omega) hM2 (by simp),
      hf _ ha halt (sharp_witness_coprime hell)]
    exact congrArg f (sharp_witness_lower_congruence hk)
  rw [allLagTable_one hb2 hell, allLagTable_sharp_witness hb2 hell] at heq
  have hpos : 0 < (b - 1) * b ^ (ell - 1) :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  omega

end NField.Alignment.BasePowerOptimality
