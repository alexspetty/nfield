/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFluctuationSum

/-!
# The collision periodic table

Generic floor-reflection, sharp-range, sign-balance, and exact finite-table
proofs for the Lean companion to "The Collision Periodic Table".
-/

namespace NField.Alignment.CollisionPeriodicTable

open scoped BigOperators
open NField.Alignment.CollisionFluctuationSum

theorem complement_div {M n x : ℕ} (hM : 0 < M)
    (hxlt : x < n * M) (hmod : x % M ≠ 0) :
    (n * M - x) / M = n - x / M - 1 := by
  let q := x / M
  let r := x % M
  have hrpos : 0 < r := by exact Nat.pos_of_ne_zero hmod
  have hrlt : r < M := Nat.mod_lt x hM
  have hq_lt : q < n := (Nat.div_lt_iff_lt_mul hM).2 hxlt
  have hdecomp : r + M * q = x := Nat.mod_add_div x M
  have heq : n * M - x =
      M * (n - q - 1) + (M - r) := by
    let k := n - q - 1
    have hn_eq : n = k + q + 1 := by
      dsimp [k]
      omega
    rw [hn_eq, ← hdecomp]
    simp only [Nat.add_mul, Nat.one_mul]
    have hk : k + q + 1 - q - 1 = k := by omega
    rw [hk, Nat.mul_comm M k, Nat.mul_comm M q]
    omega
  change (n * M - x) / M = n - q - 1
  rw [heq, Nat.mul_add_div hM]
  have : (M - r) / M = 0 := Nat.div_eq_of_lt (by omega)
  rw [this, Nat.add_zero]

theorem floorJump_complement_interior {M a n : ℕ}
    (hM : 0 < M) (halt : a < M)
    (hn : 0 < n) (hnnext : n + 1 < M)
    (hcop : Nat.Coprime a M) :
    floorJump M a n + floorJump M (M - a) n = 1 := by
  have hna : n * a < n * M := (Nat.mul_lt_mul_left hn).2 halt
  have hn1a : (n + 1) * a < (n + 1) * M :=
    (Nat.mul_lt_mul_left (by omega)).2 halt
  have hmodn : n * a % M ≠ 0 := by
    intro hzero
    have hd : M ∣ n * a := Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hdn : M ∣ n := (hcop.symm.dvd_mul_right).mp hd
    have hMn : M ≤ n := Nat.le_of_dvd hn hdn
    omega
  have hmodn1 : (n + 1) * a % M ≠ 0 := by
    intro hzero
    have hd : M ∣ (n + 1) * a := Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hdn : M ∣ n + 1 := (hcop.symm.dvd_mul_right).mp hd
    have hMn : M ≤ n + 1 := Nat.le_of_dvd (by omega) hdn
    omega
  have hdivn : (n * M - n * a) / M = n - n * a / M - 1 :=
    complement_div hM hna hmodn
  have hdivn1 : ((n + 1) * M - (n + 1) * a) / M =
      n + 1 - (n + 1) * a / M - 1 :=
    complement_div hM hn1a hmodn1
  have hA : (n + 1) * a / M ≤ n := by
    have : (n + 1) * a / M < n + 1 :=
      (Nat.div_lt_iff_lt_mul hM).2 hn1a
    omega
  have hB : n * a / M + 1 ≤ n := by
    have : n * a / M < n := (Nat.div_lt_iff_lt_mul hM).2 hna
    omega
  have hs1 : n + 1 - (n + 1) * a / M - 1 =
      n - (n + 1) * a / M := by omega
  have hs2 : n - n * a / M - 1 =
      n - (n * a / M + 1) := by omega
  unfold floorJump
  rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib,
    hdivn1, hdivn, hs1, hs2]
  rw [Nat.cast_sub hA, Nat.cast_sub hB]
  push_cast
  ring

theorem pred_mul_div_self {M a : ℕ} (hM : 0 < M) (ha : 0 < a)
    (halt : a < M) : (M - 1) * a / M = a - 1 := by
  have heq : (M - 1) * a = M * (a - 1) + (M - a) := by
    have haM : a ≤ M := by omega
    have hsum : (M - 1) * a + a =
        (M * (a - 1) + (M - a)) + a := by
      calc
      (M - 1) * a + a = ((M - 1) + 1) * a := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = M * a := by rw [Nat.sub_add_cancel (by omega : 1 ≤ M)]
      _ = M * ((a - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
      _ = M * (a - 1) + M := by rw [Nat.mul_add, Nat.mul_one]
      _ = M * (a - 1) + ((M - a) + a) := by
        rw [Nat.sub_add_cancel haM]
      _ = (M * (a - 1) + (M - a)) + a := by omega
    exact Nat.add_right_cancel hsum
  rw [heq, Nat.mul_add_div hM]
  rw [Nat.div_eq_of_lt (Nat.sub_lt hM ha)]
  omega

theorem floorJump_complement_zero {M a : ℕ} (hM : 0 < M)
    (ha : 0 < a) (halt : a < M) :
    floorJump M a 0 + floorJump M (M - a) 0 = 0 := by
  have hdiva : a / M = 0 := Nat.div_eq_of_lt halt
  have hdivcomp : (M - a) / M = 0 :=
    Nat.div_eq_of_lt (Nat.sub_lt hM ha)
  simp [floorJump, hdiva, hdivcomp]

theorem floorJump_complement_last {M a : ℕ} (hM : 0 < M)
    (ha : 0 < a) (halt : a < M) :
    floorJump M a (M - 1) + floorJump M (M - a) (M - 1) = 2 := by
  have hM1 : M - 1 + 1 = M := by omega
  have hcomp : 0 < M - a := Nat.sub_pos_of_lt halt
  have hcomp_lt : M - a < M := Nat.sub_lt hM ha
  have htopa : M * a / M = a := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left a hM
  have htopcomp : M * (M - a) / M = M - a := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left (M - a) hM
  unfold floorJump
  rw [hM1, htopa,
    pred_mul_div_self hM ha halt,
    htopcomp,
    pred_mul_div_self hM hcomp hcomp_lt]
  omega

theorem diagonal_jump_pair_sum {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2) (hcop : Nat.Coprime a (b ^ 2)) :
    ∑ n ∈ diagonalSlices b,
      (floorJump (b ^ 2) a n + floorJump (b ^ 2) (b ^ 2 - a) n) = b := by
  have hq : 0 < b ^ 2 := pow_pos (by omega) 2
  have hzero :
      floorJump (b ^ 2) a ((b + 1) * 0) +
          floorJump (b ^ 2) (b ^ 2 - a) ((b + 1) * 0) = 0 := by
    simpa using floorJump_complement_zero hq ha halt
  have hlast_index : (b + 1) * (b - 1) = b ^ 2 - 1 := by
    let k := b - 1
    have hbk : b = k + 1 := by
      dsimp [k]
      omega
    rw [hbk]
    simp
    ring_nf
    omega
  have hlast :
      floorJump (b ^ 2) a ((b + 1) * (b - 1)) +
          floorJump (b ^ 2) (b ^ 2 - a) ((b + 1) * (b - 1)) = 2 := by
    rw [hlast_index]
    exact floorJump_complement_last hq ha halt
  have hinterior (d : ℕ) (hd : d ∈ Finset.Ico 1 (b - 1)) :
      floorJump (b ^ 2) a ((b + 1) * d) +
          floorJump (b ^ 2) (b ^ 2 - a) ((b + 1) * d) = 1 := by
    have hdlo : 1 ≤ d := (Finset.mem_Ico.mp hd).1
    have hdhi : d < b - 1 := (Finset.mem_Ico.mp hd).2
    have hnpos : 0 < (b + 1) * d := by positivity
    have hnnext : (b + 1) * d + 1 < b ^ 2 := by
      have hd2 : d + 2 ≤ b := by omega
      have hmul := Nat.mul_le_mul_left (b + 1) hd2
      nlinarith
    exact floorJump_complement_interior hq halt hnpos hnnext hcop
  unfold diagonalSlices
  rw [Finset.sum_image]
  · have hrange : Finset.range b =
        insert 0 (Finset.Ico 1 (b - 1) ∪ {b - 1}) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union,
        Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [hrange]
    have hzero_not_in : 0 ∉ Finset.Ico 1 (b - 1) ∪ {b - 1} := by
      simp
      omega
    rw [Finset.sum_insert hzero_not_in, hzero]
    simp only [zero_add]
    have hlast_not_in : b - 1 ∉ Finset.Ico 1 (b - 1) := by simp
    rw [Finset.sum_union (by simp), Finset.sum_singleton, hlast]
    have hintsum :
        ∑ d ∈ Finset.Ico 1 (b - 1),
          (floorJump (b ^ 2) a ((b + 1) * d) +
            floorJump (b ^ 2) (b ^ 2 - a) ((b + 1) * d)) = b - 2 := by
      rw [Finset.sum_congr rfl hinterior]
      simp
      exact_mod_cast (show b - 1 - 1 = b - 2 by omega)
    rw [hintsum]
    omega
  · intro d hd e he hde
    exact Nat.mul_left_cancel (by omega : 0 < b + 1) hde

theorem quotient_complement_square {b a : ℕ} (hb2 : 2 ≤ b)
    (_ha : 0 < a) (halt : a < b ^ 2) (hcop : Nat.Coprime a (b ^ 2)) :
    a / b + (b ^ 2 - a) / b = b - 1 := by
  have hb : 0 < b := by omega
  have hmod : a % b ≠ 0 :=
    mod_base_ne_zero_of_coprime_square hb2 hcop
  have hdiv : (b * b - a) / b = b - a / b - 1 :=
    complement_div hb (by simpa [pow_two] using halt) hmod
  rw [show b ^ 2 = b * b by ring, hdiv]
  have hq : a / b < b := by
    apply (Nat.div_lt_iff_lt_mul hb).2
    simpa [pow_two] using halt
  omega

theorem fluctuationTable_reflection {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2) (hcop : Nat.Coprime a (b ^ 2)) :
    fluctuationTable b a + fluctuationTable b (b ^ 2 - a) = -1 := by
  have hsum := diagonal_jump_pair_sum hb2 ha halt hcop
  have hquot := quotient_complement_square hb2 ha halt hcop
  rw [Finset.sum_add_distrib] at hsum
  have hquotZ :
      ((a / b : ℕ) : ℤ) + (((b ^ 2 - a) / b : ℕ) : ℤ) =
        (b : ℤ) - 1 := by
    have hcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ b)]
      norm_num
    exact (Int.ofNat_inj.mpr hquot).trans hcast
  unfold fluctuationTable
  linear_combination hsum - hquotZ

theorem floorJump_bounds {M a n : ℕ} (hM : 0 < M) (halt : a < M) :
    0 ≤ floorJump M a n ∧ floorJump M a n ≤ 1 := by
  let x := n * a
  let q := x / M
  let r := x % M
  have hrlt : r < M := Nat.mod_lt x hM
  have hdecomp : r + M * q = x := Nat.mod_add_div x M
  have hmul : (n + 1) * a = x + a := by
    dsimp [x]
    ring
  have hdiv : (x + a) / M = q + (r + a) / M := by
    rw [← hdecomp]
    rw [show r + M * q + a = M * q + (r + a) by omega]
    exact Nat.mul_add_div hM q (r + a)
  have hsmall : (r + a) / M ≤ 1 := by
    have hlt : r + a < 2 * M := by omega
    have : (r + a) / M < 2 := (Nat.div_lt_iff_lt_mul hM).2 hlt
    omega
  unfold floorJump
  rw [hmul, hdiv]
  rw [show n * a / M = q by rfl]
  rw [Nat.cast_add]
  have hsmallZ : (((r + a) / M : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast hsmall
  have hnonnegZ : (0 : ℤ) ≤ (((r + a) / M : ℕ) : ℤ) :=
    Int.natCast_nonneg _
  constructor <;> omega

theorem floorJump_eq_one_of_threshold {M a n : ℕ}
    (hM : 0 < M) (halt : a < M)
    (hthreshold : M - a ≤ (n * a) % M) :
    floorJump M a n = 1 := by
  let x := n * a
  let q := x / M
  let r := x % M
  have hrlt : r < M := Nat.mod_lt x hM
  have hdecomp : r + M * q = x := Nat.mod_add_div x M
  have hmul : (n + 1) * a = x + a := by
    dsimp [x]
    ring
  have hdiv : (x + a) / M = q + (r + a) / M := by
    rw [← hdecomp]
    rw [show r + M * q + a = M * q + (r + a) by omega]
    exact Nat.mul_add_div hM q (r + a)
  change M - a ≤ r at hthreshold
  have hrange : M ≤ r + a ∧ r + a < 2 * M := by
    constructor <;> omega
  have hone : (r + a) / M = 1 :=
    Nat.div_eq_of_lt_le (by simpa using hrange.1) hrange.2
  unfold floorJump
  rw [hmul, hdiv, show n * a / M = q by rfl, hone]
  push_cast
  ring

theorem diagonal_floorJump_sum_le {b a : ℕ} (hb2 : 2 ≤ b)
    (halt : a < b ^ 2) :
    ∑ n ∈ diagonalSlices b, floorJump (b ^ 2) a n ≤ (b - 1 : ℕ) := by
  have hq : 0 < b ^ 2 := pow_pos (by omega) 2
  have hzero : floorJump (b ^ 2) a ((b + 1) * 0) = 0 := by
    have hdiv : a / b ^ 2 = 0 := Nat.div_eq_of_lt halt
    simp [floorJump, hdiv]
  unfold diagonalSlices
  rw [Finset.sum_image]
  · have hrange : Finset.range b = insert 0 (Finset.Ico 1 b) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hrange]
    have hzero_not_in : 0 ∉ Finset.Ico 1 b := by simp
    rw [Finset.sum_insert hzero_not_in, hzero, zero_add]
    calc
      ∑ d ∈ Finset.Ico 1 b, floorJump (b ^ 2) a ((b + 1) * d)
          ≤ ∑ _d ∈ Finset.Ico 1 b, (1 : ℤ) := by
            apply Finset.sum_le_sum
            intro d hd
            exact (floorJump_bounds hq halt).2
      _ = (b - 1 : ℕ) := by
        simp
  · intro d hd e he hde
    exact Nat.mul_left_cancel (by omega : 0 < b + 1) hde

theorem fluctuationTable_upper {b a : ℕ} (hb2 : 2 ≤ b)
    (halt : a < b ^ 2) :
    fluctuationTable b a ≤ (b : ℤ) - 2 := by
  have hsum := diagonal_floorJump_sum_le hb2 halt
  have hquot : (0 : ℤ) ≤ ((a / b : ℕ) : ℤ) := Int.natCast_nonneg _
  have hcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]
    norm_num
  unfold fluctuationTable
  rw [hcast] at hsum
  omega

theorem endpoint_diagonal_mod {b d : ℕ} (hb2 : 2 ≤ b)
    (hd : 0 < d) (hdb : d < b) :
    (((b + 1) * d) * (b - 1)) % (b ^ 2) = b ^ 2 - d := by
  have hqpos : 0 < b ^ 2 := pow_pos (by omega) 2
  have hdq : d ≤ b ^ 2 := by nlinarith
  have hprod : ((b + 1) * d) * (b - 1) + d = b ^ 2 * d := by
    let k := b - 1
    have hbk : b = k + 1 := by
      dsimp [k]
      omega
    rw [hbk]
    simp
    ring
  have hdecomp : ((b + 1) * d) * (b - 1) =
      b ^ 2 * (d - 1) + (b ^ 2 - d) := by
    have hsum : ((b + 1) * d) * (b - 1) + d =
        (b ^ 2 * (d - 1) + (b ^ 2 - d)) + d := by
      calc
        ((b + 1) * d) * (b - 1) + d = b ^ 2 * d := hprod
        _ = b ^ 2 * ((d - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
        _ = b ^ 2 * (d - 1) + b ^ 2 := by rw [Nat.mul_add, Nat.mul_one]
        _ = b ^ 2 * (d - 1) + ((b ^ 2 - d) + d) := by
          rw [Nat.sub_add_cancel hdq]
        _ = (b ^ 2 * (d - 1) + (b ^ 2 - d)) + d := by omega
    exact Nat.add_right_cancel hsum
  rw [hdecomp, Nat.add_mod, Nat.mul_mod]
  simp only [Nat.mod_self, zero_mul, Nat.zero_mod, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hqpos hd)

theorem endpoint_diagonal_sum {b : ℕ} (hb2 : 2 ≤ b) :
    ∑ n ∈ diagonalSlices b, floorJump (b ^ 2) (b - 1) n =
      (b - 1 : ℕ) := by
  have hq : 0 < b ^ 2 := pow_pos (by omega) 2
  have ha_lt : b - 1 < b ^ 2 := by
    calc
      b - 1 < b := Nat.sub_lt (by omega) (by omega)
      _ ≤ b ^ 2 := by nlinarith
  have hzero : floorJump (b ^ 2) (b - 1) ((b + 1) * 0) = 0 := by
    have hdiv : (b - 1) / b ^ 2 = 0 := Nat.div_eq_of_lt ha_lt
    simp [floorJump, hdiv]
  have hone (d : ℕ) (hdmem : d ∈ Finset.Ico 1 b) :
      floorJump (b ^ 2) (b - 1) ((b + 1) * d) = 1 := by
    have hd : 0 < d := (Finset.mem_Ico.mp hdmem).1
    have hdb : d < b := (Finset.mem_Ico.mp hdmem).2
    have hmod := endpoint_diagonal_mod hb2 hd hdb
    apply floorJump_eq_one_of_threshold hq ha_lt
    rw [hmod]
    omega
  unfold diagonalSlices
  rw [Finset.sum_image]
  · have hrange : Finset.range b = insert 0 (Finset.Ico 1 b) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hrange]
    have hzero_not_in : 0 ∉ Finset.Ico 1 b := by simp
    rw [Finset.sum_insert hzero_not_in, hzero, zero_add]
    rw [Finset.sum_congr rfl hone]
    simp
  · intro d hd e he hde
    exact Nat.mul_left_cancel (by omega : 0 < b + 1) hde

theorem fluctuationTable_at_upper_endpoint {b : ℕ} (hb2 : 2 ≤ b) :
    fluctuationTable b (b - 1) = (b : ℤ) - 2 := by
  have hsum := endpoint_diagonal_sum hb2
  have hdiv : (b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
  have hcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]
    norm_num
  unfold fluctuationTable
  rw [hdiv, hsum, hcast]
  omega

theorem fluctuationTable_lower {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2) (hcop : Nat.Coprime a (b ^ 2)) :
    -((b : ℤ) - 1) ≤ fluctuationTable b a := by
  have hreflect := fluctuationTable_reflection hb2 ha halt hcop
  have hcomp_lt : b ^ 2 - a < b ^ 2 :=
    Nat.sub_lt (pow_pos (by omega) 2) ha
  have hupper := fluctuationTable_upper hb2 hcomp_lt
  omega

theorem endpoint_coprime_square {b : ℕ} (hb2 : 2 ≤ b) :
    Nat.Coprime (b - 1) (b ^ 2) := by
  have hbdecomp : b = (b - 1) + 1 := by omega
  have hbase : Nat.Coprime (b - 1) b := by
    rw [hbdecomp]
    simp
  exact hbase.pow_right 2

theorem fluctuationTable_at_lower_endpoint {b : ℕ} (hb2 : 2 ≤ b) :
    fluctuationTable b (b ^ 2 - (b - 1)) = -((b : ℤ) - 1) := by
  have ha : 0 < b - 1 := by omega
  have halt : b - 1 < b ^ 2 := by
    calc
      b - 1 < b := Nat.sub_lt (by omega) (by omega)
      _ ≤ b ^ 2 := by nlinarith
  have hreflect := fluctuationTable_reflection hb2 ha halt
    (endpoint_coprime_square hb2)
  rw [fluctuationTable_at_upper_endpoint hb2] at hreflect
  omega

theorem sharp_unit_range {b a : ℕ} (hb2 : 2 ≤ b)
    (ha : 0 < a) (halt : a < b ^ 2) (hcop : Nat.Coprime a (b ^ 2)) :
    -((b : ℤ) - 1) ≤ fluctuationTable b a ∧
      fluctuationTable b a ≤ (b : ℤ) - 2 :=
  ⟨fluctuationTable_lower hb2 ha halt hcop,
    fluctuationTable_upper hb2 halt⟩

theorem negative_card_twice_of_reflection
    {α : Type*} [Fintype α] (e : α ≃ α) (F : α → ℤ)
    (hinvol : Function.Involutive e)
    (hreflect : ∀ a, F a + F (e a) = -1) :
    2 * Fintype.card {a : α // F a < 0} = Fintype.card α := by
  classical
  let pair : {a : α // F a < 0} ≃ {a : α // ¬F a < 0} :=
    { toFun := fun a => ⟨e a, by
        have hp := hreflect a
        omega⟩
      invFun := fun a => ⟨e a, by
        have hp := hreflect a
        omega⟩
      left_inv := fun a => by
        apply Subtype.ext
        exact hinvol a
      right_inv := fun a => by
        apply Subtype.ext
        exact hinvol a }
  have hcard : Fintype.card {a : α // F a < 0} =
      Fintype.card {a : α // ¬F a < 0} := Fintype.card_congr pair
  rw [Fintype.card_subtype_compl] at hcard
  have hle := Fintype.card_subtype_le (p := fun a : α => F a < 0)
  omega

abbrev PeriodicUnit (b : ℕ) :=
  {a : ℕ // a ∈ reducedResidues (b ^ 2)}

def periodicUnitComplement (b : ℕ) (_hb2 : 2 ≤ b) :
    PeriodicUnit b ≃ PeriodicUnit b where
  toFun a := ⟨b ^ 2 - a, by
    rcases Finset.mem_filter.mp a.property with ⟨harange, hacop⟩
    have haIco := Finset.mem_Ico.mp harange
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · exact (Nat.coprime_self_sub_left (by omega)).2 hacop⟩
  invFun a := ⟨b ^ 2 - a, by
    rcases Finset.mem_filter.mp a.property with ⟨harange, hacop⟩
    have haIco := Finset.mem_Ico.mp harange
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · exact (Nat.coprime_self_sub_left (by omega)).2 hacop⟩
  left_inv a := by
    apply Subtype.ext
    have haIco := Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1
    change b ^ 2 - (b ^ 2 - (a : ℕ)) = (a : ℕ)
    omega
  right_inv a := by
    apply Subtype.ext
    have haIco := Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1
    change b ^ 2 - (b ^ 2 - (a : ℕ)) = (a : ℕ)
    omega

theorem periodicUnitComplement_involutive (b : ℕ) (hb2 : 2 ≤ b) :
    Function.Involutive (periodicUnitComplement b hb2) :=
  (periodicUnitComplement b hb2).symm_apply_apply

theorem periodicUnit_table_reflection {b : ℕ} (hb2 : 2 ≤ b)
    (a : PeriodicUnit b) :
    fluctuationTable b a +
      fluctuationTable b (periodicUnitComplement b hb2 a) = -1 := by
  rcases Finset.mem_filter.mp a.property with ⟨harange, hcop⟩
  have haIco := Finset.mem_Ico.mp harange
  exact fluctuationTable_reflection hb2 haIco.1 haIco.2 hcop

theorem periodicUnit_card {b : ℕ} (hb2 : 2 ≤ b) :
    Fintype.card (PeriodicUnit b) = Nat.totient (b ^ 2) := by
  rw [Fintype.card_coe]
  rw [Nat.totient_eq_card_coprime]
  apply congrArg Finset.card
  ext a
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨ha0, halt⟩, hcop⟩
    exact ⟨halt, hcop.symm⟩
  · rintro ⟨halt, hcop⟩
    have ha0 : 0 < a := by
      by_contra hnot
      have hazero : a = 0 := by omega
      subst a
      simp at hcop
      nlinarith [show 2 ≤ b from hb2]
    exact ⟨⟨ha0, halt⟩, hcop.symm⟩

theorem periodicUnit_negative_count {b : ℕ} (hb2 : 2 ≤ b) :
    2 * Fintype.card
      {a : PeriodicUnit b // fluctuationTable b a < 0} =
        Nat.totient (b ^ 2) := by
  rw [← periodicUnit_card hb2]
  exact negative_card_twice_of_reflection
    (periodicUnitComplement b hb2)
    (fun a : PeriodicUnit b => fluctuationTable b a)
    (periodicUnitComplement_involutive b hb2)
    (periodicUnit_table_reflection hb2)

theorem periodicUnit_grand_mean {b : ℕ} (hb2 : 2 ≤ b) :
    (Fintype.card (PeriodicUnit b) : ℚ)⁻¹ *
      ∑ a : PeriodicUnit b, (fluctuationTable b a : ℚ) = -1 / 2 := by
  let witness : PeriodicUnit b := ⟨b - 1, by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Ico.mpr
      constructor
      · omega
      · calc
          b - 1 < b := Nat.sub_lt (by omega) (by omega)
          _ ≤ b ^ 2 := by nlinarith
    · exact endpoint_coprime_square hb2⟩
  letI : Nonempty (PeriodicUnit b) := ⟨witness⟩
  apply grand_mean_of_reflection (periodicUnitComplement b hb2)
  intro a
  exact_mod_cast periodicUnit_table_reflection hb2 a

def positiveUnitClasses (b : ℕ) : Finset ℕ :=
  (reducedResidues (b ^ 2)).filter fun a => 0 < fluctuationTable b a

def zeroUnitClasses (b : ℕ) : Finset ℕ :=
  (reducedResidues (b ^ 2)).filter fun a => fluctuationTable b a = 0

def negativeUnitClasses (b : ℕ) : Finset ℕ :=
  (reducedResidues (b ^ 2)).filter fun a => fluctuationTable b a < 0

def decimalDisplayedTable : List (ℕ × ℤ) :=
  [(1, 0), (3, 2), (7, 0), (9, 8),
   (11, -1), (13, -1), (17, 1), (19, -1),
   (21, 0), (23, -2), (27, 6), (29, 0),
   (31, -1), (33, -1), (37, -3), (39, -1),
   (41, -4), (43, 0), (47, -2), (49, 0),
   (51, -1), (53, 1), (57, -1), (59, 3),
   (61, 0), (63, 2), (67, 0), (69, 0),
   (71, -1), (73, -7), (77, 1), (79, -1),
   (81, 0), (83, -2), (87, 0), (89, 0),
   (91, -9), (93, -1), (97, -3), (99, -1)]

theorem decimal_displayed_table_complete :
    decimalDisplayedTable.toFinset =
      (reducedResidues 100).image fun a => (a, fluctuationTable 10 a) := by
  decide

theorem decimal_sign_counts :
    (positiveUnitClasses 10).card = 8 ∧
    (zeroUnitClasses 10).card = 12 ∧
    (negativeUnitClasses 10).card = 20 := by
  decide

theorem selected_base_sign_counts :
    ((reducedResidues (3 ^ 2)).card,
      (positiveUnitClasses 3).card, (zeroUnitClasses 3).card,
      (negativeUnitClasses 3).card) = (6, 1, 2, 3) ∧
    ((reducedResidues (5 ^ 2)).card,
      (positiveUnitClasses 5).card, (zeroUnitClasses 5).card,
      (negativeUnitClasses 5).card) = (20, 4, 6, 10) ∧
    ((reducedResidues (6 ^ 2)).card,
      (positiveUnitClasses 6).card, (zeroUnitClasses 6).card,
      (negativeUnitClasses 6).card) = (12, 2, 4, 6) ∧
    ((reducedResidues (7 ^ 2)).card,
      (positiveUnitClasses 7).card, (zeroUnitClasses 7).card,
      (negativeUnitClasses 7).card) = (42, 10, 11, 21) ∧
    ((reducedResidues (8 ^ 2)).card,
      (positiveUnitClasses 8).card, (zeroUnitClasses 8).card,
      (negativeUnitClasses 8).card) = (32, 7, 9, 16) ∧
    ((reducedResidues (10 ^ 2)).card,
      (positiveUnitClasses 10).card, (zeroUnitClasses 10).card,
      (negativeUnitClasses 10).card) = (40, 8, 12, 20) ∧
    ((reducedResidues (12 ^ 2)).card,
      (positiveUnitClasses 12).card, (zeroUnitClasses 12).card,
      (negativeUnitClasses 12).card) = (48, 11, 13, 24) := by
  decide

def checkedSmallBases : Finset ℕ := Finset.Icc 2 12

def checkedInputs (b : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (4 * b ^ 2 - 1)).filter fun N => N.Coprime b

end NField.Alignment.CollisionPeriodicTable
