/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFluctuationSum

/-!
# The centered collision sum

Reusable all-lag finite-table, fiber-centering, and spectral-gate proofs for
the Lean companion to "The Centered Collision Sum".
-/

namespace NField.Alignment.CenteredCollisionSum

open scoped BigOperators ComplexConjugate
open NField.CollisionDefinition
open NField.Alignment.CollisionFluctuationSum

/-! ## The all-lag finite table -/

/-- The all-lag modulus `b^(ell+1)`. -/
def allLagModulus (b ell : ℕ) : ℕ := b ^ (ell + 1)

/-- Efficient coordinate encoding of the indices whose first and last
base-`b` digits agree.  For `ell >= 1`, `d` is the common endpoint digit and
`k` encodes the free middle digits. -/
def allLagDiagonal (b ell : ℕ) : Finset ℕ :=
  ((Finset.range b).product (Finset.range (b ^ (ell - 1)))).image
    fun dk => (b ^ ell + 1) * dk.1 + b * dk.2

/-- The first/last-digit diagonal has exactly `b^ell` coordinates. -/
theorem allLagDiagonal_card {b ell : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (allLagDiagonal b ell).card = b ^ ell := by
  have hb : 0 < b := by omega
  unfold allLagDiagonal
  rw [Finset.card_image_iff.mpr]
  · change ((Finset.range b) ×ˢ
      (Finset.range (b ^ (ell - 1)))).card = b ^ ell
    rw [Finset.card_product]
    simp
    cases ell with
    | zero => omega
    | succ ell => simp [pow_succ, Nat.mul_comm]
  · rintro ⟨d, k⟩ hdk ⟨e, j⟩ hej hindex
    have hd : d < b := Finset.mem_range.mp (Finset.mem_product.mp hdk).1
    have he : e < b := Finset.mem_range.mp (Finset.mem_product.mp hej).1
    have hpowmod : b ^ ell % b = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self b (by omega))
    have h1mod : 1 % b = 1 := Nat.mod_eq_of_lt (by omega)
    have hmod := congrArg (fun n => n % b) hindex
    have hde : d = e := by
      simpa [Nat.add_mod, Nat.mul_mod, hpowmod,
        h1mod, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] using hmod
    subst e
    have hkj : b * k = b * j := Nat.add_left_cancel hindex
    have : k = j := Nat.mul_left_cancel hb hkj
    subst j
    rfl

/-- The exact finite table `T_{b,ell}(a)`. -/
def allLagTable (b ell a : ℕ) : ℤ :=
  -1 - ((a / b : ℕ) : ℤ) +
    ∑ n ∈ allLagDiagonal b ell,
      floorJump (allLagModulus b ell) a n

/-- Endpoint-corrected diagonal slice score at every lag. -/
def allLagSliceScore (b ell p : ℕ) : ℤ :=
  -1 + ∑ n ∈ allLagDiagonal b ell,
    floorJump (allLagModulus b ell) p n

/-- All-lag integer deviation after the exact slice reduction. -/
def allLagSliceDeviation (b ell p : ℕ) : ℤ :=
  allLagSliceScore b ell p - (((p - 1) / b : ℕ) : ℤ)

/-- Adding a complete all-lag modulus block contributes one copy of `t` per
diagonal slice. -/
theorem allLagSliceScore_add_modulus_mul {b ell t a : ℕ}
    (hb : 0 < b) :
    allLagSliceScore b ell (allLagModulus b ell * t + a) =
      ((allLagDiagonal b ell).card * t : ℕ) +
        allLagSliceScore b ell a := by
  have hM : 0 < allLagModulus b ell := by
    exact pow_pos hb (ell + 1)
  unfold allLagSliceScore
  simp_rw [floorJump_add_modulus_mul hM]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- Coprimality to a positive power of the base forces a nonzero remainder
modulo the base. -/
theorem mod_base_ne_zero_of_coprime_power {a b ell : ℕ}
    (hb2 : 2 ≤ b) (hcop : Nat.Coprime a (allLagModulus b ell)) :
    a % b ≠ 0 := by
  intro hmod
  have hba : b ∣ a := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hbpow : b ∣ allLagModulus b ell := by
    unfold allLagModulus
    exact dvd_pow_self b (by omega)
  have hcopb : Nat.Coprime a b :=
    Nat.Coprime.of_dvd_right hbpow hcop
  have hb1 : b = 1 := Nat.eq_one_of_dvd_coprimes hcopb hba dvd_rfl
  omega

/-- Exact all-lag periodicity of the endpoint-corrected slice deviation. -/
theorem allLagSliceDeviation_eq_table {b ell t a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (ha : 0 < a)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a := by
  have hb : 0 < b := by omega
  have hcard := allLagDiagonal_card hb2 hell
  have hpred :
      (allLagModulus b ell * t + a - 1) / b =
        b ^ ell * t + a / b := by
    have hpow : allLagModulus b ell = b * b ^ ell := by
      unfold allLagModulus
      rw [pow_succ]
      ring
    have hsub :
        allLagModulus b ell * t + a - 1 =
          b * (b ^ ell * t) + (a - 1) := by
      rw [Nat.add_sub_assoc (by omega : 1 ≤ a), hpow]
      congr 1
      ring
    rw [hsub, Nat.mul_add_div hb]
    rw [pred_div_eq_div hb ha
      (mod_base_ne_zero_of_coprime_power hb2 hcop)]
  unfold allLagSliceDeviation allLagTable
  rw [allLagSliceScore_add_modulus_mul hb, hcard, hpred]
  unfold allLagSliceScore
  push_cast
  ring

/-- Direct lag-`ell` collision count in positive residue coordinates. -/
def directAllLagCollisionCount (b ell p : ℕ) : ℕ :=
  ∑ r ∈ Finset.Ico 1 p,
    if digitBin b p r = digitBin b p ((b ^ ell * r) % p) then 1 else 0

/-- Direct all-lag integer deviation. -/
def directAllLagDeviation (b ell p : ℕ) : ℤ :=
  (directAllLagCollisionCount b ell p : ℤ) -
    (((p - 1) / b : ℕ) : ℤ)

/-! ## Exact fiber centering -/

/-- One fiber of a finite reduction map. -/
abbrev Fiber {α β : Type*} (ρ : α → β) (u : β) :=
  {a : α // ρ a = u}

/-- Exact mean of a signal on one reduction fiber. -/
noncomputable def fiberMean {α β K : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (u : β) : K :=
  (Fintype.card (Fiber ρ u) : K)⁻¹ *
    ∑ a : Fiber ρ u, T a

/-- Subtract the mean belonging to the reduction fiber of each coordinate. -/
noncomputable def centeredSignal {α β K : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (a : α) : K :=
  T a - fiberMean ρ T (ρ a)

/-- Every nonempty reduction fiber has centered sum zero exactly. -/
theorem centeredSignal_fiber_sum_zero
    {α β K : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (u : β)
    (hu : Nonempty (Fiber ρ u)) :
    ∑ a : Fiber ρ u, centeredSignal ρ T a = 0 := by
  classical
  have hcard : (Fintype.card (Fiber ρ u) : K) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hu).ne'
  have hpoint (a : Fiber ρ u) :
      centeredSignal ρ T a = T a - fiberMean ρ T u := by
    unfold centeredSignal
    rw [a.property]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  unfold fiberMean
  have hconst (c : K) :
      (∑ _a : Fiber ρ u, c) =
        (Fintype.card (Fiber ρ u) : K) * c := by simp
  have hsumMean :
      (∑ _a : Fiber ρ u,
          (Fintype.card (Fiber ρ u) : K)⁻¹ *
            ∑ a : Fiber ρ u, T a) =
        (Fintype.card (Fiber ρ u) : K) *
          ((Fintype.card (Fiber ρ u) : K)⁻¹ *
            ∑ a : Fiber ρ u, T a) := hconst _
  rw [hsumMean]
  field_simp
  ring

/-- Reflection restricts to an equivalence between complementary fibers. -/
noncomputable def reflectedFiberEquiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ρ : α → β) (rα : α → α) (rβ : β → β)
    (hα : Function.Involutive rα) (hβ : Function.Involutive rβ)
    (hcompat : ∀ a, ρ (rα a) = rβ (ρ a)) (u : β) :
    Fiber ρ u ≃ Fiber ρ (rβ u) :=
  Equiv.subtypeEquiv hα.toPerm fun a => by
    change ρ a = u ↔ ρ (rα a) = rβ u
    constructor
    · intro ha
      calc
        ρ (rα a) = rβ (ρ a) := hcompat a
        _ = rβ u := by rw [ha]
    · intro ha
      calc
        ρ a = rβ (rβ (ρ a)) := (hβ (ρ a)).symm
        _ = rβ (ρ (rα a)) := by rw [hcompat]
        _ = rβ (rβ u) := congrArg rβ ha
        _ = u := hβ u

/-- Averaging a pointwise reflection law over a fiber gives the exact
reflection law for the two fiber means. -/
theorem fiberMean_reflection
    {α β K : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (rα : α → α) (rβ : β → β)
    (hα : Function.Involutive rα) (hβ : Function.Involutive rβ)
    (hcompat : ∀ a, ρ (rα a) = rβ (ρ a))
    (hreflect : ∀ a, T a + T (rα a) = -1)
    (u : β) (hu : Nonempty (Fiber ρ u)) :
    fiberMean ρ T u + fiberMean ρ T (rβ u) = -1 := by
  classical
  let e := reflectedFiberEquiv ρ rα rβ hα hβ hcompat u
  have hcardEq : Fintype.card (Fiber ρ u) =
      Fintype.card (Fiber ρ (rβ u)) := Fintype.card_congr e
  have hsumEq :
      (∑ y : Fiber ρ (rβ u), T y) =
        ∑ x : Fiber ρ u, T (rα x) := by
    symm
    apply Fintype.sum_equiv e
    intro x
    rfl
  have hcard : (Fintype.card (Fiber ρ u) : K) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hu).ne'
  unfold fiberMean
  rw [← hcardEq, hsumEq]
  calc
    (Fintype.card (Fiber ρ u) : K)⁻¹ *
          (∑ x : Fiber ρ u, T x) +
        (Fintype.card (Fiber ρ u) : K)⁻¹ *
          (∑ x : Fiber ρ u, T (rα x)) =
      (Fintype.card (Fiber ρ u) : K)⁻¹ *
        ∑ x : Fiber ρ u, (T x + T (rα x)) := by
          rw [Finset.sum_add_distrib]
          ring
    _ = (Fintype.card (Fiber ρ u) : K)⁻¹ *
        (Fintype.card (Fiber ρ u) : K) * (-1) := by
          simp [hreflect]
    _ = -1 := by field_simp

/-- Fiber-centered reflection is exactly odd. -/
theorem centeredSignal_reflection_odd
    {α β K : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [Field K] [CharZero K]
    (ρ : α → β) (T : α → K) (rα : α → α) (rβ : β → β)
    (hα : Function.Involutive rα) (hβ : Function.Involutive rβ)
    (hcompat : ∀ a, ρ (rα a) = rβ (ρ a))
    (hreflect : ∀ a, T a + T (rα a) = -1)
    (hsurj : Function.Surjective ρ) (a : α) :
    centeredSignal ρ T (rα a) = -centeredSignal ρ T a := by
  have hu : Nonempty (Fiber ρ (ρ a)) := by
    obtain ⟨x, hx⟩ := hsurj (ρ a)
    exact ⟨⟨x, hx⟩⟩
  have hmean := fiberMean_reflection ρ T rα rβ hα hβ
    hcompat hreflect (ρ a) hu
  unfold centeredSignal
  rw [hcompat]
  have hpoint := hreflect a
  linear_combination hpoint - hmean

/-! ## The finite spectral gate -/

/-- Normalized finite coefficient in the manuscript's conjugated convention. -/
noncomputable def finiteCoefficient {α : Type*} [Fintype α]
    (f χ : α → ℂ) : ℂ :=
  (Fintype.card α : ℂ)⁻¹ * ∑ a, f a * star (χ a)

/-- An odd signal has zero coefficient against every reflection-even
channel. -/
theorem finiteCoefficient_eq_zero_of_odd_even
    {α : Type*} [Fintype α]
    (r : α → α) (hr : Function.Involutive r)
    (f χ : α → ℂ) (hf : ∀ a, f (r a) = -f a)
    (hχ : ∀ a, χ (r a) = χ a) :
    finiteCoefficient f χ = 0 := by
  classical
  let e : Equiv.Perm α := hr.toPerm
  let S : ℂ := ∑ a, f a * star (χ a)
  have hreindex :
      (∑ a, f (r a) * star (χ (r a))) = S := by
    simpa [S, e] using Equiv.sum_comp e (fun a => f a * star (χ a))
  have hneg : (∑ a, f (r a) * star (χ (r a))) = -S := by
    simp_rw [hf, hχ]
    simp [S, Finset.sum_neg_distrib]
  have hSneg : S = -S := hreindex.symm.trans hneg
  have hS : S = 0 := by
    linear_combination (1 / 2 : ℂ) * hSneg
  unfold finiteCoefficient
  change (Fintype.card α : ℂ)⁻¹ * S = 0
  rw [hS, mul_zero]

/-- Reflection plus fiber centering kills every reflection-even channel. -/
theorem centeredSignal_even_coefficient_zero
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ρ : α → β) (T : α → ℂ) (rα : α → α) (rβ : β → β)
    (hα : Function.Involutive rα) (hβ : Function.Involutive rβ)
    (hcompat : ∀ a, ρ (rα a) = rβ (ρ a))
    (hreflect : ∀ a, T a + T (rα a) = -1)
    (hsurj : Function.Surjective ρ)
    (χ : α → ℂ) (hχ : ∀ a, χ (rα a) = χ a) :
    finiteCoefficient (centeredSignal ρ T) χ = 0 := by
  apply finiteCoefficient_eq_zero_of_odd_even rα hα
  · exact centeredSignal_reflection_odd ρ T rα rβ hα hβ
      hcompat hreflect hsurj
  · exact hχ

/-- A signal with zero sum on every reduction fiber has zero coefficient
against every channel that factors through the reduction map. -/
theorem finiteCoefficient_eq_zero_of_fiber_zero
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ρ : α → β) (f : α → ℂ)
    (hfiber : ∀ u, ∑ a : Fiber ρ u, f a = 0)
    (ψ : β → ℂ) (χ : α → ℂ) (hfactor : ∀ a, χ a = ψ (ρ a)) :
    finiteCoefficient f χ = 0 := by
  classical
  have hsum : (∑ a, f a * star (χ a)) = 0 := by
    calc
      (∑ a, f a * star (χ a)) =
          ∑ u, ∑ a : Fiber ρ u, f a * star (ψ u) := by
            rw [← Fintype.sum_fiberwise ρ
              (fun a => f a * star (χ a))]
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro a _
            rw [hfactor]
            simp [a.property]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        rw [← Finset.sum_mul]
        simp [hfiber]
  unfold finiteCoefficient
  rw [hsum, mul_zero]

/-- Fiber centering therefore kills every factored channel exactly. -/
theorem centeredSignal_factored_coefficient_zero
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ρ : α → β) (T : α → ℂ) (hsurj : Function.Surjective ρ)
    (ψ : β → ℂ) (χ : α → ℂ) (hfactor : ∀ a, χ a = ψ (ρ a)) :
    finiteCoefficient (centeredSignal ρ T) χ = 0 := by
  refine finiteCoefficient_eq_zero_of_fiber_zero ρ
    (centeredSignal ρ T) ?_ ψ χ hfactor
  · intro u
    apply centeredSignal_fiber_sum_zero
    obtain ⟨a, ha⟩ := hsurj u
    exact ⟨⟨a, ha⟩⟩

/-! ## Executable exact certificates -/

/-- One coarse reduction fiber in the all-lag unit table. -/
def tableFiber (b ell u : ℕ) : Finset ℕ :=
  (reducedResidues (allLagModulus b ell)).filter fun a => a % b = u

/-- Sum of the all-lag table on one coarse fiber. -/
def tableFiberSum (b ell u : ℕ) : ℤ :=
  ∑ a ∈ tableFiber b ell u, allLagTable b ell a

/-- The diagonal cardinality is checked throughout the finite audit range
stated in the manuscript. -/
theorem small_base_lag_diagonal_cardinality :
    ∀ b ∈ Finset.Icc 2 12, ∀ ell ∈ Finset.Icc 1 3,
      (allLagDiagonal b ell).card = b ^ ell := by
  intro b hb ell hell
  exact allLagDiagonal_card (Finset.mem_Icc.mp hb).1
    (Finset.mem_Icc.mp hell).1

/-- The two exact lag-two decimal values showing that reduction modulo one
hundred no longer suffices. -/
theorem decimal_lag_two_distinguishing_values :
    directAllLagDeviation 10 2 1009 = 8 ∧
    directAllLagDeviation 10 2 1109 = -10 ∧
    allLagTable 10 2 (1009 % 1000) = 8 ∧
    allLagTable 10 2 (1109 % 1000) = -10 := by
  set_option maxRecDepth 100000 in
    decide

/-- Exact base-three column totals giving means `-2/3` and `-1/3`. -/
theorem base_three_column_totals :
    (tableFiber 3 1 1).card = 3 ∧ tableFiberSum 3 1 1 = -2 ∧
    (tableFiber 3 1 2).card = 3 ∧ tableFiberSum 3 1 2 = -1 := by
  set_option maxRecDepth 100000 in
    decide

/-- Exact base-ten lag-one column totals inherited by the centered table. -/
theorem decimal_lag_one_column_totals :
    (tableFiber 10 1 1).card = 10 ∧ tableFiberSum 10 1 1 = -17 ∧
    (tableFiber 10 1 3).card = 10 ∧ tableFiberSum 10 1 3 = -9 ∧
    (tableFiber 10 1 7).card = 10 ∧ tableFiberSum 10 1 7 = -1 ∧
    (tableFiber 10 1 9).card = 10 ∧ tableFiberSum 10 1 9 = 7 := by
  set_option maxRecDepth 100000 in
    decide

end NField.Alignment.CenteredCollisionSum
