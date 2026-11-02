/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperRoundedCutoff

/-!
# Taylor and remainder products across all partition factors

The Taylor order is the literal rounded natural number in the manuscript.
The exponents keep the complete number of partition factors. The resulting
bounds apply to every monomial with the stated occurrence count, and to
every remainder moment indexed by j at most A.
-/

set_option autoImplicit false

namespace NField.Alignment.HarperTaylorBudget

open Filter
open scoped BigOperators Topology
open NField.Alignment.HarperParameterBounds
open NField.Alignment.HarperRoundedCutoff

noncomputable def taylorArgument (ell : ℝ) : ℝ :=
  (precision ell)^(-2 : ℝ) * Real.log ((rangeCount ell : ℝ)*ell)

noncomputable def taylorOrder (x : ℝ) : ℕ :=
  100 * factorCount x * ⌊taylorArgument (cutoffLog x)⌋₊

theorem taylorArgument_eq {ell : ℝ} (hell : 0 ≤ ell) :
    taylorArgument ell = ell^(13/5 : ℝ) * Real.log ((rangeCount ell : ℝ)*ell) := by
  unfold taylorArgument precision
  rw [← Real.rpow_mul hell]
  norm_num

theorem taylorArgument_ge_one {ell : ℝ} (hell : 0 < ell) (hlog : 1 ≤ Real.log ell) :
    1 ≤ taylorArgument ell := by
  have hr := rangeCount_bounds hell hlog
  have hell1 : 1 ≤ ell := by
    have h := Real.log_le_sub_one_of_pos hell
    linarith
  have hlog' : 1 ≤ Real.log ((rangeCount ell : ℝ)*ell) := by
    apply hlog.trans
    apply Real.log_le_log hell
    nlinarith [mul_le_mul_of_nonneg_right hr.1 hell.le]
  rw [taylorArgument_eq hell.le]
  exact one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hell1 (by norm_num)) hlog'

/-- The natural and integer-floor readings of the displayed Taylor order agree. -/
theorem taylorOrder_spec {x : ℝ} (hell : 0 < cutoffLog x)
    (hlog : 1 ≤ Real.log (cutoffLog x)) :
    (taylorOrder x : ℝ) = 100 * partitionCount (cutoffLog x) *
      (⌊(precision (cutoffLog x))^(-2 : ℝ) *
        Real.log ((rangeCount (cutoffLog x) : ℝ)*cutoffLog x)⌋ : ℤ) := by
  have harg : 0 ≤ taylorArgument (cutoffLog x) :=
    le_trans zero_le_one (taylorArgument_ge_one hell hlog)
  simp only [taylorOrder, Nat.cast_mul, Nat.cast_ofNat, factorCount_eq]
  rw [natCast_floor_eq_intCast_floor harg]
  rfl

theorem taylorOrder_pos {x : ℝ} (hell : 0 < cutoffLog x)
    (hlog : 1 ≤ Real.log (cutoffLog x)) : 0 < taylorOrder x := by
  have hf : 1 ≤ ⌊taylorArgument (cutoffLog x)⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using taylorArgument_ge_one hell hlog)
  have hA : 0 < factorCount x := by unfold factorCount; omega
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hA) (by omega)

/-- The Taylor exponent is bounded by the paper's comparison exponent,
with the factor A included twice as required. -/
theorem taylor_exponent_bound {x : ℝ} (hell : 0 < cutoffLog x)
    (hlog : 1 ≤ Real.log (cutoffLog x)) :
    4*(taylorOrder x : ℝ)*(factorCount x : ℝ) ≤ comparisonExponent (cutoffLog x) := by
  have harg : 0 ≤ taylorArgument (cutoffLog x) :=
    le_trans zero_le_one (taylorArgument_ge_one hell hlog)
  have hf := Nat.floor_le harg
  have hdpow : (precision (cutoffLog x))^(-2 : ℝ) =
      ((precision (cutoffLog x))^2)⁻¹ := by
    rw [Real.rpow_neg (precision_pos hell).le]
    norm_num
  calc
    4*(taylorOrder x : ℝ)*(factorCount x : ℝ) ≤
        4*(100*(factorCount x : ℝ)*taylorArgument (cutoffLog x))*(factorCount x : ℝ) := by
      simp only [taylorOrder, Nat.cast_mul, Nat.cast_ofNat]
      gcongr
    _ = comparisonExponent (cutoffLog x) := by
      rw [factorCount_eq, taylorArgument, hdpow, comparisonExponent, div_pow]
      ring

theorem eventual_taylor_data : ∀ᶠ x : ℝ in atTop,
    0 < x ∧ 1 < primeCutoff x ∧ 0 < taylorOrder x ∧
      4*(taylorOrder x : ℝ)*(factorCount x : ℝ) ≤ comparisonExponent (cutoffLog x) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), cutoffLog_tendsto.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp cutoffLog_tendsto).eventually_ge_atTop 1]
    with x hx hell hlog
  exact ⟨hx, Real.one_lt_exp_iff.mpr hell, taylorOrder_pos hell hlog,
    taylor_exponent_bound hell hlog⟩

/-- The two exponent inequalities after the full Taylor expansion. -/
theorem eventual_taylor_size : ∀ᶠ x : ℝ in atTop,
    x*(primeCutoff x)^((2*factorCount x*(2*taylorOrder x-1) : ℕ) : ℝ) <
      x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
    x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) < x^2 := by
  filter_upwards [eventual_taylor_data, eventual_complete_product_size] with x hx hsize
  have hA : 0 < factorCount x := by unfold factorCount; omega
  have hS : 1 ≤ 2*taylorOrder x := by omega
  have he : ((2*factorCount x*(2*taylorOrder x-1) : ℕ) : ℝ) <
      4*(taylorOrder x : ℝ)*(factorCount x : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hS]
    push_cast
    have hAR : (0 : ℝ) < factorCount x := by exact_mod_cast hA
    nlinarith
  constructor
  · exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_lt hx.2.1 he) hx.1
  · exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.2.1.le hx.2.2.2) hx.1.le).trans_lt hsize

/-- Every remainder order j up to A obeys the same complete-product budget. -/
theorem eventual_remainder_size : ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, j ≤ factorCount x →
    x*((primeCutoff x)^2)^((taylorOrder x*j : ℕ) : ℝ) ≤
      x*(primeCutoff x)^(2*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
    x*(primeCutoff x)^(2*(taylorOrder x : ℝ)*(factorCount x : ℝ)) <
      x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
    x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) < x^2 := by
  filter_upwards [eventual_taylor_data, eventual_taylor_size] with x hx ht
  intro j hj
  have hP : 0 ≤ primeCutoff x := by linarith [hx.2.1]
  have hS : (0 : ℝ) < taylorOrder x := by exact_mod_cast hx.2.2.1
  have hA : (0 : ℝ) < factorCount x := by
    exact_mod_cast (show 0 < factorCount x by unfold factorCount; omega)
  refine ⟨?_, ?_, ht.2⟩
  · rw [← Real.rpow_natCast_mul hP 2]
    apply mul_le_mul_of_nonneg_left _ hx.1.le
    apply Real.rpow_le_rpow_of_exponent_le hx.2.1.le
    push_cast
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr hj : (j : ℝ) ≤ factorCount x)
      (by positivity : 0 ≤ 2*(taylorOrder x : ℝ))
  · apply mul_lt_mul_of_pos_left _ hx.1
    apply Real.rpow_lt_rpow_of_exponent_lt hx.2.1
    nlinarith [mul_pos hS hA]

def completeMonomial {ι : Type*} (n : ℕ) (s : Finset ι) (a : ι → ℕ) : ℕ :=
  n * ∏ i ∈ s, a i

/-- A bound derived from individual occurrences and their total count,
rather than supplied as a bound on the resulting product. -/
theorem completeMonomial_bound {ι : Type*} (n : ℕ) (s : Finset ι) (a : ι → ℕ)
    {x P : ℝ} {N : ℕ} (hx : (n : ℝ) ≤ x) (hP : 1 ≤ P)
    (ha : ∀ i ∈ s, (a i : ℝ) ≤ P^2) (hcount : s.card ≤ N) :
    (completeMonomial n s a : ℝ) ≤ x*P^((2*N : ℕ) : ℝ) := by
  have hpow : 1 ≤ P^2 := one_le_pow₀ hP
  have hprod : (∏ i ∈ s, (a i : ℝ)) ≤ (P^2)^N := by
    calc
      _ ≤ ∏ _i ∈ s, P^2 := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) ha
      _ = (P^2)^s.card := by simp
      _ ≤ _ := pow_le_pow_right₀ hpow hcount
  calc
    (completeMonomial n s a : ℝ) = (n : ℝ)*(∏ i ∈ s, (a i : ℝ)) := by
      simp only [completeMonomial, Nat.cast_mul, Nat.cast_prod]
    _ ≤ x*(P^2)^N := mul_le_mul hx hprod
      (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) ((Nat.cast_nonneg n).trans hx)
    _ = _ := by rw [← pow_mul, Real.rpow_natCast]

/-- Every full Taylor monomial satisfies the written product bound, with
the full factor count A and degree 2S-1 included. -/
theorem eventual_taylor_monomial_size {ι : Type*} : ∀ᶠ x : ℝ in atTop,
    ∀ (n : ℕ) (s : Finset ι) (a : ι → ℕ), (n : ℝ) ≤ x →
      (∀ i ∈ s, (a i : ℝ) ≤ (primeCutoff x)^2) →
      s.card ≤ factorCount x*(2*taylorOrder x-1) →
      (completeMonomial n s a : ℝ) ≤
        x*(primeCutoff x)^((2*factorCount x*(2*taylorOrder x-1) : ℕ) : ℝ) ∧
      x*(primeCutoff x)^((2*factorCount x*(2*taylorOrder x-1) : ℕ) : ℝ) <
        x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
      x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) < x^2 := by
  filter_upwards [eventual_taylor_data, eventual_taylor_size] with x hx ht
  intro n s a hn ha hc
  refine ⟨?_, ht⟩
  simpa only [Nat.mul_assoc] using completeMonomial_bound n s a hn hx.2.1.le ha hc

theorem eventual_remainder_monomial_size {ι : Type*} : ∀ᶠ x : ℝ in atTop,
    ∀ (j n : ℕ) (s : Finset ι) (a : ι → ℕ), j ≤ factorCount x → (n : ℝ) ≤ x →
      (∀ i ∈ s, (a i : ℝ) ≤ (primeCutoff x)^2) → s.card ≤ taylorOrder x*j →
      (completeMonomial n s a : ℝ) ≤ x*((primeCutoff x)^2)^((taylorOrder x*j : ℕ) : ℝ) ∧
      x*((primeCutoff x)^2)^((taylorOrder x*j : ℕ) : ℝ) ≤
        x*(primeCutoff x)^(2*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
      x*(primeCutoff x)^(2*(taylorOrder x : ℝ)*(factorCount x : ℝ)) <
        x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
      x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) < x^2 := by
  filter_upwards [eventual_taylor_data, eventual_remainder_size] with x hx ht
  intro j n s a hj hn ha hc
  refine ⟨?_, ht j hj⟩
  have h := completeMonomial_bound n s a hn hx.2.1.le ha hc
  simpa only [Real.rpow_natCast, pow_mul] using h

theorem eventual_prime_square_remainder_size : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ)-1
    ∀ j : ℕ, j ≤ factorCount x →
      x*((primeCutoff x)^2)^((taylorOrder x*j : ℕ) : ℝ) ≤
        x*(primeCutoff x)^(2*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
      x*(primeCutoff x)^(2*(taylorOrder x : ℝ)*(factorCount x : ℝ)) <
        x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) ∧
      x*(primeCutoff x)^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) < (p : ℝ)^2 := by
  filter_upwards [base_minus_one_tendsto.eventually eventual_remainder_size,
    eventually_ge_atTop (2 : ℕ)] with p hsize hp
  dsimp only
  intro j hj
  have h := hsize j hj
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact ⟨h.1, h.2.1, h.2.2.trans (by nlinarith)⟩

end NField.Alignment.HarperTaylorBudget
