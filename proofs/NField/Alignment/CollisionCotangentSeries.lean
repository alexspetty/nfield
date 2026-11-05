/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionFiniteSineTransform
import NField.Alignment.CollisionHarmonicSeed

/-!
# Absolutely convergent cotangent sums and gcd descent

The series are defined by the printed terms, excluding multiples of the
modulus. Periodicity gives a finite bound before any infinite rearrangement.
The unit restriction includes conductor one with its explicit zero value.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCotangentSeries

open scoped BigOperators Classical
open CollisionFiniteSineTransform

def cotangentTerm (q n : ℕ) : ℝ :=
  if q ∣ n then 0 else Real.cot (Real.pi*(n : ℝ)/(q : ℝ))/(n : ℝ)^2

def unitCotangentTerm (q n : ℕ) : ℝ :=
  if n.Coprime q then cotangentTerm q n else 0

def cotangentSum (q : ℕ) : ℝ := ∑' n, cotangentTerm q n

def unitCotangentSum (q : ℕ) : ℝ := ∑' n, unitCotangentTerm q n

@[simp] theorem cotangentTerm_zero (q : ℕ) : cotangentTerm q 0=0 := by
  simp [cotangentTerm]

@[simp] theorem cotangentTerm_one (n : ℕ) : cotangentTerm 1 n=0 := by
  simp [cotangentTerm]

@[simp] theorem unitCotangentSum_one : unitCotangentSum 1=0 := by
  simp [unitCotangentSum, unitCotangentTerm]

theorem cotangentTerm_summable {q : ℕ} (hq : 0 < q) : Summable (cotangentTerm q) := by
  let B : ℝ := ∑ a ∈ Finset.range q, ‖Real.cot (Real.pi*(a : ℝ)/(q : ℝ))‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs : Summable (fun n : ℕ => 1/(n : ℝ)^2) := by
    simp only [one_div]
    exact Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))
  apply Summable.of_norm_bounded (hs.mul_left B)
  intro n
  by_cases hn : q ∣ n
  · simp only [cotangentTerm, if_pos hn, norm_zero]
    positivity
  · have hb : ‖Real.cot (Real.pi*(n : ℝ)/(q : ℝ))‖ ≤ B := by
      rw [← cotangent_mod hq n]
      exact Finset.single_le_sum
        (f := fun a : ℕ => ‖Real.cot (Real.pi*(a : ℝ)/(q : ℝ))‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.mod_lt n hq))
    rw [cotangentTerm, if_neg hn, norm_div, norm_pow, Real.norm_natCast]
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 1/(n : ℝ)^2)

theorem unitCotangentTerm_summable {q : ℕ} (hq : 0 < q) :
    Summable (unitCotangentTerm q) := by
  apply ((cotangentTerm_summable hq).indicator {n : ℕ | n.Coprime q}).congr
  intro n
  simp [unitCotangentTerm, Set.indicator_apply]

theorem cotangentSum_positive_series {q : ℕ} (hq : 0 < q) :
    cotangentSum q = ∑' n, cotangentTerm q (n+1) := by
  simpa [cotangentSum] using ((cotangentTerm_summable hq).sum_add_tsum_nat_add 1).symm

theorem cotangentTerm_scale {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (n : ℕ) :
    cotangentTerm (d*q) (d*n)=cotangentTerm q n/(d : ℝ)^2 := by
  unfold cotangentTerm
  simp only [Nat.mul_dvd_mul_iff_left hd]
  split_ifs
  · simp
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have he : Real.pi*((d*n : ℕ) : ℝ)/((d*q : ℕ) : ℝ)=
        Real.pi*(n : ℝ)/(q : ℝ) := by
      push_cast
      field_simp
    rw [he, Nat.cast_mul, mul_pow]
    ring

theorem gcd_fiber_cotangent {q d : ℕ} (hq : 0 < q) (hd : d ∈ q.divisors) :
    (∑' n, if n.gcd q=d then cotangentTerm q n else 0)=
      unitCotangentSum (q/d)/(d : ℝ)^2 := by
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hqd : 0 < q/d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hdpos
  have hi : Function.Injective (fun m : ℕ => d*m) :=
    fun _ _ h => Nat.mul_left_cancel hdpos h
  have ht := hi.tsum_eq (f := fun n => if n.gcd q=d then cotangentTerm q n else 0) (by
    intro n hn
    by_cases hg : n.gcd q=d
    · have hdn : d ∣ n := hg ▸ Nat.gcd_dvd_left n q
      rcases hdn with ⟨m,hm⟩
      exact ⟨m,hm.symm⟩
    · simp [Function.mem_support, hg] at hn)
  rw [← ht, unitCotangentSum, ← tsum_div_const]
  apply tsum_congr
  intro m
  have hg : (d*m).gcd q=d*m.gcd (q/d) := by
    calc
      _ = (d*m).gcd (d*(q/d)) := by rw [Nat.mul_div_cancel' hdvd]
      _ = _ := Nat.gcd_mul_left d m (q/d)
  have hc : (d*m).gcd q=d ↔ m.Coprime (q/d) := by
    rw [hg, Nat.Coprime]
    constructor
    · intro h
      apply Nat.mul_left_cancel hdpos
      simpa only [mul_one] using h
    · intro h
      rw [h, mul_one]
  simp only [hc]
  by_cases hm : m.Coprime (q/d)
  · have hscale := cotangentTerm_scale hdpos hqd m
    rw [Nat.mul_div_cancel' hdvd] at hscale
    simpa only [unitCotangentTerm, if_pos hm] using hscale
  · simp [hm, unitCotangentTerm]

theorem cotangentSum_gcd_descent {q : ℕ} (hq : 0 < q) :
    cotangentSum q=∑ d ∈ q.divisors, unitCotangentSum (q/d)/(d : ℝ)^2 := by
  have hs (d : ℕ) : Summable (fun n => if n.gcd q=d then cotangentTerm q n else 0) := by
    apply ((cotangentTerm_summable hq).indicator {n : ℕ | n.gcd q=d}).congr
    intro n
    simp [Set.indicator_apply]
  have he (n : ℕ) :
      (∑ d ∈ q.divisors, if n.gcd q=d then cotangentTerm q n else 0)=cotangentTerm q n := by
    have hg : n.gcd q ∈ q.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n q,hq.ne'⟩
    rw [Finset.sum_eq_single (n.gcd q)]
    · simp
    · intro d _ hd
      exact if_neg (Ne.symm hd)
    · exact fun hn => (hn hg).elim
  calc
    cotangentSum q = ∑' n, ∑ d ∈ q.divisors,
        if n.gcd q=d then cotangentTerm q n else 0 := by simp_rw [he]; rfl
    _ = ∑ d ∈ q.divisors, ∑' n,
        if n.gcd q=d then cotangentTerm q n else 0 :=
      Summable.tsum_finsetSum (fun d _ => hs d)
    _ = _ := Finset.sum_congr rfl (fun _ hd => gcd_fiber_cotangent hq hd)

theorem cotangent_weighted_divisor_budget {q : ℕ} (hq : 0 < q) :
    (q : ℝ)^2*cotangentSum q=
      ∑ d ∈ q.divisors, (d : ℝ)^2*unitCotangentSum d := by
  rw [cotangentSum_gcd_descent hq, Finset.mul_sum,
    ← Nat.sum_div_divisors q (fun d => (d : ℝ)^2*unitCotangentSum d)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  ring

theorem cotangentSum_divisor_descent {q : ℕ} (hq : 0 < q) :
    cotangentSum q=∑ d ∈ q.divisors, ((d : ℝ)/(q : ℝ))^2*unitCotangentSum d := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_left_cancel₀ (pow_ne_zero 2 hqR)
  rw [cotangent_weighted_divisor_budget hq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  field_simp

theorem unitCotangentSum_moebius {q : ℕ} (hq : 0 < q) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2*
      cotangentSum (q/d))=unitCotangentSum q := by
  have hb := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun n => (n : ℝ)^2*unitCotangentSum n)
    (g := fun n => (n : ℝ)^2*cotangentSum n)).mp
      (fun n hn => (cotangent_weighted_divisor_budget hn).symm) q hq
  rw [Nat.sum_divisorsAntidiagonal (fun a b =>
    (ArithmeticFunction.moebius a : ℝ)*((b : ℝ)^2*cotangentSum b))] at hb
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_left_cancel₀ (pow_ne_zero 2 hqR)
  rw [← hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  ring

theorem literal_cotangent_gcd_descent {q : ℕ} (hq : 0 < q) :
    cotangentSum q=∑ d ∈ q.divisors, ((d : ℝ)/(q : ℝ))^2*unitCotangentSum d ∧
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2*
      cotangentSum (q/d))=unitCotangentSum q ∧
    unitCotangentSum 1=0 ∧ Summable (cotangentTerm q) ∧
      Summable (unitCotangentTerm q) :=
  ⟨cotangentSum_divisor_descent hq, unitCotangentSum_moebius hq,
    unitCotangentSum_one, cotangentTerm_summable hq, unitCotangentTerm_summable hq⟩

end NField.Alignment.CollisionCotangentSeries
