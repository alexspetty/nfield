/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCotangentSeriesEnclosure

/-! All sums in the conclusions are finite. Finitely supported tsums are
used only to reuse the injective reindexing by the gcd of n and q. -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionCotangentFiniteDescent
open scoped BigOperators Classical
open CollisionCotangentSeries CollisionCotangentSeriesEnclosure

def cutoff (f : ℕ → ℝ) (N n : ℕ) : ℝ := if n≤N then f n else 0

theorem cutoff_summable (f : ℕ → ℝ) (N : ℕ) : Summable (cutoff f N) := by
  apply summable_of_ne_finset_zero (s := Finset.range (N+1))
  intro n hn
  simp only [Finset.mem_range] at hn
  simp [cutoff,show ¬n≤N by omega]

theorem cutoff_tsum (f : ℕ → ℝ) (N : ℕ) :
    (∑' n,cutoff f N n)=∑ n∈Finset.range (N+1),f n := by
  rw [tsum_eq_sum (s := Finset.range (N+1)) (fun n hn => by
    simp only [Finset.mem_range] at hn
    simp [cutoff,show ¬n≤N by omega])]
  apply Finset.sum_congr rfl
  intro n hn
  simp [cutoff,show n≤N from Nat.le_of_lt_succ (Finset.mem_range.mp hn)]

theorem cutoff_cotangent_scale {d q : ℕ} (hd : 0<d) (hq : 0<q) (N n : ℕ) :
    cutoff (cotangentTerm (d*q)) N (d*n)=
      cutoff (cotangentTerm q) (N/d) n/(d : ℝ)^2 := by
  have he : d*n≤N ↔ n≤N/d := by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).symm
  simp only [cutoff,he]
  split_ifs
  · exact cotangentTerm_scale hd hq n
  · simp

theorem finite_gcd_fiber {q d : ℕ} (hq : 0<q) (hd : d∈q.divisors) (N : ℕ) :
    (∑' n,if n.gcd q=d then cutoff (cotangentTerm q) N n else 0)=
      unitCotangentPrefix (q/d) (N/d)/(d : ℝ)^2 := by
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hqd : 0<q/d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hdpos
  have hi : Function.Injective (fun m : ℕ => d*m) := fun _ _ h => Nat.mul_left_cancel hdpos h
  have ht := hi.tsum_eq (f := fun n => if n.gcd q=d then cutoff (cotangentTerm q) N n else 0) (by
    intro n hn
    by_cases hg : n.gcd q=d
    · have hdn : d∣n := hg ▸ Nat.gcd_dvd_left n q
      rcases hdn with ⟨m,hm⟩
      exact ⟨m,hm.symm⟩
    · simp [Function.mem_support,hg] at hn)
  rw [← ht]
  have hs (m : ℕ) : (if (d*m).gcd q=d then cutoff (cotangentTerm q) N (d*m) else 0)=
      cutoff (unitCotangentTerm (q/d)) (N/d) m/(d : ℝ)^2 := by
    have hg : (d*m).gcd q=d*m.gcd (q/d) := by
      calc
        _ = (d*m).gcd (d*(q/d)) := by rw [Nat.mul_div_cancel' hdvd]
        _ = _ := Nat.gcd_mul_left d m (q/d)
    have hc : (d*m).gcd q=d ↔ m.Coprime (q/d) := by
      rw [hg,Nat.Coprime]
      constructor
      · intro h
        apply Nat.mul_left_cancel hdpos
        simpa only [mul_one] using h
      · intro h
        rw [h,mul_one]
    simp only [hc]
    by_cases hm : m.Coprime (q/d)
    · rw [if_pos hm]
      have ht := cutoff_cotangent_scale hdpos hqd N m
      rw [Nat.mul_div_cancel' hdvd] at ht
      simpa only [cutoff,unitCotangentTerm,if_pos hm] using ht
    · simp [hm,cutoff,unitCotangentTerm]
  simp_rw [hs]
  rw [tsum_div_const,cutoff_tsum]
  rfl

theorem finite_cotangent_gcd_descent {q : ℕ} (hq : 0<q) (N : ℕ) :
    cotangentPrefix q N=
      ∑ d∈q.divisors,unitCotangentPrefix (q/d) (N/d)/(d : ℝ)^2 := by
  have hs (d : ℕ) : Summable (fun n => if n.gcd q=d then cutoff (cotangentTerm q) N n else 0) := by
    apply ((cutoff_summable (cotangentTerm q) N).indicator {n : ℕ | n.gcd q=d}).congr
    intro n
    simp [Set.indicator_apply]
  have he (n : ℕ) : (∑ d∈q.divisors,if n.gcd q=d then cutoff (cotangentTerm q) N n else 0)=
      cutoff (cotangentTerm q) N n := by
    have hg : n.gcd q∈q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n q,hq.ne'⟩
    rw [Finset.sum_eq_single (n.gcd q)]
    · simp
    · intro d _ hd
      exact if_neg (Ne.symm hd)
    · exact fun hn => (hn hg).elim
  rw [cotangentPrefix,← cutoff_tsum]
  calc
    _ = ∑' n,∑ d∈q.divisors,if n.gcd q=d then cutoff (cotangentTerm q) N n else 0 := by simp_rw [he]
    _ = ∑ d∈q.divisors,∑' n,if n.gcd q=d then cutoff (cotangentTerm q) N n else 0 :=
      Summable.tsum_finsetSum (fun d _ => hs d)
    _ = _ := Finset.sum_congr rfl (fun d hd => finite_gcd_fiber hq hd N)

theorem finite_cotangent_divisor_descent {q : ℕ} (hq : 0<q) (N : ℕ) :
    cotangentPrefix q N=
      ∑ d∈q.divisors,((d : ℝ)/(q : ℝ))^2*unitCotangentPrefix d (N*d/q) := by
  rw [finite_cotangent_gcd_descent hq,
    ← Nat.sum_div_divisors q (fun d => ((d : ℝ)/(q : ℝ))^2*unitCotangentPrefix d (N*d/q))]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hqd : 0<q/d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hdpos
  have he : N*(q/d)/q=N/d := by
    have hqeq : q=d*(q/d) := (Nat.mul_div_cancel' hdvd).symm
    calc
      _ = N*(q/d)/(d*(q/d)) := by nth_rw 2 [hqeq]
      _ = N/d := Nat.mul_div_mul_right N d hqd
  rw [he,Nat.cast_div hdvd (Nat.cast_ne_zero.mpr hdpos.ne')]
  field_simp

theorem cutoff_divisor_comm (N Q : ℕ) {n d : ℕ} (hd : d∣n) :
    (N*n/Q)/d=N*(n/d)/Q := by
  rw [Nat.div_div_eq_div_mul,Nat.mul_comm Q d,← Nat.div_div_eq_div_mul,Nat.mul_div_assoc N hd]

theorem finite_weighted_budget (Q N : ℕ) {n : ℕ} (hn : 0<n) :
    (n : ℝ)^2*cotangentPrefix n (N*n/Q)=
      ∑ d∈n.divisors,(d : ℝ)^2*unitCotangentPrefix d (N*d/Q) := by
  rw [finite_cotangent_gcd_descent hn,Finset.mul_sum,
    ← Nat.sum_div_divisors n (fun d => (d : ℝ)^2*unitCotangentPrefix d (N*d/Q))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [cutoff_divisor_comm N Q (Nat.dvd_of_mem_divisors hd),
    Nat.cast_div (Nat.dvd_of_mem_divisors hd) (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]
  ring

theorem finite_unit_cotangent_moebius {q : ℕ} (hq : 0<q) (N : ℕ) :
    (∑ d∈q.divisors,(ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2*
      cotangentPrefix (q/d) (N/d))=unitCotangentPrefix q N := by
  have hb := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun n => (n : ℝ)^2*unitCotangentPrefix n (N*n/q))
    (g := fun n => (n : ℝ)^2*cotangentPrefix n (N*n/q))).mp
      (fun n hn => (finite_weighted_budget q N hn).symm) q hq
  rw [Nat.sum_divisorsAntidiagonal (fun a b =>
    (ArithmeticFunction.moebius a : ℝ)*((b : ℝ)^2*cotangentPrefix b (N*b/q)))] at hb
  simp only [Nat.mul_div_cancel N hq] at hb
  have hqR : (q : ℝ)≠0 := Nat.cast_ne_zero.mpr hq.ne'
  apply mul_left_cancel₀ (pow_ne_zero 2 hqR)
  rw [Finset.mul_sum,← hb]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have he : N*(q/d)/q=N/d := by
    rw [← cutoff_divisor_comm N q hdvd,Nat.mul_div_cancel N hq]
  rw [he,Nat.cast_div hdvd (Nat.cast_ne_zero.mpr hdpos.ne')]
  field_simp

end NField.Alignment.CollisionCotangentFiniteDescent
