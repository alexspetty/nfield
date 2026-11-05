/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralMean
import NField.Alignment.CollisionSpectralPrimeMoments

/-!
# Initial-interval bounds for the logarithmic conductor correction

Exact divisibility counts control both moments. Coincident primes retain
their separate diagonal contribution in the second moment.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralNuBounds

open scoped BigOperators Classical ArithmeticFunction.zeta
open Filter ArithmeticFunction
open CollisionConductorArithmetic CollisionSpectralMean CollisionSpectralPrimeMoments

def primeProfile : ArithmeticFunction ℝ where
  toFun p := if p.Prime then primeLogWeight p else 0
  map_zero' := by simp [primeLogWeight]

theorem primeProfile_apply (p : ℕ) :
    primeProfile p=(if p.Prime then primeLogWeight p else 0) := rfl

theorem primeProfile_nonneg (p : ℕ) : 0 ≤ primeProfile p := by
  rw [primeProfile_apply]
  split_ifs
  · exact primeLogWeight_nonneg p
  · rfl

theorem nu_divisor_sum (n : ℕ) : nu n=∑ p ∈ n.divisors, primeProfile p := by
  have he : n.divisors.filter Nat.Prime=n.primeFactors := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_divisors,Nat.mem_primeFactors]
    tauto
  rw [nu,← he,Finset.sum_filter]
  rfl

theorem nu_nonneg (n : ℕ) : 0 ≤ nu n := by
  rw [nu_divisor_sum]
  exact Finset.sum_nonneg (fun p _ => primeProfile_nonneg p)

theorem nu_convolution (n : ℕ) : (primeProfile*(ζ : ArithmeticFunction ℝ)) n=nu n := by
  rw [coe_mul_zeta_apply,nu_divisor_sum]

theorem nu_first_count (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, nu n)=
      ∑ p ∈ Finset.Ioc 0 N, primeProfile p*((N/p : ℕ) : ℝ) := by
  have h := sum_Ioc_mul_zeta_eq_sum primeProfile N
  simpa only [nu_convolution] using h

theorem nat_div_cast_bound (N : ℕ) {d : ℕ} (hd : 0 < d) :
    ((N/d : ℕ) : ℝ) ≤ (N : ℝ)/(d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).mpr
  exact_mod_cast Nat.div_mul_le_self N d

theorem nu_first_bound (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, nu n) ≤ (N : ℝ)*firstPrimeMoment := by
  rw [nu_first_count]
  calc
    _ ≤ ∑ p ∈ Finset.Ioc 0 N, (N : ℝ)*firstPrimeTerm p := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hprime : p.Prime
      · rw [primeProfile_apply,if_pos hprime,firstPrimeTerm,if_pos hprime]
        have h := mul_le_mul_of_nonneg_left (nat_div_cast_bound N hprime.pos)
          (primeLogWeight_nonneg p)
        convert! h using 1
        ring
      · simp [primeProfile_apply,firstPrimeTerm,hprime]
    _ = (N : ℝ)*∑ p ∈ Finset.Ioc 0 N, firstPrimeTerm p := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (firstPrimeTerm_summable.sum_le_tsum _ (fun n _ => firstPrimeTerm_nonneg n))
      (Nat.cast_nonneg N)

theorem nu_cutoff_expansion {n N : ℕ} (hn : n∈Finset.Ioc 0 N) :
    nu n=∑ p ∈ Finset.Ioc 0 N, if p∣n then primeProfile p else 0 := by
  have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
  have he : (Finset.Ioc 0 N).filter (fun p => p∣n)=n.divisors := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Ioc,Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2,hn0.ne'⟩
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hn0,
        (Nat.le_of_dvd hn0 h.1).trans (Finset.mem_Ioc.mp hn).2⟩,h.1⟩
  rw [nu_divisor_sum,← he,Finset.sum_filter]

theorem interval_divisor_count (N d : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, if d∣n then (1 : ℝ) else 0)=((N/d : ℕ) : ℝ) := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Nat.Ioc_filter_dvd_card_eq_div]

theorem divisor_product_trace (p r n : ℕ) :
    (if p∣n then primeProfile p else 0)*(if r∣n then primeProfile r else 0)=
      primeProfile p*primeProfile r*(if p.lcm r∣n then (1 : ℝ) else 0) := by
  by_cases hp : p∣n <;> by_cases hr : r∣n <;> simp [hp,hr,Nat.lcm_dvd_iff]

theorem nu_second_count (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (nu n)^2)=
      ∑ p ∈ Finset.Ioc 0 N, ∑ r ∈ Finset.Ioc 0 N,
        primeProfile p*primeProfile r*((N/(p.lcm r) : ℕ) : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N, ∑ p ∈ Finset.Ioc 0 N, ∑ r ∈ Finset.Ioc 0 N,
        (if p∣n then primeProfile p else 0)*(if r∣n then primeProfile r else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [nu_cutoff_expansion hn,pow_two,Finset.sum_mul_sum]
    _ = ∑ p ∈ Finset.Ioc 0 N, ∑ r ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Ioc 0 N,
        (if p∣n then primeProfile p else 0)*(if r∣n then primeProfile r else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      simp only [divisor_product_trace,← Finset.mul_sum,interval_divisor_count]

theorem prime_pair_count_bound (N : ℕ) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) :
    primeLogWeight p*primeLogWeight r*((N/(p.lcm r) : ℕ) : ℝ) ≤
      (N : ℝ)*(primeLogWeight p/(p : ℝ)*(primeLogWeight r/(r : ℝ))+
        if p=r then (primeLogWeight p)^2/(p : ℝ) else 0) := by
  by_cases hpr : p=r
  · subst r
    rw [Nat.lcm_self,if_pos rfl]
    have h := mul_le_mul_of_nonneg_left (nat_div_cast_bound N hp.pos)
      (mul_nonneg (primeLogWeight_nonneg p) (primeLogWeight_nonneg p))
    calc
      _ ≤ (N : ℝ)*((primeLogWeight p)^2/(p : ℝ)) := by
        convert! h using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith [mul_self_nonneg (primeLogWeight p/(p : ℝ))]) (Nat.cast_nonneg N)
  · rw [((Nat.coprime_primes hp hr).mpr hpr).lcm_eq_mul,if_neg hpr,add_zero]
    have h := mul_le_mul_of_nonneg_left (nat_div_cast_bound N (Nat.mul_pos hp.pos hr.pos))
      (mul_nonneg (primeLogWeight_nonneg p) (primeLogWeight_nonneg r))
    convert! h using 1
    simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
    ring

theorem profile_pair_count_bound (N p r : ℕ) :
    primeProfile p*primeProfile r*((N/(p.lcm r) : ℕ) : ℝ) ≤
      (N : ℝ)*(firstPrimeTerm p*firstPrimeTerm r+if p=r then secondPrimeTerm p else 0) := by
  by_cases hp : p.Prime
  · by_cases hr : r.Prime
    · simpa only [primeProfile_apply,firstPrimeTerm,secondPrimeTerm,if_pos hp,if_pos hr] using
        prime_pair_count_bound N hp hr
    · have hpr : p≠r := fun h => hr (h ▸ hp)
      simp [primeProfile_apply,firstPrimeTerm,hr,hpr]
  · simp [primeProfile_apply,firstPrimeTerm,secondPrimeTerm,hp]

theorem nu_second_bound (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (nu n)^2) ≤
      (N : ℝ)*(firstPrimeMoment^2+secondPrimeMoment) := by
  rw [nu_second_count]
  calc
    _ ≤ ∑ p ∈ Finset.Ioc 0 N, ∑ r ∈ Finset.Ioc 0 N,
        (N : ℝ)*(firstPrimeTerm p*firstPrimeTerm r+if p=r then secondPrimeTerm p else 0) := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.sum_le_sum (fun r _ => profile_pair_count_bound N p r)
    _ = ∑ p ∈ Finset.Ioc 0 N, (N : ℝ)*
        (firstPrimeTerm p*(∑ r ∈ Finset.Ioc 0 N, firstPrimeTerm r)+secondPrimeTerm p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
      simp [hp]
    _ = (N : ℝ)*((∑ p ∈ Finset.Ioc 0 N, firstPrimeTerm p)^2+
        ∑ p ∈ Finset.Ioc 0 N, secondPrimeTerm p) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_mul,pow_two]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply add_le_add
      · exact pow_le_pow_left₀
          (Finset.sum_nonneg (fun n _ => firstPrimeTerm_nonneg n))
          (firstPrimeTerm_summable.sum_le_tsum _ (fun n _ => firstPrimeTerm_nonneg n)) 2
      · exact secondPrimeTerm_summable.sum_le_tsum _ (fun n _ => secondPrimeTerm_nonneg n)

theorem nu_first_isBigO :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, nu n) (fun x => x) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨firstPrimeMoment,?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun n _ => nu_nonneg n)),Real.norm_of_nonneg hx]
  calc
    _ ≤ (⌊x⌋₊ : ℝ)*firstPrimeMoment := nu_first_bound _
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hx) firstPrimeMoment_nonneg

theorem nu_second_isBigO :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (nu n)^2) (fun x => x) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨firstPrimeMoment^2+secondPrimeMoment,?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun n _ => sq_nonneg (nu n))),Real.norm_of_nonneg hx]
  calc
    _ ≤ (⌊x⌋₊ : ℝ)*(firstPrimeMoment^2+secondPrimeMoment) := nu_second_bound _
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hx)
        (add_nonneg (sq_nonneg firstPrimeMoment) secondPrimeMoment_nonneg)

theorem logarithmic_conductor_moment_bounds :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, nu n) (fun x => x) ∧
    Asymptotics.IsBigO atTop
      (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (nu n)^2) (fun x => x) :=
  ⟨nu_first_isBigO,nu_second_isBigO⟩

end NField.Alignment.CollisionSpectralNuBounds
