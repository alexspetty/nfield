/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMobiusDeficit
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Absolute Dirichlet series for the Mobius divisor deficit

All series below are actual real series. Euler products are used only after
absolute summability has been proved, and convolution is justified by
fiberwise summation of an absolutely convergent product series.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDivisorSeries

open scoped BigOperators Classical
open ArithmeticFunction CollisionSquarefreeEuler CollisionMobiusDeficit

def zetaKernel (s : ℝ) : ArithmeticFunction ℝ := realPower (-s)
def realZeta (s : ℝ) : ℝ := ∑' n, zetaKernel s n
def squarefreeKernel (s : ℝ) : ArithmeticFunction ℝ := absMoebius.pmul (zetaKernel s)
def squarefreeSeries (s : ℝ) : ℝ := ∑' n, squarefreeKernel s n

theorem zetaKernel_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaKernel s n := by
  unfold zetaKernel realPower
  change 0 ≤ if n=0 then (0 : ℝ) else (n : ℝ)^(-s)
  split_ifs <;> positivity

theorem zetaKernel_summable {s : ℝ} (hs : 1 < s) : Summable (zetaKernel s) := by
  apply (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).congr
  intro n
  by_cases hn : n=0
  · simp [hn,zetaKernel,realPower,Real.zero_rpow (by linarith : -s≠0)]
  · simp [zetaKernel,realPower,hn]

theorem zetaKernel_multiplicative (s : ℝ) : (zetaKernel s).IsMultiplicative :=
  realPower_multiplicative (-s)

theorem squarefreeKernel_multiplicative (s : ℝ) : (squarefreeKernel s).IsMultiplicative :=
  absMoebius_multiplicative.pmul (zetaKernel_multiplicative s)

theorem squarefreeKernel_bounds (s : ℝ) (n : ℕ) :
    0 ≤ squarefreeKernel s n ∧ squarefreeKernel s n ≤ zetaKernel s n := by
  change 0 ≤ |(moebius n : ℝ)| *zetaKernel s n ∧
    |(moebius n : ℝ)| *zetaKernel s n ≤ zetaKernel s n
  refine ⟨mul_nonneg (abs_nonneg _) (zetaKernel_nonneg s n),?_⟩
  have hm : |(moebius n : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := n))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (zetaKernel_nonneg s n)

theorem squarefreeKernel_summable {s : ℝ} (hs : 1 < s) : Summable (squarefreeKernel s) :=
  Summable.of_nonneg_of_le (fun n => (squarefreeKernel_bounds s n).1)
    (fun n => (squarefreeKernel_bounds s n).2) (zetaKernel_summable hs)

theorem realZeta_pos {s : ℝ} (hs : 1 < s) : 0 < realZeta s := by
  have h := (zetaKernel_summable hs).le_tsum 1 (fun n _ => zetaKernel_nonneg s n)
  have hone : zetaKernel s 1=1 := by simp [zetaKernel,realPower]
  rw [hone] at h
  exact lt_of_lt_of_le (by norm_num) h

theorem zetaKernel_prime_power (s : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    zetaKernel s (p^k)=((p : ℝ)^(-s))^k := by
  rw [zetaKernel,realPower_apply _ (pow_ne_zero _ hp.ne_zero),Nat.cast_pow]
  exact (Real.rpow_pow_comm (Nat.cast_nonneg p) (-s) k).symm

theorem zetaKernel_local_sum {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, zetaKernel s (p^k))=(1-(p : ℝ)^(-s))⁻¹ := by
  simp_rw [zetaKernel_prime_power s hp]
  apply tsum_geometric_of_lt_one (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem squarefreeKernel_local_sum (s : ℝ) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, squarefreeKernel s (p^k))=1+(p : ℝ)^(-s) := by
  have hz (k : ℕ) (hk : k∉Finset.range 2) : squarefreeKernel s (p^k)=0 := by
    have hk0 : k≠0 := by simp only [Finset.mem_range,not_lt] at hk; omega
    have hk1 : k≠1 := by simp only [Finset.mem_range,not_lt] at hk; omega
    simp [squarefreeKernel,absMoebius,moebius_apply_prime_pow hp hk0,hk1]
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ,squarefreeKernel,absMoebius,zetaKernel,realPower,
    moebius_apply_prime hp,hp.ne_zero]

theorem realZeta_hasProd {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => (1-(p.val : ℝ)^(-s))⁻¹) (realZeta s) := by
  have h := (zetaKernel_multiplicative s).eulerProduct_hasProd (zetaKernel_summable hs).norm
  convert! h using 1
  funext p
  exact (zetaKernel_local_sum hs p.property).symm

theorem squarefreeSeries_hasProd {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => 1+(p.val : ℝ)^(-s)) (squarefreeSeries s) := by
  have h := (squarefreeKernel_multiplicative s).eulerProduct_hasProd
    (squarefreeKernel_summable hs).norm
  convert! h using 1
  funext p
  exact (squarefreeKernel_local_sum s p.property).symm

theorem squarefreeSeries_zeta {s : ℝ} (hs : 1 < s) :
    squarefreeSeries s=realZeta s/realZeta (2*s) := by
  have h2 : 1 < 2*s := by linarith
  apply (eq_div_iff (realZeta_pos h2).ne').mpr
  have h := (squarefreeSeries_hasProd hs).mul (realZeta_hasProd h2)
  have he : (fun p : Nat.Primes =>
      (1+(p.val : ℝ)^(-s))*(1-(p.val : ℝ)^(-(2*s)))⁻¹)=
      (fun p : Nat.Primes => (1-(p.val : ℝ)^(-s))⁻¹) := by
    funext p
    have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
    have hr0 := Real.rpow_nonneg (Nat.cast_nonneg p.val) (-s)
    have hr1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith : -s < 0)
    have he2 : (p.val : ℝ)^(-(2*s))=(p.val : ℝ)^(-s)*(p.val : ℝ)^(-s) := by
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < p.val)]
      congr 1
      ring
    have hden : 1-(p.val : ℝ)^(-s)≠0 := by linarith
    have hden2 : 1-(p.val : ℝ)^(-s)*(p.val : ℝ)^(-s)≠0 := by nlinarith
    have hden2' : 1-((p.val : ℝ)^(-s))^2≠0 := by simpa only [pow_two] using hden2
    rw [he2]
    field_simp [hden,hden2']
    ring
  rw [he] at h
  exact h.unique (realZeta_hasProd hs)

theorem arithmetic_convolution_fiber (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (f*g) n=∑' b : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}, f b.val.1*g b.val.2 := by
  by_cases hn : n=0
  · subst n
    rw [ArithmeticFunction.map_zero]
    have hz : ∀ b : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {(0 : ℕ)},
        f b.val.1*g b.val.2=0 := by
      rintro ⟨⟨a,b⟩,hab⟩
      have hab0 : a*b=0 := hab
      rcases Nat.mul_eq_zero.mp hab0 with ha|hb
      · simp [ha]
      · simp [hb]
    simp only [hz,tsum_zero]
  have he : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}=(n.divisorsAntidiagonal : Set (ℕ×ℕ)) := by
    ext p
    simp [hn]
  rw [he,Finset.tsum_subtype' n.divisorsAntidiagonal (fun p => f p.1*g p.2)]
  rfl

theorem arithmetic_convolution_hasSum (f g : ArithmeticFunction ℝ)
    (hf : Summable f) (hg : Summable g) :
    HasSum (fun n => (f*g) n) ((∑' n, f n)*(∑' n, g n)) := by
  have hsum := summable_mul_of_summable_norm hf.norm hg.norm
  have h := (hf.hasSum.mul hg.hasSum hsum).tsum_fiberwise (fun p : ℕ×ℕ => p.1*p.2)
  convert! h using 1
  funext n
  exact arithmetic_convolution_fiber f g n

theorem zetaKernel_mul (s : ℝ) (a b : ℕ) :
    zetaKernel s (a*b)=zetaKernel s a*zetaKernel s b := by
  by_cases ha : a=0
  · simp [ha]
  by_cases hb : b=0
  · simp [hb]
  simp only [zetaKernel,realPower_apply _ (mul_ne_zero ha hb),realPower_apply _ ha,
    realPower_apply _ hb,Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

theorem squarefree_convolution (s : ℝ) (n : ℕ) :
    (squarefreeKernel s*zetaKernel s) n=
      (∑ d ∈ n.divisors, |(moebius d : ℝ)|) *zetaKernel s n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => squarefreeKernel s a*zetaKernel s b),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  change (|(moebius d : ℝ)| *zetaKernel s d)*zetaKernel s (n/d)=_
  rw [mul_assoc,← zetaKernel_mul,Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

theorem squarefreeDivisor_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => (2 : ℝ)^n.primeFactors.card*zetaKernel s n)
      (realZeta s^2/realZeta (2*s)) := by
  have h := arithmetic_convolution_hasSum (squarefreeKernel s) (zetaKernel s)
    (squarefreeKernel_summable hs) (zetaKernel_summable hs)
  have he (n : ℕ) : (squarefreeKernel s*zetaKernel s) n=
      (2 : ℝ)^n.primeFactors.card*zetaKernel s n := by
    by_cases hn : n=0
    · simp [hn]
    rw [squarefree_convolution,absoluteMobius_divisor_count (by omega)]
  simp_rw [he] at h
  change HasSum _ (squarefreeSeries s*realZeta s) at h
  rw [squarefreeSeries_zeta hs] at h
  convert! h using 1
  ring

def deficitSeries (s : ℝ) : ℝ := ∑' n, divisorDeficit n*zetaKernel s n

theorem deficitKernel_identity (s : ℝ) (n : ℕ) :
    divisorDeficit n*zetaKernel s n=
      (1/2 : ℝ)*((2 : ℝ)^n.primeFactors.card*zetaKernel s n)-zetaKernel s n+
        (if n=1 then (1/2 : ℝ) else 0) := by
  by_cases hn0 : n=0
  · simp [hn0]
  by_cases hn1 : n=1
  · norm_num [hn1,divisorDeficit,zetaKernel,realPower]
  simp only [divisorDeficit,if_pos (by omega : 2 ≤ n),if_neg hn1]
  ring

theorem deficitSeries_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun n => divisorDeficit n*zetaKernel s n)
      (realZeta s^2/(2*realZeta (2*s))-realZeta s+1/2) := by
  have h := (((squarefreeDivisor_hasSum hs).mul_left (1/2 : ℝ)).sub
    (zetaKernel_summable hs).hasSum).add (hasSum_ite_eq (1 : ℕ) (1/2 : ℝ))
  simp_rw [← deficitKernel_identity] at h
  change HasSum _ ((1/2 : ℝ)*(realZeta s^2/realZeta (2*s))-realZeta s+1/2) at h
  convert! h using 1
  ring

theorem deficitSeries_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n => divisorDeficit n*zetaKernel s n) :=
  (deficitSeries_hasSum hs).summable

theorem deficitSeries_formula {s : ℝ} (hs : 1 < s) :
    deficitSeries s=realZeta s^2/(2*realZeta (2*s))-realZeta s+1/2 :=
  (deficitSeries_hasSum hs).tsum_eq

theorem deficitSeries_nonneg (s : ℝ) : 0 ≤ deficitSeries s :=
  tsum_nonneg (fun n => mul_nonneg (divisorDeficit_nonneg n) (zetaKernel_nonneg s n))

theorem zetaKernel_rpow {s : ℝ} (hs : s≠0) (n : ℕ) :
    zetaKernel s n=(n : ℝ)^(-s) := by
  by_cases hn : n=0
  · simp [hn,zetaKernel,realPower,Real.zero_rpow (neg_ne_zero.mpr hs)]
  · exact realPower_apply (-s) hn

theorem realZeta_eq_riemannZeta {s : ℝ} (hs : 1 < s) :
    (realZeta s : ℂ)=riemannZeta (s : ℂ) := by
  rw [realZeta,Complex.ofReal_tsum,
    zeta_eq_tsum_one_div_nat_cpow (by simpa only [Complex.ofReal_re] using hs)]
  apply tsum_congr
  intro n
  rw [zetaKernel_rpow (by linarith : s≠0),Real.rpow_neg (Nat.cast_nonneg n),
    Complex.ofReal_inv,Complex.ofReal_cpow (Nat.cast_nonneg n),one_div]
  norm_cast

end NField.Alignment.CollisionDivisorSeries
