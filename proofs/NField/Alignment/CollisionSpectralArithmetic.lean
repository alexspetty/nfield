/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionUniformAmplitude
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The arithmetic weight in the Haar spectral tail

The weight is defined from the actual Jordan factor and conductor factor.
Its prime product and squarefree divisor correction are derived below.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralArithmetic

open scoped BigOperators Classical ArithmeticFunction.zeta
open ArithmeticFunction
open CollisionJordanVariance CollisionConductorArithmetic CollisionSquarefreeEuler

def spectralWeight (n : ℕ) : ℝ := jordanTwo n*(rho n)^2/(n : ℝ)^2

def localFactor (p : ℕ) : ℝ :=
  (1-((p : ℝ)^2)⁻¹)*((p : ℝ)^2/((p : ℝ)^2+p+1))^2

def spectralArithmetic : ArithmeticFunction ℝ := prodPrimeFactors localFactor

theorem spectralWeight_euler_product {n : ℕ} (hn : n≠0) :
    spectralWeight n=∏ p ∈ n.primeFactors, localFactor p := by
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn
  rw [spectralWeight,jordanTwo_euler_product hn,rho_euler_product hn]
  calc
    _ = (∏ p ∈ n.primeFactors, (1-((p : ℝ)^2)⁻¹))*
      (∏ p ∈ n.primeFactors, ((p : ℝ)^2/((p : ℝ)^2+p+1)))^2 := by field_simp
    _ = _ := by simp only [localFactor,Finset.prod_mul_distrib,Finset.prod_pow]

theorem spectralArithmetic_apply (n : ℕ) : spectralArithmetic n=spectralWeight n := by
  by_cases hn : n=0
  · simp [hn,spectralArithmetic,spectralWeight]
  · rw [spectralArithmetic,prodPrimeFactors_apply hn,spectralWeight_euler_product hn]

theorem spectralArithmetic_multiplicative : spectralArithmetic.IsMultiplicative :=
  IsMultiplicative.prodPrimeFactors _

theorem localFactor_formula {p : ℕ} (hp : 0<p) :
    localFactor p=(p : ℝ)^2*((p : ℝ)^2-1)/((p : ℝ)^2+p+1)^2 := by
  have hpR : (p : ℝ)≠0 := by exact_mod_cast hp.ne'
  unfold localFactor
  field_simp

theorem localFactor_pos {p : ℕ} (hp : p.Prime) : 0<localFactor p := by
  have hpR : (1 : ℝ)<p := by exact_mod_cast hp.one_lt
  rw [localFactor_formula hp.pos]
  have h : 0<(p : ℝ)^2-1 := by nlinarith
  positivity

theorem localFactor_le_one {p : ℕ} (hp : p.Prime) : localFactor p≤1 := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hD : 0<((p : ℝ)^2+p+1)^2 := by positivity
  rw [localFactor_formula hp.pos,div_le_iff₀ hD]
  nlinarith [sq_nonneg (p : ℝ),pow_nonneg hpR.le 3]

theorem localFactor_defect_bound {p : ℕ} (hp : p.Prime) :
    1-localFactor p≤2/(p : ℝ) := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hD : 0<((p : ℝ)^2+p+1)^2 := by positivity
  apply (le_div_iff₀ hpR).mpr
  apply (mul_le_mul_iff_left₀ hD).mp
  have he : ((1-localFactor p)*(p : ℝ))*((p : ℝ)^2+p+1)^2=
      2*((p : ℝ)^2+p+1)^2-(4*(p : ℝ)^2+3*p+2) := by
    rw [localFactor_formula hp.pos]
    field_simp
    ring
  rw [he]
  nlinarith [sq_nonneg (p : ℝ)]

theorem localFactor_abs_defect {p : ℕ} (hp : p.Prime) :
    |localFactor p-1|≤2/(p : ℝ) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (localFactor_le_one hp))]
  simpa only [neg_sub] using localFactor_defect_bound hp

theorem spectralWeight_pos {n : ℕ} (hn : 0<n) : 0<spectralWeight n := by
  rw [spectralWeight_euler_product hn.ne']
  exact Finset.prod_pos (fun _ hp => localFactor_pos (Nat.prime_of_mem_primeFactors hp))

theorem spectralWeight_le_one {n : ℕ} (hn : 0<n) : spectralWeight n≤1 := by
  rw [spectralWeight_euler_product hn.ne']
  apply Finset.prod_le_one
  · intro p hp
    exact (localFactor_pos (Nat.prime_of_mem_primeFactors hp)).le
  · intro p hp
    exact localFactor_le_one (Nat.prime_of_mem_primeFactors hp)

theorem spectralWeight_multiplicative {m n : ℕ} (hmn : m.Coprime n) :
    spectralWeight (m*n)=spectralWeight m*spectralWeight n := by
  simpa only [spectralArithmetic_apply] using spectralArithmetic_multiplicative.2 hmn

theorem spectralWeight_prime_power {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : a≠0) :
    spectralWeight (p^a)=localFactor p := by
  rw [spectralWeight_euler_product (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow ha hp,Finset.prod_singleton]

def spectralCorrection : ArithmeticFunction ℝ :=
  CollisionSquarefreeEuler.absMoebius.pmul (prodPrimeFactors (fun p => localFactor p-1))

theorem spectralCorrection_multiplicative : spectralCorrection.IsMultiplicative :=
  absMoebius_multiplicative.pmul (IsMultiplicative.prodPrimeFactors _)

theorem spectralCorrection_prime {p : ℕ} (hp : p.Prime) :
    spectralCorrection p=localFactor p-1 := by
  simp [spectralCorrection,CollisionSquarefreeEuler.absMoebius,
    prodPrimeFactors_apply hp.ne_zero,hp.primeFactors,moebius_apply_prime hp]

theorem spectralCorrection_prime_power {p : ℕ} (hp : p.Prime) (k : ℕ) :
    spectralCorrection (p^(k+2))=0 := by
  simp [spectralCorrection,CollisionSquarefreeEuler.absMoebius,
    moebius_apply_prime_pow hp (by omega : k+2≠0)]

theorem spectralCorrection_squarefree_support {n : ℕ} (hn : ¬Squarefree n) :
    spectralCorrection n=0 := by
  simp [spectralCorrection,CollisionSquarefreeEuler.absMoebius,
    moebius_eq_zero_of_not_squarefree hn]

theorem spectralWeight_divisor_sum {n : ℕ} (hn : 0<n) :
    spectralWeight n=∑ d ∈ n.divisors, spectralCorrection d := by
  rw [squarefree_divisor_product spectralCorrection spectralCorrection_multiplicative
    (fun _ hp k => spectralCorrection_prime_power hp k) hn.ne',
    spectralWeight_euler_product hn.ne']
  apply Finset.prod_congr rfl
  intro p hp
  rw [spectralCorrection_prime (Nat.prime_of_mem_primeFactors hp)]
  ring

theorem spectralCorrection_convolution :
    spectralCorrection*(ζ : ArithmeticFunction ℝ)=spectralArithmetic := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [coe_mul_zeta_apply,spectralArithmetic_apply,
      spectralWeight_divisor_sum (Nat.pos_of_ne_zero hn)]

end NField.Alignment.CollisionSpectralArithmetic
