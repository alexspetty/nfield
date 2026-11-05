/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Absolute convergence and positivity of the spectral Euler constant

Squarefree integers embed injectively into finite sets of primes. The
sum of positive finite products bounds the entire absolute correction
series before the multiplicative Euler-product theorem is used.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralEuler

open scoped BigOperators Classical
open ArithmeticFunction
open CollisionConductorArithmetic CollisionSquarefreeEuler CollisionZetaMoments
open CollisionSpectralArithmetic

def correctionKernel : ArithmeticFunction ℝ where
  toFun n := spectralCorrection n/(n : ℝ)
  map_zero' := by simp

theorem correctionKernel_apply (n : ℕ) :
    correctionKernel n=spectralCorrection n/(n : ℝ) := rfl

theorem correctionKernel_multiplicative : correctionKernel.IsMultiplicative := by
  refine ⟨by simp [correctionKernel_apply,spectralCorrection_multiplicative.1],?_⟩
  intro m n hmn
  simp only [correctionKernel_apply,spectralCorrection_multiplicative.2 hmn,Nat.cast_mul,
    mul_div_mul_comm]

def primeAbsolute (p : ℕ) : ℝ := if p.Prime then |localFactor p-1|/(p : ℝ) else 0

theorem primeAbsolute_nonneg (p : ℕ) : 0≤primeAbsolute p := by
  unfold primeAbsolute
  split_ifs <;> positivity

theorem primeAbsolute_bound (p : ℕ) : primeAbsolute p≤2*powerKernel 2 p := by
  by_cases hp : p.Prime
  · rw [primeAbsolute,if_pos hp]
    have h := div_le_div_of_nonneg_right (localFactor_abs_defect hp) (Nat.cast_nonneg p)
    convert! h using 1
    unfold powerKernel
    ring
  · simp only [primeAbsolute,if_neg hp]
    exact mul_nonneg (by norm_num) (powerKernel_nonneg 2 p)

theorem primeAbsolute_summable : Summable primeAbsolute :=
  Summable.of_nonneg_of_le primeAbsolute_nonneg primeAbsolute_bound
    ((powerKernel_summable (by norm_num : 1<(2 : ℕ))).mul_left 2)

theorem correctionKernel_norm_squarefree {n : ℕ} (hn : Squarefree n) :
    ‖correctionKernel n‖=∏ p ∈ n.primeFactors, primeAbsolute p := by
  have hmu : |(moebius n : ℝ)|=1 := by
    exact_mod_cast abs_moebius_eq_one_of_squarefree hn
  have hp : (∏ p ∈ n.primeFactors, (p : ℝ))=(n : ℝ) := by
    rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hn]
  rw [correctionKernel_apply,spectralCorrection,pmul_apply]
  change ‖|(moebius n : ℝ)| *prodPrimeFactors (fun p => localFactor p-1) n/(n : ℝ)‖=_
  rw [hmu,one_mul,prodPrimeFactors_apply hn.ne_zero,norm_div,Real.norm_eq_abs,
    Real.norm_natCast,Finset.abs_prod,← hp,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [primeAbsolute,if_pos (Nat.prime_of_mem_primeFactors hp)]

theorem primeFactors_injective_squarefree :
    Function.Injective (fun n : {n : ℕ // Squarefree n} => n.val.primeFactors) := by
  intro m n h
  apply Subtype.ext
  have he := congrArg (fun s : Finset ℕ => ∏ p ∈ s, p) h
  simpa only [Nat.prod_primeFactors_of_squarefree m.property,
    Nat.prod_primeFactors_of_squarefree n.property] using he

theorem correctionKernel_norm_summable : Summable (fun n => ‖correctionKernel n‖) := by
  have hs := (summable_finsetProd_of_summable_nonneg primeAbsolute_nonneg
    primeAbsolute_summable).comp_injective primeFactors_injective_squarefree
  have ht := hs.congr (fun n => (correctionKernel_norm_squarefree n.property).symm)
  have hi := (summable_subtype_iff_indicator (s := {n | Squarefree n})
    (f := fun n => ‖correctionKernel n‖)).mp ht
  have he : {n | Squarefree n}.indicator (fun n => ‖correctionKernel n‖)=
      (fun n => ‖correctionKernel n‖) := by
    funext n
    by_cases hn : Squarefree n
    · exact Set.indicator_of_mem hn _
    · simp [Set.indicator,hn,correctionKernel_apply,spectralCorrection_squarefree_support hn]
  rwa [he] at hi

theorem correctionKernel_summable : Summable correctionKernel :=
  correctionKernel_norm_summable.of_norm

theorem correctionKernel_prime {p : ℕ} (hp : p.Prime) :
    correctionKernel p=(localFactor p-1)/(p : ℝ) := by
  rw [correctionKernel_apply,spectralCorrection_prime hp]

theorem correctionKernel_prime_power {p : ℕ} (hp : p.Prime) (k : ℕ) :
    correctionKernel (p^(k+2))=0 := by
  rw [correctionKernel_apply,spectralCorrection_prime_power hp,zero_div]

theorem correctionKernel_local_sum {p : ℕ} (hp : p.Prime) :
    (∑' a : ℕ, correctionKernel (p^a))=1+(localFactor p-1)/(p : ℝ) := by
  have hz (a : ℕ) (ha : a∉Finset.range 2) : correctionKernel (p^a)=0 := by
    have ha2 : 2≤a := by simpa only [Finset.mem_range,not_lt] using ha
    rw [← Nat.sub_add_cancel ha2]
    exact correctionKernel_prime_power hp _
  rw [tsum_eq_sum hz]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    correctionKernel_multiplicative.1,correctionKernel_prime hp]

def spectralConstant : ℝ :=
  ∏' p : Nat.Primes, (1+(localFactor p.val-1)/(p.val : ℝ))

theorem spectralConstant_hasProd :
    HasProd (fun p : Nat.Primes => 1+(localFactor p.val-1)/(p.val : ℝ))
      (∑' n, correctionKernel n) := by
  have h := correctionKernel_multiplicative.eulerProduct_hasProd correctionKernel_norm_summable
  convert! h using 1
  funext p
  exact (correctionKernel_local_sum p.property).symm

theorem spectralConstant_series : spectralConstant=∑' n, spectralCorrection n/(n : ℝ) :=
  spectralConstant_hasProd.tprod_eq

theorem spectral_prime_correction_norm_summable :
    Summable (fun p : Nat.Primes => ‖(localFactor p.val-1)/(p.val : ℝ)‖) := by
  have h := correctionKernel_norm_summable.comp_injective
    (Subtype.val_injective (p := Nat.Prime))
  exact h.congr (fun p => by simp only [Function.comp_def,correctionKernel_prime p.property])

theorem spectral_euler_factor_pos (p : Nat.Primes) :
    0<1+(localFactor p.val-1)/(p.val : ℝ) := by
  have hpR : (1 : ℝ)<p.val := by exact_mod_cast p.property.one_lt
  have hl := localFactor_pos p.property
  have h : 0<((p.val : ℝ)-1+localFactor p.val)/(p.val : ℝ) :=
    div_pos (by linarith) (by linarith)
  convert! h using 1
  field_simp
  ring

theorem spectralConstant_pos : 0<spectralConstant := by
  have hlog := Real.summable_log_one_add_of_summable
    spectral_prime_correction_norm_summable.of_norm
  rw [spectralConstant,← Real.rexp_tsum_eq_tprod spectral_euler_factor_pos hlog]
  exact Real.exp_pos _

theorem spectralConstant_literal_product :
    spectralConstant=∏' p : Nat.Primes,
      (1+((1-((p.val : ℝ)^2)⁻¹)*(rho p.val)^2-1)/(p.val : ℝ)) := by
  apply tprod_congr
  intro p
  rw [rho_euler_product p.property.ne_zero,p.property.primeFactors,Finset.prod_singleton]
  rfl

end NField.Alignment.CollisionSpectralEuler
