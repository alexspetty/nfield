/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionActivationQuotient
import NField.Alignment.CollisionConcentrationLimit
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Concentration of actual infinite forcing blocks from finite prime sets

Every cutoff uses the prime-power factorization of its factorial modulus.
The selected prime set and activation mass stay fixed as the cutoff grows.
The separately proved almost-everywhere limit then gives the actual block law.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeSetConcentration

open scoped BigOperators Classical
open MeasureTheory Filter ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionActivationArithmetic CollisionActivationQuotient CollisionConcentrationLimit

def selectedFactorialEquiv (M : ℕ) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ p≤M) :
    {p : M.factorial.primeFactors // p.val∈S} ≃ S where
  toFun p := ⟨p.val.val,p.property⟩
  invFun p := ⟨⟨p.val,Nat.mem_primeFactors.mpr
    ⟨(hS p p.property).1,Nat.dvd_factorial (hS p p.property).1.pos (hS p p.property).2,
      Nat.factorial_ne_zero M⟩⟩,p.property⟩
  left_inv p := by rfl
  right_inv p := by rfl

theorem selectedFactorial_sum (M : ℕ) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ p≤M) (F : ℕ → ℝ) :
    (∑ p : {p : M.factorial.primeFactors // p.val∈S}, F p.val.val)=∑ p∈S, F p := by
  have he := Equiv.sum_comp (selectedFactorialEquiv M S hS) (fun p : S => F p.val)
  simpa only [selectedFactorialEquiv,Equiv.coe_fn_mk,Finset.sum_coe_sort] using he

theorem finite_prime_set_cutoff_concentration (S : Finset ℕ) {h M : ℕ} (hh : 0<h)
    (hS : ∀ p∈S, p.Prime ∧ 2*h≤p ∧ p≤M)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hincr : ∀ p∈S, a≤(p : ℝ)*collisionWeight p) :
    phaseHaar.real {x | forcingCutoff h M x∈Set.Icc u v}≤
      20/Real.sqrt (1+∑ p∈S, (h : ℝ)/(p : ℝ)) := by
  let p : M.factorial.primeFactors → ℕ := Subtype.val
  let e : M.factorial.primeFactors → ℕ := fun p => M.factorial.factorization p
  have hp (i : M.factorial.primeFactors) : (p i).Prime := Nat.prime_of_mem_primeFactors i.property
  have he (i : M.factorial.primeFactors) : 0<e i :=
    (hp i).factorization_pos_of_dvd (Nat.factorial_ne_zero M) (Nat.mem_primeFactors.mp i.property).2.1
  have hcover (d : ℕ) (hd : 0<d) (hdM : d≤M) : d∣∏ i : M.factorial.primeFactors, p i^e i := by
    change d∣∏ i : M.factorial.primeFactors, (i : ℕ)^M.factorial.factorization i
    rw [← Nat.prod_primeFactors_coe_pow_factorization (Nat.factorial_ne_zero M)]
    exact Nat.dvd_factorial hd hdM
  have hb := prime_power_cutoff_concentration p e hp Subtype.val_injective he
    (fun i => p i∈S) hh hcover (fun i hi => (hS (p i) hi).2.2)
    (fun i hi => (hS (p i) hi).2.1) ha huv (fun i hi => hincr (p i) hi)
  have hs : (∑ i : {i : M.factorial.primeFactors // p i∈S}, (h : ℝ)/(p i : ℝ))=
      ∑ p∈S, (h : ℝ)/(p : ℝ) := by
    simpa only [p] using selectedFactorial_sum M S
      (fun p hp => ⟨(hS p hp).1,(hS p hp).2.2⟩) (fun p : ℕ => (h : ℝ)/(p : ℝ))
  convert hb using 1
  congr 3
  rw [← hs]
  apply Finset.sum_congr
  · ext i
    simp
  · intro i _
    rfl

theorem finite_prime_set_block_concentration (S : Finset ℕ) {h : ℕ} (hh : 0<h)
    (hS : ∀ p∈S, p.Prime ∧ 2*h≤p)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hincr : ∀ p∈S, a≤(p : ℝ)*collisionWeight p) :
    phaseHaar.real {x | forcingBlock h x∈Set.Icc u v}≤
      20/Real.sqrt (1+∑ p∈S, (h : ℝ)/(p : ℝ)) := by
  apply forcingBlock_limit_concentration h (by positivity) _ huv
  intro u v huv
  filter_upwards [eventually_ge_atTop (S.sup id)] with M hM
  apply finite_prime_set_cutoff_concentration S hh _ ha huv hincr
  intro p hp
  exact ⟨(hS p hp).1,(hS p hp).2,(Finset.le_sup (f := id) hp).trans hM⟩

end NField.Alignment.CollisionPrimeSetConcentration
