/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeSetConcentration
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Absence of atoms in the actual forcing block laws

Every finite prime set gives an infinite-block atom bound. Divergence of
the prime reciprocal sum makes its activation mass arbitrarily large.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeBlockAtomless

open scoped BigOperators Classical
open MeasureTheory Filter ProfiniteRemainderMeasure CollisionRemainderDynamics
open CollisionActivationArithmetic CollisionPrimeSetConcentration
open CollisionResetIntegrability CollisionPotentialCoboundary

theorem finite_positive_lower_bound {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ i∈S, 0<f i) : ∃ a : ℝ, 0<a ∧ ∀ i∈S, a≤f i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨a,ha,haf⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min a (f i),lt_min ha (hf i (Finset.mem_insert_self i S)),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (haf j hj)

theorem finite_prime_set_block_atom_bound (S : Finset ℕ) {h : ℕ} (hh : 0<h)
    (hS : ∀ p∈S, p.Prime ∧ 2*h≤p) (u : ℝ) :
    phaseHaar.real {x | forcingBlock h x=u}≤
      20/Real.sqrt (1+∑ p∈S, (h : ℝ)/(p : ℝ)) := by
  obtain ⟨a,ha,has⟩ := finite_positive_lower_bound S (fun p => (p : ℝ)*collisionWeight p)
    (fun p hp => prime_increment_positive (hS p hp).1)
  simpa only [Set.Icc_self,Set.mem_singleton_iff] using
    finite_prime_set_block_concentration S hh hS ha (by simpa : u-u<a) has

theorem prime_reciprocal_mass_unbounded (K : ℕ) (R : ℝ) :
    ∃ S : Finset ℕ, (∀ p∈S, p.Prime ∧ K≤p) ∧ R<∑ p∈S, (1 : ℝ)/(p : ℝ) := by
  by_contra hn
  push Not at hn
  let f : ℕ → ℝ := fun p => if p.Prime ∧ K≤p then (1 : ℝ)/(p : ℝ) else 0
  have hf : ∀ p, 0≤f p := by intro p; dsimp [f]; split_ifs <;> positivity
  have hsum : Summable f := summable_of_sum_le hf (fun T => show ∑ p∈T, f p≤R from by
    have hs := hn (T.filter (fun p => p.Prime ∧ K≤p))
      (fun p hp => (Finset.mem_filter.mp hp).2)
    simpa only [Finset.sum_filter,f] using hs)
  have he : f =ᶠ[atTop] ({p : ℕ | p.Prime}).indicator (fun p => (1 : ℝ)/(p : ℝ)) := by
    filter_upwards [eventually_ge_atTop K] with p hp
    simp [f,hp,Set.indicator_apply]
  exact not_summable_one_div_on_primes ((summable_congr_atTop he).mp hsum)

theorem prime_activation_mass_unbounded {h : ℕ} (hh : 0<h) (R : ℝ) :
    ∃ S : Finset ℕ, (∀ p∈S, p.Prime ∧ 2*h≤p) ∧ R<∑ p∈S, (h : ℝ)/(p : ℝ) := by
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  obtain ⟨S,hS,hs⟩ := prime_reciprocal_mass_unbounded (2*h) (R/(h : ℝ))
  refine ⟨S,hS,?_⟩
  have ht := (div_lt_iff₀ hhR).mp hs
  calc
    R < (∑ p∈S, (1 : ℝ)/(p : ℝ))*(h : ℝ) := ht
    _ = ∑ p∈S, (h : ℝ)/(p : ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring

theorem forcingBlock_atom_zero {h : ℕ} (hh : 0<h) (u : ℝ) :
    phaseHaar.real {x | forcingBlock h x=u}=0 := by
  have hρ0 : 0≤phaseHaar.real {x | forcingBlock h x=u} := measureReal_nonneg
  apply le_antisymm _ hρ0
  by_contra hn
  have hρ : 0<phaseHaar.real {x | forcingBlock h x=u} := lt_of_not_ge hn
  let ρ : ℝ := phaseHaar.real {x | forcingBlock h x=u}
  have hr : 0<ρ := hρ
  obtain ⟨S,hS,hs⟩ := prime_activation_mass_unbounded hh (400/ρ^2)
  have hm : 0≤∑ p∈S, (h : ℝ)/(p : ℝ) := Finset.sum_nonneg (fun p _ => by positivity)
  have hp : 0<Real.sqrt (1+∑ p∈S, (h : ℝ)/(p : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hb := finite_prime_set_block_atom_bound S hh hS u
  change ρ≤20/Real.sqrt (1+∑ p∈S, (h : ℝ)/(p : ℝ)) at hb
  have ht := (le_div_iff₀ hp).mp hb
  have hsq := pow_le_pow_left₀ (mul_nonneg hr.le hp.le) ht 2
  rw [mul_pow,Real.sq_sqrt (by linarith : 0≤1+∑ p∈S, (h : ℝ)/(p : ℝ))] at hsq
  have hlarge := (div_lt_iff₀ (sq_pos_of_pos hr)).mp hs
  nlinarith [sq_pos_of_pos hr]

theorem forcingBlock_atom_measure_zero {h : ℕ} (hh : 0<h) (u : ℝ) :
    phaseHaar {x | forcingBlock h x=u}=0 := by
  exact ((ENNReal.toReal_eq_zero_iff _).mp (forcingBlock_atom_zero hh u)).resolve_right
    (measure_ne_top phaseHaar _)


theorem forcingBlock_one (x : Phase) : forcingBlock 1 x=resetFunction (translate 1 x) := by
  simp [forcingBlock]

theorem resetFunction_atom_measure_zero (u : ℝ) : phaseHaar {x | resetFunction x=u}=0 := by
  have hm := measure_preimage_mul phaseHaar (integerPhase 1) {x | resetFunction x=u}
  change phaseHaar {x | resetFunction (translate 1 x)=u}=phaseHaar {x | resetFunction x=u} at hm
  simp_rw [← forcingBlock_one] at hm
  exact hm.symm.trans (forcingBlock_atom_measure_zero (by omega : 0<1) u)

theorem increment_atom_measure_zero (u : ℝ) : phaseHaar {x | increment x=u}=0 := by
  have he : {x | increment x=u}={x | resetFunction x=1-(3/2 : ℝ)*u} := by
    ext x
    simp only [Set.mem_setOf_eq,increment]
    constructor <;> intro hx <;> linarith
  rw [he,resetFunction_atom_measure_zero]

theorem incrementBlock_atom_measure_zero {h : ℕ} (hh : 0<h) (u : ℝ) :
    phaseHaar {x | blockFunction h x=u}=0 := by
  have he : {x | blockFunction h x=u}={x | forcingBlock h x=(h : ℝ)-(3/2 : ℝ)*u} := by
    ext x
    simp only [Set.mem_setOf_eq,blockFunction_forcingBlock]
    constructor <;> intro hx <;> linarith
  rw [he,forcingBlock_atom_measure_zero hh]

theorem resetFunction_law_singleton (u : ℝ) : (Measure.map resetFunction phaseHaar) {u}=0 := by
  rw [Measure.map_apply_of_aemeasurable resetFunction_integrable.aemeasurable
    (measurableSet_singleton u)]
  exact resetFunction_atom_measure_zero u

end NField.Alignment.CollisionPrimeBlockAtomless
