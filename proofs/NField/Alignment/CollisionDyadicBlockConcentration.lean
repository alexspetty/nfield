/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDyadicPrimeMass

/-!
# The dyadic block concentration estimate

This applies the prime number theorem activation mass bound to the actual
infinite forcing block, retaining the strict logarithmic interval width.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDyadicBlockConcentration

open scoped BigOperators Classical
open Filter MeasureTheory ProfiniteRemainderMeasure
open CollisionActivationArithmetic CollisionPrimeSetConcentration CollisionDyadicPrimeMass

theorem inverseRoot_activation_bound {h L B : ℝ} (hh : 0<h) (hL : 0<L)
    (hB : h/(4*L)≤B) : 20/Real.sqrt (1+B)≤40*Real.sqrt (L/h) := by
  have hq : 0<h/(4*L) := div_pos hh (mul_pos (by norm_num) hL)
  have hroot : 0<Real.sqrt (h/(4*L)) := Real.sqrt_pos.mpr hq
  calc
    _ ≤ 20/Real.sqrt (h/(4*L)) := div_le_div_of_nonneg_left (by norm_num) hroot
      (Real.sqrt_le_sqrt (by linarith))
    _ = 40*Real.sqrt (L/h) := by
      rw [Real.sqrt_div hh.le,Real.sqrt_mul (by norm_num : (0 : ℝ)≤4),Real.sqrt_div hL.le]
      norm_num
      field_simp
      norm_num

theorem dyadic_block_concentration_eventually : ∀ᶠ P : ℕ in atTop,
    ∀ h : ℕ, 0<h → 4*h≤P → ∀ u v : ℝ, v-u<Real.log ((P : ℝ)/2)/(P : ℝ) →
      phaseHaar.real {x | forcingBlock h x∈Set.Icc u v}≤40*Real.sqrt (Real.log P/(h : ℝ)) := by
  filter_upwards [dyadic_activation_mass_lower,eventually_ge_atTop (4 : ℕ)] with P hmass hP h hh hhP u v huv
  have hp : (0 : ℝ)<P := by exact_mod_cast (show 0<P by omega)
  have hl : 0<Real.log P := Real.log_pos (by exact_mod_cast (show 1<P by omega))
  have hhalf : (1 : ℝ)<(P : ℝ)/2 := by
    have ht : (4 : ℝ)≤P := by exact_mod_cast hP
    linarith
  have hinc : 0<Real.log ((P : ℝ)/2)/(P : ℝ) := div_pos (Real.log_pos hhalf) hp
  have hS : ∀ p∈dyadicPrimes P, p.Prime ∧ 2*h≤p := by
    intro p hmem
    obtain ⟨hpp,hlo,hhi⟩ := mem_dyadicPrimes.mp hmem
    refine ⟨hpp,?_⟩
    have ht : (4 : ℝ)*h≤P := by exact_mod_cast hhP
    have hd : (2 : ℝ)*h≤p := by linarith
    exact_mod_cast hd
  have hb := finite_prime_set_block_concentration (dyadicPrimes P) hh hS hinc huv
    (fun p hmem => prime_increment_window_lower (by omega) (mem_dyadicPrimes.mp hmem).1
      (mem_dyadicPrimes.mp hmem).2.1 (mem_dyadicPrimes.mp hmem).2.2)
  exact hb.trans (inverseRoot_activation_bound (by exact_mod_cast hh) hl (hmass h))


theorem finite_range_root_lower {N P h : ℕ} (hh : 0<h) (hhN : h≤N) (hP : 4≤P) :
    1≤(Real.sqrt (N : ℝ)/Real.sqrt (Real.log 4))*Real.sqrt (Real.log P/(h : ℝ)) := by
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  have hN : (0 : ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hh hhN)
  have hl4 : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hlP : Real.log 4≤Real.log P := Real.log_le_log (by norm_num) (by exact_mod_cast hP)
  have hratio : Real.log 4/(N : ℝ)≤Real.log P/(h : ℝ) := by
    calc
      _ ≤ Real.log 4/(h : ℝ) := div_le_div_of_nonneg_left hl4.le hhR (by exact_mod_cast hhN)
      _ ≤ _ := div_le_div_of_nonneg_right hlP hhR.le
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio)
    (show 0≤Real.sqrt (N : ℝ)/Real.sqrt (Real.log 4) by positivity)
  have he : (Real.sqrt (N : ℝ)/Real.sqrt (Real.log 4))*Real.sqrt (Real.log 4/(N : ℝ))=1 := by
    rw [Real.sqrt_div hl4.le]
    have hn0 : Real.sqrt (N : ℝ)≠0 := (Real.sqrt_pos.mpr hN).ne'
    have hl0 : Real.sqrt (Real.log 4)≠0 := (Real.sqrt_pos.mpr hl4).ne'
    field_simp
  rwa [he] at hs

theorem dyadic_block_concentration_uniform : ∃ C : ℝ, 1≤C ∧
    ∀ P h : ℕ, 0<h → 4*h≤P → ∀ u v : ℝ, v-u<Real.log ((P : ℝ)/2)/(P : ℝ) →
      phaseHaar.real {x | forcingBlock h x∈Set.Icc u v}≤C*Real.sqrt (Real.log P/(h : ℝ)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp dyadic_block_concentration_eventually
  let C : ℝ := max 40 (Real.sqrt (N : ℝ)/Real.sqrt (Real.log 4))
  have h40 : (40 : ℝ)≤C := le_max_left _ _
  refine ⟨C,by linarith,?_⟩
  intro P h hh hhP u v huv
  by_cases hNP : N≤P
  · exact (hN P hNP h hh hhP u v huv).trans
      (mul_le_mul_of_nonneg_right h40 (Real.sqrt_nonneg _))
  · have hhN : h≤N := by omega
    have hP4 : 4≤P := by omega
    have hfinite := finite_range_root_lower hh hhN hP4
    have hfactor : (Real.sqrt (N : ℝ)/Real.sqrt (Real.log 4))*Real.sqrt (Real.log P/(h : ℝ))≤
        C*Real.sqrt (Real.log P/(h : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
    exact (measureReal_le_one).trans (hfinite.trans hfactor)

theorem block_concentration : ∃ C : ℝ, 0<C ∧
    ∀ P h : ℕ, 0<h → 4*h≤P → ∀ δ : ℝ, δ<Real.log ((P : ℝ)/2)/(P : ℝ) →
      (⨆ u : ℝ, phaseHaar.real {x | forcingBlock h x∈Set.Icc u (u+δ)})≤
        C*min 1 (Real.sqrt (Real.log P/(h : ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := dyadic_block_concentration_uniform
  refine ⟨C,by linarith,?_⟩
  intro P h hh hhP δ hδ
  apply ciSup_le
  intro u
  by_cases hr : 1≤Real.sqrt (Real.log P/(h : ℝ))
  · rw [min_eq_left hr,mul_one]
    exact measureReal_le_one.trans hC
  · rw [min_eq_right (le_of_not_ge hr)]
    exact hbound P h hh hhP u (u+δ) (by simpa only [add_sub_cancel_left] using hδ)

end NField.Alignment.CollisionDyadicBlockConcentration
