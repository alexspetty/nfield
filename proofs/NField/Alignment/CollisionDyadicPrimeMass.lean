/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeSetConcentration
import NField.Alignment.CollisionPrimeDistribution

/-!
# Dyadic prime activation mass from the proved prime number theorem

The number and reciprocal mass of primes in (P/2,P] are bounded below
using the actual Chebyshev theta difference. These bounds are uniform
in the block length.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDyadicPrimeMass

open scoped BigOperators Classical
open Filter MeasureTheory ProfiniteRemainderMeasure
open CollisionMertensInput CollisionPrimeDistribution
open CollisionActivationArithmetic CollisionPrimeSetConcentration

def dyadicPrimes (P : ℕ) : Finset ℕ := primesUpTo (P : ℝ)\primesUpTo ((P : ℝ)/2)

theorem mem_dyadicPrimes {P p : ℕ} : p∈dyadicPrimes P ↔
    p.Prime ∧ (P : ℝ)/2<(p : ℝ) ∧ p≤P := by
  simp only [dyadicPrimes,Finset.mem_sdiff,primesUpTo_mem]
  constructor
  · rintro ⟨⟨hp,hpP⟩,hlo⟩
    exact ⟨hp,lt_of_not_ge (fun h => hlo ⟨hp,h⟩),by exact_mod_cast hpP⟩
  · rintro ⟨hp,hlo,hpP⟩
    exact ⟨⟨hp,by exact_mod_cast hpP⟩,fun h => (not_le_of_gt hlo) h.2⟩

theorem dyadic_log_sum (P : ℕ) :
    (∑ p∈dyadicPrimes P, Real.log p)=Chebyshev.theta P-Chebyshev.theta ((P : ℝ)/2) := by
  have hs : primesUpTo ((P : ℝ)/2)⊆primesUpTo (P : ℝ) := by
    intro p hp
    obtain ⟨hp,hple⟩ := primesUpTo_mem.mp hp
    exact primesUpTo_mem.mpr ⟨hp,hple.trans (by have := Nat.cast_nonneg (α := ℝ) P; linarith)⟩
  have ht := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) hs
  change (∑ p∈dyadicPrimes P, Real.log p)+Chebyshev.theta ((P : ℝ)/2)=Chebyshev.theta P at ht
  linarith

theorem dyadic_theta_ratio_tendsto :
    Tendsto (fun x : ℝ => (Chebyshev.theta x-Chebyshev.theta (x/2))/x)
      atTop (nhds (1/2 : ℝ)) := by
  have hs := theta_ratio_tendsto.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ)<1/2))
  have hh : Tendsto (fun x : ℝ => Chebyshev.theta (x/2)/x) atTop (nhds (1/2 : ℝ)) := by
    convert hs.const_mul (1/2) using 1
    · funext x
      by_cases hx : x=0
      · simp [hx]
      · change Chebyshev.theta (x/2)/x=(1/2 : ℝ)*(Chebyshev.theta ((1/2 : ℝ)*x)/((1/2 : ℝ)*x))
        have he : (1/2 : ℝ)*x=x/2 := by ring
        rw [he]
        field_simp
    · norm_num
  have ht := theta_ratio_tendsto.sub hh
  convert ht using 1
  · funext x
    rw [sub_div]
  · norm_num

theorem dyadic_log_sum_lower : ∀ᶠ P : ℕ in atTop,
    (P : ℝ)/4≤∑ p∈dyadicPrimes P, Real.log p := by
  have hg := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((tendsto_order.mp dyadic_theta_ratio_tendsto).1 (1/4) (by norm_num))
  filter_upwards [hg,eventually_gt_atTop (0 : ℕ)] with P hP hp
  have hpR : (0 : ℝ)<P := by exact_mod_cast hp
  rw [dyadic_log_sum]
  have ht := (le_div_iff₀ hpR).mp hP.le
  linarith

theorem dyadic_log_sum_upper (P : ℕ) :
    (∑ p∈dyadicPrimes P, Real.log p)≤(dyadicPrimes P).card*Real.log P := by
  have ht : (∑ p∈dyadicPrimes P, Real.log p)≤∑ _p∈dyadicPrimes P, Real.log P := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp,hlo,hhi⟩ := mem_dyadicPrimes.mp hp
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hhi)
  simpa only [Finset.sum_const,nsmul_eq_mul] using ht

theorem dyadic_prime_count_lower : ∀ᶠ P : ℕ in atTop,
    (P : ℝ)/(4*Real.log P)≤(dyadicPrimes P).card := by
  filter_upwards [dyadic_log_sum_lower,eventually_ge_atTop (2 : ℕ)] with P hP hP2
  have hl : 0<Real.log P := Real.log_pos (by exact_mod_cast (show 1<P by omega))
  have ht := hP.trans (dyadic_log_sum_upper P)
  apply (div_le_iff₀ (mul_pos (by norm_num) hl)).mpr
  linarith

theorem dyadic_reciprocal_sum_card (P : ℕ) :
    (dyadicPrimes P).card/(P : ℝ)≤∑ p∈dyadicPrimes P, (1 : ℝ)/(p : ℝ) := by
  have ht : (∑ _p∈dyadicPrimes P, (1 : ℝ)/(P : ℝ))≤
      ∑ p∈dyadicPrimes P, (1 : ℝ)/(p : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp,_,hpP⟩ := mem_dyadicPrimes.mp hp
    exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hp.pos) (by exact_mod_cast hpP)
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one_div] using ht

theorem dyadic_reciprocal_sum_lower : ∀ᶠ P : ℕ in atTop,
    1/(4*Real.log P)≤∑ p∈dyadicPrimes P, (1 : ℝ)/(p : ℝ) := by
  filter_upwards [dyadic_prime_count_lower,eventually_ge_atTop (2 : ℕ)] with P hP hP2
  have hp : (0 : ℝ)<P := by exact_mod_cast (show 0<P by omega)
  have hl : 0<Real.log P := Real.log_pos (by exact_mod_cast (show 1<P by omega))
  have ht := div_le_div_of_nonneg_right hP hp.le
  have he : ((P : ℝ)/(4*Real.log P))/(P : ℝ)=1/(4*Real.log P) := by field_simp
  rw [he] at ht
  exact ht.trans (dyadic_reciprocal_sum_card P)

theorem dyadic_activation_mass_lower : ∀ᶠ P : ℕ in atTop, ∀ h : ℕ,
    (h : ℝ)/(4*Real.log P)≤∑ p∈dyadicPrimes P, (h : ℝ)/(p : ℝ) := by
  filter_upwards [dyadic_reciprocal_sum_lower] with P hP h
  have ht := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg h)
  simpa only [Finset.mul_sum,mul_one_div] using ht

end NField.Alignment.CollisionDyadicPrimeMass
