/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandSmallPower
import NField.Alignment.CommonResetBandPhases
import NField.Alignment.CommonResetSourceRate

/-! # Exact printed band scales and the quarter-power cost product -/

noncomputable section

namespace NField.Alignment.CommonResetPrintedScales

open scoped BigOperators
open CommonResetBandSmallPower CommonResetRootSums CommonResetConductorSelection
open CommonResetRetainedBands CommonResetBandScale CommonResetBandPhases
open CommonResetBandParameters CommonResetBandGeometry CommonResetCompletedDerivative
open CommonResetTailGrowth CommonResetDivisorFibers CommonResetBandCosts CommonResetBoxRows
open CommonResetSmallConductors

theorem rpow_three_halves {x : ℝ} (hx : 0 < x) : x^(3/2 : ℝ)=x*Real.sqrt x := by
  rw [show (3/2 : ℝ)=1+1/2 by norm_num, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem rpow_five_halves {x : ℝ} (hx : 0 < x) : x^(5/2 : ℝ)=x^2*Real.sqrt x := by
  rw [show (5/2 : ℝ)=2+1/2 by norm_num, Real.rpow_add hx, Real.rpow_two, ← Real.sqrt_eq_rpow]

def printedBandScale (p m u v j : ℕ) : ℝ :=
  (p : ℝ)^(3/2 : ℝ)/((m : ℝ)^(3/2 : ℝ)*u*Real.sqrt ((j : ℝ)*v))+
    (p : ℝ)^(3/2 : ℝ)/((m : ℝ)^(5/2 : ℝ)*u*((j : ℝ)*v)^(3/2 : ℝ))+
    (p : ℝ)/((m : ℝ)*Real.sqrt (u : ℝ)*j*v)

theorem bandScale_eq_printed {p m u v j : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hu : 0 < u) (hv : 0 < v) (hj : 0 < j) :
    plainBandScale p m u v j=printedBandScale p m u v j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  unfold plainBandScale printedBandScale rootCube
  rw [rpow_three_halves hpR, rpow_three_halves hmR, rpow_five_halves hmR,
    rpow_three_halves (mul_pos hjR hvR), Real.sqrt_mul hjR.le]
  field_simp

/-- Title: `The actual selected band satisfies the exact displayed three-term fractional-power bound`. -/
theorem selected_band_printed (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p m u v j : ℕ, p.Prime → 1 ≤ m →
      0 < u → u ≤ p → 0 < v → 0 < j → ∀ S : Finset ℕ,
      (∀ i ∈ S, ∀ k ∈ S, ∀ t, i≤t → t≤k → t∈S) →
      |∑ t ∈ conductorSelection p m u v j (quarterCutoff p) S, originalFrequency p t u v j| ≤
        C*(p : ℝ)^ε*Real.sqrt ((j*v).gcd u : ℝ)*printedBandScale p m u v j := by
  obtain ⟨C, hC, hb⟩ := selected_band_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro p m u v j hp hm hu hup hv hj S hS
  simpa only [bandScale_eq_printed hp.pos hm hu hv hj] using hb p m u v j hp hm hu hup hv hj S hS

def plainPhaseScale (p m u v j : ℕ) : ℝ :=
  Real.sqrt (p : ℝ)*Real.sqrt ((j : ℝ)*v)/Real.sqrt (m : ℝ)+
    Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)*Real.sqrt ((j : ℝ)*v))+Real.sqrt (u : ℝ)

theorem phaseScale_absorption {p u : ℕ} (hp : 1 ≤ p) (hu : 0 < u) (hup : u ≤ p)
    (m v j : ℕ) : bandPhaseScale p m u v j ≤ 3*(harmonic p : ℝ)*plainPhaseScale p m u v j := by
  unfold bandPhaseScale plainPhaseScale
  exact three_term_log_absorption (by positivity) (by positivity) (by positivity)
    (harmonic_one_le hp) (log_twice_le_harmonic hu hup)

/-- Title: `Every actual reciprocal band phase satisfies the displayed epsilon bound with the logarithm absorbed`. -/
theorem reciprocal_band_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p m u v j : ℕ, p.Prime → 1 ≤ m → m^2 ≤ p →
      ∀ (hu : 0 < u), 2*u < p → 0 < v → 0 < j → ∀ η : ℤ,
      (η=0 ∨ η=1 ∨ η=-1) → ∀ (a : ℤ) (N : ℕ),
      Set.Icc (a : ℝ) (a+N) ⊆ Set.Icc (bandLeft p m) (bandRight p m) →
      letI : NeZero u := ⟨hu.ne'⟩
      ‖reciprocalInterval (bandFrequency p u v j) a N
        (fun t : ℝ => reciprocalCoefficient p u v j η/t)‖ ≤
        C*(p : ℝ)^ε*Real.sqrt ((j*v).gcd u : ℝ)*plainPhaseScale p m u v j := by
  obtain ⟨D, hD, hd⟩ := tail_arithmetic_small_power ε hε
  refine ⟨388800*D, by positivity, ?_⟩
  intro p m u v j hp hm hmsq hu hup hv hj η hη a N hsub
  letI : NeZero u := ⟨hu.ne'⟩
  have hb := reciprocal_band_bound hp.two_le hm hmsq hu hup hv hj η hη
    (bandFrequency p u v j) a N hsub
  rw [bandFrequency_gcd hp (by omega)] at hb
  have hdiv : (u.divisors.card : ℝ) ≤ divisorMaximum p :=
    Nat.cast_le.mpr (divisor_card_le_pmaximum hp.one_le hu (by omega))
  have harith : (u.divisors.card : ℝ)*(harmonic p : ℝ) ≤ tailArithmeticCost p :=
    mul_le_mul hdiv (harmonic_le_fourth hp.one_le) (harmonic_nonneg _) (Nat.cast_nonneg _)
  have hG : 0 ≤ Real.sqrt ((j*v).gcd u : ℝ)*plainPhaseScale p m u v j := by
    unfold plainPhaseScale
    positivity
  calc
    _ ≤ 129600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandPhaseScale p m u v j := hb
    _ ≤ 129600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*
        (3*(harmonic p : ℝ)*plainPhaseScale p m u v j) :=
      mul_le_mul_of_nonneg_left (phaseScale_absorption hp.one_le hu (by omega) m v j) (by positivity)
    _ = 388800*((u.divisors.card : ℝ)*(harmonic p : ℝ))*
        (Real.sqrt ((j*v).gcd u : ℝ)*plainPhaseScale p m u v j) := by ring
    _ ≤ 388800*(D*(p : ℝ)^ε)*(Real.sqrt ((j*v).gcd u : ℝ)*plainPhaseScale p m u v j) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (harith.trans (hd p hp.one_le)) (by norm_num)) hG
    _ = _ := by ring

/-- Title: `The three literal positive budget costs have product exactly the seventh power`. -/
theorem cost_product {p V J : ℝ} (hp : 0 < p) (hV : 0 < V) (hJ : 0 < J) :
    (p^(3/2 : ℝ)*Real.sqrt (V*J))^2*(p^2/V)*(p^2/J)=p^7 := by
  rw [rpow_three_halves hp, mul_pow, mul_pow, Real.sq_sqrt hp.le,
    Real.sq_sqrt (mul_pos hV hJ).le]
  field_simp

end NField.Alignment.CommonResetPrintedScales
