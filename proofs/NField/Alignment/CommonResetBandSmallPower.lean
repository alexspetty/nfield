/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetConductorSelection
import NField.Alignment.CommonResetBoxRows

/-! # The literal standalone band estimate after divisor and logarithmic absorption -/

noncomputable section

namespace NField.Alignment.CommonResetBandSmallPower

open scoped BigOperators
open CommonResetConductorSelection CommonResetRetainedBands CommonResetBandWeighted
open CommonResetBandCosts CommonResetRootSums CommonResetBoxRows CommonResetTailGrowth
open CommonResetDivisorFibers CommonResetSmallConductors

def plainBandScale (p m u v j : ℕ) : ℝ :=
  ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
    (1/(u : ℝ))*(1/Real.sqrt (j : ℝ))*(1/Real.sqrt (v : ℝ)) +
  ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)^2*Real.sqrt (m : ℝ)))*
    (1/(u : ℝ))*rootCube j*rootCube v +
  ((p : ℝ)/m)*(1/Real.sqrt (u : ℝ))*(1/(j : ℝ))*(1/(v : ℝ))

theorem plainBandScale_nonneg (p m u v j : ℕ) : 0 ≤ plainBandScale p m u v j := by
  have hj := rootCube_nonneg j
  have hv := rootCube_nonneg v
  unfold plainBandScale
  positivity

theorem three_term_log_absorption {a b c H l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hH : 1 ≤ H) (hl : l ≤ 2*H) : a+b+c*l ≤ 3*H*(a+b+c) := by
  have h1 : a ≤ H*a := le_mul_of_one_le_left ha hH
  have h2 : b ≤ H*b := le_mul_of_one_le_left hb hH
  have h3 : c*l ≤ c*(2*H) := mul_le_mul_of_nonneg_left hl hc
  have hHa : 0 ≤ H*a := by positivity
  have hHb : 0 ≤ H*b := by positivity
  have hHc : 0 ≤ H*c := by positivity
  nlinarith

theorem band_log_absorption {p m u v j : ℕ} (hm : 0 < m) (hu : 0 < u)
    (hup : u ≤ p) (hv : 0 < v) (hj : 0 < j) :
    Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j ≤
      3*(harmonic p : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*plainBandScale p m u v j := by
  rw [band_cost_decomposition hm hu hv hj]
  have hrootj := rootCube_nonneg j
  have hrootv := rootCube_nonneg v
  have hh := three_term_log_absorption
    (a := ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)*Real.sqrt (m : ℝ)))*
      (Real.sqrt ((j*v).gcd u : ℝ)/(u : ℝ))*(1/Real.sqrt (j : ℝ))*(1/Real.sqrt (v : ℝ)))
    (b := ((p : ℝ)*Real.sqrt (p : ℝ)/((m : ℝ)^2*Real.sqrt (m : ℝ)))*
      (Real.sqrt ((j*v).gcd u : ℝ)/(u : ℝ))*rootCube j*rootCube v)
    (c := ((p : ℝ)/m)*(Real.sqrt ((j*v).gcd u : ℝ)/Real.sqrt (u : ℝ))*(1/(j : ℝ))*(1/(v : ℝ)))
    (H := (harmonic p : ℝ)) (l := Real.log (2*(u : ℝ)))
    (by positivity) (by positivity) (by positivity)
    (harmonic_one_le (by omega)) (log_twice_le_harmonic hu hup)
  convert hh using 1 <;> unfold plainBandScale <;> ring

theorem harmonic_le_fourth {p : ℕ} (hp : 1 ≤ p) : (harmonic p : ℝ) ≤ (harmonic p : ℝ)^4 := by
  have hH := harmonic_one_le hp
  calc
    _ = (harmonic p : ℝ)*1 := by ring
    _ ≤ (harmonic p : ℝ)*(harmonic p : ℝ)^3 :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hH) (harmonic_nonneg _)
    _ = _ := by ring

/-- Title: `Every actual retained band satisfies the published epsilon estimate with all inverse frequencies allowed`. -/
theorem selected_band_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p m u v j : ℕ, p.Prime → 1 ≤ m →
      0 < u → u ≤ p → 0 < v → 0 < j → ∀ S : Finset ℕ,
      (∀ i ∈ S, ∀ k ∈ S, ∀ t, i≤t → t≤k → t∈S) →
      |∑ t ∈ conductorSelection p m u v j (quarterCutoff p) S, originalFrequency p t u v j| ≤
        C*(p : ℝ)^ε*Real.sqrt ((j*v).gcd u : ℝ)*plainBandScale p m u v j := by
  obtain ⟨D, hD, hd⟩ := tail_arithmetic_small_power ε hε
  refine ⟨874800*D, by positivity, ?_⟩
  intro p m u v j hp hm hu hup hv hj S hS
  have hG : 0 ≤ Real.sqrt ((j*v).gcd u : ℝ)*plainBandScale p m u v j :=
    mul_nonneg (Real.sqrt_nonneg _) (plainBandScale_nonneg p m u v j)
  have hdiv : (u.divisors.card : ℝ) ≤ divisorMaximum p := Nat.cast_le.mpr (divisor_card_le_pmaximum hp.one_le hu hup)
  have harith : (u.divisors.card : ℝ)*(harmonic p : ℝ) ≤ tailArithmeticCost p := by
    exact mul_le_mul hdiv (harmonic_le_fourth hp.one_le) (harmonic_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ 291600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j :=
      selected_band_bound_all_u hp hm hu hv hj S hS
    _ = (291600*(u.divisors.card : ℝ))*
        (Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j) := by ring
    _ ≤ (291600*(u.divisors.card : ℝ))*
        (3*(harmonic p : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*plainBandScale p m u v j) :=
      mul_le_mul_of_nonneg_left (band_log_absorption hm hu hup hv hj) (by positivity)
    _ = 874800*((u.divisors.card : ℝ)*(harmonic p : ℝ))*
        (Real.sqrt ((j*v).gcd u : ℝ)*plainBandScale p m u v j) := by ring
    _ ≤ 874800*(D*(p : ℝ)^ε)*(Real.sqrt ((j*v).gcd u : ℝ)*plainBandScale p m u v j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (harith.trans (hd p hp.one_le)) (by norm_num)) hG
    _ = _ := by ring

end NField.Alignment.CommonResetBandSmallPower
