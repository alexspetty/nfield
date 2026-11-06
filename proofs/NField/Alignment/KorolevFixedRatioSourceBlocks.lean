/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevFixedRatioPrimePopulation
import NField.Alignment.KorolevSourceWindowDensity

/-! # Uniform fixed-ratio block populations above the contiguous source edge -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevFixedRatioSourceBlocks
open Filter KorolevPrimeWindows KorolevSourceEnvelope
open scoped Topology

/-- The lowest contiguous endpoint absorbs the modulus logarithm at quadratic size. -/
theorem contiguous_endpoint_ge {L : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hsize : 576 * (k : ℝ)^2 ≤ L) :
    8 * L ≤ upperEndpoint L (k+1) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 2*(k : ℝ)+1 := by positivity
  have hL : 0 ≤ L := (by positivity : 0 ≤ 576*(k : ℝ)^2).trans hsize
  have hquad : 64*(2*(k : ℝ)+1)^2 ≤ L := by nlinarith
  have ht : 0 ≤ L/(2*(k : ℝ)+1) := div_nonneg hL hd.le
  have he := Real.quadratic_le_exp_of_nonneg ht
  have hprod : 64*(2*(k : ℝ)+1) ≤ L/(2*(k : ℝ)+1) :=
    (le_div_iff₀ hd).mpr (by nlinarith only [hquad])
  have hsq := mul_le_mul_of_nonneg_right hprod ht
  have hcancel : (2*(k : ℝ)+1)*(L/(2*(k : ℝ)+1)) = L := by field_simp
  have hexp : 32*L ≤ Real.exp (L/(2*(k : ℝ)+1)) := by
    nlinarith only [he, hsq, hcancel, ht]
  unfold upperEndpoint
  push_cast
  convert (show 8*L ≤ Real.exp (L/(2*(k : ℝ)+1))/4 by linarith) using 1 <;> ring_nf

/-- A fixed block width is below the logarithm of every allowed lower endpoint. -/
theorem contiguous_log_ge {L A : ℝ} {k : ℕ}
    (hsize : (A + Real.log 4)*(2*(k : ℝ)+1) ≤ L) :
    A ≤ Real.log (upperEndpoint L (k+1)) := by
  rw [log_upper]
  push_cast
  have hd : 0 < 2*(k : ℝ)+1 := by positivity
  have h := (le_div_iff₀ hd).mpr hsize
  convert (show A ≤ L/(2*(k : ℝ)+1)-Real.log 4 by linarith) using 1 <;> ring_nf

/-- Actual populations in every fixed-ratio subinterval above the lowest source edge. -/
theorem block_population {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) {A u v : ℝ}
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A)
    (hsize : 576*(k : ℝ)^2 ≤ Real.log m)
    (hlogsize : (A+Real.log 4)*(2*(k : ℝ)+1) ≤ Real.log m)
    (hu : upperEndpoint (Real.log m) (k+1) ≤ u) (huv : u ≤ v)
    (hwidth : Real.log v = Real.log u + A) :
    u*A/(4*Real.log v) ≤
      (((KorolevPrimeIntervals.intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : 1 ≤ Real.log m := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hedge := contiguous_endpoint_ge hk hsize
  have hu2 : 2 ≤ u := by linarith
  have hbase := contiguous_log_ge hlogsize
  have hlog : A ≤ Real.log u := hbase.trans
    (Real.log_le_log (upperEndpoint_pos _ _) hu)
  apply KorolevFixedRatioPrimePopulation.coprime_population_lower hm hu2 huv
    (by linarith) herror hwidth hlog
  have hmul := mul_le_mul_of_nonneg_right hA (show 0 ≤ u by linarith)
  nlinarith

/-- One fixed width works uniformly for every index below the source envelope. -/
theorem eventual_envelope_block_population (A : ℝ) (hA : 1 ≤ A)
    (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ t : ℝ in atTop, ∀ m : ℕ, 0 < m → Real.log m = Real.exp t →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ envelope t → ∀ u v : ℝ,
      upperEndpoint (Real.exp t) (k+1) ≤ u → u ≤ v →
      Real.log v = Real.log u + A →
      u*A/(4*Real.log v) ≤
        (((KorolevPrimeIntervals.intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) := by
  filter_upwards [eventual_envelope_small 576,
    eventual_envelope_small (3*(A+Real.log 4))] with t hs hl m hm hcoord k hk hkenv u v hu huv hw
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hkenv 2
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsize : 576*(k : ℝ)^2 ≤ Real.exp t := by
    have hh := (div_le_iff₀ (Real.exp_pos t)).mp hs
    nlinarith only [hsq, hh]
  have hlogsize : (A+Real.log 4)*(2*(k : ℝ)+1) ≤ Real.exp t := by
    have hh := (div_le_iff₀ (Real.exp_pos t)).mp hl
    have hsmall : 2*(k : ℝ)+1 ≤ 3*(k : ℝ)^2 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
    calc
      _ ≤ (A+Real.log 4)*(3*(k : ℝ)^2) := mul_le_mul_of_nonneg_left hsmall (by linarith)
      _ ≤ 3*(A+Real.log 4)*(envelope t)^2 := by nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3*(A+Real.log 4) by linarith)]
      _ ≤ Real.exp t := by simpa only [one_mul] using hh
  rw [← hcoord] at hsize hlogsize hu
  exact block_population hm hk hA herror hsize hlogsize hu huv hw

/-- Actual block populations for both rounded source-index families. -/
theorem eventual_source_block_population (c : ℝ) (hc : 0 ≤ c) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℝ, (4/5)*t+5*Real.log t ≤ z → z ≤ t →
      ∀ m : ℕ, 0 < m → Real.log m = Real.exp t → ∀ k : ℕ, 1 ≤ k →
      (k ≤ KorolevWindowParameters.pLast t z c ∨ k ≤ KorolevWindowParameters.qLast t z c) →
      ∀ u v : ℝ, upperEndpoint (Real.exp t) (k+1) ≤ u → u ≤ v →
      Real.log v = Real.log u + A →
      u*A/(4*Real.log v) ≤
        (((KorolevPrimeIntervals.intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) := by
  filter_upwards [eventual_envelope_block_population A hA herror,
    KorolevSourceWindowDensity.eventual_index_envelope c hc]
    with t hb hi z hz hzt m hm hcoord k hk hlast u v hu huv hw
  have hii := hi z hz hzt
  have hkenv : (k : ℝ) ≤ envelope t := by
    rcases hlast with h | h
    · have hh : (k : ℝ) ≤ KorolevWindowParameters.pLast t z c := by exact_mod_cast h
      linarith [hii.1]
    · have hh : (k : ℝ) ≤ KorolevWindowParameters.qLast t z c := by exact_mod_cast h
      linarith [hii.2]
  exact hb m hm hcoord k hk hkenv u v hu huv hw

/-- The block population estimate throughout the paper's actual integer-modulus range. -/
theorem eventual_source_block_population_nat (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ m : ℕ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k : ℕ, 1 ≤ k →
      (k ≤ KorolevWindowParameters.pLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C) ∨
       k ≤ KorolevWindowParameters.qLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C)) →
      ∀ u v : ℝ, upperEndpoint (Real.log m) (k+1) ≤ u → u ≤ v →
      Real.log v = Real.log u + A →
      u*A/(4*Real.log v) ≤
        (((KorolevPrimeIntervals.intervalPrimes u v).filter (fun p => p.Coprime m)).card : ℝ) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hlog
  filter_upwards [ht.eventually (eventual_source_block_population (Real.log C)
    (Real.log_nonneg hC) A hA herror), hlog.eventually_gt_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with m hb hL hm x hlo hhi k hk hlast u v hu huv hw
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  obtain ⟨_, _, hulo, hule⟩ := KorolevSourceWindowCount.source_log_range hmR hL hlo hhi
  have hcoord : Real.log (m : ℝ) = Real.exp (Real.log (Real.log m)) :=
    (Real.exp_log (by linarith : 0 < Real.log (m : ℝ))).symm
  have hu' : upperEndpoint (Real.exp (Real.log (Real.log m))) (k+1) ≤ u := by
    simpa only [← hcoord] using hu
  exact hb (Real.log (Real.log x)) hulo hule m hmpos hcoord k hk hlast u v hu' huv hw

end NField.Alignment.KorolevFixedRatioSourceBlocks
