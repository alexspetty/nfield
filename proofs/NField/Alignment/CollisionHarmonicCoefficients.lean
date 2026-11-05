/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHarmonicRootSeries
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Harmonic derivative coefficients

The shifted coefficients H_(n+1)/(n+2) decrease to zero. The finite
Cauchy-product coefficient identity is proved directly from the harmonic
sum and reflection of the finite range.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicCoefficients

open scoped BigOperators Topology
open Filter Finset
open CollisionMassReadout CollisionAmplitudeArithmetic

def harmonicFirstKernel (n : ℕ) : ℝ := (harmonic (n-1) : ℝ)/(n : ℝ)

def shiftedHarmonicFirst (n : ℕ) : ℝ := (harmonic (n+1) : ℝ)/(n+2 : ℕ)

theorem harmonic_real_succ (n : ℕ) :
    (harmonic (n+1) : ℝ)=(harmonic n : ℝ)+1/(n+1 : ℕ) := by
  simp [harmonic_succ,one_div]

theorem harmonic_real_monotone : Monotone (fun n => (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_real_succ]
  exact le_add_of_nonneg_right (by positivity)

theorem harmonic_real_one_le {n : ℕ} (hn : 1≤n) : 1≤(harmonic n : ℝ) := by
  simpa [harmonic_succ] using harmonic_real_monotone hn

theorem harmonic_real_le_index (n : ℕ) : (harmonic n : ℝ)≤(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_real_succ]
    have hi : 1/((n+1 : ℕ) : ℝ)≤1 := by
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.succ_pos n
    push_cast
    push_cast at hi
    linarith

theorem harmonicFirstKernel_nonneg (n : ℕ) : 0 ≤ harmonicFirstKernel n :=
  div_nonneg (harmonic_nonneg _) (Nat.cast_nonneg n)

theorem harmonicFirstKernel_le_one (n : ℕ) : harmonicFirstKernel n≤1 := by
  by_cases hn : n=0
  · simp [hn,harmonicFirstKernel]
  · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).2
    exact (harmonic_real_le_index (n-1)).trans (Nat.cast_le.mpr (Nat.sub_le n 1))

theorem shiftedHarmonicFirst_eq (n : ℕ) :
    shiftedHarmonicFirst n=harmonicFirstKernel (n+2) := by
  simp [shiftedHarmonicFirst,harmonicFirstKernel]

theorem shiftedHarmonicFirst_nonneg (n : ℕ) : 0 ≤ shiftedHarmonicFirst n :=
  div_nonneg (harmonic_nonneg _) (by positivity)

theorem shiftedHarmonicFirst_antitone : Antitone shiftedHarmonicFirst := by
  apply antitone_nat_of_succ_le
  intro n
  unfold shiftedHarmonicFirst
  rw [harmonic_real_succ]
  have hH := harmonic_real_one_le (Nat.succ_pos n)
  have hn2 : (0 : ℝ)<((n+2 : ℕ) : ℝ) := by positivity
  have hn3 : (0 : ℝ)<((n+1+2 : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ hn3 hn2).2
  push_cast
  have hn2' : (n : ℝ)+2≠0 := by positivity
  field_simp
  nlinarith

theorem harmonic_over_index_tendsto_zero :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).cesaro
  simpa [harmonic,Rat.cast_sum,div_eq_mul_inv,mul_comm] using h

theorem shiftedHarmonicFirst_tendsto_zero : Tendsto shiftedHarmonicFirst atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (harmonic (n+2) : ℝ)/((n+2 : ℕ) : ℝ))
      atTop (𝓝 0) := harmonic_over_index_tendsto_zero.comp (tendsto_add_atTop_nat 2)
  apply squeeze_zero shiftedHarmonicFirst_nonneg _ hu
  intro n
  exact div_le_div_of_nonneg_right
    (harmonic_real_monotone (by omega : n+1≤n+2)) (by positivity)

theorem harmonicFirstKernel_eq_mul (n : ℕ) :
    harmonicFirstKernel n=harmonicKernel n*(n : ℝ) := by
  by_cases hn : n=0
  · simp [hn,harmonicFirstKernel,harmonicKernel]
  · unfold harmonicFirstKernel harmonicKernel
    have hnR : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr hn
    field_simp

theorem reciprocal_convolution (n : ℕ) :
    (∑ k ∈ Finset.range (n+1),
      1/(((k+1 : ℕ) : ℝ)*((n-k+1 : ℕ) : ℝ)))=2*shiftedHarmonicFirst n := by
  have hterm (k : ℕ) (hk : k∈Finset.range (n+1)) :
      1/(((k+1 : ℕ) : ℝ)*((n-k+1 : ℕ) : ℝ))=
        (1/((k+1 : ℕ) : ℝ)+1/((n-k+1 : ℕ) : ℝ))/((n+2 : ℕ) : ℝ) := by
    have hkn : k≤n := by simpa using Finset.mem_range.mp hk
    have hsum : ((k+1 : ℕ) : ℝ)+((n-k+1 : ℕ) : ℝ)=((n+2 : ℕ) : ℝ) := by
      exact_mod_cast (show (k+1)+(n-k+1)=n+2 by omega)
    have hk0 : ((k+1 : ℕ) : ℝ)≠0 := by positivity
    have hnk0 : ((n-k+1 : ℕ) : ℝ)≠0 := by positivity
    have hn0 : ((n+2 : ℕ) : ℝ)≠0 := by positivity
    field_simp
    nlinarith
  rw [Finset.sum_congr rfl hterm,← Finset.sum_div,Finset.sum_add_distrib]
  have hreflect : (∑ k ∈ Finset.range (n+1), 1/((n-k+1 : ℕ) : ℝ))=
      ∑ k ∈ Finset.range (n+1), 1/((k+1 : ℕ) : ℝ) := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun k : ℕ => 1/((k+1 : ℕ) : ℝ)) (n+1)
  rw [hreflect]
  have hsum : (∑ k ∈ Finset.range (n+1), 1/((k+1 : ℕ) : ℝ))=(harmonic (n+1) : ℝ) := by
    simp [harmonic]
  rw [hsum,shiftedHarmonicFirst]
  ring

end NField.Alignment.CollisionHarmonicCoefficients
