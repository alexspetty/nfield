/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.InverseResiduePrefixCompletion

/-! # Sawtooth frequency grouping for arbitrary nonnegative gcd weights -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SawtoothGcdWeightedFrequency
open CarryBoundarySpectra DedekindFourierMoment DedekindInverseResidueTransform
  DedekindReciprocity
open scoped BigOperators Classical

/-- Grouping a frequency by its gcd cancels that gcd against circular distance. -/
theorem grouped_frequency_bound {q g : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hgdiv : g ∣ q) (hgpos : 0 < g) (hQ : 2 ≤ q/g) {W : ℕ → ℝ} (hW : 0 ≤ W g) :
    (∑ u ∈ (Finset.Ico 1 (q/g)).filter (fun u => u.Coprime (q/g)),
      ‖sawtoothFourier q (g*u)‖ * W ((g*u).gcd q)) ≤
        (q : ℝ)/2*(harmonic q : ℝ)*(W g/(g : ℝ)) := by
  have hqfactor : q = g*(q/g) := (Nat.mul_div_cancel' hgdiv).symm
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  have hpoint : ∀ u ∈ (Finset.Ico 1 (q/g)).filter (fun u => u.Coprime (q/g)),
      ‖sawtoothFourier q (g*u)‖ * W ((g*u).gcd q) ≤
        ((q : ℝ)/4*(W g/(g : ℝ)))*(1/(circularDistance (q/g) u : ℝ)) := by
    intro u hu
    have huI := Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1
    have hcop := (Finset.mem_filter.mp hu).2
    have hguPos : 0 < g*u := Nat.mul_pos hgpos huI.1
    have hguLt : g*u < q := by rw [hqfactor]; exact (Nat.mul_lt_mul_left hgpos).2 huI.2
    have hgcd : (g*u).gcd q = g := by rw [hqfactor, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    have hdist : circularDistance q (g*u) = g*circularDistance (q/g) u := by
      conv_lhs => rw [hqfactor]
      exact circularDistance_mul_left (Nat.le_of_lt huI.2)
    have hdistPos : (0 : ℝ) < circularDistance (q/g) u := by
      exact_mod_cast circularDistance_pos huI.1 huI.2
    have hf := norm_sawtoothFourier_le (by omega : 0 < q) hguPos hguLt
    rw [hdist] at hf
    rw [hgcd]
    calc
      _ ≤ ((q : ℝ)/(4*((g*circularDistance (q/g) u : ℕ) : ℝ)))*W g :=
        mul_le_mul_of_nonneg_right hf hW
      _ = _ := by
        push_cast
        field_simp
  calc
    _ ≤ ∑ u ∈ (Finset.Ico 1 (q/g)).filter (fun u => u.Coprime (q/g)),
        ((q : ℝ)/4*(W g/(g : ℝ)))*(1/(circularDistance (q/g) u : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ u ∈ Finset.Ico 1 (q/g),
        ((q : ℝ)/4*(W g/(g : ℝ)))*(1/(circularDistance (q/g) u : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u hu hn
      positivity
    _ = ((q : ℝ)/4*(W g/(g : ℝ))) *
        ∑ u ∈ Finset.Ico 1 (q/g), 1/(circularDistance (q/g) u : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ((q : ℝ)/4*(W g/(g : ℝ)))*(2*(harmonic (q/g) : ℝ)) := by
      gcongr
      exact circularReciprocal_sum_le_harmonic (by omega)
    _ ≤ ((q : ℝ)/4*(W g/(g : ℝ)))*(2*(harmonic q : ℝ)) := by
      gcongr
      exact_mod_cast harmonic_cast_mono (Nat.div_le_self q g)
    _ = _ := by ring

/-- The full natural-frequency sum is controlled by the reciprocal divisor-weight sum. -/
theorem natural_frequency_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (W : ℕ → ℝ) (hW : ∀ g ∈ q.divisors, 0 ≤ W g) :
    (∑ n ∈ Finset.Ico 1 q, ‖sawtoothFourier q n‖ * W (n.gcd q)) ≤
      (q : ℝ)/2*(harmonic q : ℝ)*∑ g ∈ q.divisors, W g/(g : ℝ) := by
  rw [sum_Ico_gcd_unit_reindex hq]
  calc
    _ ≤ ∑ g ∈ q.divisors.filter (fun g => 2 ≤ q/g),
        (q : ℝ)/2*(harmonic q : ℝ)*(W g/(g : ℝ)) := by
      apply Finset.sum_le_sum
      intro g hg
      have hd := (Finset.mem_filter.mp hg).1
      exact grouped_frequency_bound hq (Nat.mem_divisors.mp hd).1
        (Nat.pos_of_mem_divisors hd) (Finset.mem_filter.mp hg).2 (hW g hd)
    _ ≤ ∑ g ∈ q.divisors, (q : ℝ)/2*(harmonic q : ℝ)*(W g/(g : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro g hg hn
      have hw := hW g hg
      have hH : (0 : ℝ) ≤ harmonic q := by
        exact_mod_cast (show (0 : ℚ) ≤ harmonic q by unfold harmonic; positivity)
      positivity
    _ = _ := by rw [Finset.mul_sum]

/-- The intrinsic cyclic sum equals the actual nonzero natural-frequency sum; the zero coefficient vanishes. -/
theorem cyclic_eq_natural {q : ℕ} [NeZero q] (hq : 2 ≤ q) (W : ℕ → ℝ) :
    (∑ j : ZMod q, ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ * W (j.val.gcd q)) =
      ∑ n ∈ Finset.Ico 1 q, ‖sawtoothFourier q n‖ * W (n.gcd q) := by
  let w : ℕ → ℝ := fun n => if n=0 then 0 else ‖sawtoothFourier q n‖*W (n.gcd q)
  have hzero : ZMod.dft (centeredSawtooth : ZMod q → ℂ) (0 : ZMod q) = 0 := by
    have hz := sawtoothFourier_zero (by omega : 0 < q)
    rw [sawtoothFourier_eq_dft] at hz
    simpa using hz
  calc
    _ = ∑ n : Fin q, w n.val := by
      rw [← (ZMod.finEquiv q).toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro n hn
      have he : ((ZMod.finEquiv q).toEquiv n : ZMod q) = (n.val : ZMod q) := by
        simpa using ConductorDepthSawtooth.finEquiv_eq_natCast n
      rw [he, ZMod.val_natCast_of_lt n.isLt]
      unfold w
      by_cases hn0 : n.val=0
      · simp [hn0, hzero]
      · rw [if_neg hn0, norm_dft_centeredSawtooth_eq, ZMod.val_natCast_of_lt n.isLt]
    _ = ∑ n ∈ Finset.range q, w n := Fin.sum_univ_eq_sum_range w q
    _ = _ := by
      rw [sum_range_eq_sum_Ico_one w (by omega)]
      · apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := by have := (Finset.mem_Ico.mp hn).1; omega
        simp only [w, hn0, ite_false]
      · simp [w]

/-- Arbitrary nonnegative gcd weights retain their exact reciprocal divisor cost. -/
theorem cyclic_frequency_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (W : ℕ → ℝ) (hW : ∀ g ∈ q.divisors, 0 ≤ W g) :
    (∑ j : ZMod q, ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ * W (j.val.gcd q)) ≤
      (q : ℝ)/2*(harmonic q : ℝ)*∑ g ∈ q.divisors, W g/(g : ℝ) := by
  rw [cyclic_eq_natural hq W]
  exact natural_frequency_bound hq W hW

/-- The small gcd exponent from the actual prime-block norm yields a near-one reciprocal divisor sum. -/
theorem rpow_frequency_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q) (ε : ℝ) :
    (∑ j : ZMod q, ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
      (j.val.gcd q : ℝ)^ε)/(q : ℝ) ≤
      (harmonic q : ℝ)/2*∑ g ∈ q.divisors, (g : ℝ)^(ε-1) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hh := cyclic_frequency_bound hq (fun g => (g : ℝ)^ε)
    (fun g hg => Real.rpow_nonneg (Nat.cast_nonneg g) ε)
  have he : (∑ g ∈ q.divisors, (g : ℝ)^ε/(g : ℝ)) =
      ∑ g ∈ q.divisors, (g : ℝ)^(ε-1) := by
    apply Finset.sum_congr rfl
    intro g hg
    exact (Real.rpow_sub_one (by exact_mod_cast (Nat.pos_of_mem_divisors hg).ne' : (g : ℝ) ≠ 0) ε).symm
  rw [he] at hh
  apply (div_le_iff₀ hqR).mpr
  nlinarith only [hh]

end NField.Alignment.SawtoothGcdWeightedFrequency
