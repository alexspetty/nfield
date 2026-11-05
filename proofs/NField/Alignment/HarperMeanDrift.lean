/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperMeanDriftLocal

/-!
# Uniform cumulative leading-mean drift

Reversed-block growth sums the Mertens errors geometrically. The literal
small-frequency condition gives a summable reciprocal 4/3-power error.
Every initial sum of the leading means differs from its number of blocks
by one fixed constant, independent of family length and the first endpoint.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperMeanDrift
open scoped BigOperators Topology
open Filter Set HarperPrimeBlocks HarperPrimeBlockGrowth HarperPrimeRangeCharacteristic
  HarperPrimeBlockVariance HarperGaussianSmoothingScales HarperPathGrid HarperMeanDriftLocal

def frequencyError (j : ℕ) : ℝ := 1/((j : ℝ)+1)^(4/3 : ℝ)
def frequencyErrorTotal : ℝ := ∑' j : ℕ, frequencyError j
def cumulativeMeanConstant : ℝ := 2*meanMertensConstant+(3/4)*frequencyErrorTotal

theorem frequencyError_summable : Summable frequencyError := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (4/3)).mpr (by norm_num)
  have habs (n : ℕ) : |(n : ℝ)+1| = (n : ℝ)+1 := abs_of_nonneg (by positivity)
  unfold frequencyError
  simpa only [habs] using h

theorem frequencyErrorTotal_nonneg : 0 ≤ frequencyErrorTotal :=
  tsum_nonneg (fun j => by unfold frequencyError; positivity)

theorem cumulativeMeanConstant_pos : 0 < cumulativeMeanConstant := by
  unfold cumulativeMeanConstant
  nlinarith [meanMertensConstant_pos,frequencyErrorTotal_nonneg]

theorem finite_frequencyError_sum (n : ℕ) :
    (∑ i : Fin n, frequencyError i.val) ≤ frequencyErrorTotal := by
  rw [Fin.sum_univ_eq_sum_range]
  exact Summable.sum_le_tsum _ (fun j _ => by unfold frequencyError; positivity)
    frequencyError_summable

theorem reversed_inverse_log_sum {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l)
    (hfirst : 1 ≤ Real.log (blockUpper x (l 0))) :
    (∑ i : Fin (n+1), 1/Real.log (blockUpper x (l i))) ≤ 2 := by
  have hi (i : Fin (n+1)) : 1/Real.log (blockUpper x (l i)) ≤ (1/(2 : ℝ))^i.val := by
    have he : (2 : ℝ)^i.val ≤ Real.exp (i.val : ℝ) := by
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo i.val)
    have hg := reversed_block_log_growth hx hl i
    have hpow : (2 : ℝ)^i.val ≤ Real.log (blockUpper x (l i)) := by
      have hh := mul_le_mul_of_nonneg_left hfirst (Real.exp_nonneg (i.val : ℝ))
      nlinarith
    have h := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
    simpa only [one_div_pow] using h
  calc
    _ ≤ ∑ i : Fin (n+1), (1/(2 : ℝ))^i.val := Finset.sum_le_sum (fun i _ => hi i)
    _ ≤ 2 := by simpa only [Fin.sum_univ_eq_sum_range] using sum_geometric_two_le (n+1)

theorem eventual_mean_parameters :
    ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧ 2 ≤ sourceCutoff X ∧
      blockVariance X ≤ 3/4 ∧ 1 ≤ Real.log X := by
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1)),
    eventual_cutoff_conditions,eventual_blockVariance_bounds] with X hX hcut hv
  have hlog := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hX)
  rw [Real.log_exp] at hlog
  exact ⟨(le_max_left _ _).trans hX,hcut.1,hv.2,hlog⟩

theorem source_cumulative_mean_error :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ t : Fin (n+1) → ℝ,
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        ∀ j, |partialSum (fun i => rangeMean (primeBlock x (l i)) (fun _ => t i)) j-
          ((j.val : ℝ)+1)| ≤ cumulativeMeanConstant := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp eventual_mean_parameters
  refine ⟨X₀,fun x hx n l hl hfirst t ht j => ?_⟩
  have hi (i : Fin (n+1)) := hX₀ _
    (hfirst.trans (blockUpper_antitone hx.le (hl.antitone (Fin.zero_le i))))
  have hm (i : Fin (n+1)) :
      |rangeMean (primeBlock x (l i)) (fun _ => t i)-1| ≤
        meanMertensConstant/Real.log (blockUpper x (l i))+(3/4)*frequencyError i.val := by
    have h := source_mean_error hx (l i) (t i) (hi i).1 (hi i).2.1 (hi i).2.2.1
    have hs := small_frequency_square (by linarith [(hi i).2.2.2])
      (by positivity : (0 : ℝ) < (i.val : ℝ)+1) (ht i)
    have he : ((i.val : ℝ)+1)^(-(4/3 : ℝ)) = frequencyError i.val := by
      rw [Real.rpow_neg (by positivity)]
      simp only [frequencyError,one_div]
    rw [he] at hs
    linarith
  have hlog := reversed_inverse_log_sum hx hl (hi 0).2.2.2
  have hfreq := finite_frequencyError_sum (n+1)
  have hsum : (∑ i : Fin (n+1),
      |rangeMean (primeBlock x (l i)) (fun _ => t i)-1|) ≤ cumulativeMeanConstant := by
    calc
      _ ≤ ∑ i : Fin (n+1), (meanMertensConstant/Real.log (blockUpper x (l i))+
          (3/4)*frequencyError i.val) := Finset.sum_le_sum (fun i _ => hm i)
      _ = meanMertensConstant*(∑ i : Fin (n+1), 1/Real.log (blockUpper x (l i)))+
          (3/4)*∑ i : Fin (n+1), frequencyError i.val := by
        simp only [div_eq_mul_inv,Finset.sum_add_distrib,Finset.mul_sum,one_mul]
      _ ≤ cumulativeMeanConstant := by
        unfold cumulativeMeanConstant
        nlinarith [meanMertensConstant_pos]
  have hcount : (∑ i ∈ Finset.Iic j, (1 : ℝ)) = (j.val : ℝ)+1 := by
    simp [Fin.card_Iic]
  rw [← hcount]
  unfold partialSum
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => abs_nonneg _)).trans hsum)

end NField.Alignment.HarperMeanDrift
