/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryRealFractionalParts

/-! # The literal logarithmically weighted fractional-part sum -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealLogWeightedFractionalParts
open scoped BigOperators Topology Classical
open Filter SecondaryRealFractionalParts

def logWeightedFractionalParts (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,Real.log n/(n:ℝ)*Int.fract (X/n)

theorem harmonic_predecessor_log_error {n : ℕ} (hn : 1≤n) :
    0≤(harmonic (n-1):ℝ)-Real.log n ∧ (harmonic (n-1):ℝ)-Real.log n≤1 := by
  have hlow := log_add_one_le_harmonic (n-1)
  rw [Nat.sub_add_cancel hn] at hlow
  have hmono : (harmonic (n-1):ℝ)≤(harmonic n:ℝ) := by
    have he := harmonic_succ (n-1)
    rw [Nat.sub_add_cancel hn] at he
    have hr := congrArg (fun q : ℚ => (q:ℝ)) he
    push_cast at hr
    have hi : 0≤(n:ℝ) := Nat.cast_nonneg n
    have hinv := inv_nonneg.mpr hi
    linarith
  have hupper := harmonic_le_one_add_log n
  constructor <;> linarith

theorem harmonic_log_weight_gap {X : ℝ} (hX : 1≤X) :
    |weightedFractionalParts X-logWeightedFractionalParts X|≤1+Real.log X := by
  unfold weightedFractionalParts logWeightedFractionalParts
  rw [← Finset.sum_sub_distrib]
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) :
      |(harmonic (n-1):ℝ)/(n:ℝ)*Int.fract (X/n)-
        Real.log n/(n:ℝ)*Int.fract (X/n)|≤(n:ℝ)⁻¹ := by
    have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hh := harmonic_predecessor_log_error (Finset.mem_Icc.mp hn).1
    have he : (harmonic (n-1):ℝ)/(n:ℝ)*Int.fract (X/n)-
        Real.log n/(n:ℝ)*Int.fract (X/n)=
        ((harmonic (n-1):ℝ)-Real.log n)*Int.fract (X/n)/(n:ℝ) := by ring
    have hfrac0 := Int.fract_nonneg (X/n)
    have hfrac1 := (Int.fract_lt_one (X/n)).le
    rw [he,abs_of_nonneg (div_nonneg (mul_nonneg hh.1 hfrac0) hn0.le)]
    have hm := mul_le_mul hh.2 hfrac1 hfrac0 (by norm_num : (0:ℝ)≤1)
    have hd := div_le_div_of_nonneg_right hm hn0.le
    simpa only [one_mul,one_div] using hd
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        |(harmonic (n-1):ℝ)/(n:ℝ)*Int.fract (X/n)-Real.log n/(n:ℝ)*Int.fract (X/n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,(n:ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (harmonic ⌊X⌋₊:ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := harmonic_floor_le_one_add_log X hX

/-- Title: `Logarithmically weighted fractional parts at real cutoffs`. -/
theorem log_weighted_fractional_parts :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ X : ℝ in atTop,
      |logWeightedFractionalParts X-(1/4:ℝ)*Real.log X^2|≤
        C*(Real.log X)^(5/3:ℝ) := by
  obtain ⟨C,hC,h⟩ := weighted_fractional_parts
  refine ⟨C+2,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (3:ℝ)] with X hbound hX
  have hg := harmonic_log_weight_gap (by linarith : 1≤X)
  have hl : 1≤Real.log X :=
    (by linarith [Real.log_three_gt_d9] : (1:ℝ)≤Real.log 3).trans
      (Real.log_le_log (by norm_num) hX)
  have hp := Real.self_le_rpow_of_one_le hl (by norm_num : (1:ℝ)≤5/3)
  change Real.log X≤(Real.log X)^(5/3:ℝ) at hp
  have ht := abs_sub_le (logWeightedFractionalParts X) (weightedFractionalParts X)
    ((1/4:ℝ)*Real.log X^2)
  have hg' : |logWeightedFractionalParts X-weightedFractionalParts X|≤1+Real.log X := by
    rwa [abs_sub_comm]
  change |weightedFractionalParts X-(1/4:ℝ)*Real.log X^2|≤
    C*(Real.log X)^(5/3:ℝ) at hbound
  nlinarith

end NField.Alignment.RealLogWeightedFractionalParts
