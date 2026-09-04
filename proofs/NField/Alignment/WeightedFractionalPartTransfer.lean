/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ReducedHarmonicMobius
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Weighted fractional-part transfer

This module isolates the published Saffari--Vaughan distribution estimate on
the exact rational arguments used by the finite Möbius transform.  All
integration and finite partial-summation steps are carried out below that
source boundary.
-/

namespace NField.Alignment.WeightedFractionalPartTransfer

open scoped BigOperators Interval
open Set MeasureTheory
open NField.Alignment.ReducedHarmonicMobius
open NField.Alignment.SecondaryCapacityLedger

/-- Logarithmically weighted distribution function of the fractional parts
`{N/(d*n)}`. -/
noncomputable def weightedFractionalDistribution
    (N d Y : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹ *
    if quotientFractionalPart N d n < α then 1 else 0

/-- The `log(X)^(2/3)` error scale in the published distribution theorem,
with the exact rational argument `X=N/d`. -/
noncomputable def fractionalDistributionScale (N d : ℕ) : ℝ :=
  Real.rpow (Real.log ((N : ℝ) / (d : ℝ))) (2 / 3 : ℝ)

/-- Saffari--Vaughan's logarithmically weighted distribution theorem, stated
on the exact rational arguments consumed here.  This is the external source
input, rather than the later weighted-moment conclusion. -/
def SaffariVaughanDistributionEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N d Y α,
    0 < d → 3 * d ≤ N → 2 ≤ Y → d * Y ≤ N →
    0 ≤ α → α ≤ 1 →
    |weightedFractionalDistribution N d Y α -
        α * Real.log Y| ≤ C * fractionalDistributionScale N d

/-- The first fractional moment used in partial summation. -/
noncomputable def fractionalFirstMoment (N d Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y,
    (n : ℝ)⁻¹ * quotientFractionalPart N d n

theorem quotientFractionalPart_nonneg (N : ℕ) {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    0 ≤ quotientFractionalPart N d n := by
  unfold quotientFractionalPart
  positivity

theorem quotientFractionalPart_lt_one (N : ℕ) {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    quotientFractionalPart N d n < 1 := by
  have hdn : 0 < d * n := Nat.mul_pos hd hn
  have hmod : N % (d * n) < d * n := Nat.mod_lt N hdn
  unfold quotientFractionalPart
  exact (div_lt_one (by exact_mod_cast hdn)).2 (by exact_mod_cast hmod)

/-- Integral of one threshold indicator, including the midpoint convention at
the threshold. -/
theorem integral_threshold_indicator
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ α in (0 : ℝ)..1, if u < α then (1 : ℝ) else 0) = 1 - u := by
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu0, hu1⟩
  calc
    (∫ α in (0 : ℝ)..1, if u < α then (1 : ℝ) else 0) =
        ∫ α in (0 : ℝ)..1,
          1 - {x : ℝ | x ≤ u}.indicator (fun _ => (1 : ℝ)) α := by
      apply intervalIntegral.integral_congr
      intro α _hα
      by_cases hle : α ≤ u
      · simp [hle, not_lt.mpr hle]
      · simp [hle, lt_of_not_ge hle]
    _ = (∫ _α in (0 : ℝ)..1, (1 : ℝ)) -
        ∫ α in (0 : ℝ)..1,
          {x : ℝ | x ≤ u}.indicator (fun _ => (1 : ℝ)) α := by
      have hi : IntervalIntegrable
          ({x : ℝ | x ≤ u}.indicator fun _ => (1 : ℝ)) volume 0 1 := by
        constructor
        · exact intervalIntegrable_const.1.indicator measurableSet_Iic
        · exact intervalIntegrable_const.2.indicator measurableSet_Iic
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    _ = 1 - u := by
      rw [intervalIntegral.integral_indicator hu]
      simp

theorem intervalIntegrable_threshold_indicator (u : ℝ) :
    IntervalIntegrable
      (fun α => if u < α then (1 : ℝ) else 0) volume 0 1 := by
  have hi : IntervalIntegrable
      ((Set.Ioi u).indicator fun _ => (1 : ℝ)) volume 0 1 := by
    constructor
    · exact intervalIntegrable_const.1.indicator measurableSet_Ioi
    · exact intervalIntegrable_const.2.indicator measurableSet_Ioi
  change IntervalIntegrable
    ((Set.Ioi u).indicator fun _ => (1 : ℝ)) volume 0 1
  exact hi

/-- Integrating the finite distribution function gives harmonic mass minus
the first fractional moment. -/
theorem integral_weightedFractionalDistribution
    {N d Y : ℕ} (hd : 0 < d) :
    (∫ α in (0 : ℝ)..1, weightedFractionalDistribution N d Y α) =
      (harmonic Y : ℝ) - fractionalFirstMoment N d Y := by
  unfold weightedFractionalDistribution fractionalFirstMoment
  rw [intervalIntegral.integral_finsetSum]
  · rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [intervalIntegral.integral_const_mul]
    rw [integral_threshold_indicator
      (quotientFractionalPart_nonneg N hd hnpos)
      (quotientFractionalPart_lt_one N hd hnpos).le]
    ring
  · intro n hn
    exact (intervalIntegrable_threshold_indicator
      (quotientFractionalPart N d n)).const_mul _

/-- Uniform first-moment consequence of the published distribution theorem. -/
def FractionalFirstMomentEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N d Y,
    0 < d → 3 * d ≤ N → 2 ≤ Y → d * Y ≤ N →
    |fractionalFirstMoment N d Y - (1 / 2 : ℝ) * Real.log Y| ≤
      C * (1 + fractionalDistributionScale N d)

theorem fractionalDistributionScale_nonneg
    {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    0 ≤ fractionalDistributionScale N d := by
  unfold fractionalDistributionScale
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    simpa using (show (d : ℝ) ≤ (N : ℝ) by exact_mod_cast hdN)
  exact Real.rpow_nonneg (Real.log_nonneg hratio) _

/-- Saffari--Vaughan's uniform distribution estimate implies the exact
rational-argument first-moment estimate by integrating the threshold
distribution. -/
theorem fractional_first_moment_of_saffari_vaughan
    (hSV : SaffariVaughanDistributionEstimate) :
    FractionalFirstMomentEstimate := by
  rcases hSV with ⟨C, hC, hSV⟩
  refine ⟨C + 1, by positivity, ?_⟩
  intro N d Y hd hNd hY hYNd
  have hdistIntegrable : IntervalIntegrable
      (weightedFractionalDistribution N d Y) volume 0 1 := by
    unfold weightedFractionalDistribution
    have hsum := IntervalIntegrable.sum (Finset.Icc 1 Y) fun n hn =>
      (intervalIntegrable_threshold_indicator
        (quotientFractionalPart N d n)).const_mul ((n : ℝ)⁻¹)
    apply hsum.congr
    intro α _hα
    simp only [Finset.sum_apply]
  have hlinearIntegrable : IntervalIntegrable
      (fun α : ℝ => α * Real.log Y) volume 0 1 := by
    exact (continuous_id.mul continuous_const).intervalIntegrable 0 1
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1)
    (f := fun α => weightedFractionalDistribution N d Y α -
      α * Real.log Y)
    (C := C * fractionalDistributionScale N d) (by
      intro α hα
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hα
      simpa [Real.norm_eq_abs] using
        hSV N d Y α hd hNd hY hYNd hα.1.le hα.2)
  rw [intervalIntegral.integral_sub hdistIntegrable hlinearIntegrable,
    integral_weightedFractionalDistribution hd,
    intervalIntegral.integral_mul_const,
    integral_id] at hintegral
  norm_num at hintegral
  have hlogY : Real.log Y ≤ (harmonic Y : ℝ) := by
    calc
      Real.log Y ≤ Real.log (Y + 1) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast Nat.le_succ Y
      _ ≤ (harmonic Y : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          log_add_one_le_harmonic Y
  have hharmonicY : (harmonic Y : ℝ) ≤ 1 + Real.log Y :=
    harmonic_le_one_add_log Y
  have hHerror : |(harmonic Y : ℝ) - Real.log Y| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlogY)]
    linarith
  have hdecomp :
      fractionalFirstMoment N d Y - (1 / 2 : ℝ) * Real.log Y =
        -(((harmonic Y : ℝ) - fractionalFirstMoment N d Y) -
            (1 / 2 : ℝ) * Real.log Y) +
          ((harmonic Y : ℝ) - Real.log Y) := by ring
  rw [hdecomp]
  calc
    |-(((harmonic Y : ℝ) - fractionalFirstMoment N d Y) -
          (1 / 2 : ℝ) * Real.log Y) +
        ((harmonic Y : ℝ) - Real.log Y)| ≤
      |((harmonic Y : ℝ) - fractionalFirstMoment N d Y) -
          (1 / 2 : ℝ) * Real.log Y| +
        |(harmonic Y : ℝ) - Real.log Y| := by
      simpa only [abs_neg] using abs_add_le
        (-(((harmonic Y : ℝ) - fractionalFirstMoment N d Y) -
          (1 / 2 : ℝ) * Real.log Y))
        ((harmonic Y : ℝ) - Real.log Y)
    _ ≤ C * fractionalDistributionScale N d + 1 := by
      gcongr
    _ ≤ (C + 1) * (1 + fractionalDistributionScale N d) := by
      have hs := fractionalDistributionScale_nonneg hd (by omega : d ≤ N)
      nlinarith

/-- The same first moment centered at one half of the harmonic number.  This
form makes the subsequent finite Abel main term exactly evaluable. -/
def HarmonicFirstMomentEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N d Y,
    0 < d → 3 * d ≤ N → 2 ≤ Y → d * Y ≤ N →
    |fractionalFirstMoment N d Y -
        (1 / 2 : ℝ) * (harmonic Y : ℝ)| ≤
      C * (1 + fractionalDistributionScale N d)

theorem harmonic_first_moment_of_fractional_first_moment
    (hfirst : FractionalFirstMomentEstimate) :
    HarmonicFirstMomentEstimate := by
  rcases hfirst with ⟨C, hC, hfirst⟩
  refine ⟨C + 1, by positivity, ?_⟩
  intro N d Y hd hNd hY hYNd
  have hlogY : Real.log Y ≤ (harmonic Y : ℝ) := by
    calc
      Real.log Y ≤ Real.log (Y + 1) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast Nat.le_succ Y
      _ ≤ (harmonic Y : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          log_add_one_le_harmonic Y
  have hharmonicY : (harmonic Y : ℝ) ≤ 1 + Real.log Y :=
    harmonic_le_one_add_log Y
  have hHerror : |(harmonic Y : ℝ) - Real.log Y| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlogY)]
    linarith
  have hdecomp :
      fractionalFirstMoment N d Y -
          (1 / 2 : ℝ) * (harmonic Y : ℝ) =
        (fractionalFirstMoment N d Y -
          (1 / 2 : ℝ) * Real.log Y) -
        (1 / 2 : ℝ) * ((harmonic Y : ℝ) - Real.log Y) := by ring
  rw [hdecomp]
  calc
    |(fractionalFirstMoment N d Y -
          (1 / 2 : ℝ) * Real.log Y) -
        (1 / 2 : ℝ) * ((harmonic Y : ℝ) - Real.log Y)| ≤
      |fractionalFirstMoment N d Y -
          (1 / 2 : ℝ) * Real.log Y| +
        (1 / 2 : ℝ) * |(harmonic Y : ℝ) - Real.log Y| := by
      calc
        _ ≤ |fractionalFirstMoment N d Y -
              (1 / 2 : ℝ) * Real.log Y| +
            |(1 / 2 : ℝ) * ((harmonic Y : ℝ) - Real.log Y)| :=
          abs_sub _ _
        _ = _ := by norm_num [abs_mul]
    _ ≤ C * (1 + fractionalDistributionScale N d) + 1 / 2 := by
      exact add_le_add (hfirst N d Y hd hNd hY hYNd)
        (by nlinarith [hHerror])
    _ ≤ (C + 1) * (1 + fractionalDistributionScale N d) := by
      have hs := fractionalDistributionScale_nonneg hd (by omega : d ≤ N)
      nlinarith

/-- Harmonic-weighted moment with an arbitrary terminal cutoff. -/
noncomputable def harmonicWeightedFractionalMoment
    (N d Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y,
    (harmonic (n - 1) : ℝ) * (n : ℝ)⁻¹ *
      quotientFractionalPart N d n

/-- Exact finite Abel summation for the harmonic weight. -/
theorem harmonic_weighted_partial_summation (N d Y : ℕ) :
    harmonicWeightedFractionalMoment N d Y =
      (harmonic (Y - 1) : ℝ) * fractionalFirstMoment N d Y -
        ∑ y ∈ Finset.Ico 1 Y,
          fractionalFirstMoment N d y / (y : ℝ) := by
  induction Y with
  | zero =>
      simp [harmonicWeightedFractionalMoment, fractionalFirstMoment]
  | succ Y ih =>
      by_cases hY : Y = 0
      · subst Y
        simp [harmonicWeightedFractionalMoment, fractionalFirstMoment]
      · have hYpos : 0 < Y := Nat.pos_of_ne_zero hY
        have hWrec :
            harmonicWeightedFractionalMoment N d (Y + 1) =
              harmonicWeightedFractionalMoment N d Y +
                (harmonic Y : ℝ) * ((Y + 1 : ℕ) : ℝ)⁻¹ *
                  quotientFractionalPart N d (Y + 1) := by
          unfold harmonicWeightedFractionalMoment
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y + 1)]
          simp only [Nat.add_sub_cancel]
        have hArec :
            fractionalFirstMoment N d (Y + 1) =
              fractionalFirstMoment N d Y +
                ((Y + 1 : ℕ) : ℝ)⁻¹ *
                  quotientFractionalPart N d (Y + 1) := by
          unfold fractionalFirstMoment
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y + 1)]
        have hCrec :
            (∑ y ∈ Finset.Ico 1 (Y + 1),
                fractionalFirstMoment N d y / (y : ℝ)) =
              (∑ y ∈ Finset.Ico 1 Y,
                fractionalFirstMoment N d y / (y : ℝ)) +
                fractionalFirstMoment N d Y / (Y : ℝ) := by
          rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ Y)]
        rw [hWrec, ih, hArec, hCrec]
        simp only [Nat.succ_sub_one]
        have hpred : Y - 1 + 1 = Y := Nat.sub_add_cancel hYpos
        have hharm := harmonic_succ (Y - 1)
        rw [hpred] at hharm
        have hharmR := congrArg (fun q : ℚ => (q : ℝ)) hharm
        simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hharmR
        rw [hharmR]
        field_simp [show (Y : ℝ) ≠ 0 by exact_mod_cast hY]
        ring

/-- Finite second-order harmonic sum. -/
noncomputable def secondHarmonicSum (Y : ℕ) : ℝ :=
  ∑ y ∈ Finset.Icc 1 Y, (y : ℝ)⁻¹ ^ 2

/-- Exact quadratic identity for the harmonic Abel main term. -/
theorem sum_harmonic_div_eq_square (Y : ℕ) :
    (∑ y ∈ Finset.Icc 1 Y, (harmonic y : ℝ) / (y : ℝ)) =
      ((harmonic Y : ℝ) ^ 2 + secondHarmonicSum Y) / 2 := by
  induction Y with
  | zero => simp [secondHarmonicSum]
  | succ Y ih =>
      have hsecond :
          secondHarmonicSum (Y + 1) =
            secondHarmonicSum Y + ((Y + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
        unfold secondHarmonicSum
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y + 1)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y + 1)]
      rw [hsecond, ih]
      have hharm := harmonic_succ Y
      have hharmR := congrArg (fun q : ℚ => (q : ℝ)) hharm
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hharmR
      rw [hharmR]
      ring

/-- The main term produced by exact harmonic partial summation. -/
noncomputable def harmonicAbelMain (Y : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (harmonic (Y - 1) : ℝ) * (harmonic Y : ℝ) -
    (1 / 2 : ℝ) *
      ∑ y ∈ Finset.Ico 1 Y, (harmonic y : ℝ) / (y : ℝ)

theorem secondHarmonicSum_nonneg (Y : ℕ) :
    0 ≤ secondHarmonicSum Y := by
  unfold secondHarmonicSum
  positivity

theorem secondHarmonicSum_le_harmonic (Y : ℕ) :
    secondHarmonicSum Y ≤ (harmonic Y : ℝ) := by
  unfold secondHarmonicSum
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro y hy
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (Finset.mem_Icc.mp hy).1
  have hyone : (1 : ℝ) ≤ y := by
    exact_mod_cast (Finset.mem_Icc.mp hy).1
  have hinv : (0 : ℝ) ≤ (y : ℝ)⁻¹ := inv_nonneg.mpr hypos.le
  have hinvOne : (y : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hypos).2 hyone
  nlinarith

/-- The exact harmonic main differs from one quarter of `log(Y)^2` by only a
linear logarithm. -/
theorem harmonicAbelMain_log_square_bound
    {Y : ℕ} (hY : 1 ≤ Y) :
    |harmonicAbelMain Y - (1 / 4 : ℝ) * Real.log Y ^ 2| ≤
      2 * (1 + Real.log Y) := by
  by_cases hYone : Y = 1
  · subst Y
    norm_num [harmonicAbelMain, secondHarmonicSum, harmonic]
  let H : ℝ := (harmonic (Y - 1) : ℝ)
  let L : ℝ := Real.log Y
  let H₂ : ℝ := secondHarmonicSum (Y - 1)
  have hYpos : 0 < Y := hY
  have hYtwo : 2 ≤ Y := by omega
  have hpred : Y - 1 + 1 = Y := Nat.sub_add_cancel hY
  have hsumIco :
      (∑ y ∈ Finset.Ico 1 Y, (harmonic y : ℝ) / (y : ℝ)) =
        (H ^ 2 + H₂) / 2 := by
    have hsets : Finset.Ico 1 Y = Finset.Icc 1 (Y - 1) := by
      ext y
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hsets]
    exact sum_harmonic_div_eq_square (Y - 1)
  have hharm := harmonic_succ (Y - 1)
  rw [hpred] at hharm
  have hharmR := congrArg (fun q : ℚ => (q : ℝ)) hharm
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hharmR
  have hmain :
      harmonicAbelMain Y =
        (1 / 4 : ℝ) * H ^ 2 + (1 / 2 : ℝ) * H / (Y : ℝ) -
          (1 / 4 : ℝ) * H₂ := by
    unfold harmonicAbelMain
    rw [hsumIco, hharmR]
    dsimp [H, H₂]
    ring
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by exact_mod_cast hY)
  have hLH : L ≤ H := by
    dsimp [L, H]
    have hbase := log_add_one_le_harmonic (Y - 1)
    rw [hpred] at hbase
    exact hbase
  have hHupper : H ≤ 1 + L := by
    dsimp [H, L]
    have hbase :
        (harmonic (Y - 1) : ℝ) ≤
          1 + Real.log ((Y - 1 : ℕ) : ℝ) :=
      harmonic_le_one_add_log (Y - 1)
    have hcastPos : (0 : ℝ) < (Y - 1 : ℕ) := by
      exact_mod_cast (show 0 < Y - 1 by omega)
    have hcastLe : ((Y - 1 : ℕ) : ℝ) ≤ (Y : ℝ) := by
      exact_mod_cast Nat.sub_le Y 1
    have hlogLe :
        Real.log ((Y - 1 : ℕ) : ℝ) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log hcastPos hcastLe
    linarith
  have hH0 : 0 ≤ H := hL0.trans hLH
  have hH₂0 : 0 ≤ H₂ := secondHarmonicSum_nonneg _
  have hH₂H : H₂ ≤ H := secondHarmonicSum_le_harmonic _
  have hYinv : (0 : ℝ) ≤ (Y : ℝ)⁻¹ := by positivity
  have hYinvOne : (Y : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by exact_mod_cast hYpos)).2 (by exact_mod_cast hY)
  have hsquare : |H ^ 2 - L ^ 2| ≤ 1 + 2 * L := by
    rw [abs_of_nonneg (by nlinarith : 0 ≤ H ^ 2 - L ^ 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hLH) (add_nonneg hH0 hL0)]
  rw [hmain]
  have hsplit :
      (1 / 4 : ℝ) * H ^ 2 + (1 / 2 : ℝ) * H / (Y : ℝ) -
          (1 / 4 : ℝ) * H₂ - (1 / 4 : ℝ) * L ^ 2 =
        (1 / 4 : ℝ) * (H ^ 2 - L ^ 2) +
          (1 / 2 : ℝ) * H * (Y : ℝ)⁻¹ -
          (1 / 4 : ℝ) * H₂ := by ring
  rw [hsplit]
  calc
    |(1 / 4 : ℝ) * (H ^ 2 - L ^ 2) +
          (1 / 2 : ℝ) * H * (Y : ℝ)⁻¹ -
          (1 / 4 : ℝ) * H₂| ≤
      (1 / 4 : ℝ) * |H ^ 2 - L ^ 2| +
        (1 / 2 : ℝ) * H * (Y : ℝ)⁻¹ +
        (1 / 4 : ℝ) * H₂ := by
      calc
        _ ≤ |(1 / 4 : ℝ) * (H ^ 2 - L ^ 2)| +
            |(1 / 2 : ℝ) * H * (Y : ℝ)⁻¹| +
            |(1 / 4 : ℝ) * H₂| := by
          calc
            _ ≤ |(1 / 4 : ℝ) * (H ^ 2 - L ^ 2) +
                  (1 / 2 : ℝ) * H * (Y : ℝ)⁻¹| +
                |(1 / 4 : ℝ) * H₂| := abs_sub _ _
            _ ≤ _ := by
              gcongr
              exact abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg hH0, abs_of_nonneg hYinv,
            abs_of_nonneg hH₂0]
          norm_num
    _ ≤ 2 * (1 + L) := by nlinarith

/-- The cutoff form is exactly the weighted fractional-part sum when the
cutoff is the full rational quotient. -/
theorem harmonicWeightedFractionalMoment_eq_weightedFractionalPartsAtQuotient
    (N d : ℕ) :
    harmonicWeightedFractionalMoment N d (N / d) =
      weightedFractionalPartsAtQuotient N d := by
  unfold harmonicWeightedFractionalMoment weightedFractionalPartsAtQuotient
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem weightedFractionalPartsAtQuotient_nonneg
    (N : ℕ) {d : ℕ} (hd : 0 < d) :
    0 ≤ weightedFractionalPartsAtQuotient N d := by
  unfold weightedFractionalPartsAtQuotient
  apply Finset.sum_nonneg
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hharm : 0 ≤ (harmonic (n - 1) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  exact mul_nonneg (div_nonneg hharm (by positivity))
    (quotientFractionalPart_nonneg N hd hnpos)

theorem weightedFractionalPartsAtQuotient_le_one_of_quotient_le_two
    (N : ℕ) {d : ℕ} (hd : 0 < d) (hQ : N / d ≤ 2) :
    weightedFractionalPartsAtQuotient N d ≤ 1 := by
  have hterm : ∀ n ∈ Finset.Icc 1 (N / d),
      (harmonic (n - 1) : ℝ) / (n : ℝ) *
          quotientFractionalPart N d n ≤
        (harmonic (n - 1) : ℝ) / (n : ℝ) := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hweight : 0 ≤ (harmonic (n - 1) : ℝ) / (n : ℝ) := by
      have hharm : 0 ≤ (harmonic (n - 1) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        positivity
      exact div_nonneg hharm (by positivity)
    exact mul_le_of_le_one_right hweight
      (quotientFractionalPart_lt_one N hd hnpos).le
  unfold weightedFractionalPartsAtQuotient
  calc
    (∑ n ∈ Finset.Icc 1 (N / d),
        (harmonic (n - 1) : ℝ) / (n : ℝ) *
          quotientFractionalPart N d n) ≤
      ∑ n ∈ Finset.Icc 1 (N / d),
        (harmonic (n - 1) : ℝ) / (n : ℝ) := by
      exact Finset.sum_le_sum hterm
    _ ≤ 1 := by
      interval_cases hq : N / d <;>
        norm_num [harmonic, Finset.sum_Icc_succ_top]

/-- Abel summation transfers the uniform first-moment estimate to the
harmonic-weighted moment.  No asymptotic input is used in this step. -/
theorem harmonic_weighted_moment_of_harmonic_first_moment
    (hfirst : HarmonicFirstMomentEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d Y,
      0 < d → 3 * d ≤ N → 2 ≤ Y → d * Y ≤ N →
      |harmonicWeightedFractionalMoment N d Y - harmonicAbelMain Y| ≤
        C * (1 + Real.log Y) * (1 + fractionalDistributionScale N d) := by
  rcases hfirst with ⟨C, hC, hfirst⟩
  refine ⟨2 * (C + 1), by positivity, ?_⟩
  intro N d Y hd hNd hY hYNd
  let B : ℝ := (C + 1) * (1 + fractionalDistributionScale N d)
  have hscale : 0 ≤ fractionalDistributionScale N d :=
    fractionalDistributionScale_nonneg hd (by omega)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hBbase : 1 ≤ B := by
    dsimp [B]
    nlinarith
  have herrorY :
      |fractionalFirstMoment N d Y -
          (1 / 2 : ℝ) * (harmonic Y : ℝ)| ≤ B := by
    exact (hfirst N d Y hd hNd hY hYNd).trans (by
      dsimp [B]
      gcongr
      linarith)
  have herror : ∀ y ∈ Finset.Ico 1 Y,
      |fractionalFirstMoment N d y -
          (1 / 2 : ℝ) * (harmonic y : ℝ)| ≤ B := by
    intro y hy
    have hyI := Finset.mem_Ico.mp hy
    by_cases hyone : y = 1
    · subst y
      have hfrac0 := quotientFractionalPart_nonneg N hd (by omega : 0 < 1)
      have hfrac1 := quotientFractionalPart_lt_one N hd (by omega : 0 < 1)
      have hsmall :
          |fractionalFirstMoment N d 1 -
              (1 / 2 : ℝ) * (harmonic 1 : ℝ)| ≤ 1 := by
        norm_num [fractionalFirstMoment, harmonic]
        rw [abs_le]
        constructor <;> linarith
      exact hsmall.trans hBbase
    · have hy2 : 2 ≤ y := by omega
      have hdy : d * y ≤ N := by
        exact (Nat.mul_le_mul_left d (Nat.le_of_lt hyI.2)).trans hYNd
      exact (hfirst N d y hd hNd hy2 hdy).trans (by
        dsimp [B]
        gcongr
        linarith)
  have hsumDecomp :
      (∑ y ∈ Finset.Ico 1 Y,
          (fractionalFirstMoment N d y -
            (1 / 2 : ℝ) * (harmonic y : ℝ)) / (y : ℝ)) =
        (∑ y ∈ Finset.Ico 1 Y,
          fractionalFirstMoment N d y / (y : ℝ)) -
        (1 / 2 : ℝ) *
          ∑ y ∈ Finset.Ico 1 Y, (harmonic y : ℝ) / (y : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  have hdecomp :
      harmonicWeightedFractionalMoment N d Y - harmonicAbelMain Y =
        (harmonic (Y - 1) : ℝ) *
            (fractionalFirstMoment N d Y -
              (1 / 2 : ℝ) * (harmonic Y : ℝ)) -
          ∑ y ∈ Finset.Ico 1 Y,
            (fractionalFirstMoment N d y -
              (1 / 2 : ℝ) * (harmonic y : ℝ)) / (y : ℝ) := by
    rw [harmonic_weighted_partial_summation, hsumDecomp]
    unfold harmonicAbelMain
    ring
  have hreciprocal :
      (∑ y ∈ Finset.Ico 1 Y, (y : ℝ)⁻¹) =
        (harmonic (Y - 1) : ℝ) := by
    rw [Ico_one_eq_Icc_one_pred (by omega : 0 < Y), harmonic_eq_sum_Icc]
    push_cast
    rfl
  have hH0 : 0 ≤ (harmonic (Y - 1) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hHupper : (harmonic (Y - 1) : ℝ) ≤ 1 + Real.log Y := by
    have hmono : (harmonic (Y - 1) : ℝ) ≤ (harmonic Y : ℝ) := by
      rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
      push_cast
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        simp only [Finset.mem_Icc] at hy ⊢
        omega
      · intro y _hy _hynot
        positivity
    exact hmono.trans (harmonic_le_one_add_log Y)
  rw [hdecomp]
  calc
    |(harmonic (Y - 1) : ℝ) *
          (fractionalFirstMoment N d Y -
            (1 / 2 : ℝ) * (harmonic Y : ℝ)) -
        ∑ y ∈ Finset.Ico 1 Y,
          (fractionalFirstMoment N d y -
            (1 / 2 : ℝ) * (harmonic y : ℝ)) / (y : ℝ)| ≤
      (harmonic (Y - 1) : ℝ) * B +
        ∑ y ∈ Finset.Ico 1 Y, B * (y : ℝ)⁻¹ := by
      calc
        _ ≤ |(harmonic (Y - 1) : ℝ) *
              (fractionalFirstMoment N d Y -
                (1 / 2 : ℝ) * (harmonic Y : ℝ))| +
            |∑ y ∈ Finset.Ico 1 Y,
              (fractionalFirstMoment N d y -
                (1 / 2 : ℝ) * (harmonic y : ℝ)) / (y : ℝ)| :=
          abs_sub _ _
        _ ≤ (harmonic (Y - 1) : ℝ) * B +
            ∑ y ∈ Finset.Ico 1 Y,
              |(fractionalFirstMoment N d y -
                (1 / 2 : ℝ) * (harmonic y : ℝ)) / (y : ℝ)| := by
          gcongr
          · rw [abs_mul, abs_of_nonneg hH0]
            gcongr
          · exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          gcongr with y hy
          rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y)]
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (herror y hy) (by positivity)
    _ = 2 * (harmonic (Y - 1) : ℝ) * B := by
      rw [← Finset.mul_sum, hreciprocal]
      ring
    _ ≤ 2 * (C + 1) * (1 + Real.log Y) *
          (1 + fractionalDistributionScale N d) := by
      calc
        2 * (harmonic (Y - 1) : ℝ) * B ≤
            2 * (1 + Real.log Y) * B := by
          gcongr
        _ = _ := by
          dsimp [B]
          ring

/-- Uniform rational-argument form of the weighted fractional-parts lemma,
centered at the exact natural quotient.  This is the form consumed by the
finite Möbius transform. -/
def RationalFloorWeightedFractionalPartsEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N d,
    0 < d → 3 * d ≤ N →
    |weightedFractionalPartsAtQuotient N d -
        (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| ≤
      C * (1 + Real.log ((N / d : ℕ) : ℝ)) *
        (1 + fractionalDistributionScale N d)

/-- The published distribution estimate implies the uniform rational form by
the already formalized integration and Abel steps. -/
theorem rational_floor_weighted_fractional_parts_of_saffari_vaughan
    (hSV : SaffariVaughanDistributionEstimate) :
    RationalFloorWeightedFractionalPartsEstimate := by
  rcases harmonic_weighted_moment_of_harmonic_first_moment
      (harmonic_first_moment_of_fractional_first_moment
        (fractional_first_moment_of_saffari_vaughan hSV)) with
    ⟨C, hC, hweighted⟩
  refine ⟨C + 2, by positivity, ?_⟩
  intro N d hd hNd
  have hQ : 3 ≤ N / d := by
    exact (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hNd)
  have hdQ : d * (N / d) ≤ N := Nat.mul_div_le N d
  have hweightedQ := hweighted N d (N / d) hd hNd (by omega) hdQ
  rw [harmonicWeightedFractionalMoment_eq_weightedFractionalPartsAtQuotient]
    at hweightedQ
  have hmain := harmonicAbelMain_log_square_bound
    (show 1 ≤ N / d by omega)
  have hscale0 : 0 ≤ fractionalDistributionScale N d :=
    fractionalDistributionScale_nonneg hd (by omega)
  have hlog0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N / d by omega))
  calc
    |weightedFractionalPartsAtQuotient N d -
        (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| ≤
      |weightedFractionalPartsAtQuotient N d - harmonicAbelMain (N / d)| +
        |harmonicAbelMain (N / d) -
          (1 / 4 : ℝ) * Real.log ((N / d : ℕ) : ℝ) ^ 2| :=
      abs_sub_le _ _ _
    _ ≤ C * (1 + Real.log ((N / d : ℕ) : ℝ)) *
          (1 + fractionalDistributionScale N d) +
        2 * (1 + Real.log ((N / d : ℕ) : ℝ)) :=
      add_le_add hweightedQ hmain
    _ ≤ (C + 2) * (1 + Real.log ((N / d : ℕ) : ℝ)) *
          (1 + fractionalDistributionScale N d) := by
      nlinarith [mul_nonneg
        (show 0 ≤ 1 + Real.log ((N / d : ℕ) : ℝ) by linarith)
        (show 0 ≤ 1 + fractionalDistributionScale N d by linarith)]

/-- The source distribution theorem yields the manuscript's weighted
fractional-parts estimate at integral arguments. -/
theorem weighted_fractional_parts_of_saffari_vaughan
    (hSV : SaffariVaughanDistributionEstimate) :
    EventualErrorBound
      (fun N => weightedFractionalPartsAtQuotient N 1)
      (fun N => (1 / 4 : ℝ) * Real.log N ^ 2)
      (fun N => Real.rpow (Real.log N) (5 / 3 : ℝ)) := by
  rcases harmonic_weighted_moment_of_harmonic_first_moment
      (harmonic_first_moment_of_fractional_first_moment
        (fractional_first_moment_of_saffari_vaughan hSV)) with
    ⟨C, hC, hweighted⟩
  refine ⟨4 * C + 8, by positivity, 3, ?_⟩
  intro N hN
  have hlog : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) ≤ 1.0986122885 := by norm_num
      _ ≤ Real.log 3 := (Real.log_three_gt_d9).le
      _ ≤ Real.log N :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hscale0 : 0 ≤ fractionalDistributionScale N 1 :=
    fractionalDistributionScale_nonneg (by omega) (by omega)
  have hrpow23 :
      (1 : ℝ) ≤ Real.rpow (Real.log N) (2 / 3 : ℝ) :=
    Real.one_le_rpow hlog (by norm_num)
  have hproduct :
      (1 + Real.log N) * (1 + fractionalDistributionScale N 1) ≤
        4 * Real.rpow (Real.log N) (5 / 3 : ℝ) := by
    have hfactorOne : 1 + Real.log N ≤ 2 * Real.log N := by linarith
    have hfactorTwo :
        1 + fractionalDistributionScale N 1 ≤
          2 * Real.rpow (Real.log N) (2 / 3 : ℝ) := by
      have hscaleEq : fractionalDistributionScale N 1 =
          Real.rpow (Real.log N) (2 / 3 : ℝ) := by
        simp [fractionalDistributionScale]
      rw [hscaleEq]
      linarith
    have hmul := mul_le_mul hfactorOne hfactorTwo
      (by positivity) (by positivity)
    calc
      (1 + Real.log N) * (1 + fractionalDistributionScale N 1) ≤
          (2 * Real.log N) *
            (2 * Real.rpow (Real.log N) (2 / 3 : ℝ)) := hmul
      _ = 4 * Real.rpow (Real.log N) (5 / 3 : ℝ) := by
        have hrpowAdd := Real.rpow_add
          (show 0 < Real.log N by linarith) (1 : ℝ) (2 / 3 : ℝ)
        rw [Real.rpow_one] at hrpowAdd
        calc
          (2 * Real.log N) *
              (2 * Real.rpow (Real.log N) (2 / 3 : ℝ)) =
              4 * (Real.log N *
                Real.rpow (Real.log N) (2 / 3 : ℝ)) := by ring
          _ = 4 * Real.rpow (Real.log N) (1 + 2 / 3 : ℝ) := by
            exact congrArg (fun x : ℝ => 4 * x) hrpowAdd.symm
          _ = 4 * Real.rpow (Real.log N) (5 / 3 : ℝ) := by
            congr 2
            ring
  have hweightedN := hweighted N 1 N (by omega) (by omega)
    (by omega) (by simp)
  have hmomentEq :=
    harmonicWeightedFractionalMoment_eq_weightedFractionalPartsAtQuotient N 1
  simp only [Nat.div_one] at hmomentEq
  rw [hmomentEq] at hweightedN
  have hmain := harmonicAbelMain_log_square_bound (show 1 ≤ N by omega)
  calc
    |weightedFractionalPartsAtQuotient N 1 -
        (1 / 4 : ℝ) * Real.log N ^ 2| ≤
      |weightedFractionalPartsAtQuotient N 1 - harmonicAbelMain N| +
        |harmonicAbelMain N - (1 / 4 : ℝ) * Real.log N ^ 2| := by
      exact (abs_sub_le _ _ _)
    _ ≤ C * ((1 + Real.log N) *
          (1 + fractionalDistributionScale N 1)) +
        2 * (1 + Real.log N) := by
      exact add_le_add (by simpa [mul_assoc] using hweightedN) hmain
    _ ≤ (4 * C + 8) *
        Real.rpow (Real.log N) (5 / 3 : ℝ) := by
      have hlinear :
          1 + Real.log N ≤
            4 * Real.rpow (Real.log N) (5 / 3 : ℝ) := by
        have hrpow53 :
            Real.log N ≤ Real.rpow (Real.log N) (5 / 3 : ℝ) :=
          Real.self_le_rpow_of_one_le hlog (by norm_num)
        nlinarith [Real.one_le_rpow hlog (by norm_num : (0 : ℝ) ≤ 5 / 3)]
      nlinarith [mul_le_mul_of_nonneg_left hproduct hC]

end NField.Alignment.WeightedFractionalPartTransfer
