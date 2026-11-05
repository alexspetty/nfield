/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionStationaryAgeAsymptotic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Nat.Periodic

/-!
# Cycle-stationary probability and total-variation convergence

The state space retains the cycle label as well as its residue. The
stationary distribution is an actual probability mass function. Cesaro
averaging takes the first `N+1` integer resolutions, beginning at zero.
-/

noncomputable section

set_option autoImplicit false

namespace NField.Alignment.CollisionCycleStationarity

open scoped BigOperators ENNReal NNReal
open Filter MeasureTheory
open CollisionRemainderDynamics CollisionMassReadout CollisionIntegerSingularity

abbrev CycleState := Σ k : ℕ, Fin k

def stationaryMass (z : CycleState) : ℝ := collisionWeight z.1 / z.1

def orbitMass (n : ℕ) (z : CycleState) : ℝ :=
  if n % z.1 = z.2.val then collisionWeight z.1 else 0

theorem stationaryMass_nonneg (z : CycleState) : 0 ≤ stationaryMass z := by
  unfold stationaryMass
  exact div_nonneg (collisionWeight_nonneg _) (Nat.cast_nonneg _)

theorem orbitMass_nonneg (n : ℕ) (z : CycleState) : 0 ≤ orbitMass n z := by
  unfold orbitMass
  split_ifs <;> simp [collisionWeight_nonneg]

theorem stationaryMass_cycle_sum (k : ℕ) :
    (∑ r : Fin k, stationaryMass ⟨k,r⟩) = collisionWeight k := by
  by_cases hk : k = 0
  · subst k; simp [stationaryMass]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simp only [stationaryMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

theorem orbitMass_cycle_sum (n k : ℕ) :
    (∑ r : Fin k, orbitMass n ⟨k,r⟩) = collisionWeight k := by
  by_cases hk : k = 0
  · subst k; simp [orbitMass]
  · let r₀ : Fin k := ⟨n % k, Nat.mod_lt n (Nat.pos_of_ne_zero hk)⟩
    have he (r : Fin k) : n % k = r.val ↔ r = r₀ := by
      simp only [Fin.ext_iff, r₀]
      exact eq_comm
    simp [orbitMass, he]

theorem stationaryMass_summable : Summable stationaryMass := by
  apply (summable_sigma_of_nonneg stationaryMass_nonneg).mpr
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype, stationaryMass_cycle_sum] using collisionWeight_summable

theorem stationaryMass_tsum : (∑' z, stationaryMass z) = 1 := by
  rw [stationaryMass_summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype, stationaryMass_cycle_sum, collisionWeight_tsum]

theorem orbitMass_summable (n : ℕ) : Summable (orbitMass n) := by
  apply (summable_sigma_of_nonneg (orbitMass_nonneg n)).mpr
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype, orbitMass_cycle_sum] using collisionWeight_summable

theorem orbitMass_tsum (n : ℕ) : (∑' z, orbitMass n z) = 1 := by
  rw [(orbitMass_summable n).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype, orbitMass_cycle_sum, collisionWeight_tsum]

def stationaryPMF : PMF CycleState :=
  ⟨fun z => ENNReal.ofReal (stationaryMass z), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg stationaryMass_nonneg stationaryMass_summable,
      stationaryMass_tsum, ENNReal.ofReal_one]⟩

def orbitPMF (n : ℕ) : PMF CycleState :=
  ⟨fun z => ENNReal.ofReal (orbitMass n z), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg (orbitMass_nonneg n) (orbitMass_summable n),
      orbitMass_tsum, ENNReal.ofReal_one]⟩

def averageMass (N : ℕ) (z : CycleState) : ℝ :=
  (∑ n ∈ Finset.range (N+1), orbitMass n z) / (N+1 : ℕ)

theorem averageMass_nonneg (N : ℕ) (z : CycleState) : 0 ≤ averageMass N z := by
  unfold averageMass
  exact div_nonneg (Finset.sum_nonneg (fun n _ => orbitMass_nonneg n z)) (Nat.cast_nonneg _)

theorem averageMass_cycle_sum (N k : ℕ) :
    (∑ r : Fin k, averageMass N ⟨k,r⟩) = collisionWeight k := by
  simp only [averageMass, ← Finset.sum_div, Finset.sum_comm (s := Finset.univ),
    orbitMass_cycle_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN : ((N+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem periodic_sum_blocks (f : ℕ → ℝ) (k : ℕ) (hf : Function.Periodic f k) (t : ℕ) :
    (∑ n ∈ Finset.range (t*k), f n) = (t : ℝ) * ∑ n ∈ Finset.range k, f n := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have he : (∑ n ∈ Finset.range k, f (t*k+n)) = ∑ n ∈ Finset.range k, f n := by
      apply Finset.sum_congr rfl
      intro n hn
      simpa only [Nat.cast_id, Nat.add_comm] using (hf.nat_mul t n)
    rw [he, Nat.cast_add, Nat.cast_one]
    ring

theorem periodic_sum_decomposition (f : ℕ → ℝ) (k N : ℕ) (hf : Function.Periodic f k) :
    (∑ n ∈ Finset.range N, f n) =
      (N/k : ℕ) * (∑ n ∈ Finset.range k, f n) + ∑ n ∈ Finset.range (N%k), f n := by
  have hN : N = (N/k)*k + N%k := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod N k).symm
  conv_lhs => rw [hN]
  rw [Finset.sum_range_add, periodic_sum_blocks f k hf]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [Nat.cast_id, Nat.add_comm] using (hf.nat_mul (N/k) n)

def residueIndicator (k r n : ℕ) : ℝ := if n % k = r then 1 else 0

theorem residueIndicator_periodic (k r : ℕ) : Function.Periodic (residueIndicator k r) k := by
  intro n
  simp [residueIndicator, Nat.add_mod_right]

theorem residueIndicator_cycle_sum {k r : ℕ} (hr : r < k) :
    (∑ n ∈ Finset.range k, residueIndicator k r n) = 1 := by
  have he (n : ℕ) (hn : n ∈ Finset.range k) :
      residueIndicator k r n = if n = r then 1 else 0 := by
    simp [residueIndicator, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
  rw [Finset.sum_congr rfl he]
  simp [hr]

theorem residueIndicator_sum_error {k r : ℕ} (hr : r < k) (N : ℕ) :
    |(∑ n ∈ Finset.range N, residueIndicator k r n) - (N : ℝ)/k| ≤ k + 1 := by
  rw [periodic_sum_decomposition _ k N (residueIndicator_periodic k r),
    residueIndicator_cycle_sum hr, mul_one]
  have hk : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmod := Nat.mod_lt N hk
  have hN : (N : ℝ) = (N/k : ℕ) * (k : ℝ) + (N%k : ℕ) := by
    exact_mod_cast (show N = (N/k)*k + N%k by simpa [Nat.mul_comm] using (Nat.div_add_mod N k).symm)
  have hs0 : 0 ≤ ∑ n ∈ Finset.range (N%k), residueIndicator k r n := by
    apply Finset.sum_nonneg
    intro n hn
    unfold residueIndicator
    split_ifs <;> norm_num
  have hs1 : (∑ n ∈ Finset.range (N%k), residueIndicator k r n) ≤ (N%k : ℕ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (N%k), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        unfold residueIndicator
        split_ifs <;> norm_num
      _ = _ := by simp
  have hdiv : (N/k : ℕ) ≤ (N : ℝ)/k ∧ (N : ℝ)/k ≤ (N/k : ℕ) + 1 := by
    constructor
    · apply (le_div_iff₀ hkR).mpr
      linarith [show (0 : ℝ) ≤ (N%k : ℕ) by positivity]
    · apply (div_le_iff₀ hkR).mpr
      have hm : ((N%k : ℕ) : ℝ) ≤ k := by exact_mod_cast hmod.le
      linarith
  apply abs_le.mpr
  constructor <;> linarith [show ((N%k : ℕ) : ℝ) ≤ k by exact_mod_cast hmod.le]

theorem averageMass_indicator (N : ℕ) (z : CycleState) :
    averageMass N z = collisionWeight z.1 *
      (∑ n ∈ Finset.range (N+1), residueIndicator z.1 z.2.val n) / (N+1 : ℕ) := by
  unfold averageMass
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  unfold orbitMass residueIndicator
  split_ifs <;> simp

theorem averageMass_error (N : ℕ) (z : CycleState) :
    |averageMass N z - stationaryMass z| ≤
      collisionWeight z.1 * (z.1 + 1) / (N+1 : ℕ) := by
  have hk : 0 < z.1 := by have := z.2.isLt; omega
  have hkR : (z.1 : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hNR : ((N+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : averageMass N z - stationaryMass z =
      (collisionWeight z.1 / (N+1 : ℕ)) *
        ((∑ n ∈ Finset.range (N+1), residueIndicator z.1 z.2.val n) - (N+1 : ℕ)/z.1) := by
    rw [averageMass_indicator, stationaryMass]
    field_simp
  rw [he, abs_mul, abs_of_nonneg (div_nonneg (collisionWeight_nonneg _) (by positivity))]
  have hb := mul_le_mul_of_nonneg_left (residueIndicator_sum_error z.2.isLt (N+1))
    (div_nonneg (collisionWeight_nonneg z.1) (show (0 : ℝ) ≤ (N+1 : ℕ) by positivity))
  simpa only [div_mul_eq_mul_div, Nat.cast_add, Nat.cast_one] using hb

theorem averageMass_tendsto (z : CycleState) :
    Tendsto (fun N => averageMass N z) atTop (nhds (stationaryMass z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun N => abs_nonneg _) (fun N => averageMass_error N z)
  have hi : Tendsto (fun N : ℕ => (((N+1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  simpa [div_eq_mul_inv] using hi.const_mul (collisionWeight z.1 * (z.1 + 1))

def cycleVariation (N k : ℕ) : ℝ :=
  ∑ r : Fin k, |averageMass N ⟨k,r⟩ - stationaryMass ⟨k,r⟩|

theorem cycleVariation_nonneg (N k : ℕ) : 0 ≤ cycleVariation N k := by
  unfold cycleVariation
  positivity

theorem cycleVariation_le (N k : ℕ) : cycleVariation N k ≤ 2 * collisionWeight k := by
  calc
    _ ≤ ∑ r : Fin k, (averageMass N ⟨k,r⟩ + stationaryMass ⟨k,r⟩) := by
      apply Finset.sum_le_sum
      intro r hr
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (averageMass_nonneg _ _),
        abs_of_nonneg (stationaryMass_nonneg _)])
    _ = _ := by rw [Finset.sum_add_distrib, averageMass_cycle_sum, stationaryMass_cycle_sum]; ring

theorem cycleVariation_tendsto (k : ℕ) :
    Tendsto (fun N => cycleVariation N k) atTop (nhds 0) := by
  have ht := tendsto_finsetSum (s := Finset.univ) (fun r (_ : r ∈ (Finset.univ : Finset (Fin k))) =>
    ((averageMass_tendsto ⟨k,r⟩).sub_const (stationaryMass ⟨k,r⟩)).abs)
  simpa only [sub_self, abs_zero, Finset.sum_const_zero, cycleVariation] using ht

/-- Half of the absolutely summed mass discrepancy is the usual discrete
total-variation distance. The grouping retains the complete cycle label. -/
def totalVariation (N : ℕ) : ℝ := (1/2 : ℝ) * ∑' k, cycleVariation N k

theorem absolute_mass_discrepancy_summable (N : ℕ) :
    Summable (fun z : CycleState => |averageMass N z - stationaryMass z|) := by
  apply (summable_sigma_of_nonneg (fun z => abs_nonneg _)).mpr
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  simp only [tsum_fintype]
  exact Summable.of_nonneg_of_le (cycleVariation_nonneg N) (cycleVariation_le N)
    (collisionWeight_summable.mul_left 2)

theorem totalVariation_eq_mass_discrepancy (N : ℕ) :
    totalVariation N = (1/2 : ℝ) * ∑' z : CycleState,
      |averageMass N z - stationaryMass z| := by
  rw [(absolute_mass_discrepancy_summable N).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype, totalVariation, cycleVariation]

theorem totalVariation_tendsto_zero : Tendsto totalVariation atTop (nhds 0) := by
  unfold totalVariation
  have ht := tendsto_tsum_of_dominated_convergence (collisionWeight_summable.mul_left 2)
    cycleVariation_tendsto (Eventually.of_forall (fun N k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cycleVariation_nonneg N k)]
      exact cycleVariation_le N k))
  simpa only [tsum_zero, mul_zero] using ht.const_mul (1/2 : ℝ)

def ageMass (z : CycleState) : ℝ := (z.2.val : ℝ) * stationaryMass z

theorem ageMass_nonneg (z : CycleState) : 0 ≤ ageMass z :=
  mul_nonneg (Nat.cast_nonneg _) (stationaryMass_nonneg _)

theorem ageMass_cycle_sum (k : ℕ) :
    (∑ r : Fin k, ageMass ⟨k,r⟩) = collisionWeight k * ((k : ℝ)-1)/2 := by
  by_cases hk : k = 0
  · subst k; simp [ageMass]
  · have hkp : 0 < k := Nat.pos_of_ne_zero hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hs := congrArg (fun n : ℕ => (n : ℝ)) (Finset.sum_range_id_mul_two k)
    push_cast at hs
    rw [Nat.cast_sub hkp] at hs
    simp only [Nat.cast_one] at hs
    have hr : (∑ r : Fin k, (r.val : ℝ)) = (k : ℝ)*((k : ℝ)-1)/2 := by
      rw [Fin.sum_univ_eq_sum_range]
      linarith
    simp only [ageMass, stationaryMass, ← Finset.sum_mul]
    rw [hr]
    field_simp

theorem ageMass_truncated (M : ℕ) :
    (∑ k ∈ Finset.range (M+1), ∑ r : Fin k, ageMass ⟨k,r⟩) =
      (3/2 : ℝ) * stationaryAge collisionWeight M := by
  simp only [ageMass_cycle_sum]
  rw [sum_range_zero_one (fun k => collisionWeight k * ((k : ℝ)-1)/2)
    (by simp) (by simp), stationaryAge]
  rw [← Finset.sum_div]
  ring

theorem ageMass_not_summable : ¬ Summable ageMass := by
  intro hs
  have hrows := ((summable_sigma_of_nonneg ageMass_nonneg).mp hs).2
  have hbound (M : ℕ) := hrows.sum_le_tsum (Finset.range (M+1))
    (fun k _ => tsum_nonneg (fun r => ageMass_nonneg ⟨k,r⟩))
  simp only [tsum_fintype, ageMass_truncated] at hbound
  have hg := stationaryAge_tendsto_atTop.eventually_gt_atTop
    ((2/3 : ℝ) * ((∑' k, ∑ r : Fin k, ageMass ⟨k,r⟩) + 1))
  obtain ⟨M,hM⟩ := hg.exists
  have hb := hbound M
  linarith

/-- The stationary probability has infinite expected (nonnegative) cycle age. -/
theorem stationary_mean_age_infinite :
    (∑' z : CycleState, ENNReal.ofReal (ageMass z)) = ∞ := by
  let a : CycleState → ℝ≥0 := fun z => ⟨ageMass z, ageMass_nonneg z⟩
  have he (z : CycleState) : ENNReal.ofReal (ageMass z) = (a z : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal (ageMass_nonneg z)
  simp_rw [he]
  exact ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr ageMass_not_summable

theorem averageMass_summable (N : ℕ) : Summable (averageMass N) := by
  apply (summable_sigma_of_nonneg (averageMass_nonneg N)).mpr
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype, averageMass_cycle_sum] using collisionWeight_summable

theorem averageMass_tsum (N : ℕ) : (∑' z, averageMass N z) = 1 := by
  rw [(averageMass_summable N).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype, averageMass_cycle_sum, collisionWeight_tsum]

def averagePMF (N : ℕ) : PMF CycleState :=
  ⟨fun z => ENNReal.ofReal (averageMass N z), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg (averageMass_nonneg N) (averageMass_summable N),
      averageMass_tsum, ENNReal.ofReal_one]⟩

theorem stationaryPMF_toReal (z : CycleState) :
    (stationaryPMF z).toReal = collisionWeight z.1 / z.1 :=
  ENNReal.toReal_ofReal (stationaryMass_nonneg z)

theorem averagePMF_toReal (N : ℕ) (z : CycleState) :
    (averagePMF N z).toReal = averageMass N z :=
  ENNReal.toReal_ofReal (averageMass_nonneg N z)

theorem averagePMF_cesaro (N : ℕ) (z : CycleState) :
    (averagePMF N z).toReal =
      (∑ n ∈ Finset.range (N+1), (orbitPMF n z).toReal) / (N+1 : ℕ) := by
  rw [averagePMF_toReal, averageMass]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact (ENNReal.toReal_ofReal (orbitMass_nonneg n z)).symm

theorem stationaryPMF_mean_age :
    (∑' z : CycleState, (z.2.val : ℝ≥0∞) * stationaryPMF z) = ∞ := by
  have he (z : CycleState) : (z.2.val : ℝ≥0∞) * stationaryPMF z =
      ENNReal.ofReal (ageMass z) := by
    change (z.2.val : ℝ≥0∞) * ENNReal.ofReal (stationaryMass z) = _
    rw [ageMass, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp
  simp_rw [he]
  exact stationary_mean_age_infinite

theorem totalVariation_eq_pmf (N : ℕ) :
    totalVariation N = (1/2 : ℝ) * ∑' z : CycleState,
      |(averagePMF N z).toReal - (stationaryPMF z).toReal| := by
  rw [totalVariation_eq_mass_discrepancy]
  simp only [averagePMF_toReal, stationaryPMF_toReal, stationaryMass]

/-- All clauses of the manuscript's truncated stationary-age proposition,
for the normalized countable cycle probability and its Cesaro averages. -/
theorem truncated_stationary_age :
    Asymptotics.IsBigO atTop
      (fun M : ℕ => stationaryAge collisionWeight M - Real.log M^2/Real.pi^2)
      (fun M : ℕ => Real.log (2*(M : ℝ))) ∧
    (∀ z : CycleState, (stationaryPMF z).toReal = collisionWeight z.1 / z.1) ∧
    ((∑' z : CycleState, (z.2.val : ℝ≥0∞) * stationaryPMF z) = ∞) ∧
    Tendsto (fun N => (1/2 : ℝ) * ∑' z : CycleState,
      |(averagePMF N z).toReal - (stationaryPMF z).toReal|) atTop (nhds 0) := by
  refine ⟨CollisionStationaryAgeAsymptotic.stationaryAge_isBigO_log,
    stationaryPMF_toReal, stationaryPMF_mean_age, ?_⟩
  simpa only [← totalVariation_eq_pmf] using totalVariation_tendsto_zero

end NField.Alignment.CollisionCycleStationarity
