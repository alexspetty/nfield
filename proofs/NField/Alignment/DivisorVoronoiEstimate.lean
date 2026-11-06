/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.DivisorSawtoothIdentity
import NField.Alignment.ReciprocalSawtoothGlobal
import NField.Alignment.DivisorSmoothingScales

/-! # The literal cubic-root divisor summatory estimate -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorVoronoiEstimate
open scoped BigOperators Topology
open Filter Asymptotics DivisorHyperbolaIdentity DivisorSawtoothIdentity
  ReciprocalFloorSmoothing ReciprocalSawtoothGlobal DivisorSmoothingScales

def divisorError (x : ℝ) : ℝ :=
  divisorCount ⌊x⌋₊-(x*Real.log x+(2*Real.eulerMascheroniConstant-1)*x)

def divisorScale (x : ℝ) : ℝ := x^(1/3 : ℝ)*Real.log (2*x)

theorem sqrt_cutoff {x : ℝ} (hx : 1≤x) :
    1≤⌊Real.sqrt x⌋₊ ∧ (⌊Real.sqrt x⌋₊ : ℝ)^2≤x ∧
      x<((⌊Real.sqrt x⌋₊ : ℝ)+1)^2 := by
  have hx0 : 0≤x := by linarith
  have hs1 := Real.one_le_sqrt.mpr hx
  have hM : 1≤⌊Real.sqrt x⌋₊ := (Nat.one_le_floor_iff _).mpr hs1
  have hlo := Nat.floor_le (Real.sqrt_nonneg x)
  have hhi := Nat.lt_floor_add_one (Real.sqrt x)
  have hsq := Real.sq_sqrt hx0
  have hM0 : (0 : ℝ)≤⌊Real.sqrt x⌋₊ := Nat.cast_nonneg _
  refine ⟨hM,?_,?_⟩
  · nlinarith [Real.sqrt_nonneg x]
  · nlinarith [Real.sqrt_nonneg x]

/-- Small parameters are covered by an explicit square-root bound. -/
theorem divisor_error_trivial {x : ℝ} (hx : 1≤x) :
    |divisorError x|≤14+Real.sqrt x := by
  obtain ⟨hM,hlo,hhi⟩ := sqrt_cutoff hx
  have hb := real_divisor_error_bound hM hlo hhi
  have hs := floor_saw_prefix_trivial 0 ⌊Real.sqrt x⌋₊ x
  have hfloor := Nat.floor_le (Real.sqrt_nonneg x)
  unfold divisorError
  linarith

theorem divisor_scale_lower {x : ℝ} (hx : 1≤x) : Real.log 2≤divisorScale x := by
  have hx0 : 0<x := by linarith
  have ht : 1≤x^(1/3 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hl : Real.log 2≤Real.log (2*x) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hl0 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  unfold divisorScale
  nlinarith

theorem eventual_divisor_estimate : ∀ᶠ x : ℝ in atTop,
    |divisorError x|≤(18+1400/Real.log 2)*divisorScale x := by
  filter_upwards [eventual_smoothing_scale,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hlog
  obtain ⟨hx1,hT,hscale⟩ := hx
  have hx0 : 0<x := by linarith
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hM,hlo,hhi⟩ := sqrt_cutoff hx1
  have hs := floor_global_log_bound ⌊Real.sqrt x⌋₊ (Real.sqrt x) (x^(1/3 : ℝ)) hM
    (Nat.floor_le (Real.sqrt_nonneg x)) hT
    (by rw [Real.sq_sqrt hx0.le,cubic_root_cube hx0.le])
    (by simpa only [Real.sq_sqrt hx0.le] using hscale)
  rw [Real.sq_sqrt hx0.le] at hs
  have he := real_divisor_error_bound hM hlo hhi
  have hlog2x : Real.log (2*x)=Real.log 2+Real.log x :=
    Real.log_mul (by norm_num) hx0.ne'
  have hlogle : Real.log x≤Real.log (2*x) := by rw [hlog2x]; linarith
  have hlog1 : 1≤Real.log (2*x) := hlog.trans hlogle
  have hscale1 : 1≤divisorScale x := by unfold divisorScale; nlinarith
  have hc : 0≤1400/Real.log 2 := by positivity
  unfold divisorError
  calc
    _ ≤ 14+2*|floorSawPrefix 0 ⌊Real.sqrt x⌋₊ x| := he
    _ ≤ 14+2*(2+1400*x^(1/3 : ℝ)*(Real.log (Real.sqrt x)/Real.log 2)) := by linarith
    _ = 18+(1400/Real.log 2)*(x^(1/3 : ℝ)*Real.log x) := by
      rw [Real.log_sqrt hx0.le]
      ring
    _ ≤ 18*divisorScale x+(1400/Real.log 2)*divisorScale x := by
      apply add_le_add
      · nlinarith
      · apply mul_le_mul_of_nonneg_left _ hc
        exact mul_le_mul_of_nonneg_left hlogle (Real.rpow_nonneg hx0.le _)
    _ = _ := by ring

/-- Title: `The cubic-root divisor summatory estimate`. -/
theorem divisor_error_isBigO : divisorError =O[atTop] divisorScale := by
  apply IsBigO.of_bound (18+1400/Real.log 2)
  filter_upwards [eventual_divisor_estimate,eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs,Real.norm_of_nonneg ((Real.log_nonneg (by norm_num : (1 : ℝ)≤2)).trans (divisor_scale_lower hx1))]
  exact hx

/-- One absolute constant covers every real cutoff at least one. -/
theorem divisor_estimate_all_real : ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 1≤x →
    |divisorError x|≤C*divisorScale x := by
  obtain ⟨R,hR⟩ := eventually_atTop.1 eventual_divisor_estimate
  let U : ℝ := max R 1
  have hU : 1≤U := le_max_right _ _
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let C₀ : ℝ := 18+1400/Real.log 2
  let C₁ : ℝ := (14+Real.sqrt U)/Real.log 2
  have hC₀ : 0<C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0<C₁ := by dsimp [C₁]; positivity
  refine ⟨C₀+C₁,by positivity,?_⟩
  intro x hx
  have hs := divisor_scale_lower hx
  have hs0 : 0≤divisorScale x := hl2.le.trans hs
  by_cases hxU : U≤x
  · have hb := hR x ((le_max_left R 1).trans hxU)
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [C₀]; linarith) hs0)
  · have hxU' : x≤U := le_of_lt (lt_of_not_ge hxU)
    have hb := (divisor_error_trivial hx).trans
      (add_le_add le_rfl (Real.sqrt_le_sqrt hxU'))
    have he : C₁*Real.log 2=14+Real.sqrt U := by dsimp [C₁]; field_simp
    have hmul := mul_le_mul_of_nonneg_left hs hC₁.le
    rw [he] at hmul
    exact (hb.trans hmul).trans (mul_le_mul_of_nonneg_right (by linarith) hs0)

end NField.Alignment.DivisorVoronoiEstimate
