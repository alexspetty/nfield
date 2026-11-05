/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCylinderMeans
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Continuous collision ramp energy

The fractional-part rows are integrated on literal affine cells of the
unit interval. Their exact Gram form connects the finite boundary response
to the already constructed gcd capacity.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionRampEnergy

open scoped BigOperators Classical
open MeasureTheory
open CollisionRemainderDynamics CollisionRemainderCovariance

def affineRow (r : ℕ) (x : ℝ) : ℝ := Int.fract ((r : ℝ)*x)-1/2

def midpointRow (r : ℕ) (x : ℝ) : ℝ :=
  if Int.fract ((r : ℝ)*x)=0 then 0 else affineRow r x

theorem affineRow_measurable (r : ℕ) : Measurable (affineRow r) := by
  unfold affineRow
  fun_prop

theorem affineRow_norm_le (r : ℕ) (x : ℝ) : ‖affineRow r x‖ ≤ 1/2 := by
  rw [affineRow, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Int.fract_nonneg ((r : ℝ)*x), Int.fract_lt_one ((r : ℝ)*x)]

theorem affineRow_intervalIntegrable (r : ℕ) (a b : ℝ) :
    IntervalIntegrable (affineRow r) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (affineRow_measurable r).aestronglyMeasurable
  filter_upwards [] with x
  simpa using (affineRow_norm_le r x).trans (by norm_num : (1/2 : ℝ) ≤ 1)

theorem affineProduct_intervalIntegrable (r s : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => affineRow r x*affineRow s x) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    ((affineRow_measurable r).mul (affineRow_measurable s)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖affineRow r x*affineRow s x‖ ≤ ‖(1 : ℝ)‖
  rw [norm_mul, norm_one]
  have h := mul_le_mul (affineRow_norm_le r x) (affineRow_norm_le s x)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/2)
  linarith

theorem integral_uniform_cells {m : ℕ} (hm : 0 < m) (F : ℝ → ℝ)
    (hF : ∀ a b, IntervalIntegrable F volume a b) :
    (∫ x in (0 : ℝ)..1, F x) = (1/(m : ℝ))*
      ∑ j ∈ Finset.range m, ∫ t in (0 : ℝ)..1, F (((j : ℝ)+t)/(m : ℝ)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ)/(m : ℝ)) (n := m) (f := F)
    (fun j _ => hF _ _)
  simp only [Nat.cast_zero, zero_div, div_self hmR] at hs
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ht := intervalIntegral.integral_comp_mul_add F
    (a := (0 : ℝ)) (b := 1) (c := 1/(m : ℝ)) (by positivity : 1/(m : ℝ) ≠ 0)
    ((j : ℝ)/(m : ℝ))
  have harg (t : ℝ) : (m : ℝ)⁻¹*t+(j : ℝ)/(m : ℝ) = ((j : ℝ)+t)/(m : ℝ) := by ring
  simp only [one_div, inv_inv, smul_eq_mul, mul_zero, zero_add, mul_one] at ht
  simp only [harg] at ht
  have he : (m : ℝ)⁻¹+(j : ℝ)/(m : ℝ) = ((j+1 : ℕ) : ℝ)/(m : ℝ) := by
    push_cast; ring
  rw [he] at ht
  rw [ht]
  field_simp

theorem fract_affine_cell {d : ℕ} (hd : 0 < d) (j : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Int.fract (((j : ℝ)+t)/(d : ℝ)) = ((j%d : ℕ)+t)/(d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply Int.fract_eq_iff.mpr
  refine ⟨by positivity, ?_, ((j/d : ℕ) : ℤ), ?_⟩
  · apply (div_lt_one hdR).mpr
    have hm : ((j%d : ℕ) : ℝ)+1 ≤ d := by exact_mod_cast Nat.mod_lt j hd
    linarith
  · have he : ((j : ℝ)) = ((j%d : ℕ) : ℝ)+(d : ℝ)*((j/d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div j d).symm
    simp only [Int.cast_natCast]
    rw [he]
    field_simp
    ring

theorem affineRow_on_cell {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (j : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    affineRow r (((j : ℝ)+t)/((r : ℝ)*(s : ℝ))) =
      (centeredRemainder s j+(t-1/2))/(s : ℝ) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [affineRow]
  have he : (r : ℝ)*(((j : ℝ)+t)/((r : ℝ)*(s : ℝ))) = ((j : ℝ)+t)/(s : ℝ) := by
    field_simp
  rw [he, fract_affine_cell hs j ht0 ht1, centeredRemainder]
  field_simp
  ring

theorem centered_translate_multiple {k L : ℕ} (hkL : k ∣ L) (t j : ℕ) :
    centeredRemainder k (t+L*j) = centeredRemainder k t := by
  simp [centeredRemainder, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hkL]

theorem centered_sum_multiple {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (∑ j ∈ Finset.range (m*k), centeredRemainder k j) = 0 := by
  rw [sum_range_product m k]
  simp only [centered_translate_multiple (dvd_refl k), centered_cycle_sum hk,
    Finset.sum_const_zero]

theorem covariance_product_cycle {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (∑ j ∈ Finset.range (r*s), centeredRemainder r j*centeredRemainder s j) =
      (r : ℝ)*(s : ℝ)*((r.gcd s : ℝ)^2-1)/12 := by
  rw [← Nat.gcd_mul_lcm r s, sum_range_product (r.gcd s) (r.lcm s)]
  simp only [centered_translate_multiple (Nat.dvd_lcm_left r s),
    centered_translate_multiple (Nat.dvd_lcm_right r s), remainder_covariance_sum hr hs,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have he : (r.gcd s : ℝ)*(r.lcm s : ℝ)=(r : ℝ)*(s : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm r s
  calc
    _ = ((r.gcd s : ℝ)*(r.lcm s : ℝ))*((r.gcd s : ℝ)^2-1)/12 := by ring
    _ = _ := by rw [he]

theorem affine_cell_sum {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (t : ℝ) :
    (∑ j ∈ Finset.range (r*s),
      ((centeredRemainder s j+(t-1/2))/(s : ℝ))*
      ((centeredRemainder r j+(t-1/2))/(r : ℝ))) =
      ((r.gcd s : ℝ)^2-1)/12+(t-1/2)^2 := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have he (j : ℕ) :
      ((centeredRemainder s j+(t-1/2))/(s : ℝ))*
      ((centeredRemainder r j+(t-1/2))/(r : ℝ)) =
      (centeredRemainder r j*centeredRemainder s j+
        (t-1/2)*centeredRemainder s j+(t-1/2)*centeredRemainder r j+
        (t-1/2)^2)/((r : ℝ)*(s : ℝ)) := by ring
  simp only [he, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [covariance_product_cycle hr hs, centered_sum_multiple hs r,
    show (∑ j ∈ Finset.range (r*s), centeredRemainder r j)=0 by
      rw [Nat.mul_comm r s]; exact centered_sum_multiple hr s]
  push_cast
  field_simp
  ring

theorem unit_centered_square_integral :
    (∫ t in (0 : ℝ)..1, (t-1/2)^2) = 1/12 := by
  have he (t : ℝ) : (t-1/2)^2=t^2-t+1/4 := by ring
  have hp : IntervalIntegrable (fun t : ℝ => t^2) volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  have hi : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  simp only [he]
  rw [intervalIntegral.integral_add (hp.sub hi) intervalIntegrable_const,
    intervalIntegral.integral_sub hp hi]
  norm_num [integral_pow, integral_id]

theorem affine_ramp_gram {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, affineRow r x*affineRow s x) =
      (r.gcd s : ℝ)^2/(12*(r : ℝ)*(s : ℝ)) := by
  rw [integral_uniform_cells (Nat.mul_pos hr hs) _ (affineProduct_intervalIntegrable r s)]
  let F : ℕ → ℝ → ℝ := fun j t =>
    ((centeredRemainder s j+(t-1/2))/(s : ℝ))*
    ((centeredRemainder r j+(t-1/2))/(r : ℝ))
  have hint (j : ℕ) : IntervalIntegrable (F j) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have he (j : ℕ) :
      (∫ t in (0 : ℝ)..1,
        affineRow r (((j : ℝ)+t)/(r*s : ℕ))*
        affineRow s (((j : ℝ)+t)/(r*s : ℕ))) = ∫ t in (0 : ℝ)..1, F j t := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    simp only [Nat.cast_mul]
    rw [affineRow_on_cell hr hs j ht.1.le ht.2]
    rw [mul_comm (r : ℝ) (s : ℝ), affineRow_on_cell hs hr j ht.1.le ht.2]
  simp only [he]
  rw [← intervalIntegral.integral_finsetSum (fun j _ => hint j)]
  have hsum (t : ℝ) : (∑ j ∈ Finset.range (r*s), F j t) =
      ((r.gcd s : ℝ)^2-1)/12+(t-1/2)^2 := affine_cell_sum hr hs t
  simp only [hsum]
  have hp : IntervalIntegrable (fun t : ℝ => (t-1/2)^2) volume 0 1 :=
    ((continuous_id.sub continuous_const).pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hp,
    unit_centered_square_integral, intervalIntegral.integral_const]
  push_cast
  simp only [sub_zero, one_smul]
  ring

theorem midpointRow_ae_affineRow {r : ℕ} (hr : 0 < r) :
    midpointRow r =ᵐ[volume] affineRow r := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  filter_upwards [(Set.countable_range (fun z : ℤ => (z : ℝ)/(r : ℝ))).ae_notMem volume]
    with x hx
  apply if_neg
  intro h
  obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h
  apply hx
  refine ⟨z, ?_⟩
  dsimp only
  rw [hz]
  field_simp

theorem midpointRow_intervalIntegrable {r : ℕ} (hr : 0 < r) (a b : ℝ) :
    IntervalIntegrable (midpointRow r) volume a b :=
  (affineRow_intervalIntegrable r a b).congr_ae
    (ae_restrict_of_ae (midpointRow_ae_affineRow hr).symm)

theorem midpoint_ramp_gram {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, midpointRow r x*midpointRow s x) =
      (r.gcd s : ℝ)^2/(12*(r : ℝ)*(s : ℝ)) := by
  rw [← affine_ramp_gram hr hs]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [midpointRow_ae_affineRow hr, midpointRow_ae_affineRow hs]
    with x hx hy
  simp only [hx, hy, implies_true]

theorem unit_centered_integral : (∫ t in (0 : ℝ)..1, t-1/2) = 0 := by
  have hi : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
  norm_num [integral_id]

theorem affineRow_mean_zero {r : ℕ} (hr : 0 < r) :
    (∫ x in (0 : ℝ)..1, affineRow r x) = 0 := by
  rw [integral_uniform_cells hr _ (affineRow_intervalIntegrable r)]
  have he (j : ℕ) :
      (∫ t in (0 : ℝ)..1, affineRow r (((j : ℝ)+t)/(r : ℝ))) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, t-1/2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        simpa [centeredRemainder, Nat.mod_one] using
          affineRow_on_cell hr (by norm_num : 0 < 1) j ht.1.le ht.2
      _ = 0 := unit_centered_integral
  simp only [he, Finset.sum_const_zero, mul_zero]

theorem midpointRow_mean_zero {r : ℕ} (hr : 0 < r) :
    (∫ x in (0 : ℝ)..1, midpointRow r x) = 0 := by
  calc
    _ = ∫ x in (0 : ℝ)..1, affineRow r x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [midpointRow_ae_affineRow hr] with x hx
      exact fun _ => hx
    _ = 0 := affineRow_mean_zero hr

def affineResponse (N : ℕ) (x : ℝ) : ℝ :=
  2*∑ r ∈ Finset.Icc 1 N, affineRow r x

def boundaryResponse (N : ℕ) (x : ℝ) : ℝ :=
  2*∑ r ∈ Finset.Icc 1 N, midpointRow r x

theorem boundaryResponse_ae_affineResponse (N : ℕ) :
    boundaryResponse N =ᵐ[volume] affineResponse N := by
  have he : ∀ᵐ x ∂volume, ∀ r : ℕ, 0 < r → midpointRow r x=affineRow r x := by
    rw [ae_all_iff]
    intro r
    by_cases hr : 0 < r
    · filter_upwards [midpointRow_ae_affineRow hr] with x hx
      exact fun _ => hx
    · simp only [hr, false_implies, Filter.eventually_true]
  filter_upwards [he] with x hx
  unfold boundaryResponse affineResponse
  congr 1
  exact Finset.sum_congr rfl (fun r hr => hx r (Finset.mem_Icc.mp hr).1)

theorem boundaryResponse_mean_zero (N : ℕ) :
    (∫ x in (0 : ℝ)..1, boundaryResponse N x) = 0 := by
  unfold boundaryResponse
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun r hr => midpointRow_intervalIntegrable (Finset.mem_Icc.mp hr).1 0 1)]
  rw [Finset.sum_eq_zero (fun r hr => midpointRow_mean_zero (Finset.mem_Icc.mp hr).1),
    mul_zero]

theorem affineResponse_square (N : ℕ) (x : ℝ) :
    affineResponse N x^2 = 4*∑ r ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N,
      affineRow r x*affineRow s x := by
  rw [affineResponse, mul_pow, show (2 : ℝ)^2=4 by norm_num, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]

theorem affineResponse_energy (N : ℕ) :
    (∫ x in (0 : ℝ)..1, affineResponse N x^2) =
      (1/3 : ℝ)*∑ r ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N,
        (r.gcd s : ℝ)^2/((r : ℝ)*(s : ℝ)) := by
  simp_rw [affineResponse_square]
  have hint (r : ℕ) : IntervalIntegrable
      (fun x : ℝ => ∑ s ∈ Finset.Icc 1 N, affineRow r x*affineRow s x) volume 0 1 := by
    exact ⟨integrable_finsetSum _ (fun s _ => (affineProduct_intervalIntegrable r s 0 1).1),
      integrable_finsetSum _ (fun s _ => (affineProduct_intervalIntegrable r s 0 1).2)⟩
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun r _ => hint r)]
  simp_rw [intervalIntegral.integral_finsetSum
    (fun s _ => affineProduct_intervalIntegrable _ s 0 1)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [affine_ramp_gram (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hs).1]
  ring

theorem boundaryResponse_energy (N : ℕ) :
    (∫ x in (0 : ℝ)..1, boundaryResponse N x^2) =
      SecondaryCapacityLedger.continuousCapacity N := by
  have he : (∫ x in (0 : ℝ)..1, boundaryResponse N x^2) =
      ∫ x in (0 : ℝ)..1, affineResponse N x^2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [boundaryResponse_ae_affineResponse N] with x hx
    exact fun _ => congrArg (fun t : ℝ => t^2) hx
  rw [he, affineResponse_energy]
  have hbox : GcdLcmCapacity.gcdLcmSquareSum N =
      ∑ r ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N,
        (r.gcd s : ℝ)^2/((r : ℝ)*(s : ℝ)) := by
    unfold GcdLcmCapacity.gcdLcmSquareSum GcdLcmCapacity.gcdLcmKernel
    calc
      _ = ∑ i : PrimeSquareCollisionWindow.FirstWindowIndex (N+1),
          ∑ s ∈ Finset.Icc 1 N,
            (Nat.gcd (PrimeSquareCollisionWindow.firstWindowNat i) s : ℝ)^2/
              ((PrimeSquareCollisionWindow.firstWindowNat i : ℝ)*(s : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact CollisionPotentialConvergence.sum_firstWindow_eq_Icc N
          (fun s => (Nat.gcd (PrimeSquareCollisionWindow.firstWindowNat i) s : ℝ)^2/
            ((PrimeSquareCollisionWindow.firstWindowNat i : ℝ)*(s : ℝ)))
      _ = _ := CollisionPotentialConvergence.sum_firstWindow_eq_Icc N
        (fun r => ∑ s ∈ Finset.Icc 1 N, (r.gcd s : ℝ)^2/((r : ℝ)*(s : ℝ)))
  have hc := GcdLcmCapacity.gcdLcmSquareSum_eq_three_continuousCapacity N
  rw [hbox] at hc
  linarith

theorem midpointRow_formula (r : ℕ) (x : ℝ) :
    midpointRow r x =
      if (r : ℝ)*x ∈ Set.range (Int.cast : ℤ → ℝ) then 0
      else Int.fract ((r : ℝ)*x)-1/2 := by
  simp only [midpointRow, affineRow, Int.fract_eq_zero_iff]

theorem boundaryResponse_formula (N : ℕ) (x : ℝ) :
    boundaryResponse N x = 2*∑ r ∈ Finset.Icc 1 N, midpointRow r x := rfl

theorem midpointRow_periodic (r : ℕ) : Function.Periodic (midpointRow r) 1 := by
  intro x
  simp only [midpointRow, affineRow, mul_add, mul_one, Int.fract_add_natCast]

theorem boundaryResponse_periodic (N : ℕ) : Function.Periodic (boundaryResponse N) 1 := by
  intro x
  unfold boundaryResponse
  congr 1
  exact Finset.sum_congr rfl (fun r _ => midpointRow_periodic r x)

end NField.Alignment.CollisionRampEnergy
