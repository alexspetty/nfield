/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealTrigonometricEnergy
import NField.Alignment.PeriodicSamplingBound

/-! # Uniform arithmetic-grid sampling of a finite Fourier polynomial -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealTrigonometricSampling
open scoped BigOperators
open MeasureTheory RealTrigonometricEnergy PeriodicSamplingBound

theorem integral_deriv_energy_le (S : Finset ℤ) (c : ℤ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hfreq : ∀ n ∈ S, |(n:ℝ)| ≤ K) :
    (∫ t in (0:ℝ)..1, ‖trigDeriv S c t‖^2) ≤
      (2*Real.pi*K)^2*∑ n ∈ S, ‖c n‖^2 := by
  rw [show (fun t => ‖trigDeriv S c t‖^2) =
      (fun t => ‖trig S (fun n => c n*(2*Real.pi*Complex.I*n)) t‖^2) from rfl,
    integral_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnorm : ‖c n*(2*Real.pi*Complex.I*n)‖ ≤ (2*Real.pi*K)*‖c n‖ := by
    have h := mul_le_mul_of_nonneg_left (hfreq n hn)
      (show 0 ≤ ‖c n‖*(2*Real.pi) by positivity)
    simpa [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_assoc, mul_comm, mul_left_comm] using h
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem trig_grid_energy_le (S : Finset ℤ) (c : ℤ → ℂ) (K : ℝ)
    (hK : 0 < K) (hfreq : ∀ n ∈ S, |(n:ℝ)| ≤ K)
    (a δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    δ*(∑ j ∈ Finset.range N, ‖trig S c (a+(j:ℝ)*δ)‖^2) ≤
      ((N:ℝ)*δ+1)*(1+4*Real.pi*K*δ)*(∑ n ∈ S, ‖c n‖^2) := by
  let g := fun t : ℝ => ‖trig S c t‖^2
  let q := fun t : ℝ => ‖trigDeriv S c t‖^2
  let E := ∑ n ∈ S, ‖c n‖^2
  let L := 2*Real.pi*K
  let B := fun t : ℝ => L*g t+L⁻¹*q t
  have hL : 0 < L := by dsimp [L]; positivity
  have hg : Continuous g := (continuous_trig S c).norm.pow 2
  have hq : Continuous q :=
    (continuous_trig S (fun n => c n*(2*Real.pi*Complex.I*n))).norm.pow 2
  have hB : Continuous B := (continuous_const.mul hg).add (continuous_const.mul hq)
  have hg0 (t : ℝ) : 0 ≤ g t := sq_nonneg _
  have hq0 (t : ℝ) : 0 ≤ q t := sq_nonneg _
  have hB0 (t : ℝ) : 0 ≤ B t := by dsimp [B]; positivity
  have hgp : Function.Periodic g 1 := by
    intro t
    dsimp [g]
    rw [periodic_trig S c t]
  have hBp : Function.Periodic B 1 := by
    intro t
    dsimp [B,g,q,trigDeriv]
    rw [periodic_trig S c t, periodic_trig S _ t]
  have hgd : Differentiable ℝ g := fun t => ((hasDerivAt_trig S c t).norm_sq).differentiableAt
  have hdb (t : ℝ) : ‖deriv g t‖ ≤ B t := deriv_energy_bound S c L hL t
  have hgi : (∫ t in (0:ℝ)..1, g t) = E := integral_energy S c
  have hqi : (∫ t in (0:ℝ)..1, q t) ≤ L^2*E :=
    integral_deriv_energy_le S c K hK.le hfreq
  have hBi : (∫ t in (0:ℝ)..1, B t) ≤ 2*L*E := by
    have he : (∫ t in (0:ℝ)..1, B t) =
        L*(∫ t in (0:ℝ)..1, g t)+L⁻¹*(∫ t in (0:ℝ)..1, q t) := by
      dsimp [B]
      rw [intervalIntegral.integral_add (f := fun t => L*g t) (g := fun t => L⁻¹*q t)
        ((continuous_const.mul hg).intervalIntegrable 0 1)
        ((continuous_const.mul hq).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [he,hgi]
    have h := mul_le_mul_of_nonneg_left hqi (inv_nonneg.mpr hL.le)
    calc
      _ ≤ L*E+L⁻¹*(L^2*E) := add_le_add (le_refl _) h
      _ = _ := by field_simp <;> ring
  have hab : a ≤ a+(N:ℝ)*δ := by
    linarith [mul_nonneg (Nat.cast_nonneg N) hδ.le]
  have hpg := periodic_integral_le g hg hgp hg0 a (a+(N:ℝ)*δ) hab
  have hpB := periodic_integral_le B hB hBp hB0 a (a+(N:ℝ)*δ) hab
  simp only [add_sub_cancel_left, hgi] at hpg hpB
  have hs := grid_sampling_bound g B hg hgd hB hB0 hdb a δ hδ N
  have hpb : (∫ t in a..a+(N:ℝ)*δ, B t) ≤ ((N:ℝ)*δ+1)*(2*L*E) :=
    hpB.trans (mul_le_mul_of_nonneg_left hBi (by positivity))
  calc
    _ ≤ (∫ t in a..a+(N:ℝ)*δ, g t)+δ*(∫ t in a..a+(N:ℝ)*δ, B t) := hs
    _ ≤ ((N:ℝ)*δ+1)*E+δ*(((N:ℝ)*δ+1)*(2*L*E)) :=
      add_le_add hpg (mul_le_mul_of_nonneg_left hpb hδ.le)
    _ = _ := by dsimp [L,E]; ring

end NField.Alignment.RealTrigonometricSampling
