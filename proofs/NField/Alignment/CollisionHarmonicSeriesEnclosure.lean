/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionComplexSeriesEnclosure
import NField.Alignment.CollisionHarmonicRootAverage
import NField.Alignment.CollisionHarmonicCoefficients
import NField.Alignment.CollisionRationalZetaTail

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionHarmonicSeriesEnclosure
open scoped BigOperators
open CollisionComplexPhaseEnclosure CollisionComplexSeriesEnclosure CollisionHarmonicRootSeries
open CollisionAmplitudeArithmetic CollisionHarmonicSeed CollisionPositiveLogTail
open CollisionInverseRemainder CollisionInverseRationalBound CollisionHarmonicCoefficients
open CollisionRationalZetaTail CollisionHarmonicRootAverage

def harmonicPowerPrefix (z : ℂ) (N : ℕ) : ℂ := ∑ n∈Finset.range (N+1),harmonicPowerTerm z n
def cubicCosinePrefix (θ : ℝ) (N : ℕ) : ℝ := ∑ n∈Finset.range (N+1),cubicCosineTerm θ n
def quadraticSinePrefix (θ : ℝ) (N : ℕ) : ℝ := ∑ n∈Finset.range (N+1),quadraticSineTerm θ n

theorem harmonic_kernel_majorant (n : ℕ) : harmonicKernel n ≤ positiveLogKernel n := by
  unfold harmonicKernel positiveLogKernel
  exact div_le_div_of_nonneg_right
    ((harmonic_real_monotone (Nat.sub_le n 1)).trans (harmonic_le_one_add_log n)) (sq_nonneg _)

theorem harmonic_kernel_binary_tail {N b : ℕ} (hN : 1≤N) (hb : 2*N≤2^b) :
    (∑' n,harmonicKernel (n+N+1)) ≤ (2*(b : ℝ)+3)/(N : ℝ) := by
  have hs := harmonicKernel_hasSum.summable.comp_injective
    (show Function.Injective (fun n : ℕ => n+N+1) from fun a b h => by dsimp at h; omega)
  have h := hs.tsum_le_tsum (fun n => harmonic_kernel_majorant (n+N+1)) (positiveLog_shift_summable hN)
  apply (h.trans (positiveLog_shift_bound hN)).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hl := log_le_binary_bound hN hb
  linarith

theorem harmonic_polylog_tail {z : ℂ} (hz : ‖z‖≤1) {N b : ℕ}
    (hN : 1≤N) (hb : 2*N≤2^b) :
    ‖harmonicPolylog z-harmonicPowerPrefix z N‖ ≤ (2*(b : ℝ)+3)/(N : ℝ) := by
  exact norm_series_tail_bound (harmonicPowerTerm_summable hz) N
    (harmonicKernel_hasSum.summable.comp_injective (fun a b h => by omega))
    (fun n => harmonicPowerTerm_bound hz (n+N+1)) (harmonic_kernel_binary_tail hN hb)

theorem harmonic_polylog_enclosure {z : ℂ} (hz : ‖z‖≤1) {N b : ℕ}
    (hN : 1≤N) (hb : 2*N≤2^b) {rl ru il iu : ℝ}
    (hp : rectangleContains (harmonicPowerPrefix z N) rl ru il iu) :
    rectangleContains (harmonicPolylog z)
      (rl-(2*(b : ℝ)+3)/(N : ℝ)) (ru+(2*(b : ℝ)+3)/(N : ℝ))
      (il-(2*(b : ℝ)+3)/(N : ℝ)) (iu+(2*(b : ℝ)+3)/(N : ℝ)) :=
  norm_error_rectangle hp (harmonic_polylog_tail hz hN hb)

theorem cubic_cosine_tail (θ : ℝ) {N : ℕ} (hN : 1≤N) :
    |cubicCosine θ-cubicCosinePrefix θ N| ≤ 1/(2*(N : ℝ)^2) := by
  apply real_series_tail_bound (cubicCosineTerm_summable θ) N
    (cubeKernel_summable.comp_injective (fun a b h => by omega))
    (fun n => cubicCosineTerm_bound θ (n+N+1))
  simpa only [cubeKernel,Function.comp_def,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using cube_tail_bound hN

theorem quadratic_sine_tail (θ : ℝ) {N : ℕ} (hN : 1≤N) :
    |quadraticSine θ-quadraticSinePrefix θ N| ≤ 1/(N : ℝ) :=
  real_series_tail_bound (quadraticSineTerm_summable θ) N
    (inverseSquare_summable.comp_injective (fun a b h => by omega))
    (fun n => quadraticSineTerm_bound θ (n+N+1)) (reciprocal_square_tail hN)

theorem harmonic_zero_prefix (N : ℕ) : harmonicPowerPrefix 0 N=0 := by
  apply Finset.sum_eq_zero
  intro n _
  by_cases hn : n=0
  · simp [hn,harmonicPowerTerm,harmonicKernel]
  · simp [harmonicPowerTerm,zero_pow hn]

theorem harmonic_zero_exact : rectangleContains (harmonicPolylog 0) 0 0 0 0 := by
  simp [harmonicPolylog_zero,rectangleContains]

theorem harmonic_endpoint_enclosure {zl zu : ℝ} (hz : zl≤zetaThree ∧ zetaThree≤zu) :
    rectangleContains (harmonicBoundary 0) zl zu 0 0 ∧
      zl≤cubicCosine 0 ∧ cubicCosine 0≤zu ∧ quadraticSine 0=0 := by
  simp only [harmonicBoundary_zero,cubicCosine_zero,quadraticSine_zero,rectangleContains,
    Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨⟨hz.1,hz.2,le_rfl,le_rfl⟩,hz.1,hz.2,True.intro⟩

theorem harmonic_root_finite_average {q : ℕ} (hq : 0<q) (N : ℕ) :
    (∑ a∈Finset.range q,harmonicPowerPrefix (Complex.exp ((rootAngle q a : ℂ)*Complex.I)) N)=
      (q : ℂ)*((∑ n∈Finset.range (N+1),if q∣n then harmonicKernel n else 0 : ℝ) : ℂ) := by
  unfold harmonicPowerPrefix harmonicPowerTerm
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,root_power_sum hq]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp [mul_comm]

theorem harmonic_seed_prefix_binary_enclosure {q N b : ℕ} (hq : 0<q)
    (hN : 1≤N) (hb : 2*N≤2^b) :
    (∑ n∈Finset.range (N+1),if q∣n then harmonicKernel n else 0) ≤ harmonicSeed q ∧
    harmonicSeed q ≤ (∑ n∈Finset.range (N+1),if q∣n then harmonicKernel n else 0)+
      (2*(b : ℝ)+3)/(N : ℝ) := by
  have hs := (harmonicKernel_hasSum.summable.indicator {n : ℕ | q∣n}).congr
    (show ∀ n, {n : ℕ | q∣n}.indicator harmonicKernel n=(if q∣n then harmonicKernel n else 0) by
      intro n; simp [Set.indicator_apply])
  have hsplit := hs.sum_add_tsum_nat_add (N+1)
  have he : (∑' n,if q∣n then harmonicKernel n else 0)=harmonicSeed q := by
    rw [← tsum_multiples hq]
    rfl
  rw [he] at hsplit
  have ht0 : 0≤∑' n,if q∣n+(N+1) then harmonicKernel (n+(N+1)) else 0 :=
    tsum_nonneg (fun n => by split_ifs <;> simp [harmonicKernel_nonneg])
  have htail := (hs.comp_injective
    (show Function.Injective (fun n : ℕ => n+(N+1)) from fun a b h => by dsimp at h; omega)).tsum_le_tsum
    (fun n => show (if q∣n+(N+1) then harmonicKernel (n+(N+1)) else 0) ≤ harmonicKernel (n+(N+1)) by
      split_ifs <;> simp [harmonicKernel_nonneg])
    (harmonicKernel_hasSum.summable.comp_injective (fun a b h => by omega))
  have hb' := harmonic_kernel_binary_tail hN hb
  simp only [← Nat.add_assoc] at hsplit ht0 htail
  constructor <;> linarith

end NField.Alignment.CollisionHarmonicSeriesEnclosure
