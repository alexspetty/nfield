/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.BernoulliSmoothingFourier
import NField.Alignment.ReciprocalArcBlock

/-! # Exact smoothing error and square-root frequency bounds on reciprocal blocks -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalSawtoothSmoothing
open scoped BigOperators Classical
open CollisionDedekindPairing RealSawtoothDistribution BernoulliSymmetricSmoothing
  ReciprocalArcBlock ReciprocalSecondMoment ReciprocalWeightedBlocks

def sawtoothPrefix (p M : ℕ) (Q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, periodicSawtooth (Q/((p+i+1 : ℕ) : ℝ))

def smoothedPrefix (p M : ℕ) (Q δ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, smoothedSaw δ (Q/((p+i+1 : ℕ) : ℝ))

theorem sawtooth_prefix_trivial (p M : ℕ) (Q : ℝ) : |sawtoothPrefix p M Q| ≤ M/2 := by
  unfold sawtoothPrefix
  calc
    _ ≤ ∑ i ∈ Finset.range M, |periodicSawtooth (Q/((p+i+1 : ℕ) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range M, (1/2 : ℝ) :=
      Finset.sum_le_sum (fun _ _ => sawtooth_abs_bound _)
    _ = _ := by simp; ring

/-- The exact smoothing error is paid only at the selected short-arc points. -/
theorem block_smoothing_error (p M H : ℕ) (X T : ℝ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hH : 2 ≤ H) (hpX : (p : ℝ) ≤ X)
    (hHT : (p : ℝ)/(H : ℝ) ≤ T) (hT : 0 < T)
    (hX : X^2 ≤ T^3) (hlog : (p : ℝ)*(1+Real.log p) ≤ 4*T^2) :
    |sawtoothPrefix p M (X^2)-smoothedPrefix p M (X^2) (1/(H : ℝ))| ≤ 1160*T := by
  have hH0 : (0 : ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hδ : 0 < 1/(H : ℝ) := by positivity
  have hδ1 : 1/(H : ℝ) ≤ 1/2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2)
    exact_mod_cast hH
  let s := (Finset.range M).filter fun i =>
    ∃ z : ℤ, |X^2/((p+i+1 : ℕ) : ℝ)-z| ≤ 1/(H : ℝ)
  have herr : |sawtoothPrefix p M (X^2)-smoothedPrefix p M (X^2) (1/(H : ℝ))| ≤
      (s.card : ℝ) := by
    unfold sawtoothPrefix smoothedPrefix
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ Finset.range M,
          |periodicSawtooth (X^2/((p+i+1 : ℕ) : ℝ))-
            smoothedSaw (1/(H : ℝ)) (X^2/((p+i+1 : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range M,
          if ∃ z : ℤ, |X^2/((p+i+1 : ℕ) : ℝ)-z| ≤ 1/(H : ℝ) then (1 : ℝ) else 0 :=
        Finset.sum_le_sum (fun _ _ => smoothed_error_bound hδ hδ1 _)
      _ = _ := by simp [s,Finset.sum_boole]
  apply herr.trans
  apply reciprocal_arc_block p M X ((p : ℝ)/(H : ℝ)) T s hp hM hpX
    (by positivity) hHT hT hX hlog (Finset.filter_subset _ _)
  intro i hi
  obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hi).2
  refine ⟨z,?_⟩
  have he : ((p : ℝ)/(H : ℝ))/(p : ℝ)=1/(H : ℝ) := by field_simp
  rwa [he]

/-- A frequency bound with its square-root dependence retained explicitly. -/
theorem reciprocal_frequency_root_bound (p M n : ℕ) (Q : ℝ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hn : 1 ≤ n) (hPQ : (p : ℝ)^2 ≤ Q) :
    ‖reciprocalPrefix p M ((n : ℝ)*Q)‖ ≤
      6*Real.sqrt (Q/(p : ℝ))*Real.sqrt (n : ℝ)+
        64*Real.sqrt ((p : ℝ)*(1+Real.log p)) := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast hp
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
  have hQ : 0 < Q := (sq_pos_of_pos hp0).trans_le hPQ
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hqn : (p : ℝ)^2 ≤ (n : ℝ)*Q := by nlinarith
  have hb := reciprocal_prefix_sq_bound p M ((n : ℝ)*Q) hp hM hqn
  have ha : (6*Real.sqrt (Q/(p : ℝ))*Real.sqrt (n : ℝ))^2 =
      36*(Q/(p : ℝ))*(n : ℝ) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),
      Real.sq_sqrt (by positivity : 0 ≤ Q/(p : ℝ))]
    norm_num
  have hc : (64*Real.sqrt ((p : ℝ)*(1+Real.log p)))^2 =
      4096*(p : ℝ)*(1+Real.log p) := by
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)*(1+Real.log p))]
    ring
  have hnonneg : 0 ≤ 6*Real.sqrt (Q/(p : ℝ))*Real.sqrt (n : ℝ) := by positivity
  have hnonneg' : 0 ≤ 64*Real.sqrt ((p : ℝ)*(1+Real.log p)) := by positivity
  have he : 32*((n : ℝ)*Q)/(p : ℝ)=32*(Q/(p : ℝ))*(n : ℝ) := by ring
  rw [he] at hb
  nlinarith [mul_nonneg hnonneg hnonneg',div_pos hQ hp0]

end NField.Alignment.ReciprocalSawtoothSmoothing
