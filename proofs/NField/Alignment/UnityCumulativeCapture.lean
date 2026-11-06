/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityFiniteGram

/-!
# Cumulative native capture and complete recovery

These are conditional recovery criteria for actual native gains. The
hypotheses that their normalized sums diverge are not asserted or removed.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityCumulativeCapture
open scoped BigOperators
open Filter Topology
open UnityNativeHilbert UnityNativeProjection UnityFiniteGram

/-- Any achievable native gain is paid into reciprocal deficit. -/
theorem gain_le_capacity_step {N M : ℕ} (hNM : N≤M) (G : ℝ)
    (hG : G≤deficit N-deficit M) : G/(deficit N)^2 ≤ capacity M-capacity N := by
  rw [capacity_difference]
  calc
    G/(deficit N)^2 ≤ (deficit N-deficit M)/(deficit N)^2 :=
      div_le_div_of_nonneg_right hG (sq_nonneg _)
    _ ≤ (deficit N-deficit M)/(deficit N*deficit M) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr (deficit_antitone hNM))
        (mul_pos (deficit_pos N) (deficit_pos M))
        (by nlinarith [deficit_antitone hNM, deficit_pos N])

/-- Title: `Normalized capture is paid into native capacity`.

 Literal capacity telescope along any admitted increasing cutoffs. -/
theorem capacity_telescope (cutoff : ℕ → ℕ) (hcut : Monotone cutoff) (G : ℕ → ℝ)
    (hG : ∀k, G k≤deficit (cutoff k)-deficit (cutoff (k+1))) (K : ℕ) :
    (∑ k ∈ Finset.range K, G k/(deficit (cutoff k))^2) ≤
      capacity (cutoff K)-capacity (cutoff 0) := by
  calc
    _ ≤ ∑ k ∈ Finset.range K, (capacity (cutoff (k+1))-capacity (cutoff k)) := by
      apply Finset.sum_le_sum
      intro k _
      exact gain_le_capacity_step (hcut (by omega)) (G k) (hG k)
    _ = _ := Finset.sum_range_sub (fun k => capacity (cutoff k)) K

/-- Divergence of actual normalized capture forces unbounded native capacity. -/
theorem normalized_capture_capacity (cutoff : ℕ → ℕ) (hcut : Monotone cutoff) (G : ℕ → ℝ)
    (hG0 : ∀k, 0≤G k) (hG : ∀k, G k≤deficit (cutoff k)-deficit (cutoff (k+1)))
    (hdiv : ¬Summable (fun k => G k/(deficit (cutoff k))^2)) :
    Tendsto capacity atTop atTop := by
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => div_nonneg (hG0 k) (sq_nonneg _))).mp hdiv
  have hc : Tendsto (fun K => capacity (cutoff K)) atTop atTop := by
    apply tendsto_atTop_mono _ ht
    intro K
    have h := capacity_telescope cutoff hcut G hG K
    have hp : 0≤capacity (cutoff 0) := inv_nonneg.mpr (deficit_pos _).le
    linarith
  exact tendsto_atTop_of_monotone_of_subseq capacity_monotone hc

theorem normalized_capture_recovery (cutoff : ℕ → ℕ) (hcut : Monotone cutoff) (G : ℕ → ℝ)
    (hG0 : ∀k, 0≤G k) (hG : ∀k, G k≤deficit (cutoff k)-deficit (cutoff (k+1)))
    (hdiv : ¬Summable (fun k => G k/(deficit (cutoff k))^2)) :
    Tendsto deficit atTop (𝓝 0) := by
  have hc := normalized_capture_capacity cutoff hcut G hG0 hG hdiv
  have h := tendsto_inv_atTop_zero.comp hc
  simpa only [Function.comp_def, capacity, inv_inv] using h

/-- Title: `Unnormalized native gains have a finite total budget`.

 Unnormalized achievable gains always have a finite native budget. -/
theorem total_gain_budget (cutoff : ℕ → ℕ) (G : ℕ → ℝ)
    (hG0 : ∀k, 0≤G k) (hG : ∀k, G k≤deficit (cutoff k)-deficit (cutoff (k+1))) :
    Summable G ∧ (∑' k, G k)≤deficit (cutoff 0) := by
  have hs (K : ℕ) : (∑ k ∈ Finset.range K, G k)≤deficit (cutoff 0) := by
    calc
      _ ≤ ∑ k ∈ Finset.range K, (deficit (cutoff k)-deficit (cutoff (k+1))) :=
        Finset.sum_le_sum (fun k _ => hG k)
      _ = deficit (cutoff 0)-deficit (cutoff K) := Finset.sum_range_sub' _ _
      _ ≤ deficit (cutoff 0) := sub_le_self _ (deficit_pos _).le
  exact ⟨summable_of_sum_range_le hG0 hs, Real.tsum_le_of_sum_range_le hG0 hs⟩

/-- The weaker fractional normalization still suffices for recovery. -/
theorem fractional_capture_recovery (cutoff : ℕ → ℕ) (hcut : Monotone cutoff) (G : ℕ → ℝ)
    (hG0 : ∀k, 0≤G k) (hG : ∀k, G k≤deficit (cutoff k)-deficit (cutoff (k+1)))
    (hdiv : ¬Summable (fun k => G k/deficit (cutoff k))) :
    Tendsto deficit atTop (𝓝 0) := by
  apply normalized_capture_recovery cutoff hcut G hG0 hG
  intro hs
  apply hdiv
  apply Summable.of_nonneg_of_le (fun k => div_nonneg (hG0 k) (deficit_pos _).le) _ hs
  intro k
  apply div_le_div_of_nonneg_left (hG0 k) (sq_pos_of_pos (deficit_pos _))
  have hp := deficit_pos (cutoff k)
  have h1 := deficit_le_one (cutoff k)
  nlinarith

/-- The manuscript's geometric chain, including its prescribed block length. -/
def chain (N₀ L k : ℕ) : ℕ := N₀*4^(L*k)

theorem chain_monotone (N₀ L : ℕ) : Monotone (chain N₀ L) := by
  intro i j hij
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left L hij)

/-- Title: `Divergent native capture forces complete recovery`.

 Actual finite probe gains satisfy the full divergent-capture criterion. -/
theorem actual_probe_capture {ι : ℕ → Type*} [∀k, Fintype (ι k)]
    (N₀ L : ℕ) (v : ∀k, ι k → NativeHilbert)
    (hv : ∀k i, v k i∈clockSpace (chain N₀ L (k+1)))
    (hdiv : ¬Summable (fun k => jointGain (v k) (UnityNativeHilbert.residual (chain N₀ L k)) /
      (deficit (chain N₀ L k))^2)) :
    Tendsto capacity atTop atTop ∧ Tendsto deficit atTop (𝓝 0) := by
  let G := fun k => jointGain (v k) (UnityNativeHilbert.residual (chain N₀ L k))
  have hG0 : ∀k, 0≤G k := fun k => jointGain_nonneg _ _
  have hG : ∀k, G k≤deficit (chain N₀ L k)-deficit (chain N₀ L (k+1)) := fun k =>
    jointGain_le_native_gain (chain_monotone N₀ L (by omega)) (v k) (hv k)
  exact ⟨normalized_capture_capacity _ (chain_monotone N₀ L) G hG0 hG hdiv,
    normalized_capture_recovery _ (chain_monotone N₀ L) G hG0 hG hdiv⟩

/-- Title: `Cumulative fractional capture forces native recovery`.

 The cumulative fractional-capture proposition for actual native finite families. -/
theorem actual_fractional_capture {ι : ℕ → Type*} [∀k, Fintype (ι k)]
    (N₀ L : ℕ) (v : ∀k, ι k → NativeHilbert)
    (hv : ∀k i, v k i∈clockSpace (chain N₀ L (k+1))) :
    let G := fun k => jointGain (v k) (UnityNativeHilbert.residual (chain N₀ L k))
    (¬Summable (fun k => G k/deficit (chain N₀ L k)) → Tendsto deficit atTop (𝓝 0)) ∧
      Summable G ∧ (∑' k, G k)≤deficit N₀ := by
  dsimp only
  let G := fun k => jointGain (v k) (UnityNativeHilbert.residual (chain N₀ L k))
  have hG0 : ∀k, 0≤G k := fun k => jointGain_nonneg _ _
  have hG : ∀k, G k≤deficit (chain N₀ L k)-deficit (chain N₀ L (k+1)) := fun k =>
    jointGain_le_native_gain (chain_monotone N₀ L (by omega)) (v k) (hv k)
  refine ⟨fun hdiv => fractional_capture_recovery _ (chain_monotone N₀ L) G hG0 hG hdiv, ?_⟩
  simpa [G, chain] using total_gain_budget (chain N₀ L) G hG0 hG

end NField.Alignment.UnityCumulativeCapture
