/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.ReciprocalFloorSmoothing

/-! # Choosing the smoothing cutoff uniformly on every nontrivial block -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalSmoothingCutoff
open scoped BigOperators

theorem cutoff_constraints (p : ℕ) (X T : ℝ)
    (hT : 1 ≤ T) (hpT : 2*T < (p : ℝ)) (hpX : (p : ℝ) ≤ X)
    (hXT : X^2 ≤ T^3) (hlog : X*(2+Real.log (X^2))^3 ≤ T^2) :
    let H : ℕ := ⌈(p : ℝ)/T⌉₊
    2 ≤ H ∧ H ≤ p ∧ (p : ℝ)/(H : ℝ) ≤ T ∧
      X^2/(p : ℝ)*(H : ℝ) ≤ 4*T^2 ∧
      (p : ℝ)*(1+Real.log p) ≤ 4*T^2 ∧
      (p : ℝ)*(1+Real.log p)*((harmonic H : ℝ)+1)^2 ≤ T^2 := by
  let H : ℕ := ⌈(p : ℝ)/T⌉₊
  have hT0 : 0<T := by linarith
  have hp0 : (0 : ℝ)<p := by linarith
  have hp1 : (1 : ℝ)≤p := by linarith
  have hX1 : 1≤X := hp1.trans hpX
  have hX0 : 0<X := by linarith
  have hpQ : (p : ℝ)≤X^2 := by nlinarith
  have hQ1 : 1≤X^2 := by nlinarith
  have hHlow : (p : ℝ)/T ≤ H := Nat.le_ceil _
  have hHhigh : (H : ℝ)<(p : ℝ)/T+1 := Nat.ceil_lt_add_one (by positivity)
  have hH2 : 2≤H := by
    have : 2 < (p : ℝ)/T := (lt_div_iff₀ hT0).mpr (by linarith)
    have : (2 : ℝ)<H := this.trans_le hHlow
    exact_mod_cast (by linarith : (2 : ℝ)≤H)
  have hH0 : (0 : ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have hHp : H≤p := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hT0).mpr
    nlinarith
  have hHT : (p : ℝ)/(H : ℝ)≤T := by
    apply (div_le_iff₀ hH0).mpr
    have := (div_le_iff₀ hT0).mp hHlow
    nlinarith
  have hHtwice : (H : ℝ)≤2*((p : ℝ)/T) := by
    have : 2 < (p : ℝ)/T := (lt_div_iff₀ hT0).mpr (by linarith)
    linarith
  have hfreq : X^2/(p : ℝ)*(H : ℝ)≤4*T^2 := by
    calc
      _ ≤ X^2/(p : ℝ)*(2*((p : ℝ)/T)) :=
        mul_le_mul_of_nonneg_left hHtwice (by positivity)
      _ = 2*X^2/T := by field_simp
      _ ≤ 2*T^2 := by apply (div_le_iff₀ hT0).mpr; nlinarith
      _ ≤ _ := by nlinarith [sq_nonneg T]
  let L := 2+Real.log (X^2)
  have hL2 : 2≤L := by dsimp [L]; linarith [Real.log_nonneg hQ1]
  have hlogp : 0≤Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlogpq : Real.log (p : ℝ)≤Real.log (X^2) := Real.log_le_log hp0 hpQ
  have hlogH : Real.log (H : ℝ)≤Real.log (X^2) :=
    Real.log_le_log hH0 ((by exact_mod_cast hHp : (H : ℝ)≤p).trans hpQ)
  have hhmass : (harmonic H : ℝ)+1 ≤ L := by
    have hh := harmonic_le_one_add_log H
    dsimp [L]
    linarith
  have hh0 : 0≤(harmonic H : ℝ)+1 := by
    have hh : (0 : ℝ)≤harmonic H := by
      rw [harmonic_eq_sum_Icc,Rat.cast_sum]
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hbase : (p : ℝ)*(1+Real.log p)≤X*L := by
    apply mul_le_mul hpX (by dsimp [L]; linarith) (by positivity) hX0.le
  have hmass : (p : ℝ)*(1+Real.log p)*((harmonic H : ℝ)+1)^2≤T^2 := by
    calc
      _ ≤ (X*L)*L^2 := mul_le_mul hbase (pow_le_pow_left₀ hh0 hhmass 2)
        (sq_nonneg _) (by positivity)
      _ = X*L^3 := by ring
      _ ≤ T^2 := hlog
  have hbaseT : (p : ℝ)*(1+Real.log p)≤4*T^2 := by
    have hpow : L≤L^3 := by nlinarith [sq_nonneg (L-1)]
    have hXL : X*L≤T^2 := (mul_le_mul_of_nonneg_left hpow hX0.le).trans hlog
    nlinarith [sq_nonneg T]
  exact ⟨hH2,hHp,hHT,hfreq,hbaseT,hmass⟩

end NField.Alignment.ReciprocalSmoothingCutoff
