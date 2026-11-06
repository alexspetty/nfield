/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.DivisorWindowResidue
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The printed divisor-window estimate from exact divisor pairing -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorWindowCount
open scoped BigOperators Classical
open DivisorWindowPairing DivisorWindowResidue SquareLockCarrierMass SquareLockCountBound

theorem small_divisors_eq_filter {p n : ℕ} (hn : 0<n) :
    smallDivisors p n = (Finset.Icc 1 p).filter (fun k => k∣n) := by
  ext k
  simp only [smallDivisors,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨hk,hkp⟩
    exact ⟨⟨Nat.pos_of_mem_divisors hk,hkp⟩,Nat.dvd_of_mem_divisors hk⟩
  · rintro ⟨⟨hk,hkp⟩,hkd⟩
    exact ⟨Nat.mem_divisors.mpr ⟨hkd,hn.ne'⟩,hkp⟩

theorem window_divisor_sum_pairing {p C : ℕ} (hp : 2≤p) (hhalf : 2*C≤p) :
    (∑ n ∈ Finset.Icc (p^2-C) (p^2+C), (n.divisors.card : ℝ)) ≤
      2*∑ k ∈ Finset.Icc 1 p, ((intervalMultiples (p^2-C) (p^2+C) k).card : ℝ) := by
  have hCsq : C<p^2 := by nlinarith
  have hn (n : ℕ) (hn : n∈Finset.Icc (p^2-C) (p^2+C)) : 0<n ∧ n<(p+1)^2 := by
    have := Finset.mem_Icc.mp hn
    constructor
    · omega
    · nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.Icc (p^2-C) (p^2+C), 2*((smallDivisors p n).card : ℝ) := by
      apply Finset.sum_le_sum
      intro n hni
      exact_mod_cast divisor_count_le_twice_small (hn n hni).1 (hn n hni).2
    _ = 2*∑ n ∈ Finset.Icc (p^2-C) (p^2+C), ((smallDivisors p n).card : ℝ) := by rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      calc
        _ = ∑ n ∈ Finset.Icc (p^2-C) (p^2+C), ∑ k ∈ Finset.Icc 1 p,
            if k∣n then (1:ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hni
          rw [small_divisors_eq_filter (hn n hni).1]
          simp [← Finset.sum_filter]
        _ = ∑ k ∈ Finset.Icc 1 p, ∑ n ∈ Finset.Icc (p^2-C) (p^2+C),
            if k∣n then (1:ℝ) else 0 := Finset.sum_comm
        _ = _ := by simp [intervalMultiples,← Finset.sum_filter]

theorem window_modulus_bound {p C k : ℕ} (hp : p.Prime) (hC : 1≤C)
    (hhalf : 2*C≤p) (hk : k∈Finset.Icc 1 p) :
    ((intervalMultiples (p^2-C) (p^2+C) k).card : ℝ) ≤
      6*(C:ℝ)/(k:ℝ)+(if k∈smallDisplacementCarriers p C ∨ k=p then 1 else 0) := by
  obtain ⟨hk1,hkp⟩ := Finset.mem_Icc.mp hk
  have hk0 : 0<k := by omega
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hCsq : C≤p^2 := by nlinarith [hp.two_le]
  have hwidth : (p^2+C)-(p^2-C)=2*C := by omega
  by_cases hsmall : k≤2*C
  · have hb := interval_multiples_real_bound (show p^2-C≤p^2+C by omega) hk0
    rw [hwidth] at hb
    have hsmallR : (k:ℝ)≤2*C := by exact_mod_cast hsmall
    have hscale : (2:ℝ)≤4*C/k := (le_div_iff₀ hkR).mpr (by nlinarith)
    have hi : (0:ℝ)≤(if k∈smallDisplacementCarriers p C ∨ k=p then 1 else 0) := by split_ifs <;> norm_num
    push_cast at hb
    calc
      _ ≤ (2:ℝ)*C/k+2 := hb
      _ ≤ (6:ℝ)*C/k+(if k∈smallDisplacementCarriers p C ∨ k=p then 1 else 0) := by
        have he : (6:ℝ)*C/k=2*C/k+4*C/k := by ring
        rw [he]
        linarith
  · have hb := window_large_modulus_bound hp hC hhalf (by omega : 2*C<k) hkp
    have hbR : ((intervalMultiples (p^2-C) (p^2+C) k).card : ℝ) ≤
        (if k∈smallDisplacementCarriers p C ∨ k=p then 1 else 0) := by exact_mod_cast hb
    exact hbR.trans (le_add_of_nonneg_left (by positivity))

theorem window_moduli_sum_bound {p C : ℕ} (hp : p.Prime) (hC : 1≤C)
    (hhalf : 2*C≤p) :
    (∑ k ∈ Finset.Icc 1 p, ((intervalMultiples (p^2-C) (p^2+C) k).card : ℝ)) ≤
      6*C*(harmonic p : ℝ)+(smallDisplacementCarriers p C).card+1 := by
  have hind : (∑ k ∈ Finset.Icc 1 p,
      if k∈smallDisplacementCarriers p C ∨ k=p then (1:ℝ) else 0) ≤
      (smallDisplacementCarriers p C).card+1 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul,mul_one]
    have hsub : (Finset.Icc 1 p).filter (fun k => k∈smallDisplacementCarriers p C ∨ k=p) ⊆
        smallDisplacementCarriers p C ∪ {p} := by
      intro k hk
      simpa only [Finset.mem_union,Finset.mem_singleton] using (Finset.mem_filter.mp hk).2
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simpa using (show (((Finset.Icc 1 p).filter (fun k => k∈smallDisplacementCarriers p C ∨ k=p)).card : ℝ) ≤
      ((smallDisplacementCarriers p C ∪ {p}).card : ℝ) from by exact_mod_cast Finset.card_le_card hsub).trans
      (by exact_mod_cast Finset.card_union_le (smallDisplacementCarriers p C) {p})
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 p, (6*(C:ℝ)/(k:ℝ)+
        (if k∈smallDisplacementCarriers p C ∨ k=p then 1 else 0)) := by
      exact Finset.sum_le_sum (fun k hk => window_modulus_bound hp hC hhalf hk)
    _ = 6*C*(harmonic p : ℝ)+∑ k ∈ Finset.Icc 1 p,
        (if k∈smallDisplacementCarriers p C ∨ k=p then (1:ℝ) else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum,div_eq_mul_inv]
    _ ≤ _ := by linarith

/-- Title: `Divisor count in the prime-square window`. -/
theorem prime_square_divisor_window_bound {p C : ℕ} (hp : p.Prime) (hC : 1≤C)
    (hhalf : 2*C≤p) :
    (∑ n ∈ Finset.Icc (p^2-C) (p^2+C), (n.divisors.card : ℝ)) ≤
      5000*((C:ℝ)*Real.log (2*p)+Real.rpow p (2/3:ℝ)*Real.log (2*p)) := by
  have hpR : (1:ℝ)≤p := by exact_mod_cast (show 1≤p from hp.one_lt.le)
  have hL : (1/2:ℝ)≤Real.log (2*p) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hlp : Real.log (p:ℝ)≤Real.log (2*p) := Real.log_le_log (by linarith) (by nlinarith)
  have hH : (harmonic p : ℝ)≤3*Real.log (2*p) := by
    linarith [harmonic_le_one_add_log p]
  have hprod := mul_le_mul_of_nonneg_left hH (show (0:ℝ)≤6*C by positivity)
  have hCR : (1:ℝ)≤C := by exact_mod_cast hC
  have hCL : (1/2:ℝ)≤(C:ℝ)*Real.log (2*p) := by nlinarith
  have hpow : 0≤Real.rpow (p:ℝ) (2/3:ℝ)*Real.log (2*p) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (by linarith)
  have hb := window_divisor_sum_pairing hp.two_le hhalf
  have hm := window_moduli_sum_bound hp hC hhalf
  have hs := square_lock_count_bound p C hp.two_le hC
  nlinarith

end NField.Alignment.DivisorWindowCount
