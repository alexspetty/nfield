/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothRough
import NField.Alignment.HarperRetainedSum

/-!
# Exact retained support and its rough-factor fibers

The retained support excludes positive y-smooth integers. At P <= y this
condition depends only on the canonical P-rough part. A fiber over m is
exactly multiplication by m of the P-smooth integers through N/m.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRoughSupport

open scoped BigOperators
open HarperSmoothRough HarperSmoothDivisor HarperSmoothCount
  HarperSmoothConvolution HarperRetainedSum CollisionMertensInput

def retainedSupport (N : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n ∉ smoothIntegers y)

def roughSupport (N : ℕ) (P y : ℝ) : Finset ℕ :=
  (retainedSupport N y).filter (fun m => m.Coprime (primeBase P))

theorem smooth_mono {P y : ℝ} (hPy : P ≤ y) {n : ℕ} (hn : n ∈ smoothIntegers P) :
    n ∈ smoothIntegers y := by
  obtain ⟨hn0, hn⟩ := smoothIntegers_mem.mp hn
  exact smoothIntegers_mem.mpr ⟨hn0, fun r hr hd => (hn r hr hd).trans hPy⟩

theorem roughPart_dvd {b n : ℕ} (hn : 0 < n) : roughPart b n ∣ n :=
  ⟨supportedPart b n, (roughPart_mul_supportedPart hn).symm⟩

theorem smooth_iff_rough_smooth {P y : ℝ} (hPy : P ≤ y) {n : ℕ} (hn : 0 < n) :
    n ∈ smoothIntegers y ↔ roughPart (primeBase P) n ∈ smoothIntegers y := by
  constructor
  · intro h
    exact smooth_of_dvd h (roughPart_dvd hn)
  · intro h
    have hs := smooth_mono hPy (canonical_smooth_part (P := P) hn)
    simpa only [roughPart_mul_supportedPart hn] using smooth_mul h hs

theorem roughPart_self {P : ℝ} {m : ℕ} (hm : 0 < m) (hcop : m.Coprime (primeBase P)) :
    roughPart (primeBase P) m = m := by
  simpa only [mul_one] using
    roughPart_mul_of_supported_coprime hm (by decide : 0 < 1) (supported_one _) hcop

theorem retained_rough_image {P y : ℝ} (hPy : P ≤ y) (N : ℕ) :
    (retainedSupport N y).image (roughPart (primeBase P)) = roughSupport N P y := by
  classical
  ext m
  constructor
  · rintro hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hn, hns⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 < n := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨roughPart_pos hn0, (Nat.le_of_dvd hn0 (roughPart_dvd hn0)).trans hnN⟩, ?_⟩,
      roughPart_coprime_base hn0⟩
    exact fun h => hns ((smooth_iff_rough_smooth hPy hn0).mpr h)
  · intro hm
    obtain ⟨hm, hcop⟩ := Finset.mem_filter.mp hm
    have hm0 : 0 < m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    exact Finset.mem_image.mpr ⟨m, hm, roughPart_self hm0 hcop⟩

theorem smoothSet_quotient (N m : ℕ) (P : ℝ) :
    smoothSet ((N : ℝ) / (m : ℝ)) P =
      (Finset.Icc 1 (N / m)).filter (fun d => d ∈ smoothIntegers P) := by
  ext d
  simp only [smoothSet, Nat.floor_div_eq_div, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_Icc, Nat.succ_le_iff]

/-- Multiplication by a positive rough m gives precisely its retained fiber. -/
theorem smooth_mul_mem_fiber {N m d : ℕ} {P y : ℝ}
    (hm : m ∈ roughSupport N P y) (hd : d ∈ smoothSet ((N : ℝ) / (m : ℝ)) P) :
    m * d ∈ (retainedSupport N y).filter (fun n => roughPart (primeBase P) n = m) := by
  obtain ⟨hm, hcop⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmrange, hmnot⟩ := Finset.mem_filter.mp hm
  have hm0 : 0 < m := (Finset.mem_Icc.mp hmrange).1
  rw [smoothSet_quotient] at hd
  obtain ⟨hdrange, hds⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd0, hdN⟩ := Finset.mem_Icc.mp hdrange
  have hle : m * d ≤ N := by
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hdN
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hm0 hd0, hle⟩, ?_⟩, ?_⟩
  · intro h
    exact hmnot (smooth_of_dvd h (dvd_mul_right m d))
  · exact roughPart_mul_of_supported_coprime hm0 hd0
      ((supported_iff_smooth hd0).mpr hds) hcop

theorem smooth_part_mem_quotient {N m n : ℕ} {P y : ℝ}
    (hn : n ∈ (retainedSupport N y).filter (fun n => roughPart (primeBase P) n = m)) :
    supportedPart (primeBase P) n ∈ smoothSet ((N : ℝ) / (m : ℝ)) P := by
  obtain ⟨hn, he⟩ := Finset.mem_filter.mp hn
  have hnrange := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hn0 : 0 < n := hnrange.1
  have hm0 : 0 < m := he ▸ roughPart_pos hn0
  rw [smoothSet_quotient]
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨supportedPart_pos hn0, ?_⟩,
    canonical_smooth_part hn0⟩
  apply (Nat.le_div_iff_mul_le hm0).mpr
  rw [mul_comm, ← he, roughPart_mul_supportedPart hn0]
  exact hnrange.2

theorem smooth_fiber_sum {N m : ℕ} {P y : ℝ} (hm : m ∈ roughSupport N P y)
    (w z : ℕ → ℂ) :
    (∑ n ∈ (retainedSupport N y).filter (fun n => roughPart (primeBase P) n = m),
      w n * z (supportedPart (primeBase P) n)) =
      ∑ d ∈ smoothSet ((N : ℝ) / (m : ℝ)) P, w (m*d) * z d := by
  classical
  have hm0 : 0 < m :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1).1
  have hcop := (Finset.mem_filter.mp hm).2
  symm
  apply Finset.sum_bij (fun d _ => m*d)
  · exact fun d hd => smooth_mul_mem_fiber hm hd
  · intro d hd e he h
    exact (Nat.mul_left_cancel_iff hm0).mp h
  · intro n hn
    refine ⟨supportedPart (primeBase P) n, smooth_part_mem_quotient hn, ?_⟩
    have hn0 : 0 < n :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1
    rw [← (Finset.mem_filter.mp hn).2, roughPart_mul_supportedPart hn0]
  · intro d hd
    have hds := smoothSet_mem.mp hd
    rw [supportedPart_mul_of_supported_coprime hm0 hds.1
      ((supported_iff_smooth hds.1).mpr hds.2.2) hcop]

theorem rough_coprime_iff (P : ℝ) (m : ℕ) :
    m.Coprime (primeBase P) ↔ ∀ r : ℕ, r.Prime → r ∣ m → P < (r : ℝ) := by
  constructor
  · intro h r hr hd
    by_contra hn
    have hb := (prime_dvd_primeBase hr).mpr (primesUpTo_mem.mpr ⟨hr, le_of_not_gt hn⟩)
    have hdiv := Nat.dvd_gcd hd hb
    rw [h.gcd_eq_one] at hdiv
    exact hr.not_dvd_one hdiv
  · intro h
    by_contra hc
    obtain ⟨r, hr, hm, hb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact (not_lt_of_ge (primesUpTo_mem.mp ((prime_dvd_primeBase hr).mp hb)).2) (h r hr hm)

theorem not_smooth_iff_large_prime {n : ℕ} (hn : 0 < n) (y : ℝ) :
    n ∉ smoothIntegers y ↔ ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ y < (r : ℝ) := by
  classical
  constructor
  · intro h
    by_contra hex
    apply h
    refine smoothIntegers_mem.mpr ⟨hn.ne', ?_⟩
    intro r hr hd
    apply le_of_not_gt
    intro hy
    exact hex ⟨r, hr, hd, hy⟩
  · rintro ⟨r, hr, hd, hy⟩ hs
    exact (not_lt_of_ge ((smoothIntegers_mem.mp hs).2 r hr hd)) hy

theorem roughSupport_mem {N m : ℕ} {P y : ℝ} :
    m ∈ roughSupport N P y ↔
      0 < m ∧ m ≤ N ∧ (∀ r : ℕ, r.Prime → r ∣ m → P < (r : ℝ)) ∧
        ∃ r : ℕ, r.Prime ∧ r ∣ m ∧ y < (r : ℝ) := by
  simp only [roughSupport, retainedSupport, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hpos, hle⟩, hnot⟩, hcop⟩
    exact ⟨hpos, hle, (rough_coprime_iff P m).mp hcop,
      (not_smooth_iff_large_prime hpos y).mp hnot⟩
  · rintro ⟨hpos, hle, hrough, hlarge⟩
    exact ⟨⟨⟨hpos, hle⟩, (not_smooth_iff_large_prime hpos y).mpr hlarge⟩,
      (rough_coprime_iff P m).mpr hrough⟩

theorem roughSupport_gt_y {N m : ℕ} {P y : ℝ} (hm : m ∈ roughSupport N P y) :
    y < (m : ℝ) := by
  obtain ⟨hm0, _, _, r, hr, hd, hy⟩ := roughSupport_mem.mp hm
  exact hy.trans_le (by exact_mod_cast Nat.le_of_dvd hm0 hd)

theorem retained_sum_eq_support (N : ℕ) (y : ℝ) (w z : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, retainedCoefficient y w n * z n) =
      ∑ n ∈ retainedSupport N y, w n * z n := by
  rw [retainedSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n ∈ smoothIntegers y <;> simp [retainedCoefficient, hn]

end NField.Alignment.HarperRoughSupport
