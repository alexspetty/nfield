/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerWeightedDiscrepancy

/-! # Positive-frequency weighted discrepancy -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.FejerPositiveFrequencies
open FejerWeightedWindow FejerWeightedDiscrepancy
open scoped BigOperators Classical ComplexConjugate

def positiveError {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ‖∑ i ∈ s, (w i : ℂ)*fourier (h : ℤ) (x i)‖ / h

theorem weighted_negative_norm {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (k : ℤ) :
    ‖∑ i ∈ s, (w i : ℂ)*fourier (-k) (x i)‖ =
      ‖∑ i ∈ s, (w i : ℂ)*fourier k (x i)‖ := by
  have he : (∑ i ∈ s, (w i : ℂ)*fourier (-k) (x i)) =
      conj (∑ i ∈ s, (w i : ℂ)*fourier k (x i)) := by
    simp [map_sum, map_mul]
  rw [he, Complex.norm_conj]

theorem frequency_partition (H : ℕ) : (frequencies H).erase 0 =
    (Finset.Icc 1 H).image (fun n : ℕ => (n : ℤ)) ∪
      (Finset.Icc 1 H).image (fun n : ℕ => -(n : ℤ)) := by
  ext k
  simp only [frequencies, Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hk, hlo, hhi⟩
    by_cases hp : 0 ≤ k
    · left
      have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hp
      exact ⟨k.toNat, by omega, he⟩
    · right
      have he : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      exact ⟨(-k).toNat, by omega, by omega⟩
  · rintro (⟨n, ⟨hlo, hhi⟩, rfl⟩ | ⟨n, ⟨hlo, hhi⟩, rfl⟩) <;> omega

/-- Both signs of every nonzero mode contribute the same amount. -/
theorem spectralError_pairing {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (x : ι → AddCircle (1 : ℝ)) (H : ℕ) :
    spectralError s w x H = (2/Real.pi)*positiveError s w x H := by
  have hd : Disjoint ((Finset.Icc 1 H).image (fun n : ℕ => (n : ℤ)))
      ((Finset.Icc 1 H).image (fun n : ℕ => -(n : ℤ))) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hl
    simp only [Finset.mem_Icc] at hn hm
    omega
  unfold spectralError
  rw [frequency_partition, Finset.sum_union hd, Finset.sum_image, Finset.sum_image]
  · simp only [weighted_negative_norm, Int.cast_neg, Int.cast_natCast, abs_neg]
    unfold positiveError
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    ring
  · intro n hn m hm he
    change -(n : ℤ) = -(m : ℤ) at he
    exact_mod_cast (neg_injective he)
  · intro n hn m hm he
    change (n : ℤ) = (m : ℤ) at he
    exact_mod_cast he

/-- Soft weighted discrepancy in positive-frequency form, uniform in the threshold. -/
theorem weighted_discrepancy {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (H : ℕ) (hH : 16 ≤ H) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |thresholdSum s w t α - α*(∑ i ∈ s, w i)| ≤
      4*((Real.sqrt (H : ℝ))⁻¹*(∑ i ∈ s, w i) +
        positiveError s w (fun i => (t i : AddCircle (1 : ℝ))) H) := by
  have he := discrepancy_sqrt s w t hw H hH α hα0 hα1
  rw [spectralError_pairing] at he
  have hp : 0 ≤ positiveError s w (fun i => (t i : AddCircle (1 : ℝ))) H := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hc : 2/Real.pi ≤ 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.two_le_pi]
  have hh := mul_le_mul_of_nonneg_right hc hp
  nlinarith

end NField.Alignment.FejerPositiveFrequencies
