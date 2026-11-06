/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaProductCutoffCompletion
import NField.Alignment.FiniteIntervalCompletion

/-! # Harmonic cost of the actual coupled product cutoff -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaProductCutoffCost
open KaratsubaProductCutoffCompletion SpectralPower
open scoped BigOperators Classical

def prefixIndicator {m : ℕ} [NeZero m] (N : ℕ) (t : ZMod m) : ℂ :=
  if t.val < N then 1 else 0

/-- The exact transform of an initial segment is the checked interval transform. -/
theorem dft_prefixIndicator {m N : ℕ} [NeZero m] (hN : N ≤ m) (c : ZMod m) :
    ZMod.dft (prefixIndicator N) c = intervalFourier m N c := by
  rw [ZMod.dft_apply]
  rw [← (ZMod.finEquiv m).toEquiv.sum_comp]
  have heq : (∑ t : Fin m, ZMod.stdAddChar (-(((ZMod.finEquiv m).toEquiv t)*c)) •
      prefixIndicator N ((ZMod.finEquiv m).toEquiv t)) =
      ∑ n ∈ Finset.range m, if n < N then ZMod.stdAddChar (-((n : ZMod m)*c)) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    rw [show ((ZMod.finEquiv m).toEquiv t : ZMod m) = (t.val : ZMod m) by
      simpa using ConductorDepthSawtooth.finEquiv_eq_natCast t]
    unfold prefixIndicator
    rw [ZMod.val_natCast_of_lt t.isLt]
    by_cases hc : t.val < N <;> simp [hc, smul_eq_mul]
  rw [heq]
  have hf : (Finset.range m).filter (fun n => n < N) = Finset.range N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hf]
  unfold intervalFourier
  rfl

/-- The normalized Fourier L1 cost of any initial segment is at most one plus a harmonic sum. -/
theorem prefix_completionCost_le {m N : ℕ} [NeZero m] (hN : N ≤ m) :
    completionCost (prefixIndicator (m := m) N) ≤ 1+(harmonic m : ℝ) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold completionCost
  simp_rw [dft_prefixIndicator hN]
  apply (div_le_iff₀ hmR).mpr
  have hh := FiniteIntervalCompletion.interval_fourier_norm_sum hm N
  have hNR : (N : ℝ) ≤ m := by exact_mod_cast hN
  nlinarith only [hh, hNR]

/-- A positive product cap is exactly an initial segment, with its zero residue retained. -/
theorem productCutoff_eq_prefix {m : ℕ} [NeZero m] (l h X : ℕ) (hl : 0 < l) (hh : 0 < h) :
    productCutoff (m := m) l h X = prefixIndicator (min m (X/(l^2*h)+1)) := by
  funext t
  have hd : 0 < l^2*h := Nat.mul_pos (pow_pos hl 2) hh
  have ht : t.val < m := ZMod.val_lt t
  have hc : l^2*t.val*h ≤ X ↔ t.val < min m (X/(l^2*h)+1) := by
    rw [lt_min_iff]
    constructor
    · intro hcap
      refine ⟨ht, ?_⟩
      have hdiv : t.val ≤ X/(l^2*h) := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith only [hcap])
      omega
    · rintro ⟨_, hval⟩
      have hdiv : t.val ≤ X/(l^2*h) := by omega
      have hp := (Nat.le_div_iff_mul_le hd).mp hdiv
      nlinarith only [hp]
  unfold productCutoff prefixIndicator
  simp only [hc]

/-- The literal coupled cutoff has uniform harmonic completion cost. -/
theorem product_completionCost_le {m : ℕ} [NeZero m] (l h X : ℕ) (hl : 0 < l) (hh : 0 < h) :
    completionCost (productCutoff (m := m) l h X) ≤ 1+(harmonic m : ℝ) := by
  rw [productCutoff_eq_prefix l h X hl hh]
  exact prefix_completionCost_le (min_le_left _ _)

/-- The coupled cutoff loses at most a harmonic factor against the full shifted bilinear family. -/
theorem norm_productCutoffSum_le_harmonic (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (l h X : ℕ) (hl : 0 < l) (hh : 0 < h) (a b : ZMod m)
    (hrect : ∀ p ∈ P, ∀ q ∈ Q, p*q < m) {B : ℝ}
    (hbound : ∀ c : ZMod m, ‖KaratsubaBilinearReduction.bilinearPrimeSum P Q a (b+c)‖ ≤ B) :
    ‖productCutoffSum P Q l h X a b‖ ≤ (1+(harmonic m : ℝ))*B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbound 0)
  exact (norm_productCutoffSum_le P Q l h X a b hrect hbound).trans
    (mul_le_mul_of_nonneg_right (product_completionCost_le l h X hl hh) hB)

end NField.Alignment.KaratsubaProductCutoffCost
