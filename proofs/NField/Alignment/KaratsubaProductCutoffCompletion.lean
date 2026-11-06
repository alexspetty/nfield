/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSubsetBilinear
import Mathlib.Analysis.Fourier.ZMod

/-! # Exact cyclic completion of a coupled prime-product cutoff -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaProductCutoffCompletion
open KaratsubaBilinearReduction
open scoped BigOperators Classical

def phase {m : ℕ} [NeZero m] (a b : ZMod m) (p q : ℕ) : ℂ :=
  ZMod.stdAddChar (a*(p : ZMod m)⁻¹*(q : ZMod m)⁻¹+b*(p : ZMod m)*(q : ZMod m))

def weightedProductSum (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (a b : ZMod m) (W : ZMod m → ℂ) : ℂ :=
  ∑ p ∈ P, ∑ q ∈ Q, W ((p : ZMod m)*(q : ZMod m))*phase a b p q

def completionCost {m : ℕ} [NeZero m] (W : ZMod m → ℂ) : ℝ :=
  (∑ c : ZMod m, ‖ZMod.dft W c‖)/(m : ℝ)

def productCutoff {m : ℕ} [NeZero m] (l h X : ℕ) (t : ZMod m) : ℂ :=
  if l^2*t.val*h ≤ X then 1 else 0

def productCutoffSum (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (l h X : ℕ) (a b : ZMod m) : ℂ :=
  ∑ p ∈ P, ∑ q ∈ Q, if l^2*p*q*h ≤ X then phase a b p q else 0

/-- The ordinary prime sum has the literal finite-set double-sum form. -/
theorem bilinear_eq_double_sum (P Q : Finset ℕ) {m : ℕ} [NeZero m] (a b : ZMod m) :
    bilinearPrimeSum P Q a b = ∑ p ∈ P, ∑ q ∈ Q, phase a b p q := by
  have hh := KaratsubaSubsetBilinear.filtered_eq_indicator P Q (fun _ => True) (fun _ => True) a b
  simpa [KaratsubaSubsetBilinear.weightedBilinearSum, phase] using hh

/-- Fourier inversion uses Mathlib's exact cyclic transform convention. -/
theorem inversion {m : ℕ} [NeZero m] (W : ZMod m → ℂ) (x : ZMod m) :
    W x = (m : ℂ)⁻¹ * ∑ c : ZMod m, ZMod.stdAddChar (c*x)*ZMod.dft W c := by
  have hh := congrFun (ZMod.dft.symm_apply_apply W) x
  rw [ZMod.invDFT_apply] at hh
  simpa only [smul_eq_mul] using hh.symm

/-- A product frequency only shifts the unrestricted ordinary bilinear frequency. -/
theorem phase_shift {m : ℕ} [NeZero m] (a b c : ZMod m) (p q : ℕ) :
    ZMod.stdAddChar (c*((p : ZMod m)*(q : ZMod m)))*phase a b p q = phase a (b+c) p q := by
  unfold phase
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Any cyclic product weight completes exactly into ordinary-frequency shifts. -/
theorem weightedProductSum_fourier (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (a b : ZMod m) (W : ZMod m → ℂ) :
    weightedProductSum P Q a b W = (m : ℂ)⁻¹ *
      ∑ c : ZMod m, ZMod.dft W c * bilinearPrimeSum P Q a (b+c) := by
  have hpoint (p q : ℕ) : W ((p : ZMod m)*(q : ZMod m))*phase a b p q =
      (m : ℂ)⁻¹ * ∑ c : ZMod m, ZMod.dft W c * phase a (b+c) p q := by
    rw [inversion W, mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    rw [show ZMod.stdAddChar (c*((p : ZMod m)*(q : ZMod m)))*ZMod.dft W c*phase a b p q =
      ZMod.dft W c*(ZMod.stdAddChar (c*((p : ZMod m)*(q : ZMod m)))*phase a b p q) by ring,
      phase_shift]
  unfold weightedProductSum
  simp_rw [hpoint]
  simp_rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_comm (s := Q) (t := Finset.univ)]
  rw [Finset.sum_comm]
  simp only [bilinear_eq_double_sum, Finset.mul_sum]

/-- The literal integer product cutoff is a cyclic weight only on an unaliased rectangle. -/
theorem productCutoffSum_eq_weighted (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (l h X : ℕ) (a b : ZMod m) (hrect : ∀ p ∈ P, ∀ q ∈ Q, p*q < m) :
    productCutoffSum P Q l h X a b = weightedProductSum P Q a b (productCutoff l h X) := by
  unfold productCutoffSum weightedProductSum
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  unfold productCutoff
  rw [← Nat.cast_mul, ZMod.val_natCast_of_lt (hrect p hp q hq)]
  simp [mul_assoc, ite_mul]

/-- Completion costs exactly its Fourier L1 norm against a uniform shifted-sum estimate. -/
theorem norm_weightedProductSum_le (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (a b : ZMod m) (W : ZMod m → ℂ) {B : ℝ}
    (hbound : ∀ c : ZMod m, ‖bilinearPrimeSum P Q a (b+c)‖ ≤ B) :
    ‖weightedProductSum P Q a b W‖ ≤ completionCost W * B := by
  rw [weightedProductSum_fourier, norm_mul, norm_inv, Complex.norm_natCast]
  have hh : ‖∑ c : ZMod m, ZMod.dft W c * bilinearPrimeSum P Q a (b+c)‖ ≤
      ∑ c : ZMod m, ‖ZMod.dft W c‖ * B := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c hc
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound c) (norm_nonneg _)
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ c : ZMod m, ‖ZMod.dft W c‖ * B :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = completionCost W * B := by rw [← Finset.sum_mul]; unfold completionCost; ring

/-- The coupled integer cutoff is controlled by a valid completed family of bilinear sums. -/
theorem norm_productCutoffSum_le (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (l h X : ℕ) (a b : ZMod m) (hrect : ∀ p ∈ P, ∀ q ∈ Q, p*q < m) {B : ℝ}
    (hbound : ∀ c : ZMod m, ‖bilinearPrimeSum P Q a (b+c)‖ ≤ B) :
    ‖productCutoffSum P Q l h X a b‖ ≤ completionCost (productCutoff (m := m) l h X) * B := by
  rw [productCutoffSum_eq_weighted P Q l h X a b hrect]
  exact norm_weightedProductSum_le P Q a b _ hbound

end NField.Alignment.KaratsubaProductCutoffCompletion
