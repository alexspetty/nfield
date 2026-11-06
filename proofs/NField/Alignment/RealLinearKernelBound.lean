/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealPolynomialFrequency
import NField.Alignment.RealTrigonometricSampling

/-! # Arithmetic-grid bounds for the real polynomial frequency kernel -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealLinearKernelBound
open scoped BigOperators ComplexConjugate
open RealPolynomialMomentBox RealPolynomialFrequency RealTrigonometricEnergy
  RealTrigonometricSampling

theorem fourier_eq_realCharacter (n : ℤ) (t : ℝ) :
    fourier n (t : AddCircle (1:ℝ)) = realCharacter ((n:ℝ)*t) := by
  change fourier n (t : AddCircle (1:ℝ)) = fourier 1 (((n:ℝ)*t) : AddCircle (1:ℝ))
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_mul,
    Complex.ofReal_intCast, Int.cast_one, mul_one]
  congr 1
  ring

theorem dirichlet_trig (K : ℕ) (β v : ℝ) :
    trig (Finset.Icc (-(K:ℤ)) K) (fun _ => 1) (β*v) =
      ∑ u ∈ Finset.Icc (-(K:ℤ)) K, realCharacter (β*(u:ℝ)*v) := by
  simp only [trig, one_mul, fourier_eq_realCharacter]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem symmetric_Icc_card (K : ℕ) :
    (Finset.Icc (-(K:ℤ)) (K:ℤ)).card = 2*K+1 := by
  rw [Int.card_Icc]
  omega

theorem sum_symmetric_Icc (K : ℕ) (f : ℤ → ℝ) :
    (∑ v ∈ Finset.Icc (-(K:ℤ)) K, f v) =
      ∑ j ∈ Finset.range (2*K+1), f (-(K:ℤ)+(j:ℤ)) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have h : ((K:ℤ)+1-(-(K:ℤ))).toNat = 2*K+1 := by omega
  simp only [h, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]

theorem linearKernel_sq_grid_bound (β : ℝ) (hβ : 0 < β) (K : ℕ) (hK : 0 < K) :
    β*linearKernel β K^2 ≤
      (2*(K:ℝ)+1)^2*((2*(K:ℝ)+1)*β+1)*(1+4*Real.pi*K*β) := by
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let D := trig S (fun _ => (1:ℂ))
  have hfreq (n : ℤ) (hn : n ∈ S) : |(n:ℝ)| ≤ (K:ℝ) := by
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
    exact abs_le.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hgrid := trig_grid_energy_le S (fun _ => (1:ℂ)) (K:ℝ)
    (by exact_mod_cast hK) hfreq (-(K:ℝ)*β) β hβ (2*K+1)
  have hcard : (S.card:ℝ) = 2*(K:ℝ)+1 := by
    change ((Finset.Icc (-(K:ℤ)) (K:ℤ)).card:ℝ) = _
    rw [symmetric_Icc_card]
    push_cast
    rfl
  have hE : (∑ n ∈ S, ‖(1:ℂ)‖^2) = 2*(K:ℝ)+1 := by
    simp only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  rw [hE] at hgrid
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ))
    (fun v => ‖D (β*(v:ℝ))‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at hcs
  have hsum : (∑ v ∈ S, ‖D (β*(v:ℝ))‖) = linearKernel β K := by
    simp only [D,S,dirichlet_trig,linearKernel]
  rw [hsum] at hcs
  have hsum2 : (∑ v ∈ S, ‖D (β*(v:ℝ))‖^2) =
      ∑ j ∈ Finset.range (2*K+1), ‖D (-(K:ℝ)*β+(j:ℝ)*β)‖^2 := by
    rw [show S = Finset.Icc (-(K:ℤ)) (K:ℤ) from rfl, sum_symmetric_Icc]
    apply Finset.sum_congr rfl
    intro j _
    congr 3
    push_cast
    ring
  rw [hsum2] at hcs
  have h := mul_le_mul_of_nonneg_left hcs hβ.le
  have hg := mul_le_mul_of_nonneg_left hgrid (show 0 ≤ 2*(K:ℝ)+1 by positivity)
  push_cast at hg
  nlinarith

end NField.Alignment.RealLinearKernelBound
