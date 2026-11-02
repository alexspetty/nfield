/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SawtoothLValue

/-!
# The ordered L(1) endpoint for arbitrary zero-mean periodic functions

Finite Fourier inversion and the proved principal-log endpoint identify
the naturally ordered partial sums with Mathlib's actual continued
L-function. No absolute convergence at one or character primitivity is
assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPeriodicLValue

open scoped BigOperators Topology ZMod
open Filter SawtoothLValue

def orderedLPartial {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range M, Φ ((n+1 : ℕ) : ZMod q)/((n+1 : ℕ) : ℂ)

theorem character_nat_power {q : ℕ} [NeZero q] (j : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (-(j*(n : ZMod q)))=ZMod.stdAddChar (-j)^n := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [nsmul_eq_mul, mul_comm]

theorem orderedLPartial_dft {q : ℕ} [NeZero q] (Ψ : ZMod q → ℂ) (M : ℕ) :
    orderedLPartial (ZMod.dft Ψ) M=
      ∑ j : ZMod q, Ψ j * ∑ n ∈ Finset.range M,
        ZMod.stdAddChar (-j)^(n+1)/((n+1 : ℕ) : ℂ) := by
  unfold orderedLPartial
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [character_nat_power]
  ring

theorem dft_orderedLPartial_tendsto {q : ℕ} [NeZero q]
    (Ψ : ZMod q → ℂ) (hΨ : Ψ 0=0) :
    Tendsto (orderedLPartial (ZMod.dft Ψ)) atTop
      (𝓝 (ZMod.LFunction (ZMod.dft Ψ) 1)) := by
  rw [ZMod.LFunction_dft Ψ (Or.inl hΨ)]
  simp_rw [show orderedLPartial (ZMod.dft Ψ)=fun M =>
    ∑ j : ZMod q, Ψ j * ∑ n ∈ Finset.range M,
      ZMod.stdAddChar (-j)^(n+1)/((n+1 : ℕ) : ℂ) from
        funext (orderedLPartial_dft Ψ)]
  apply tendsto_finsetSum
  intro j _
  by_cases hj : j=0
  · simp [hj,hΨ]
  · have hzNorm : ‖ZMod.stdAddChar (-j)‖=1 := by
      rw [ZMod.stdAddChar_apply]
      exact Circle.norm_coe _
    have hz : ZMod.stdAddChar (-j) ≠ 1 := by
      intro he
      have hn : -j=0 := ZMod.injective_stdAddChar (by simpa using he)
      exact hj (neg_eq_zero.mp hn)
    rw [expZeta_one_eq_neg_log (-j) (neg_ne_zero.mpr hj)]
    exact (tendsto_harmonic_geometric hzNorm hz).const_mul (Ψ j)

theorem orderedLPartial_tendsto {q : ℕ} [NeZero q]
    (Φ : ZMod q → ℂ) (hΦ : ∑ j : ZMod q, Φ j=0) :
    Tendsto (orderedLPartial Φ) atTop (𝓝 (ZMod.LFunction Φ 1)) := by
  have hz : (ZMod.dft.symm Φ) 0=0 := by
    rw [ZMod.invDFT_apply']
    simp [ZMod.dft_apply_zero,hΦ]
  simpa only [LinearEquiv.apply_symm_apply] using
    dft_orderedLPartial_tendsto (ZMod.dft.symm Φ) hz

theorem odd_character_ordered_L_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) :
    Tendsto (orderedLPartial χ) atTop (𝓝 (DirichletCharacter.LFunction χ 1)) := by
  have ho : Function.Odd (fun x : ZMod q => χ x) :=
    fun x => DirichletCharacter.Odd.eval_neg χ x hχ
  exact orderedLPartial_tendsto χ ho.sum_eq_zero

end NField.Alignment.CollisionPeriodicLValue
