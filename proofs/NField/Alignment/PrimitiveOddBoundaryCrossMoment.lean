/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveOddBoundaryMean

/-!
# Mixed and twisted primitive-odd boundary moments

The mixed criterion retains both signals and every signed cross term. A
balanced odd first signal suffices; the second signal is unrestricted.
Multiplication by a unit then converts the exact spatial cross-pairing
into a character twist, with its conjugation direction proved explicitly.
-/

set_option autoImplicit false
namespace NField.Alignment.PrimitiveOddBoundaryMean

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
attribute [local instance] Classical.propDecidable

theorem boundary_cross_expand {m : ℕ} [NeZero m]
    (μ ν : UnitClass m → ℂ) :
    (∑ χ : Character m with χ.IsPrimitive ∧ χ.Odd,
      star (boundaryFlux μ χ) * boundaryFlux ν χ) =
      ∑ x : UnitClass m, ∑ y : UnitClass m,
        ν x * star (μ y) * primitiveOddKernel x y := by
  classical
  unfold boundaryFlux
  simp_rw [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  unfold primitiveOddKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem mixed_fiber_pairing_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ρ : ι → κ) (target : ι → κ) (μ ν : ι → ℂ)
    (hbalance : ∀ r : κ, ∑ x : ι with ρ x = r, μ x = 0) :
    (∑ x : ι, ∑ y : ι,
      ν x * star (μ y) * (if target x = ρ y then 1 else 0)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  have hs : (∑ y : ι with ρ y = target x, star (μ y)) = 0 := by
    rw [← star_sum, hbalance, star_zero]
  calc
    (∑ y : ι, ν x * star (μ y) * (if target x = ρ y then 1 else 0)) =
        ν x * ∑ y : ι with ρ y = target x, star (μ y) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : target x = ρ y
      · rw [if_pos h, if_pos h.symm, mul_one]
      · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
    _ = 0 := by rw [hs, mul_zero]

/-- Mixed primitive-odd Parseval with a balanced odd first signal.
The second signal is unrestricted, so both signed cross terms are retained. -/
theorem boundary_cross_criterion
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hN : 2 ≤ N)
    (μ ν : UnitClass (p ^ N) → ℂ)
    (hbalance : ∀ r : UnitClass (p ^ (N - 1)),
      ∑ x : UnitClass (p ^ N) with previousUnit (by omega) x = r, μ x = 0)
    (hodd : ∀ x : UnitClass (p ^ N), μ (-x) = -μ x) :
    (∑ χ : Character (p ^ N) with χ.IsPrimitive ∧ χ.Odd,
      star (boundaryFlux μ χ) * boundaryFlux ν χ) =
      ((p ^ N).totient : ℂ) *
        ∑ x : UnitClass (p ^ N), ν x * star (μ x) := by
  classical
  rw [boundary_cross_expand]
  simp_rw [primitiveOddKernel_eq_primePowerKernel hp hN]
  rw [doublePairing_distribute]
  have hdiag : (∑ x : UnitClass (p ^ N), ∑ y : UnitClass (p ^ N),
      ν x * star (μ y) * (if x = y then 1 else 0)) =
      ∑ x : UnitClass (p ^ N), ν x * star (μ x) := by simp
  have hanti : (∑ x : UnitClass (p ^ N), ∑ y : UnitClass (p ^ N),
      ν x * star (μ y) * (if -x = y then 1 else 0)) =
      -(∑ x : UnitClass (p ^ N), ν x * star (μ x)) := by
    simp [hodd, Finset.sum_neg_distrib]
  have hlow := mixed_fiber_pairing_zero
    (previousUnit (p := p) (N := N) (by omega))
    (previousUnit (p := p) (N := N) (by omega)) μ ν hbalance
  have hlowanti := mixed_fiber_pairing_zero
    (previousUnit (p := p) (N := N) (by omega))
    (fun x => -(previousUnit (p := p) (N := N) (by omega) x)) μ ν hbalance
  rw [hdiag, hanti, hlow, hlowanti]
  ring

/-- Twisting a character coordinate retains its complete spatial cross-pairing. -/
theorem boundary_twist_criterion
    {p N : ℕ} [NeZero (p ^ N)] [NeZero (p ^ (N - 1))]
    (hp : p.Prime) (hN : 2 ≤ N)
    (μ : UnitClass (p ^ N) → ℂ) (z : UnitClass (p ^ N))
    (hbalance : ∀ r : UnitClass (p ^ (N - 1)),
      ∑ x : UnitClass (p ^ N) with previousUnit (by omega) x = r, μ x = 0)
    (hodd : ∀ x : UnitClass (p ^ N), μ (-x) = -μ x) :
    (∑ χ : Character (p ^ N) with χ.IsPrimitive ∧ χ.Odd,
      (Complex.normSq (boundaryFlux μ χ) : ℂ) * χ z.val) =
      ((p ^ N).totient : ℂ) *
        ∑ x : UnitClass (p ^ N), μ x * star (μ (z*x)) := by
  classical
  have h := boundary_cross_criterion hp hN μ (fun x => μ (z⁻¹*x)) hbalance hodd
  have hflux (χ : Character (p ^ N)) :
      boundaryFlux (fun x => μ (z⁻¹*x)) χ = χ z.val * boundaryFlux μ χ := by
    unfold boundaryFlux
    calc
      (∑ x : UnitClass (p ^ N), μ (z⁻¹*x) * χ x.val) =
          ∑ x : UnitClass (p ^ N), μ (z⁻¹*(z*x)) * χ (z*x).val :=
        (Equiv.sum_comp (Equiv.mulLeft z)
          (fun x => μ (z⁻¹*x) * χ x.val)).symm
      _ = χ z.val * ∑ x : UnitClass (p ^ N), μ x * χ x.val := by
        simp only [inv_mul_cancel_left, Units.val_mul, map_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hspace : (∑ x : UnitClass (p ^ N), μ (z⁻¹*x) * star (μ x)) =
      ∑ x : UnitClass (p ^ N), μ x * star (μ (z*x)) := by
    calc
      (∑ x : UnitClass (p ^ N), μ (z⁻¹*x) * star (μ x)) =
          ∑ x : UnitClass (p ^ N), μ (z⁻¹*(z*x)) * star (μ (z*x)) :=
        (Equiv.sum_comp (Equiv.mulLeft z)
          (fun x => μ (z⁻¹*x) * star (μ x))).symm
      _ = _ := by simp only [inv_mul_cancel_left]
  rw [hspace] at h
  simp_rw [hflux] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply]
  ring

end NField.Alignment.PrimitiveOddBoundaryMean
