/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovCongruencing
import NField.Alignment.KaratsubaHolder
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Residue-class Holder for finite moment counts

Mathlib's character orthogonality identifies the exact collision count with
a finite Fourier moment. Holder then groups all free coordinates into a
single residue class. The group and tuple maps below are generic; the
integer Vinogradov application uses a modulus large enough to avoid aliasing.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.VinogradovHolder
open scoped BigOperators Classical

def collisionCount {α G : Type*} [Fintype α] [DecidableEq G] (f : α → G) : ℕ :=
  (Finset.univ.filter fun uv : α × α => f uv.1 = f uv.2).card

/-- Character orthogonality counts the original ordered pairs exactly. -/
theorem character_pair_count {α G : Type*} [Fintype α] [AddCommGroup G]
    [Fintype G] [DecidableEq G] (f : α → G) :
    (∑ ψ : AddChar G ℂ, (∑ x, ψ (f x)) * (starRingEnd ℂ) (∑ x, ψ (f x))) =
      (Fintype.card G : ℂ) * collisionCount f := by
  have hp (ψ : AddChar G ℂ) (x y : α) :
      ψ (f x) * (starRingEnd ℂ) (ψ (f y)) = ψ (f x - f y) := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
  simp only [map_sum, Finset.sum_mul_sum]
  simp_rw [hp]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (AddChar G ℂ))),
    AddChar.sum_apply_eq_ite, sub_eq_zero]
  simp only [collisionCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_one, mul_zero]

theorem character_norm_pair_count {α G : Type*} [Fintype α] [AddCommGroup G]
    [Fintype G] [DecidableEq G] (f : α → G) :
    (∑ ψ : AddChar G ℂ, ‖∑ x, ψ (f x)‖ ^ 2) =
      (Fintype.card G : ℝ) * collisionCount f := by
  have h := character_pair_count f
  simp_rw [Complex.mul_conj] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using hr

/-- Sum of a fixed-size head and `s` free coordinate values. -/
def sumMap {α β G : Type*} [AddCommMonoid G] (f : α → G) (g : β → G) (s : ℕ)
    (u : α × (Fin s → β)) : G := f u.1 + ∑ i, g (u.2 i)

private theorem char_sum {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (ψ : AddChar G ℂ) (f : ι → G) : ψ (∑ i, f i) = ∏ i, ψ (f i) := by
  simpa only [AddChar.toMonoidHom_apply, toAdd_prod, toAdd_ofAdd] using
    map_prod ψ.toMonoidHom (fun i => Multiplicative.ofAdd (f i)) Finset.univ

theorem character_sumMap {α β G : Type*} [Fintype α] [Fintype β]
    [AddCommGroup G] (f : α → G) (g : β → G) (s : ℕ) (ψ : AddChar G ℂ) :
    (∑ u : α × (Fin s → β), ψ (sumMap f g s u)) =
      (∑ a, ψ (f a)) * (∑ b, ψ (g b)) ^ s := by
  simp only [sumMap, Fintype.sum_prod_type, AddChar.map_add_eq_mul,
    char_sum, ← Finset.mul_sum]
  rw [Fintype.sum_pow]
  rw [Finset.sum_mul]

theorem mixed_norm_moment {α β G : Type*} [Fintype α] [Fintype β]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : α → G) (g : β → G) (s : ℕ) :
    (∑ ψ : AddChar G ℂ, ‖∑ a, ψ (f a)‖ ^ 2 * ‖∑ b, ψ (g b)‖ ^ (2 * s)) =
      (Fintype.card G : ℝ) * collisionCount (sumMap f g s) := by
  have h := character_norm_pair_count (sumMap f g s)
  simp only [character_sumMap, norm_mul, norm_pow, mul_pow, ← pow_mul] at h
  simpa only [Nat.mul_comm s 2] using h

/-- The exact finite Holder count inequality for any partition of the free coordinates. -/
theorem partition_holder_count {α β ρ G : Type*}
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq ρ]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : α → G) (g : β → G) (c : β → ρ) {s : ℕ} (hs : 0 < s) :
    collisionCount (sumMap f g s) ≤
      Fintype.card ρ ^ (2 * s - 1) *
        ∑ r : ρ, collisionCount (sumMap f (fun b : {b // c b = r} => g b.val) s) := by
  have hsplit (ψ : AddChar G ℂ) :
      (∑ b, ψ (g b)) = ∑ r : ρ, ∑ b : {b // c b = r}, ψ (g b.val) := by
    exact (Fintype.sum_fiberwise c (fun b => ψ (g b))).symm
  have hp (ψ : AddChar G ℂ) :
      ‖∑ b, ψ (g b)‖ ^ (2 * s) ≤
        (Fintype.card ρ : ℝ) ^ (2 * s - 1) *
          ∑ r : ρ, ‖∑ b : {b // c b = r}, ψ (g b.val)‖ ^ (2 * s) := by
    rw [hsplit]
    simpa only [Finset.card_univ] using KaratsubaHolder.norm_sum_pow_le
      Finset.univ (fun r : ρ => ∑ b : {b // c b = r}, ψ (g b.val)) (by omega)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (AddChar G ℂ)))
    (fun ψ _ => mul_le_mul_of_nonneg_left (hp ψ) (sq_nonneg ‖∑ a, ψ (f a)‖))
  have hr :
      (Fintype.card G : ℝ) * collisionCount (sumMap f g s) ≤
        (Fintype.card G : ℝ) *
          ((Fintype.card ρ : ℝ) ^ (2 * s - 1) *
            ∑ r : ρ, (collisionCount (sumMap f (fun b : {b // c b = r} => g b.val) s) : ℝ)) := by
    calc
      _ = _ := (mixed_norm_moment f g s).symm
      _ ≤ _ := hsum
      _ = (Fintype.card ρ : ℝ) ^ (2 * s - 1) *
          ∑ ψ : AddChar G ℂ, ∑ r : ρ,
            ‖∑ a, ψ (f a)‖ ^ 2 * ‖∑ b : {b // c b = r}, ψ (g b.val)‖ ^ (2 * s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ψ _
        rw [← Finset.mul_sum]
        ring
      _ = (Fintype.card ρ : ℝ) ^ (2 * s - 1) *
          ∑ r : ρ, ∑ ψ : AddChar G ℂ,
            ‖∑ a, ψ (f a)‖ ^ 2 * ‖∑ b : {b // c b = r}, ψ (g b.val)‖ ^ (2 * s) := by
        rw [Finset.sum_comm]
      _ = _ := by
        simp_rw [mixed_norm_moment, ← Finset.mul_sum]
        ring
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  exact_mod_cast (mul_le_mul_iff_right₀ hG).mp hr

end NField.Alignment.VinogradovHolder
