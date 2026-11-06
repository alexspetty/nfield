/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.VinogradovMomentFibers
import NField.Alignment.KaratsubaHolder
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic

/-! # Finite real-character moments for the reciprocal phase argument

These identities keep the integer power-sum vectors, their multiplicities,
and both applications of Holder. The target group need not be finite.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealBilinearMoment
open scoped BigOperators Classical ComplexConjugate
open KaratsubaFiberEnergy

def tupleDifference {α G : Type*} [AddCommGroup G] (f : α → G) (s : ℕ)
    (uv : (Fin s → α) × (Fin s → α)) : G :=
  (∑ i, f (uv.1 i)) - ∑ i, f (uv.2 i)

theorem character_sum {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (ψ : AddChar G ℂ) (f : ι → G) : ψ (∑ i, f i) = ∏ i, ψ (f i) := by
  simpa only [AddChar.toMonoidHom_apply, toAdd_prod, toAdd_ofAdd] using
    map_prod ψ.toMonoidHom (fun i => Multiplicative.ofAdd (f i)) Finset.univ

theorem character_conj {G : Type*} [AddCommGroup G] (ψ : AddChar G ℂ)
    (hψ : ∀ x, ‖ψ x‖ = 1) (x : G) : conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]

theorem even_moment_expansion {α G : Type*} [Fintype α] [AddCommGroup G]
    (ψ : AddChar G ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (f : α → G) (s : ℕ) :
    ((‖∑ x, ψ (f x)‖ ^ (2*s) : ℝ) : ℂ) =
      ∑ uv : (Fin s → α) × (Fin s → α), ψ (tupleDifference f s uv) := by
  have hp : (∑ x, ψ (f x)) ^ s =
      ∑ u : Fin s → α, ψ (∑ i, f (u i)) := by
    rw [Fintype.sum_pow]
    simp_rw [character_sum]
  calc
    _ = (∑ x, ψ (f x))^s * conj ((∑ x, ψ (f x))^s) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul]
      congr 2
      omega
    _ = _ := by
      rw [hp, map_sum, Finset.sum_mul_sum]
      simp only [Fintype.sum_prod_type, tupleDifference, sub_eq_add_neg,
        character_conj ψ hψ, AddChar.map_add_eq_mul]

theorem fiber_sum_le {α G : Type*} [Fintype α] [DecidableEq G]
    (f : α → G) (S : Finset G) (J : ℝ)
    (hS : ∀ x, f x ∈ S)
    (hf : ∀ t ∈ S, (fiberCount f t : ℝ) ≤ J)
    (F : G → ℝ) (hF : ∀ t, 0 ≤ F t) :
    (∑ x, F (f x)) ≤ J * ∑ t ∈ S, F t := by
  have he : (∑ x, F (f x)) = ∑ t ∈ S, (fiberCount f t : ℝ)*F t := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S)
      (g := f) (fun x _ => hS x)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [show (∑ x ∈ Finset.univ with f x = t, F (f x)) =
        ∑ _x ∈ Finset.univ with f _x = t, F t by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]]
    simp [fiberCount]
  rw [he, Finset.mul_sum]
  exact Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right (hf t ht) (hF t)

theorem moment_sum_bound {ι α G : Type*} [Fintype ι] [Fintype α]
    [AddCommGroup G] (B : G → AddChar G ℂ)
    (hB : ∀ x y, ‖B x y‖ = 1) (g : ι → G) (f : α → G) (s : ℕ) :
    (∑ i, ‖∑ x, B (g i) (f x)‖^(2*s)) ≤
      ∑ uv : (Fin s → α) × (Fin s → α),
        ‖∑ i, B (g i) (tupleDifference f s uv)‖ := by
  have he : ((∑ i, ‖∑ x, B (g i) (f x)‖^(2*s) : ℝ) : ℂ) =
      ∑ uv : (Fin s → α) × (Fin s → α),
        ∑ i, B (g i) (tupleDifference f s uv) := by
    rw [Complex.ofReal_sum]
    simp_rw [even_moment_expansion _ (hB _) f s]
    exact Finset.sum_comm
  have hn := norm_sum_le Finset.univ
    (fun uv : (Fin s → α) × (Fin s → α) =>
      ∑ i, B (g i) (tupleDifference f s uv))
  rw [← he, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hn
  exact hn

/-- Both Holder steps reduce the literal bilinear sum to the actual integer
moment population and the finite frequency box. -/
theorem bilinear_moment_bound {α G : Type*} [Fintype α]
    [AddCommGroup G] [DecidableEq G] (B : G → AddChar G ℂ)
    (hB : ∀ x y, ‖B x y‖ = 1) (hsym : ∀ x y, B x y = B y x)
    (f : α → G) (s : ℕ) (hs : 1 ≤ s) (S : Finset G) (J : ℝ)
    (hJ : 0 ≤ J) (hS : ∀ uv, tupleDifference f s uv ∈ S)
    (hf : ∀ t ∈ S, (fiberCount (tupleDifference f s) t : ℝ) ≤ J) :
    ‖∑ x, ∑ y, B (f x) (f y)‖^(4*s^2) ≤
      (Fintype.card α : ℝ)^(4*s*(2*s-1))*J^2*
        ∑ v ∈ S, ‖∑ u ∈ S, B u v‖ := by
  let R := fun t : G => ∑ x, B (f x) t
  have hfirst : ‖∑ x, ∑ y, B (f x) (f y)‖^(2*s) ≤
      (Fintype.card α : ℝ)^(2*s-1)*
        ∑ uv : (Fin s → α) × (Fin s → α), ‖R (tupleDifference f s uv)‖ := by
    have h := KaratsubaHolder.norm_sum_pow_le Finset.univ
      (fun x => ∑ y, B (f x) (f y)) (show 1 ≤ 2*s by omega)
    simp only [Finset.card_univ] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (moment_sum_bound B hB f f s) (by positivity))
  have hpower := pow_le_pow_left₀ (by positivity) hfirst (2*s)
  rw [mul_pow] at hpower
  have hholder := KaratsubaHolder.sum_norm_pow_le Finset.univ
    (fun uv : (Fin s → α) × (Fin s → α) => R (tupleDifference f s uv))
    (show 1 ≤ 2*s by omega)
  have hcard : (Finset.univ : Finset ((Fin s → α) × (Fin s → α))).card =
      Fintype.card α ^ (2*s) := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [← pow_add]
    congr 1
    omega
  rw [hcard, Nat.cast_pow, ← pow_mul] at hholder
  have hsecond : (∑ uv : (Fin s → α) × (Fin s → α),
      ‖R (tupleDifference f s uv)‖^(2*s)) ≤
      J^2*∑ v ∈ S, ‖∑ u ∈ S, B u v‖ := by
    have hfib := fiber_sum_le (tupleDifference f s) S J hS hf
      (fun t => ‖R t‖^(2*s)) (fun _ => by positivity)
    have hbox : (∑ t ∈ S, ‖R t‖^(2*s)) ≤
        ∑ uv : (Fin s → α) × (Fin s → α),
          ‖∑ u ∈ S, B u (tupleDifference f s uv)‖ := by
      have h := moment_sum_bound B hB (fun t : {t // t ∈ S} => t.val) f s
      change (∑ t : S, ‖∑ x, B t.val (f x)‖^(2*s)) ≤
        ∑ uv : (Fin s → α) × (Fin s → α),
          ‖∑ u : S, B u.val (tupleDifference f s uv)‖ at h
      have hleft := Finset.sum_coe_sort S
        (fun t : G => ‖∑ x, B t (f x)‖^(2*s))
      have hright (uv : (Fin s → α) × (Fin s → α)) := Finset.sum_coe_sort S
        (fun u : G => B u (tupleDifference f s uv))
      rw [hleft] at h
      simp_rw [hright] at h
      simpa only [R, hsym] using h
    have hlast := fiber_sum_le (tupleDifference f s) S J hS hf
      (fun t => ‖∑ u ∈ S, B u t‖) (fun _ => norm_nonneg _)
    calc
      _ ≤ J * ∑ t ∈ S, ‖R t‖^(2*s) := hfib
      _ ≤ J * ∑ uv : (Fin s → α) × (Fin s → α),
          ‖∑ u ∈ S, B u (tupleDifference f s uv)‖ :=
        mul_le_mul_of_nonneg_left hbox hJ
      _ ≤ J*(J*∑ v ∈ S, ‖∑ u ∈ S, B u v‖) :=
        mul_le_mul_of_nonneg_left hlast hJ
      _ = _ := by ring
  have hfinish := hpower.trans (mul_le_mul_of_nonneg_left
    (hholder.trans (mul_le_mul_of_nonneg_left hsecond (by positivity))) (by positivity))
  rw [← pow_mul, ← pow_mul] at hfinish
  have he : 2*s*(2*s) = 4*s^2 := by ring
  have hfac : (Fintype.card α : ℝ)^((2*s-1)*2*s)*
      (Fintype.card α : ℝ)^(2*s*(2*s-1)) =
        (Fintype.card α : ℝ)^(4*s*(2*s-1)) := by
    rw [← pow_add]
    congr 1
    ring
  simpa only [he, ← mul_assoc, hfac] using hfinish

end NField.Alignment.RealBilinearMoment
