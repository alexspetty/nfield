/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.TorusProjection
/-! # The exact first-coordinate marginal of the primitive torus -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.PrimitiveCoordinates

open scoped BigOperators
open NField.Alignment CollisionRemainderCovariance

theorem real_filter_card {α : Type*} [DecidableEq α] (s : Finset α)
    (P : α → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ)=∑ a ∈ s, if P a then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  simp

theorem coprime_repeated_card (r g : ℕ) :
    ((Finset.range (r*g)).filter (fun b => g.Coprime b)).card=r*g.totient := by
  suffices h : ((((Finset.range (r*g)).filter (fun b => g.Coprime b)).card : ℝ))=
      ((r*g.totient : ℕ) : ℝ) by exact_mod_cast h
  rw [real_filter_card, sum_range_product]
  simp_rw [Nat.coprime_add_mul_left_right]
  have hphi : (∑ b ∈ Finset.range g, if g.Coprime b then (1 : ℝ) else 0)=(g.totient : ℝ) := by
    rw [← real_filter_card]
    rfl
  simp only [hphi, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]

def marginalCount (n a : ℕ) : ℕ :=
  ((Finset.range n).filter (fun b => primitiveAt n a b)).card

theorem primitive_marginal (n a : ℕ) :
    marginalCount n a=(n/(a.gcd n))*(a.gcd n).totient := by
  unfold marginalCount
  simp_rw [primitive_at_iff]
  let g := a.gcd n
  let r := n/g
  have hdiv : g ∣ n := Nat.gcd_dvd_right a n
  have he : r*g=n := Nat.div_mul_cancel hdiv
  change ((Finset.range n).filter (fun b => g.Coprime b)).card=r*g.totient
  rw [← he, coprime_repeated_card]

theorem primitive_marginal_reduced {n : ℕ} (hn : 0 < n) (a : ℕ) :
    let r := n/(a.gcd n)
    marginalCount n a=r*(n/r).totient := by
  let g := a.gcd n
  let r := n/g
  have hgp : 0 < g := Nat.gcd_pos_of_pos_right a hn
  have hdiv : g ∣ n := Nat.gcd_dvd_right a n
  have hrp : 0 < r := Nat.div_pos (Nat.le_of_dvd hn hdiv) hgp
  have he : r*g=n := Nat.div_mul_cancel hdiv
  have hnr : n/r=g := by
    calc
      n/r=(r*g)/r := by rw [he]
      _=g := Nat.mul_div_right g hrp
  change marginalCount n a=r*(n/r).totient
  rw [hnr]
  exact primitive_marginal n a

theorem torus_reduced_denominator {n : ℕ} (hn : 0 < n) (a : ℕ) :
    ((a : ℚ)/(n : ℚ)).den=n/(a.gcd n) := by
  rw [Rat.natCast_div_eq_divInt, Rat.den_divInt]
  simp [hn.ne', Nat.gcd_comm]

theorem primitive_marginal_rational {n : ℕ} (hn : 0 < n) (a : ℕ) :
    marginalCount n a=((a : ℚ)/(n : ℚ)).den*
      (n/((a : ℚ)/(n : ℚ)).den).totient := by
  rw [torus_reduced_denominator hn]
  exact primitive_marginal_reduced hn a

end NField.ResetForests.PrimitiveCoordinates
