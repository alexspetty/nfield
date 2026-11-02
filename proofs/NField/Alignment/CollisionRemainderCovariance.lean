/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRemainderDynamics
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

/-!
# Remainder covariance on complete residue cycles

The shared gcd residue and the two coprime quotient residues are retained
explicitly. The calculations use complete cycles, not sampled examples.
-/

namespace NField.Alignment.CollisionRemainderCovariance

open scoped BigOperators
open NField.Alignment.CollisionRemainderDynamics

theorem sum_range_product (m d : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range (m * d), f n) =
      ∑ j ∈ Finset.range m, ∑ t ∈ Finset.range d, f (t + d * j) := by
  have h := Equiv.sum_comp (@finProdFinEquiv m d) (fun n => f n.val)
  change (∑ p : Fin m × Fin d, f (p.2.val + d * p.1.val)) = _ at h
  rw [Fintype.sum_prod_type] at h
  calc
    _ = ∑ n : Fin (m * d), f n.val := (Fin.sum_univ_eq_sum_range f _).symm
    _ = ∑ j : Fin m, ∑ t : Fin d, f (t.val + d * j.val) := h.symm
    _ = ∑ j : Fin m, ∑ t ∈ Finset.range d, f (t + d * j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Fin.sum_univ_eq_sum_range (fun t => f (t + d * j.val)) d
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun j => ∑ t ∈ Finset.range d, f (t + d * j)) m

noncomputable def coprimeResidueEquiv {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : u.Coprime v) : Fin (u * v) ≃ Fin u × Fin v :=
  Equiv.ofBijective
    (fun j => (⟨j.val % u, Nat.mod_lt _ hu⟩, ⟨j.val % v, Nat.mod_lt _ hv⟩))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro j k hjk
      have h₁ : j.val % u = k.val % u := congrArg (fun p => p.1.val) hjk
      have h₂ : j.val % v = k.val % v := congrArg (fun p => p.2.val) hjk
      apply Fin.ext
      exact ((Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h₁, h₂⟩).eq_of_lt_of_lt
        j.isLt k.isLt,
      by simp⟩)

theorem coprime_residue_sum {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : u.Coprime v) (F : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range (u * v), F (j % u) (j % v)) =
      ∑ a ∈ Finset.range u, ∑ b ∈ Finset.range v, F a b := by
  have he := Equiv.sum_comp (coprimeResidueEquiv hu hv h)
    (fun p => F p.1.val p.2.val)
  change (∑ j : Fin (u * v), F (j.val % u) (j.val % v)) = _ at he
  rw [Fintype.sum_prod_type] at he
  calc
    _ = ∑ j : Fin (u * v), F (j.val % u) (j.val % v) :=
      (Fin.sum_univ_eq_sum_range (fun j => F (j % u) (j % v)) _).symm
    _ = ∑ a : Fin u, ∑ b : Fin v, F a.val b.val := he
    _ = ∑ a : Fin u, ∑ b ∈ Finset.range v, F a.val b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fin.sum_univ_eq_sum_range (F a.val) v
    _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range v, F a b) u

theorem affine_mod {d u t : ℕ} (_hd : 0 < d) (hu : 0 < u)
    (ht : t < d) (j : ℕ) :
    (t + d * j) % (d * u) = t + d * (j % u) := by
  have hj := Nat.mod_lt j hu
  have hlt : t + d * (j % u) < d * u := by nlinarith
  have he : t + d * j = t + d * (j % u) + (d * u) * (j / u) := by
    have he := Nat.mod_add_div j u
    nlinarith
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem centered_affine {d u t : ℕ} (hd : 0 < d) (hu : 0 < u)
    (ht : t < d) (j : ℕ) :
    centeredRemainder (d * u) (t + d * j) =
      centeredRemainder d t + (d : ℝ) * centeredRemainder u j := by
  unfold centeredRemainder
  rw [affine_mod hd hu ht, Nat.mod_eq_of_lt ht]
  push_cast
  ring

theorem sum_range_real_id (d : ℕ) :
    (∑ t ∈ Finset.range d, (t : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_real_sq (d : ℕ) :
    (∑ t ∈ Finset.range d, (t : ℝ) ^ 2) =
      (d : ℝ) * ((d : ℝ) - 1) * (2 * (d : ℝ) - 1) / 6 := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem centered_cycle_square (d : ℕ) :
    (∑ t ∈ Finset.range d, centeredRemainder d t ^ 2) =
      (d : ℝ) * ((d : ℝ) ^ 2 - 1) / 12 := by
  have he : (∑ t ∈ Finset.range d, centeredRemainder d t ^ 2) =
      (∑ t ∈ Finset.range d, (t : ℝ) ^ 2) -
        ((d : ℝ) - 1) * (∑ t ∈ Finset.range d, (t : ℝ)) +
        (d : ℝ) * (((d : ℝ) - 1) / 2) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hc : (d : ℝ) * (((d : ℝ) - 1) / 2) ^ 2 =
        ∑ _t ∈ Finset.range d, (((d : ℝ) - 1) / 2) ^ 2 := by simp
    rw [hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [centeredRemainder, Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
    ring
  rw [he, sum_range_real_id, sum_range_real_sq]
  ring

theorem shifted_centered_cycle_sum {u : ℕ} (hu : 0 < u) (x c : ℝ) :
    (∑ j ∈ Finset.range u, (x + c * centeredRemainder u j)) = (u : ℝ) * x := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, centered_cycle_sum hu]
  simp

theorem coprime_conditional_product {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : u.Coprime v) (x c : ℝ) :
    (∑ j ∈ Finset.range (u * v),
      (x + c * centeredRemainder u j) * (x + c * centeredRemainder v j)) =
        (u : ℝ) * (v : ℝ) * x ^ 2 := by
  have hr (k j : ℕ) : centeredRemainder k (j % k) = centeredRemainder k j := by
    simp [centeredRemainder]
  have he := coprime_residue_sum hu hv h
    (fun a b => (x + c * centeredRemainder u a) * (x + c * centeredRemainder v b))
  simp only [hr] at he
  rw [he]
  simp_rw [← Finset.mul_sum, shifted_centered_cycle_sum hv]
  rw [← Finset.sum_mul, shifted_centered_cycle_sum hu]
  ring

/-- The shared residue is the only surviving covariance after the two
coprime quotient residues are summed. -/
theorem covariance_factored {d u v : ℕ} (hd : 0 < d) (hu : 0 < u) (hv : 0 < v)
    (h : u.Coprime v) :
    (∑ n ∈ Finset.range (u * v * d),
      centeredRemainder (d * u) n * centeredRemainder (d * v) n) =
        (u * v * d : ℕ) * ((d : ℝ) ^ 2 - 1) / 12 := by
  rw [sum_range_product (u * v) d, Finset.sum_comm]
  have he : (∑ t ∈ Finset.range d, ∑ j ∈ Finset.range (u * v),
      centeredRemainder (d * u) (t + d * j) *
        centeredRemainder (d * v) (t + d * j)) =
      ∑ t ∈ Finset.range d, (u : ℝ) * (v : ℝ) * centeredRemainder d t ^ 2 := by
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    simp_rw [centered_affine hd hu ht', centered_affine hd hv ht']
    exact coprime_conditional_product hu hv h _ _
  rw [he, ← Finset.mul_sum, centered_cycle_square]
  push_cast
  ring

theorem gcd_factor_lcm {k l : ℕ} (hk : 0 < k) (_hl : 0 < l) :
    k / k.gcd l * (l / k.gcd l) * k.gcd l = k.lcm l := by
  have hd := Nat.gcd_pos_of_pos_left l hk
  have hk' := Nat.mul_div_cancel' (Nat.gcd_dvd_left k l)
  have hl' := Nat.mul_div_cancel' (Nat.gcd_dvd_right k l)
  have he := Nat.gcd_mul_lcm k l
  apply Nat.eq_of_mul_eq_mul_left hd
  calc
    k.gcd l * (k / k.gcd l * (l / k.gcd l) * k.gcd l) =
      (k.gcd l * (k / k.gcd l)) * (k.gcd l * (l / k.gcd l)) := by ring
    _ = k.gcd l * k.lcm l := by rw [hk', hl', he]

/-- The unnormalized complete-cycle covariance for arbitrary positive
periods, including unequal and noncoprime periods. -/
theorem remainder_covariance_sum {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    (∑ n ∈ Finset.range (k.lcm l), centeredRemainder k n * centeredRemainder l n) =
      (k.lcm l : ℝ) * ((k.gcd l : ℝ) ^ 2 - 1) / 12 := by
  have hd := Nat.gcd_pos_of_pos_left l hk
  have hu := Nat.div_gcd_pos_of_pos_left l hk
  have hv : 0 < l / k.gcd l := by
    simpa only [Nat.gcd_comm] using Nat.div_gcd_pos_of_pos_left k hl
  have he := covariance_factored hd hu hv (Nat.coprime_div_gcd_div_gcd hd)
  rw [gcd_factor_lcm hk hl, Nat.mul_div_cancel' (Nat.gcd_dvd_left k l),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right k l)] at he
  exact he

/-- Dividing by the cycle length gives the exact gcd covariance. -/
theorem remainder_covariance {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    (∑ n ∈ Finset.range (k.lcm l), centeredRemainder k n * centeredRemainder l n) /
      (k.lcm l : ℝ) = ((k.gcd l : ℝ) ^ 2 - 1) / 12 := by
  rw [remainder_covariance_sum hk hl]
  have hL : (k.lcm l : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hk hl).ne'
  field_simp

end NField.Alignment.CollisionRemainderCovariance
