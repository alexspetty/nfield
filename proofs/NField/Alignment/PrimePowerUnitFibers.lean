/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanPrimePowerStationary
import Mathlib.GroupTheory.Index

/-!
# Exact unit-lift multiplicities between prime-power rings

Surjective unit reduction has uniform fibers. Their cardinality is
computed from the actual unit groups, giving the precise multiplicity
in the stationary-phase count rather than an assumed lift parameter.
-/

set_option autoImplicit false
namespace NField.Alignment.PrimePowerUnitFibers
open scoped BigOperators Classical
open KloostermanPrimePowerStationary InverseAdditiveCompletion

private theorem card_eq_card_mul_fiber {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (y : H) :
    Fintype.card G = Fintype.card H*(Finset.univ.filter (fun x => f x=y)).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := f) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ] at h
  rw [h]
  have he (z : H) : (Finset.univ.filter (fun x => f x=z)).card =
      (Finset.univ.filter (fun x => f x=y)).card :=
    MonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  simp only [he,Finset.sum_const,Finset.card_univ,smul_eq_mul]

/-- Every unit modulo p^m has exactly p^(k-m) unit lifts modulo p^k,
for 1<=m<=k, including p=2. -/
theorem card_unit_fiber (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m ≤ k) (v : (ZMod (p^m))ˣ) :
    (Finset.univ.filter (fun u : (ZMod (p^k))ˣ =>
      ZMod.unitsMap (Nat.pow_dvd_pow p hmk) u=v)).card = p^(k-m) := by
  have h := card_eq_card_mul_fiber (ZMod.unitsMap (Nat.pow_dvd_pow p hmk))
    (ZMod.unitsMap_surjective _) v
  have hcard : Fintype.card ((ZMod (p^k))ˣ) =
      Fintype.card ((ZMod (p^m))ˣ)*p^(k-m) := by
    rw [ZMod.card_units_eq_totient,ZMod.card_units_eq_totient,
      Nat.totient_prime_pow (Fact.out : p.Prime) (by omega),
      Nat.totient_prime_pow (Fact.out : p.Prime) (by omega)]
    calc
      p^(k-1)*(p-1) = p^((m-1)+(k-m))*(p-1) := by congr 2; omega
      _ = _ := by rw [pow_add]; ring
  have hpos : 0<Fintype.card ((ZMod (p^m))ˣ) := Fintype.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h.symm.trans hcard)

/-- Every predicate on the reduced units pulls back with the same exact
p^(k-m) multiplicity. -/
theorem card_unit_preimage (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m ≤ k) (P : (ZMod (p^m))ˣ → Prop) :
    (Finset.univ.filter (fun u : (ZMod (p^k))ˣ =>
      P (ZMod.unitsMap (Nat.pow_dvd_pow p hmk) u))).card =
      p^(k-m)*(Finset.univ.filter P).card := by
  let f := ZMod.unitsMap (Nat.pow_dvd_pow p hmk)
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun u : (ZMod (p^k))ˣ => P (f u)))
    (t := Finset.univ.filter P) (f := f)
    (fun u hu => by simpa using hu)
  rw [h]
  have he (v : (ZMod (p^m))ˣ) (hv : v∈Finset.univ.filter P) :
      ((Finset.univ.filter (fun u : (ZMod (p^k))ˣ => P (f u))).filter
        (fun u => f u=v)).card = p^(k-m) := by
    have hvP : P v := (Finset.mem_filter.mp hv).2
    have hset : (Finset.univ.filter (fun u : (ZMod (p^k))ˣ => P (f u))).filter
        (fun u => f u=v) = Finset.univ.filter (fun u => f u=v) := by
      ext u
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · exact And.right
      · intro hu
        exact ⟨hu ▸ hvP,hu⟩
    rw [hset]
    exact card_unit_fiber p k m hm hmk v
  calc
    _ = ∑ _v ∈ Finset.univ.filter P, p^(k-m) := Finset.sum_congr rfl he
    _ = _ := by simp [Nat.mul_comm]

/-- The actual prime-power complete sum is bounded by p^s times the
number of solutions of the critical quadratic in the smaller unit group. -/
theorem complete_inverse_norm_le_reduced_count (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s<k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k)) :
    ‖completeInverseSum r j t‖ ≤ (p:ℝ)^s*
      ((Finset.univ.filter (fun v : (ZMod (p^(k-s)))ˣ =>
        reduction p k s (-t)*(v:ZMod (p^(k-s)))^2=reduction p k s (j*r))).card:ℝ) := by
  have h := complete_inverse_norm_le_critical_count p k s hs.le hk r j t
  have he := card_unit_preimage p k (k-s) (by omega) (Nat.sub_le k s)
    (fun v : (ZMod (p^(k-s)))ˣ =>
      reduction p k s (-t)*(v:ZMod (p^(k-s)))^2=reduction p k s (j*r))
  have hexp : k-(k-s)=s := by omega
  rw [hexp] at he
  have he' : (Finset.univ.filter (fun u : (ZMod (p^k))ˣ =>
      reduction p k s (-t)*(reduction p k s (u:ZMod (p^k)))^2=
        reduction p k s (j*r))).card =
      p^s*(Finset.univ.filter (fun v : (ZMod (p^(k-s)))ˣ =>
        reduction p k s (-t)*(v:ZMod (p^(k-s)))^2=reduction p k s (j*r))).card := by
    simpa only [ZMod.unitsMap_val,reduction,ZMod.castHom_apply] using he
  rw [he',Nat.cast_mul,Nat.cast_pow] at h
  exact h

end NField.Alignment.PrimePowerUnitFibers
