/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ScaledResidueLift
import Mathlib.GroupTheory.Index

/-!
# Exact multiplicity of residue reduction in finite sums

Each reduction fiber from modulus q=m*n to modulus n has m elements.
The literal finite sum of a function of the reduced residue is therefore
m times its sum over the smaller ring.
-/

set_option autoImplicit false
namespace NField.Alignment.ResidueReductionSum
open scoped BigOperators Classical

/-- The exact cardinality of every residue-reduction fiber. -/
theorem card_reduction_fiber (m n q : ℕ) [NeZero n] [NeZero q]
    (hq : m*n=q) (y : ZMod n) :
    (Finset.univ.filter (fun x : ZMod q =>
      ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n) x=y)).card=m := by
  let f := ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n)
  have hf : Function.Surjective f := ZMod.castHom_surjective _
  have he (z : ZMod n) : (Finset.univ.filter (fun x : ZMod q => f x=z)).card =
      (Finset.univ.filter (fun x : ZMod q => f x=y)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := f) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ,he,Finset.sum_const,smul_eq_mul,ZMod.card] at h
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
  change n*(Finset.univ.filter (fun x : ZMod q => f x=y)).card=n*m
  exact h.symm.trans (hq.symm.trans (Nat.mul_comm m n))

/-- The actual sum of a function pulled back under residue reduction,
with its exact multiplicity. -/
theorem sum_reduction (m n q : ℕ) [NeZero n] [NeZero q]
    (hq : m*n=q) (f : ZMod n → ℂ) :
    (∑ x : ZMod q,
      f (ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n) x)) =
        (m:ℂ)*∑ y : ZMod n, f y := by
  let r := ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n)
  have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := r) (fun _ _ => Finset.mem_univ _) (fun x => f (r x))
  change (∑ x : ZMod q, f (r x)) = _
  rw [← h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ _x ∈ Finset.univ.filter (fun x : ZMod q => r x=y), f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = (m:ℂ)*f y := by
      rw [Finset.sum_const,nsmul_eq_mul]
      change ((Finset.univ.filter (fun x : ZMod q => r x=y)).card:ℂ)*f y=_
      rw [card_reduction_fiber m n q hq y]

end NField.Alignment.ResidueReductionSum
