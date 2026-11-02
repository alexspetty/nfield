/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CyclicUnitQuadraticRoots

/-!
# Quadratic unit roots modulo powers of two

The square-map image contains the square of 5, whose known order bounds
the kernel by four. No cyclicity of the full unit group is assumed.
-/

set_option autoImplicit false
namespace NField.Alignment.TwoPowerUnitQuadraticRoots
open scoped BigOperators Classical

/-- The square-map kernel has at most four elements above modulus eight. -/
theorem square_kernel_card_le_four (n : ℕ) :
    Nat.card (powMonoidHom (α := (ZMod (2^(n+3)))ˣ) 2).ker ≤ 4 := by
  let f := powMonoidHom (α := (ZMod (2^(n+3)))ˣ) 2
  have hfive : IsUnit (5:ZMod (2^(n+3))) :=
    (ZMod.isUnit_iff_coprime 5 (2^(n+3))).mpr ((by decide : Nat.Coprime 5 2).pow_right _)
  let u := hfive.unit
  have hu : orderOf u=2^(n+1) := by
    rw [← orderOf_injective _ Units.coeHom_injective u,Units.coeHom_apply]
    change orderOf (hfive.unit:ZMod (2^(n+3)))=2^(n+1)
    rw [hfive.unit_spec]
    exact ZMod.orderOf_five (n+1)
  have hu2 : orderOf (u^2)=2^n := by
    rw [orderOf_pow_of_dvd (by decide : (2:ℕ)≠0)
      (hu ▸ dvd_pow_self 2 (by omega : n+1≠0)),hu,pow_succ,Nat.mul_div_left _ (by decide)]
  have hi : 2^n ≤ Nat.card f.range := by
    rw [← hu2]
    exact f.range.orderOf_le_card (Set.toFinite _) ⟨u,rfl⟩
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  have hg : Nat.card ((ZMod (2^(n+3)))ˣ)=4*2^n := by
    rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp only [show n+3-1=n+2 by omega,pow_add]
    ring
  rw [hg] at hc
  have hle := Nat.mul_le_mul_left (Nat.card f.ker) hi
  rw [hc] at hle
  exact Nat.le_of_mul_le_mul_right hle (by positivity : 0<2^n)

/-- Every actual square-map fiber modulo a power of two has at most four units. -/
theorem card_square_fiber_le_four (m : ℕ) (v : (ZMod (2^m))ˣ) :
    (Finset.univ.filter (fun u : (ZMod (2^m))ˣ => u^2=v)).card ≤ 4 := by
  by_cases hm : m≤2
  · letI := (ZMod.isCyclic_units_two_pow_iff m).mpr hm
    exact (CyclicUnitQuadraticRoots.card_square_fiber_le_two v).trans (by decide)
  · obtain ⟨n,rfl⟩ : ∃ n, m=n+3 := ⟨m-3,by omega⟩
    by_cases hv : ∃ u : (ZMod (2^(n+3)))ˣ, u^2=v
    · have he := MonoidHom.card_fiber_eq_of_mem_range
        (powMonoidHom (α := (ZMod (2^(n+3)))ˣ) 2) hv
        (show (1:(ZMod (2^(n+3)))ˣ)∈Set.range (powMonoidHom 2) from ⟨1,by simp⟩)
      change (Finset.univ.filter (fun u : (ZMod (2^(n+3)))ˣ => u^2=v)).card =
        (Finset.univ.filter (fun u : (ZMod (2^(n+3)))ˣ => u^2=1)).card at he
      rw [he]
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,MonoidHom.mem_ker,
        powMonoidHom_apply] using square_kernel_card_le_four n
    · have he : Finset.univ.filter (fun u : (ZMod (2^(n+3)))ˣ => u^2=v)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact hv ⟨u,(Finset.mem_filter.mp hu).2⟩
      rw [he]
      simp

/-- A bound on square fibers bounds quadratic unit roots when one coefficient is a unit. -/
theorem card_quadratic_units_le_of_square_bound {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] (C : ℕ)
    (hsq : ∀ v : Rˣ, (Finset.univ.filter (fun u : Rˣ => u^2=v)).card≤C)
    (a b : R) (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b)).card ≤ C := by
  by_cases hr : ∃ u : Rˣ, a*(u:R)^2=b
  · obtain ⟨u0,hu0⟩ := hr
    have ha : IsUnit a := hab.elim id (fun hb =>
      (IsUnit.mul_iff.mp (show IsUnit (a*(u0:R)^2) from hu0.symm ▸ hb)).1)
    have he : Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b) =
        Finset.univ.filter (fun u : Rˣ => u^2=u0^2) := by
      ext u
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro hu
        apply Units.ext
        exact ha.mul_left_cancel (hu.trans hu0.symm)
      · intro hu
        have hv := congrArg (fun z : Rˣ => (z:R)) hu
        simpa only [Units.val_pow_eq_pow_val] using (congrArg (fun z : R => a*z) hv).trans hu0
    rw [he]
    exact hsq (u0^2)
  · have he : Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hr ⟨u,(Finset.mem_filter.mp hu).2⟩
    rw [he]
    simp

/-- The actual reduced quadratic unit-root count at powers of two is at most four. -/
theorem two_power_quadratic_count (m : ℕ) (a b : ZMod (2^m))
    (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : (ZMod (2^m))ˣ => a*(u:ZMod (2^m))^2=b)).card ≤ 4 :=
  card_quadratic_units_le_of_square_bound 4 (card_square_fiber_le_four m) a b hab

end NField.Alignment.TwoPowerUnitQuadraticRoots
