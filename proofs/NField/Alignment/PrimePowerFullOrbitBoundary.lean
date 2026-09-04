/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExactConductorEnergy
import Mathlib.GroupTheory.Index

/-!
# Prime-power full-orbit boundary

The additive edge of the full unit orbit modulo `p^e` is pulled back from the
single residue class `1` modulo `p`.  The generic pullback theorem below shows
that its character flux is the fiber thickness times a subgroup character
sum.  Primitivity kills that sum above conductor `p`.
-/

namespace NField.Alignment.PrimePowerFullOrbitBoundary

noncomputable section

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.ConductorBoundaryLedger
open NField.Alignment.ExactConductorEnergy

/-- Character sum over a finite subgroup.  The definition hides the harmless
choice of a finite enumeration. -/
noncomputable def subgroupCharacterSum
    {G : Type*} [CommGroup G] [Fintype G]
    (H : Subgroup G) (χ : G →* ℂˣ) : ℂ := by
  classical
  exact ∑ h : G with h ∈ H, (χ h : ℂ)

/-- Negative indicator of a subgroup. -/
noncomputable def negativeSubgroupIndicator
    {G : Type*} [Group G] (H : Subgroup G) (x : G) : ℂ := by
  classical
  exact if x ∈ H then -1 else 0

/-- A nontrivial character sums to zero on a finite subgroup. -/
theorem subgroup_character_sum_eq_zero
    {G : Type*} [CommGroup G] [Fintype G]
    (H : Subgroup G) (χ : G →* ℂˣ)
    (hχ : ∃ h : H, ((χ h.val : ℂ) ≠ 1)) :
    subgroupCharacterSum H χ = 0 := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨a, ha⟩ := hχ
  let shift : H ≃ H := Equiv.mulLeft a
  have hshift :
      (∑ h : H, (χ h.val : ℂ)) =
        ∑ h : H, (χ (a.val * h.val) : ℂ) := by
    symm
    exact Equiv.sum_comp shift (fun h : H => (χ h.val : ℂ))
  have hscale :
      (∑ h : H, (χ (a.val * h.val) : ℂ)) =
        (χ a.val : ℂ) * ∑ h : H, (χ h.val : ℂ) := by
    simp_rw [map_mul, Units.val_mul]
    rw [Finset.mul_sum]
  have hzero :
      ((χ a.val : ℂ) - 1) * ∑ h : H, (χ h.val : ℂ) = 0 := by
    rw [sub_mul, one_mul, ← hscale, ← hshift]
    ring
  have hsub : (∑ h : H, (χ h.val : ℂ)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ha)
  unfold subgroupCharacterSum
  rw [Finset.sum_subtype
    (p := fun h : G => h ∈ H)
    (s := Finset.univ.filter fun h : G => h ∈ H)
    (by intro h; simp) (fun h => (χ h : ℂ))]
  exact hsub

/-- Every fiber of a surjective homomorphism of finite groups has cardinality
equal to the cardinality of its kernel. -/
theorem card_fiber_eq_card_ker
    {G K : Type*} [Group G] [Group K]
    [Fintype G] [Fintype K] [DecidableEq K]
    (π : G →* K) (hπ : Function.Surjective π) (y : K) :
    ((Finset.univ.filter fun x : G => π x = y).card) =
      Fintype.card π.ker := by
  have hy : y ∈ Set.range π := hπ y
  have hone : (1 : K) ∈ Set.range π := ⟨1, map_one π⟩
  calc
    ((Finset.univ.filter fun x : G => π x = y).card) =
        ((Finset.univ.filter fun x : G => π x = 1).card) :=
      MonoidHom.card_fiber_eq_of_mem_range π hy hone
    _ = Fintype.card π.ker := by
      classical
      let e : {x : G // π x = 1} ≃ π.ker :=
        { toFun := fun x => ⟨x.val, x.property⟩
          invFun := fun x => ⟨x.val, x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Fintype.card_congr e]
      exact (Fintype.card_subtype (fun x : G => π x = 1)).symm

/-- Pulling an indicator boundary back through a surjective finite group map
multiplies its character flux by the kernel thickness. -/
theorem pullback_subgroup_boundary_flux
    {G K : Type*} [CommGroup G] [CommGroup K]
    [Fintype G] [Fintype K] [DecidableEq K]
    (π : G →* K) (hπ : Function.Surjective π)
    (H : Subgroup K) (χ : K →* ℂˣ) :
    (∑ x : G,
      negativeSubgroupIndicator H (π x) * (χ (π x) : ℂ)) =
      -(Fintype.card π.ker : ℂ) * subgroupCharacterSum H χ := by
  classical
  unfold negativeSubgroupIndicator subgroupCharacterSum
  calc
    (∑ x : G,
        (if π x ∈ H then (-1 : ℂ) else 0) * (χ (π x) : ℂ)) =
      ∑ y : K, ∑ x : G with π x = y,
        (if π x ∈ H then (-1 : ℂ) else 0) * (χ (π x) : ℂ) := by
          symm
          exact Finset.sum_fiberwise Finset.univ π
            (fun x => (if π x ∈ H then (-1 : ℂ) else 0) * (χ (π x) : ℂ))
    _ = ∑ y : K,
        (Fintype.card π.ker : ℂ) *
          ((if y ∈ H then (-1 : ℂ) else 0) * (χ y : ℂ)) := by
          apply Finset.sum_congr rfl
          intro y _
          calc
            (∑ x : G with π x = y,
                (if π x ∈ H then (-1 : ℂ) else 0) * (χ (π x) : ℂ)) =
              ∑ x : G with π x = y,
                (if y ∈ H then (-1 : ℂ) else 0) * (χ y : ℂ) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [(Finset.mem_filter.mp hx).2]
            _ = (Fintype.card π.ker : ℂ) *
                ((if y ∈ H then (-1 : ℂ) else 0) * (χ y : ℂ)) := by
                  rw [Finset.sum_const, nsmul_eq_mul,
                    card_fiber_eq_card_ker π hπ y]
    _ = -(Fintype.card π.ker : ℂ) *
        ∑ h : K with h ∈ H, (χ h : ℂ) := by
          rw [Finset.mul_sum]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : y ∈ H <;> simp [hy]

/-- The kernel size of reduction from units modulo `p^e` to units modulo
`p^f` is exactly `p^(e-f)`. -/
theorem primePower_unitsMap_kernel_card
    {p e f : ℕ} [NeZero (p ^ e)] [NeZero (p ^ f)]
    (hp : p.Prime) (hf : 1 ≤ f) (hfe : f ≤ e) :
    Fintype.card (ZMod.unitsMap (pow_dvd_pow p hfe)).ker = p ^ (e - f) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ f) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let π := ZMod.unitsMap (pow_dvd_pow p hfe)
  have hsurj : Function.Surjective π :=
    ZMod.unitsMap_surjective (pow_dvd_pow p hfe)
  have hrange : Nat.card π.range = Nat.card (UnitClass (p ^ f)) := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    simp
  have hcard := π.ker.card_mul_index
  rw [Subgroup.index_ker, hrange] at hcard
  simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hcard
  have hepos : 0 < e := by omega
  rw [Nat.totient_prime_pow hp hepos,
    Nat.totient_prime_pow hp (by omega : 0 < f)] at hcard
  have hpow : p ^ (e - 1) = p ^ (e - f) * p ^ (f - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hcard
  have hcancel : 0 < p ^ (f - 1) * (p - 1) :=
    Nat.mul_pos (pow_pos hp.pos _) (Nat.sub_pos_of_lt hp.one_lt)
  have hresult : Fintype.card π.ker = p ^ (e - f) := by
    apply Nat.eq_of_mul_eq_mul_right hcancel
    simpa [mul_assoc] using hcard
  simpa [π] using hresult

/-- The special reduction from units modulo `p^e` directly to units modulo
`p` has kernel cardinality `p^(e-1)`. -/
theorem prime_unitsMap_kernel_card
    {p e : ℕ} [NeZero (p ^ e)] [NeZero p]
    (hp : p.Prime) (he : 1 ≤ e) :
    Fintype.card (ZMod.unitsMap
      (dvd_pow_self p (by omega : e ≠ 0))).ker = p ^ (e - 1) := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let π := ZMod.unitsMap (dvd_pow_self p (by omega : e ≠ 0))
  have hsurj : Function.Surjective π :=
    ZMod.unitsMap_surjective (dvd_pow_self p (by omega : e ≠ 0))
  have hrange : Nat.card π.range = Nat.card (UnitClass p) := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    simp
  have hcard := π.ker.card_mul_index
  rw [Subgroup.index_ker, hrange] at hcard
  simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hcard
  rw [Nat.totient_prime_pow hp (by omega : 0 < e),
    Nat.totient_prime hp] at hcard
  have hcancel : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hresult : Fintype.card π.ker = p ^ (e - 1) := by
    apply Nat.eq_of_mul_eq_mul_right hcancel
    simpa [mul_assoc] using hcard
  simpa [π] using hresult

/-- The visible boundary of the full unit orbit modulo `p^e`: on units it is
minus the indicator of the residue class `1` modulo `p`. -/
noncomputable def fullOrbitVisibleBoundary
    {p e : ℕ} (he : 1 ≤ e) (u : UnitClass (p ^ e)) : ℂ :=
  if ZMod.unitsMap (dvd_pow_self p (by omega : e ≠ 0)) u = 1 then -1 else 0

/-- Exact flux of the full-orbit boundary against a primitive source at level
`p^f`.  The formula is a kernel-thickness multiple of the source character sum
on the principal-unit subgroup. -/
theorem fullOrbit_primitiveSourceFlux
    {p e f : ℕ} [NeZero (p ^ e)] [NeZero (p ^ f)] [NeZero p]
    (hp : p.Prime) (he : 1 ≤ e)
    (hf : 1 ≤ f) (hfe : f ≤ e) (ψ : Character (p ^ f)) :
    (∑ u : UnitClass (p ^ e),
      fullOrbitVisibleBoundary he u *
        ψ (ZMod.unitsMap (pow_dvd_pow p hfe) u).val) =
      -(p ^ (e - f) : ℂ) *
        subgroupCharacterSum
          (ZMod.unitsMap (dvd_pow_self p (by omega : f ≠ 0))).ker
          ψ.toUnitHom := by
  classical
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ f) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let π := ZMod.unitsMap (pow_dvd_pow p hfe)
  let H := (ZMod.unitsMap (dvd_pow_self p (by omega : f ≠ 0))).ker
  have hsurj : Function.Surjective π :=
    ZMod.unitsMap_surjective (pow_dvd_pow p hfe)
  have hmem (u : UnitClass (p ^ e)) :
      π u ∈ H ↔ ZMod.unitsMap
          (dvd_pow_self p (by omega : e ≠ 0)) u = 1 := by
    change ZMod.unitsMap (dvd_pow_self p (by omega : f ≠ 0))
        (ZMod.unitsMap (pow_dvd_pow p hfe) u) = 1 ↔ _
    rw [← MonoidHom.comp_apply]
    rw [ZMod.unitsMap_comp]
  have hflux := pullback_subgroup_boundary_flux π hsurj H ψ.toUnitHom
  have hkcard : Fintype.card π.ker = p ^ (e - f) := by
    simpa [π] using primePower_unitsMap_kernel_card hp hf hfe
  rw [hkcard] at hflux
  simpa [π, H, fullOrbitVisibleBoundary, hmem,
    negativeSubgroupIndicator] using hflux

/-- At conductor `p` every primitive odd source has flux `-p^(e-1)`. -/
theorem fullOrbit_primeSourceFlux
    {p e : ℕ} [NeZero (p ^ e)] [NeZero p]
    (hp : p.Prime) (he : 1 ≤ e)
    (ψ : Character p) :
    (∑ u : UnitClass (p ^ e),
      fullOrbitVisibleBoundary he u *
        ψ (ZMod.unitsMap (dvd_pow_self p (by omega : e ≠ 0)) u).val) =
      -(p ^ (e - 1) : ℂ) := by
  classical
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let π := ZMod.unitsMap (dvd_pow_self p (by omega : e ≠ 0))
  have hsurj : Function.Surjective π :=
    ZMod.unitsMap_surjective (dvd_pow_self p (by omega : e ≠ 0))
  have hflux := pullback_subgroup_boundary_flux π hsurj
    (⊥ : Subgroup (UnitClass p)) ψ.toUnitHom
  have hkcard : Fintype.card π.ker = p ^ (e - 1) := by
    simpa [π] using prime_unitsMap_kernel_card hp he
  rw [hkcard] at hflux
  have hbot : subgroupCharacterSum
      (⊥ : Subgroup (UnitClass p)) ψ.toUnitHom = 1 := by
    unfold subgroupCharacterSum
    calc
      (∑ x : UnitClass p with x ∈ (⊥ : Subgroup (UnitClass p)),
          (ψ.toUnitHom x : ℂ)) = (ψ.toUnitHom 1 : ℂ) := by
            apply Finset.sum_eq_single 1
            · intro b hb hne
              have hb1 : b = 1 := by
                simpa using (Finset.mem_filter.mp hb).2
              exact (hne hb1).elim
            · intro hnot
              exact (hnot (by simp)).elim
      _ = 1 := by simp
  rw [hbot] at hflux
  simpa [π, fullOrbitVisibleBoundary,
    negativeSubgroupIndicator] using hflux

/-- A primitive character at level `p^f`, with `f >= 2`, is nontrivial on the
principal-unit kernel of reduction to level `p`. -/
theorem primitive_nontrivial_on_principalUnits
    {p f : ℕ} [NeZero (p ^ f)]
    (hp : p.Prime) (hf : 2 ≤ f)
    (ψ : Character (p ^ f)) (hψ : ψ.IsPrimitive) :
    ∃ h : (ZMod.unitsMap (dvd_pow_self p (by omega : f ≠ 0))).ker,
      ((ψ.toUnitHom h.val : ℂ) ≠ 1) := by
  letI : NeZero (p ^ f) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_contra htrivial
  push Not at htrivial
  have hfactor : ψ.FactorsThrough p :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap
      (dvd_pow_self p (by omega : f ≠ 0))).2 (by
        intro h hh
        apply Units.ext
        exact htrivial ⟨h, hh⟩)
  have hcond : ψ.conductor ∣ p :=
    (DirichletCharacter.mem_conductorSet_iff_conductor_dvd ψ
      (dvd_pow_self p (by omega : f ≠ 0))).1 hfactor
  rw [hψ] at hcond
  have hpow : p ^ f ∣ p ^ 1 := by simpa using hcond
  have hle : f ≤ 1 :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow
  omega

/-- Every primitive source strictly above conductor `p` has zero flux. -/
theorem fullOrbit_higherSourceFlux_zero
    {p e f : ℕ} [NeZero (p ^ e)] [NeZero (p ^ f)] [NeZero p]
    (hp : p.Prime) (he : 1 ≤ e)
    (hf : 2 ≤ f) (hfe : f ≤ e)
    (ψ : Character (p ^ f)) (hψ : ψ.IsPrimitive) :
    (∑ u : UnitClass (p ^ e),
      fullOrbitVisibleBoundary he u *
        ψ (ZMod.unitsMap (pow_dvd_pow p hfe) u).val) = 0 := by
  rw [fullOrbit_primitiveSourceFlux hp he (by omega) hfe ψ]
  have hsum := subgroup_character_sum_eq_zero
    (ZMod.unitsMap (dvd_pow_self p (by omega : f ≠ 0))).ker
    ψ.toUnitHom (primitive_nontrivial_on_principalUnits hp hf ψ hψ)
  rw [hsum]
  ring

/-- At an odd prime, the number of primitive odd characters is `(p-1)/2`. -/
theorem primitiveOddCharacterCount_prime
    {p : ℕ} [NeZero p] (hp : p.Prime) (hpodd : p ≠ 2) :
    (primitiveOddCharacterCount p : ℝ) = (p - 1 : ℝ) / 2 := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  letI : Fact (2 < p) := ⟨by omega⟩
  have hneg : -(1 : UnitClass p) ≠ 1 := by
    intro h
    have hv := congrArg Units.val h
    exact ZMod.neg_one_ne_one (by simpa using hv)
  have hprim (χ : Character p) (hoddχ : χ.Odd) : χ.IsPrimitive := by
    unfold DirichletCharacter.IsPrimitive
    have hdiv := χ.conductor_dvd_level
    rcases (Nat.dvd_prime hp).mp hdiv with hc | hc
    · exfalso
      have hone : χ = 1 :=
        (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hc
      subst χ
      apply hoddχ.not_even
      unfold DirichletCharacter.Even
      exact MulChar.one_apply isUnit_neg_one
    · exact hc
  have hkernel :
      primitiveOddKernel (1 : UnitClass p) (1 : UnitClass p) =
        oddCharacterKernel (1 : UnitClass p) (1 : UnitClass p) := by
    classical
    unfold primitiveOddKernel oddCharacterKernel
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hoddχ : χ.Odd
    · simp [hoddχ, hprim χ hoddχ]
    · simp [hoddχ]
  apply Complex.ofReal_injective
  push_cast
  rw [← primitiveOddKernel_one_eq_count, hkernel,
    oddCharacterKernel_eq]
  simp [hneg, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  ring

/-- Exact energy at conductor `p` for the full unit orbit modulo `p^e`. -/
theorem fullOrbit_primeConductorEnergy
    {p e : ℕ} [NeZero (p ^ e)] [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) (he : 1 ≤ e) :
    exactConductorEnergy p (fullOrbitVisibleBoundary (p := p) he) =
      ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (2 * e - 2) := by
  have hdiv : p ∣ p ^ e := dvd_pow_self p (by omega)
  rw [exactConductorEnergy_eq_primitiveSourceEnergy hdiv hp.pos]
  unfold primitiveSourceEnergy
  -- Expose each source flux and replace it by the common prime-level value.
  have hflux (ψ : Character p) :
      (∑ u : UnitClass (p ^ e),
        fullOrbitVisibleBoundary (p := p) he u * ψ (pushdownUnit hdiv u).val) =
        -(p ^ (e - 1) : ℂ) := by
    simpa [pushdownUnit] using fullOrbit_primeSourceFlux hp he ψ
  simp_rw [hflux]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (primitiveOddCharacterCount p : ℝ) *
      ‖-(p ^ (e - 1) : ℂ)‖ ^ 2 = _
  rw [primitiveOddCharacterCount_prime hp hpodd]
  rw [norm_neg, norm_pow, norm_natCast]
  rw [← pow_mul]
  congr 2
  omega

/-- Exact energy vanishes at every primitive prime-power conductor above `p`. -/
theorem fullOrbit_higherConductorEnergy_zero
    {p e f : ℕ} [NeZero (p ^ e)] [NeZero (p ^ f)] [NeZero p]
    (hp : p.Prime) (he : 1 ≤ e) (hf : 2 ≤ f) (hfe : f ≤ e) :
    exactConductorEnergy (p ^ f) (fullOrbitVisibleBoundary (p := p) he) = 0 := by
  classical
  have hdiv : p ^ f ∣ p ^ e := pow_dvd_pow p hfe
  rw [exactConductorEnergy_eq_primitiveSourceEnergy hdiv
    (pow_pos hp.pos f)]
  unfold primitiveSourceEnergy
  apply Finset.sum_eq_zero
  intro ψ hψ
  have hz := fullOrbit_higherSourceFlux_zero hp he hf hfe ψ
    (Finset.mem_filter.mp hψ).2.1
  rw [show (∑ x : UnitClass (p ^ e),
      fullOrbitVisibleBoundary (p := p) he x *
        ψ (pushdownUnit hdiv x).val) = 0 by
    simpa [pushdownUnit] using hz]
  simp

/-- Conductor one contains no odd character energy. -/
theorem exactConductorEnergy_one_eq_zero
    {m : ℕ} [NeZero m] (μ : UnitClass m → ℂ) :
    exactConductorEnergy 1 μ = 0 := by
  classical
  unfold exactConductorEnergy
  apply Finset.sum_eq_zero
  intro χ hχ
  have hprop := (Finset.mem_filter.mp hχ).2
  have hone : χ = 1 :=
    (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hprop.2
  subst χ
  have heven : (1 : Character m).Even := by
    unfold DirichletCharacter.Even
    exact MulChar.one_apply isUnit_neg_one
  exfalso
  apply hprop.1.not_even
  exact heven

/-- Complete prime-power support law indexed by the divisor exponent. -/
theorem fullOrbit_exactConductorEnergy_pow
    {p e f : ℕ} [NeZero (p ^ e)] [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) (he : 1 ≤ e) (hfe : f ≤ e) :
    exactConductorEnergy (p ^ f) (fullOrbitVisibleBoundary (p := p) he) =
      if f = 1 then
        ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (2 * e - 2)
      else 0 := by
  by_cases hf0 : f = 0
  · subst f
    simp [exactConductorEnergy_one_eq_zero]
  by_cases hf1 : f = 1
  · subst f
    simpa using fullOrbit_primeConductorEnergy hp hpodd he
  · have hf2 : 2 ≤ f := by omega
    letI : NeZero (p ^ f) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [if_neg hf1]
    exact fullOrbit_higherConductorEnergy_zero hp he hf2 hfe

/-- The full odd energy equals the single surviving conductor-`p` energy. -/
theorem fullOrbit_fullOddBoundaryEnergy
    {p e : ℕ} [NeZero (p ^ e)] [NeZero p]
    (hp : p.Prime) (hpodd : p ≠ 2) (he : 1 ≤ e) :
    fullOddBoundaryEnergy (fullOrbitVisibleBoundary (p := p) he) =
      ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (2 * e - 2) := by
  rw [fullOddBoundaryEnergy_eq_sum_exactConductor]
  have hpdiv : p ∈ (p ^ e).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_pow_self p (by omega),
      pow_ne_zero _ hp.ne_zero⟩
  rw [Finset.sum_eq_single p]
  · exact fullOrbit_primeConductorEnergy hp hpodd he
  · intro d hd hdp
    obtain ⟨f, hfe, rfl⟩ :=
      (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
    rw [fullOrbit_exactConductorEnergy_pow hp hpodd he hfe]
    have hf1 : f ≠ 1 := by
      intro hf
      subst f
      simp at hdp
    rw [if_neg hf1]
  · intro hnot
    exact (hnot hpdiv).elim

end

end NField.Alignment.PrimePowerFullOrbitBoundary
