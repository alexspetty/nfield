/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarrySpectralBridge

/-!
# Prime-square sawtooth energy

This module expands the first-window sawtooth square mass into the Dedekind
collision double sum.  The only missing residues are the multiples of the
prime; they are parametrized exactly by `ZMod p`, where the centered sawtooth
reduces to the lower modulus.  The previously proved weighted lower correction
then cancels the entire discrepancy.
-/

namespace NField.Alignment.PrimeSquareSawtoothEnergy

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionRatioCompression
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarrySpectralBridge
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareDedekindCorrection

/-- Canonical embedding of the prime multiples modulo `p^2`. -/
def primeMultiple
    {p : ℕ} [NeZero (p ^ 2)] (t : ZMod p) : ZMod (p ^ 2) :=
  ((p * t.val : ℕ) : ZMod (p ^ 2))

theorem primeMultiple_val
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)] (t : ZMod p) :
    (primeMultiple t).val = p * t.val := by
  unfold primeMultiple
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  have ht := t.val_lt
  nlinarith

theorem primeMultiple_nonunit
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (t : ZMod p) : ¬IsUnit (primeMultiple t) := by
  intro hunit
  have hcop : (p * t.val).Coprime (p ^ 2) := by
    apply (ZMod.isUnit_iff_coprime (p * t.val) (p ^ 2)).mp
    rw [show ((p * t.val : ℕ) : ZMod (p ^ 2)) = primeMultiple t by rfl]
    exact hunit
  have hpdivLeft : p ∣ p * t.val := dvd_mul_right p t.val
  have hpdivRight : p ∣ p ^ 2 := dvd_pow_self p (by omega)
  have hpone : p = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hpdivLeft hpdivRight
  exact hp.ne_one hpone

/-- Every nonunit modulo `p^2` is represented uniquely by one prime multiple. -/
noncomputable def primeMultipleEquivNonunits
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)] (hp : p.Prime) :
    ZMod p ≃ {x : ZMod (p ^ 2) // ¬IsUnit x} := by
  let f : ZMod p → {x : ZMod (p ^ 2) // ¬IsUnit x} :=
    fun t => ⟨primeMultiple t, primeMultiple_nonunit hp t⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t hst
    apply ZMod.val_injective
    have hv := congrArg
      (fun x : {x : ZMod (p ^ 2) // ¬IsUnit x} => x.val.val) hst
    change (primeMultiple s).val = (primeMultiple t).val at hv
    rw [primeMultiple_val, primeMultiple_val] at hv
    exact Nat.mul_left_cancel hp.pos hv
  · intro x
    have hpdiv : p ∣ x.val.val := by
      by_contra hnot
      have hcop : x.val.val.Coprime (p ^ 2) :=
        hp.coprime_pow_of_not_dvd hnot
      have hunit : IsUnit x.val := by
        rw [← ZMod.natCast_zmod_val x.val]
        exact (ZMod.isUnit_iff_coprime x.val.val (p ^ 2)).mpr hcop
      exact x.property hunit
    have hqLt : x.val.val / p < p := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      have hx := x.val.val_lt
      simpa [pow_two] using hx
    let t : ZMod p := (x.val.val / p : ℕ)
    refine ⟨t, Subtype.ext ?_⟩
    apply ZMod.val_injective
    rw [primeMultiple_val]
    have htval : t.val = x.val.val / p := by
      dsimp [t]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hqLt]
    rw [htval, Nat.mul_div_cancel' hpdiv]

/-- Exact partition of a prime-square residue sum into units and prime
multiples. -/
theorem sum_primeSquare_eq_units_add_multiples
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)] (hp : p.Prime)
    (F : ZMod (p ^ 2) → ℂ) :
    (∑ x : ZMod (p ^ 2), F x) =
      (∑ u : UnitClass (p ^ 2), F u.val) +
        ∑ t : ZMod p, F (primeMultiple t) := by
  classical
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod (p ^ 2))) IsUnit F
  have hunit :
      (∑ x ∈ (Finset.univ : Finset (ZMod (p ^ 2))) with IsUnit x, F x) =
        ∑ u : UnitClass (p ^ 2), F u.val := by
    calc
      (∑ x ∈ (Finset.univ : Finset (ZMod (p ^ 2))) with IsUnit x, F x) =
          ∑ x : {x : ZMod (p ^ 2) // IsUnit x}, F x.val := by
            exact Finset.sum_subtype
              ((Finset.univ : Finset (ZMod (p ^ 2))).filter IsUnit)
              (by intro x; simp) F
      _ = ∑ u : UnitClass (p ^ 2), F u.val := by
            symm
            apply Fintype.sum_equiv unitsEquivIsUnit
            intro u
            rfl
  have hnonunit :
      (∑ x ∈ (Finset.univ : Finset (ZMod (p ^ 2))) with ¬IsUnit x, F x) =
        ∑ t : ZMod p, F (primeMultiple t) := by
    calc
      (∑ x ∈ (Finset.univ : Finset (ZMod (p ^ 2))) with ¬IsUnit x, F x) =
          ∑ x : {x : ZMod (p ^ 2) // ¬IsUnit x}, F x.val := by
            exact Finset.sum_subtype
              ((Finset.univ : Finset (ZMod (p ^ 2))).filter fun x => ¬IsUnit x)
              (by intro x; simp) F
      _ = ∑ t : ZMod p, F (primeMultiple t) := by
            symm
            apply Fintype.sum_equiv (primeMultipleEquivNonunits hp)
            intro t
            rfl
  rw [← hunit, ← hnonunit]
  exact hpartition.symm

/-- The centered sawtooth on a prime multiple reduces exactly to the lower
prime modulus. -/
theorem centeredSawtooth_primeMultiple
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)] (hp : p.Prime) (t : ZMod p) :
    centeredSawtooth (primeMultiple t) = centeredSawtooth t := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold centeredSawtooth
  by_cases ht : t = 0
  · subst t
    simp [primeMultiple]
  · have hlift : primeMultiple t ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [primeMultiple_val] at hv
      simp at hv
      rcases hv with hpzero | htzero
      · exact hp.ne_zero hpzero
      · exact ht htzero
    rw [if_neg hlift, if_neg ht, primeMultiple_val]
    push_cast
    field_simp [hpC]

/-- Prime multiplication intertwines a prime-square unit with its reduction
modulo the prime. -/
theorem unit_mul_primeMultiple
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)] (hp : p.Prime)
    (h : UnitClass (p ^ 2)) (t : ZMod p) :
    h.val * primeMultiple t =
      primeMultiple ((primeReduction hp h).val * t) := by
  apply ZMod.val_injective
  rw [ZMod.val_mul, primeMultiple_val, primeMultiple_val]
  unfold primeReduction
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_mul]
  have hleft : h.val.val * (p * t.val) = p * (h.val.val * t.val) := by ring
  rw [ZMod.val_natCast]
  rw [hleft]
  have hmod : p * (h.val.val * t.val) % p ^ 2 =
      p * ((h.val.val * t.val) % p) := by
    simpa [pow_two] using
      (Nat.mul_mod_mul_left p (h.val.val * t.val) p)
  rw [hmod]
  congr 1
  simp [Nat.mul_mod]

/-- Sawtooth multiplication on prime multiples is exactly lower-modulus
multiplication by the reduced unit. -/
theorem centeredSawtooth_unit_mul_primeMultiple
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)] (hp : p.Prime)
    (h : UnitClass (p ^ 2)) (t : ZMod p) :
    centeredSawtooth (h.val * primeMultiple t) =
      centeredSawtooth ((primeReduction hp h).val * t) := by
  rw [unit_mul_primeMultiple hp, centeredSawtooth_primeMultiple hp]

/-- Dedekind correlation restricted to prime-square units. -/
noncomputable def unitDedekindSum
    {m : ℕ} [NeZero m] (h : UnitClass m) : ℂ :=
  ∑ x : UnitClass m,
    centeredSawtooth x.val * centeredSawtooth (h.val * x.val)

theorem unitDedekindSum_inv
    {m : ℕ} [NeZero m] (h : UnitClass m) :
    unitDedekindSum h⁻¹ = unitDedekindSum h := by
  classical
  unfold unitDedekindSum
  let e : UnitClass m ≃ UnitClass m := Equiv.mulLeft h
  have hreindex := e.sum_comp (fun x : UnitClass m =>
    centeredSawtooth x.val * centeredSawtooth (h⁻¹.val * x.val))
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [e]
  change centeredSawtooth (h.val * x.val) *
      centeredSawtooth ((h⁻¹ * (h * x)).val) =
    centeredSawtooth x.val * centeredSawtooth (h.val * x.val)
  simp [mul_comm]

/-- Exact prime-square unit/nonunit split of the Dedekind sum. -/
theorem dedekindSum_eq_unit_add_lower
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)] (hp : p.Prime)
    (h : UnitClass (p ^ 2)) :
    dedekindSum h = unitDedekindSum h + lowerDedekindKernel hp h := by
  unfold dedekindSum unitDedekindSum lowerDedekindKernel primeDedekindSum
  rw [sum_primeSquare_eq_units_add_multiples hp]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [centeredSawtooth_primeMultiple hp,
    centeredSawtooth_unit_mul_primeMultiple hp]

/-- One pair of first-window coordinates has unit-group correlation equal to
the unit-restricted Dedekind sum at their ratio. -/
theorem shortWindow_pair_correlation
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (i j : FirstWindowIndex p) :
    (∑ a : UnitClass (p ^ 2),
      centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val) *
        centeredSawtooth ((firstWindowUnit hp j)⁻¹.val * a.val)) =
      unitDedekindSum ((firstWindowUnit hp i)⁻¹ *
        firstWindowUnit hp j) := by
  classical
  let k := firstWindowUnit hp i
  let u := firstWindowUnit hp j
  let e : UnitClass (p ^ 2) ≃ UnitClass (p ^ 2) := Equiv.mulLeft k
  have hreindex := e.sum_comp (fun a : UnitClass (p ^ 2) =>
    centeredSawtooth (k⁻¹.val * a.val) *
      centeredSawtooth (u⁻¹.val * a.val))
  rw [← hreindex]
  have hpoint (x : UnitClass (p ^ 2)) :
      centeredSawtooth (k⁻¹.val * (k * x).val) *
          centeredSawtooth (u⁻¹.val * (k * x).val) =
        centeredSawtooth x.val *
          centeredSawtooth (((k⁻¹ * u)⁻¹).val * x.val) := by
    have hleft : k⁻¹.val * (k * x).val = x.val := by
      change (k⁻¹ * (k * x)).val = x.val
      congr 1
      group
    have hright : u⁻¹.val * (k * x).val =
        ((k⁻¹ * u)⁻¹).val * x.val := by
      change (u⁻¹ * (k * x)).val = ((k⁻¹ * u)⁻¹ * x).val
      congr 1
      group
    rw [hleft, hright]
  change (∑ x : UnitClass (p ^ 2),
      centeredSawtooth (k⁻¹.val * (k * x).val) *
        centeredSawtooth (u⁻¹.val * (k * x).val)) =
    unitDedekindSum (k⁻¹ * u)
  calc
    _ = ∑ x : UnitClass (p ^ 2), centeredSawtooth x.val *
          centeredSawtooth (((k⁻¹ * u)⁻¹).val * x.val) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hpoint x
    _ = unitDedekindSum (k⁻¹ * u)⁻¹ := rfl
    _ = unitDedekindSum (k⁻¹ * u) := unitDedekindSum_inv (k⁻¹ * u)

/-- Expanding the real short-window convolution square gives the exact
unit-restricted Dedekind collision double sum. -/
theorem shortWindow_complexSquareMass_eq_unitDedekindDoubleSum
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    (∑ a : UnitClass (p ^ 2),
      shortWindowSawtoothSignal hp a * shortWindowSawtoothSignal hp a) =
      collisionDoubleSum (firstCollisionWindow hp) unitDedekindSum := by
  classical
  unfold shortWindowSawtoothSignal
  calc
    (∑ a : UnitClass (p ^ 2),
        (∑ i : FirstWindowIndex p,
          centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val)) *
        ∑ j : FirstWindowIndex p,
          centeredSawtooth ((firstWindowUnit hp j)⁻¹.val * a.val)) =
      ∑ a : UnitClass (p ^ 2), ∑ i : FirstWindowIndex p,
        ∑ j : FirstWindowIndex p,
          centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val) *
            centeredSawtooth ((firstWindowUnit hp j)⁻¹.val * a.val) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ =
      ∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        ∑ a : UnitClass (p ^ 2),
          centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val) *
            centeredSawtooth ((firstWindowUnit hp j)⁻¹.val * a.val) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        unitDedekindSum ((firstWindowUnit hp i)⁻¹ *
          firstWindowUnit hp j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact shortWindow_pair_correlation hp i j
    _ = collisionDoubleSum (firstCollisionWindow hp) unitDedekindSum := by
        unfold collisionDoubleSum firstCollisionWindow
        rw [sum_image_injective (firstWindowUnit hp)
          (firstWindowUnit_injective hp)]
        apply Finset.sum_congr rfl
        intro i _
        rw [sum_image_injective (firstWindowUnit hp)
          (firstWindowUnit_injective hp)]

/-- The collision double sum of the lower-modulus correction is zero. -/
theorem lowerDedekindCollisionDoubleSum_eq_zero
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    collisionDoubleSum (firstCollisionWindow hp) (lowerDedekindKernel hp) = 0 := by
  have hzero := weightedLowerDedekindCorrection_eq_zero hp hpodd
  unfold weightedLowerDedekindCorrection at hzero
  rw [weightedRatioSum_eq_collisionDoubleSum] at hzero
  exact hzero

/-- After the lower correction cancels, the unit-restricted and full
Dedekind collision double sums are exactly equal. -/
theorem unitDedekindDoubleSum_eq_full
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    collisionDoubleSum (firstCollisionWindow hp) unitDedekindSum =
      primeSquareCollisionDoubleSum hp := by
  have hsplit :
      collisionDoubleSum (firstCollisionWindow hp) dedekindSum =
        collisionDoubleSum (firstCollisionWindow hp) unitDedekindSum +
          collisionDoubleSum (firstCollisionWindow hp)
            (lowerDedekindKernel hp) := by
    unfold collisionDoubleSum
    simp_rw [dedekindSum_eq_unit_add_lower hp]
    simp_rw [Finset.sum_add_distrib]
  rw [lowerDedekindCollisionDoubleSum_eq_zero hp hpodd, add_zero] at hsplit
  exact hsplit.symm

/-- Casting the real norm square of the real-valued convolution recovers its
ordinary complex square. -/
theorem shortWindow_normSquare_cast
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (a : UnitClass (p ^ 2)) :
    ((‖shortWindowSawtoothSignal hp a‖ ^ 2 : ℝ) : ℂ) =
      shortWindowSawtoothSignal hp a * shortWindowSawtoothSignal hp a := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  exact congrArg (fun z : ℂ => z * shortWindowSawtoothSignal hp a)
    (star_shortWindowSawtoothSignal hp a)

/-- The concrete class-centered carry energy is exactly the manuscript's
Dedekind collision energy. -/
theorem primeCarryEnergy_eq_dedekindCollisionEnergy
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) (hpodd : p ≠ 2) :
    (primeCarryEnergy hp : ℂ) = dedekindCollisionEnergy hp := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (NField.Alignment.CenteredCollisionSum.allLagModulus p 1) := by
    simpa [NField.Alignment.CenteredCollisionSum.allLagModulus] using
      (inferInstance : NeZero (p ^ 2))
  have hcast := congrArg (fun x : ℝ => (x : ℂ))
    (primeCarryEnergy_eq_shortWindow hp hpodd)
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_sum] at hcast
  calc
    (primeCarryEnergy hp : ℂ) =
        4 * ∑ a : UnitClass (p ^ 2),
          ((‖shortWindowSawtoothSignal hp a‖ ^ 2 : ℝ) : ℂ) := hcast
    _ = 4 * ∑ a : UnitClass (p ^ 2),
          shortWindowSawtoothSignal hp a * shortWindowSawtoothSignal hp a := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          exact shortWindow_normSquare_cast hp a
    _ = 4 * collisionDoubleSum (firstCollisionWindow hp) unitDedekindSum := by
          rw [shortWindow_complexSquareMass_eq_unitDedekindDoubleSum hp]
    _ = 4 * primeSquareCollisionDoubleSum hp := by
          rw [unitDedekindDoubleSum_eq_full hp hpodd]
    _ = dedekindCollisionEnergy hp :=
          (dedekindCollisionEnergy_eq_doubleSum hp).symm

end NField.Alignment.PrimeSquareSawtoothEnergy
