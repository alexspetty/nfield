/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TrueChannelPrimeLimits
import NField.Alignment.UnitFiberMeans
import NField.Alignment.ConductorFourCoefficient
import NField.Alignment.PeriodicBernoulliDistribution
import NField.Alignment.FiniteActivePrimeDecomposition
import NField.Alignment.GeneralNeutrality
import NField.Alignment.CenteredCollisionClosure

/-!
# The General Neutrality Theorem

## Coverage

The results prove neutrality for true prime channels and simultaneous
squarefree channels, including their cardinalities, raw means and harmonic
limits. The conductor-four silence and active-character decomposition are
formalized. Convergence below one remains open.

## Scope and assumptions

The channel formulas distinguish primes dividing the base from primes coprime
to it. The simultaneous-channel theorem requires squarefree `Q` and uses the
compatible classes modulo `lcm(m,Q)`. The harmonic limits use fixed
progressions. The conductor-four silence is for the stated decimal lag-one
table, not a claim for every base. Numerical ledgers retain finite
computational scope. Convergence below one remains open.
-/

namespace NField.Papers.GeneralNeutrality

open scoped BigOperators ComplexConjugate Topology
open Filter
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionTransform
open NField.Alignment.CenteredCollisionClosure
open NField.Alignment.NeutralityTheorem
open NField.Alignment.GeneralNeutrality

/-! ## The concrete finite table -/

/-- The direct collision deviation is the exact finite table throughout every
coprime progression. -/
theorem direct_finite_table_determination
    {b ell t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcop

/-- Concrete reflection on every unit representative. -/
theorem exact_reflection {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagTable b ell a +
      allLagTable b ell (allLagModulus b ell - a) = -1 :=
  allLagTable_reflection hb2 hell ha halt hcop

/-- Reflection fixes the raw mean of the unit table at `-1/2`. -/
theorem exact_grand_mean
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (Fintype.card (UnitClass (allLagModulus b ell)) : ℂ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b ell), allLagUnitTable b ell a =
      -1 / 2 :=
  allLagUnitTable_grand_mean hb2 hell

/-- Every natural representative fiber contains exactly `b^ell` entries. -/
theorem exact_reduction_fiber_cardinality {b ell u : ℕ}
    (hb2 : 2 ≤ b) (hu : u ∈ reducedResidues b) :
    (tableFiber b ell u).card = b ^ ell :=
  tableFiber_card hb2 hu

/-- Every natural coarse fiber has exact centered sum zero. -/
theorem exact_natural_fiber_centering
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
        centeredCollisionTransform b ell a = 0 :=
  natural_centering_fiber_sum_zero u

/-- The naturally centered table has total mass zero. -/
theorem exact_centered_total_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a : UnitClass (allLagModulus b ell),
      centeredCollisionTransform b ell a = 0 :=
  centeredCollisionTransform_sum_zero

/-- Reflected coarse fibers have exact means summing to `-1`. -/
theorem exact_natural_fiber_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  natural_fiber_mean_reflection hb2 hell u

/-- Natural centering turns the concrete reflection law into oddness. -/
theorem exact_centered_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTransform b ell (-a) =
      -centeredCollisionTransform b ell a :=
  natural_centered_reflection hb2 hell a

/-! ## Internal residue slices -/

/-- The table modulus is at least two in every manuscript case. -/
theorem table_modulus_ge_two {b ell : ℕ} (hb2 : 2 ≤ b) :
    2 ≤ allLagModulus b ell := by
  unfold allLagModulus
  exact hb2.trans (Nat.le_pow (by omega))

/-- Every odd prime has one unique reflection-fixed internal label. -/
theorem internal_fixed_label_exists_unique
    {b ell q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    ∃! j : ZMod q, 2 * j = (allLagModulus b ell : ZMod q) :=
  oddPrime_internal_fixed_label_existsUnique hq hq2

/-- Reflection sends the internal slice labeled `j` to the slice labeled
`m-j`. -/
theorem internal_slice_reflection
    {b ell q : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (j : ZMod q) (a : UnitClass (allLagModulus b ell))
    (ha : internalResidue (q := q) a = j) :
    internalResidue (q := q) (-a) =
      (allLagModulus b ell : ZMod q) - j :=
  internalResidue_reflected (table_modulus_ge_two hb2) j a ha

/-- The fixed internal slice has the exact raw total and centered total stated
in the manuscript. -/
theorem internal_fixed_slice_neutrality
    {b ell q : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (j : ZMod q)
    (hfixed : 2 * j = (allLagModulus b ell : ZMod q)) :
    (2 * ∑ a : CoordinateSlice
        (internalResidue (m := allLagModulus b ell) (q := q)) j,
        allLagUnitTable b ell a =
      -(Fintype.card (CoordinateSlice
        (internalResidue (m := allLagModulus b ell) (q := q)) j) : ℂ)) ∧
    (∑ a : CoordinateSlice
        (internalResidue (m := allLagModulus b ell) (q := q)) j,
        centeredCollisionTransform b ell a) = 0 := by
  have hpreserve : ∀ a : UnitClass (allLagModulus b ell),
      internalResidue (q := q) a = j →
        internalResidue (q := q) (-a) = j := by
    intro a ha
    exact internalResidue_fixed_preserved
      (table_modulus_ge_two hb2) j hfixed a ha
  have hraw := coordinateSlices_raw_pair
    (internalResidue (m := allLagModulus b ell) (q := q)) j j
    (allLagUnitTable b ell) (fun a => -a)
    (by intro a; simp) hpreserve hpreserve
    (allLagUnitTable_reflection hb2 hell)
  constructor
  · simpa [two_mul] using hraw.2
  · apply coordinateSlice_centered_sum_zero
      (internalResidue (m := allLagModulus b ell) (q := q)) j
      (centeredCollisionTransform b ell) (fun a => -a)
    · intro a
      simp
    · exact hpreserve
    · exact centeredCollisionTransform_odd hb2 hell

/-- A nonempty fixed internal slice has raw mean `-1/2`. -/
theorem internal_fixed_slice_raw_mean
    {b ell q : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (j : ZMod q)
    (hfixed : 2 * j = (allLagModulus b ell : ZMod q))
    [Nonempty (CoordinateSlice
      (internalResidue (m := allLagModulus b ell) (q := q)) j)] :
    (Fintype.card (CoordinateSlice
      (internalResidue (m := allLagModulus b ell) (q := q)) j) : ℂ)⁻¹ *
      ∑ a : CoordinateSlice
        (internalResidue (m := allLagModulus b ell) (q := q)) j,
        allLagUnitTable b ell a = -1 / 2 := by
  apply coordinateSlice_raw_mean_eq_negative_half
    (internalResidue (m := allLagModulus b ell) (q := q)) j
    (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · intro a ha
    exact internalResidue_fixed_preserved
      (table_modulus_ge_two hb2) j hfixed a ha
  · exact allLagUnitTable_reflection hb2 hell

/-- The representative and quotient coordinates reconstruct every true
residue. -/
theorem quotient_residue_correction (m t a q : ℕ) :
    ((m * t + a : ℕ) : ZMod q) =
      (a : ZMod q) + (m : ZMod q) * (t : ZMod q) := by
  push_cast
  ring

/-- The table modulus is coprime to every prime that does not divide the
base. -/
theorem table_modulus_coprime_prime {b ell q : ℕ}
    (hq : Nat.Prime q) (hqb : ¬q ∣ b) :
    Nat.Coprime (allLagModulus b ell) q := by
  have hbq : Nat.Coprime b q :=
    (hq.coprime_iff_not_dvd.mpr hqb).symm
  unfold allLagModulus
  exact Nat.Coprime.pow_left (ell + 1) hbq

/-- The base divides its complete table modulus. -/
theorem base_dvd_table_modulus {b ell : ℕ} :
    b ∣ allLagModulus b ell := by
  unfold allLagModulus
  exact dvd_pow_self b (by omega)

/-- A true channel for a prime not dividing the base is independently
centered-neutral. -/
theorem prime_channel_coprime_neutral
    {b ell q : ℕ} [NeZero b] [NeZero q]
    [NeZero (allLagModulus b ell)]
    (_hb2 : 2 ≤ b) (_hell : 1 ≤ ell)
    (hq : Nat.Prime q) (hqb : ¬q ∣ b) (r : UnitClass q) :
    ∑ A : GeneralCarryChannel
        (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) r,
      centeredSignal (coarseUnitReduction b ell)
        (allLagUnitTable b ell)
        ((generalCrtUnitEquiv
          (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) A.1).1) = 0 :=
  generalCarryChannel_centered_sum_zero
    (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) r
    (coarseUnitReduction b ell) (allLagUnitTable b ell)
    (coarseUnitReduction_surjective b ell)

/-- Its exact size is `phi(b^(ell+1))`. -/
theorem prime_channel_coprime_card
    {b ell q : ℕ} [NeZero b] [NeZero q]
    [NeZero (allLagModulus b ell)]
    (hq : Nat.Prime q) (hqb : ¬q ∣ b) (r : UnitClass q) :
    Fintype.card
      (GeneralCarryChannel
        (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) r) =
        (allLagModulus b ell).totient :=
  generalCarryChannel_card
    (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) r

/-- Its uncentered table mean is exactly `-1/2`. -/
theorem prime_channel_coprime_raw_mean
    {b ell q : ℕ} [NeZero b] [NeZero q]
    [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hq : Nat.Prime q) (hqb : ¬q ∣ b) (r : UnitClass q) :
    (Fintype.card
      (GeneralCarryChannel
        (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) r) : ℂ)⁻¹ *
      ∑ A : GeneralCarryChannel
          (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) r,
        allLagUnitTable b ell
          ((generalCrtUnitEquiv
            (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) A.1).1) =
          -1 / 2 := by
  apply generalCarryChannel_raw_mean_eq_negative_half
    (table_modulus_coprime_prime (b := b) (ell := ell) hq hqb) r
    (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · exact allLagUnitTable_reflection hb2 hell

/-- A true channel for a prime dividing the base is a compatible selected
union of complete coarse fibers and is independently neutral. -/
theorem prime_channel_dividing_neutral
    {b ell q : ℕ} [NeZero b] [NeZero q]
    [NeZero (allLagModulus b ell)]
    (_hb2 : 2 ≤ b) (_hell : 1 ≤ ell)
    (_hq : Nat.Prime q) (hqb : q ∣ b) (r : UnitClass q) :
    ∑ a : CompatibleChannel hqb
        (base_dvd_table_modulus (b := b) (ell := ell)) r,
      centeredSignal
        (unitReduction (base_dvd_table_modulus (b := b) (ell := ell)))
        (allLagUnitTable b ell) a.1 = 0 :=
  compatibleChannel_centered_sum_zero hqb
    (base_dvd_table_modulus (b := b) (ell := ell)) r
    (allLagUnitTable b ell)

/-- Its exact size is `phi(m)/(q-1)`. -/
theorem prime_channel_dividing_card
    {b ell q : ℕ} [NeZero b] [NeZero q]
    [NeZero (allLagModulus b ell)]
    (hq : Nat.Prime q) (hqb : q ∣ b) (r : UnitClass q) :
    Fintype.card (CompatibleChannel hqb
      (base_dvd_table_modulus (b := b) (ell := ell)) r) =
      (allLagModulus b ell).totient / (q - 1) := by
  simpa [Nat.totient_prime hq] using
    compatibleChannel_card hqb
      (base_dvd_table_modulus (b := b) (ell := ell)) r

/-- The generalized-CRT compatible simultaneous channel is independently
neutral for every divisor `d` of the base. -/
theorem simultaneous_compatible_neutral
    {b ell d : ℕ} [NeZero b] [NeZero d]
    [NeZero (allLagModulus b ell)]
    (hdb : d ∣ b) (r : UnitClass d) :
    ∑ a : CompatibleChannel hdb
        (base_dvd_table_modulus (b := b) (ell := ell)) r,
      centeredSignal
        (unitReduction (base_dvd_table_modulus (b := b) (ell := ell)))
        (allLagUnitTable b ell) a.1 = 0 :=
  compatibleChannel_centered_sum_zero hdb
    (base_dvd_table_modulus (b := b) (ell := ell)) r
    (allLagUnitTable b ell)

/-- Its exact compatible-channel size is `phi(m)/phi(d)`. -/
theorem simultaneous_compatible_card
    {b ell d : ℕ} [NeZero b] [NeZero d]
    [NeZero (allLagModulus b ell)]
    (hdb : d ∣ b) (r : UnitClass d) :
    Fintype.card (CompatibleChannel hdb
      (base_dvd_table_modulus (b := b) (ell := ell)) r) =
      (allLagModulus b ell).totient / d.totient :=
  compatibleChannel_card hdb
    (base_dvd_table_modulus (b := b) (ell := ell)) r

/-- Simultaneous coprime channels contain the complete table and are neutral. -/
theorem simultaneous_coprime_neutral
    {b ell Q : ℕ} [NeZero b] [NeZero Q]
    [NeZero (allLagModulus b ell)]
    (hcop : Nat.Coprime (allLagModulus b ell) Q)
    (r : UnitClass Q) :
    ∑ A : GeneralCarryChannel hcop r,
      centeredSignal (coarseUnitReduction b ell)
        (allLagUnitTable b ell)
        ((generalCrtUnitEquiv hcop A.1).1) = 0 :=
  generalCarryChannel_centered_sum_zero hcop r
    (coarseUnitReduction b ell) (allLagUnitTable b ell)
    (coarseUnitReduction_surjective b ell)

/-- A squarefree channel in units modulo `lcm(m,Q)` is independently
centered-neutral. -/
theorem simultaneous_squarefree_neutral
    {b ell Q : ℕ} [NeZero b] [NeZero Q]
    [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) Q)]
    [NeZero (Nat.gcd (allLagModulus b ell) Q)]
    (hQ : Squarefree Q) (r : UnitClass Q) :
    (∑ A : LcmCarryChannel (m := allLagModulus b ell) (Q := Q) r,
      centeredSignal (coarseUnitReduction b ell) (allLagUnitTable b ell)
        (unitReduction (Nat.dvd_lcm_left (allLagModulus b ell) Q) A.1)) = 0 :=
  simultaneous_squarefree_channel_neutral hQ r

/-- The simultaneous channel has both exact totient-quotient cardinalities
from the manuscript. -/
theorem simultaneous_squarefree_card
    {b ell Q : ℕ} [NeZero b] [NeZero Q]
    [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) Q)]
    [NeZero (Nat.gcd (allLagModulus b ell) Q)]
    (hQ : Squarefree Q) (r : UnitClass Q) :
    Fintype.card
        (LcmCarryChannel (m := allLagModulus b ell) (Q := Q) r) =
        (allLagModulus b ell).totient / (Nat.gcd Q b).totient ∧
      Fintype.card
        (LcmCarryChannel (m := allLagModulus b ell) (Q := Q) r) =
        (Nat.lcm (allLagModulus b ell) Q).totient / Q.totient := by
  simpa [squarefree_table_gcd hQ, Nat.gcd_comm] using
    (lcmCarryChannel_card
      (m := allLagModulus b ell) (Q := Q) r)

/-- Coprimality with the base is equivalent to coprimality with the complete
table modulus in the direction needed by the channel theorem. -/
theorem table_modulus_coprime_of_base_coprime
    {b ell Q : ℕ} (hcop : Nat.Coprime Q b) :
    Nat.Coprime (allLagModulus b ell) Q := by
  unfold allLagModulus
  exact Nat.Coprime.pow_left (ell + 1) hcop.symm

/-- When `Q` is coprime to the base, the simultaneous channel has raw mean
`-1/2`. -/
theorem simultaneous_coprime_raw_mean
    {b ell Q : ℕ} [NeZero b] [NeZero Q]
    [NeZero (allLagModulus b ell)]
    [NeZero (Nat.lcm (allLagModulus b ell) Q)]
    [NeZero (Nat.gcd (allLagModulus b ell) Q)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hcop : Nat.Coprime Q b) (r : UnitClass Q) :
    (Fintype.card
        (LcmCarryChannel (m := allLagModulus b ell) (Q := Q) r) : ℂ)⁻¹ *
      ∑ A : LcmCarryChannel (m := allLagModulus b ell) (Q := Q) r,
        allLagUnitTable b ell
          (unitReduction (Nat.dvd_lcm_left (allLagModulus b ell) Q) A.1) =
      -1 / 2 := by
  apply lcmCarryChannel_raw_mean_eq_negative_half
    (table_modulus_coprime_of_base_coprime hcop) r
    (allLagUnitTable b ell) (fun a => -a)
  · intro a
    simp
  · exact allLagUnitTable_reflection hb2 hell

/-- Even character channels vanish after compatible centering. -/
theorem even_character_gate
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    {β : Type*} [Fintype β] [DecidableEq β]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ρ : UnitClass (allLagModulus b ell) → β)
    (rβ : β → β) (hβ : Function.Involutive rβ)
    (hcompat : ∀ a, ρ (-a) = rβ (ρ a))
    (hsurj : Function.Surjective ρ)
    (χ : Character (allLagModulus b ell))
    (heven : χ (-1 : ZMod (allLagModulus b ell)) = 1) :
    collisionCoefficient
      (centeredSignal ρ (allLagUnitTable b ell)) χ = 0 :=
  centered_allLag_even_character_zero hb2 hell ρ rβ hβ
    hcompat hsurj χ heven

/-- Characters descending to the base vanish after fiber centering. -/
theorem base_factored_character_gate
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    {β : Type*} [Fintype β] [DecidableEq β]
    (ρ : UnitClass (allLagModulus b ell) → β)
    (hsurj : Function.Surjective ρ)
    (ψ : β → ℂ) (χ : Character (allLagModulus b ell))
    (hfactor : ∀ a, χ a.val = ψ (ρ a)) :
    collisionCoefficient
      (centeredSignal ρ (allLagUnitTable b ell)) χ = 0 :=
  centered_allLag_factored_character_zero ρ hsurj ψ χ hfactor

/-- The decimal lag-one conductor-four numerator vanishes exactly. -/
theorem conductor_four_silence : conductorFourCenteredNumerator = 0 :=
  conductorFourCenteredNumerator_eq_zero

/-- The conductor-four sign is not a function of reduction modulo ten. -/
theorem conductor_four_does_not_descend :
    1 % 10 = 11 % 10 ∧ chiFourSign 1 ≠ chiFourSign 11 :=
  conductorFour_not_base_factored

/-- Exact finite character decomposition for every weighted packet. -/
theorem finite_character_decomposition
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (F : UnitClass q → ℂ) (residue : ι → UnitClass q)
    (weight : ι → ℂ) :
    ∑ i, F (residue i) * weight i =
      ∑ χ : Character q, collisionCoefficient F χ *
        ∑ i, χ (residue i).val * weight i :=
  exact_finite_character_decomposition F residue weight

/-- Once the classwise Mertens residual limits are supplied, exact channel
neutrality cancels the common logarithmic term and leaves a finite limit. -/
theorem channel_convergence_from_class_residuals
    {m Q : ℕ} [NeZero m] [NeZero Q]
    [NeZero (Nat.lcm m Q)]
    {iota : Type*} {lfilter : Filter iota}
    (r : UnitClass Q)
    (f : LcmCarryChannel (m := m) (Q := Q) r → ℝ)
    (A : iota → LcmCarryChannel (m := m) (Q := Q) r → ℝ)
    (common : iota → ℝ)
    (K : LcmCarryChannel (m := m) (Q := Q) r → ℝ)
    (hzero : ∑ a, f a = 0)
    (hclass : ∀ a,
      Tendsto (fun x => A x a - common x) lfilter (nhds (K a))) :
    Tendsto (fun x => ∑ a, f a * A x a) lfilter
      (nhds (∑ a, f a * K a)) :=
  centered_progression_residual_limit f A common K hzero hclass

#check direct_finite_table_determination
#check exact_reflection
#check exact_grand_mean
#check exact_reduction_fiber_cardinality
#check exact_natural_fiber_centering
#check exact_centered_total_zero
#check exact_natural_fiber_mean_reflection
#check exact_centered_reflection
#check internal_fixed_label_exists_unique
#check internal_slice_reflection
#check internal_fixed_slice_neutrality
#check internal_fixed_slice_raw_mean
#check quotient_residue_correction
#check prime_channel_coprime_neutral
#check prime_channel_coprime_card
#check prime_channel_coprime_raw_mean
#check prime_channel_dividing_neutral
#check prime_channel_dividing_card
#check simultaneous_compatible_neutral
#check simultaneous_compatible_card
#check simultaneous_coprime_neutral
#check simultaneous_squarefree_neutral
#check simultaneous_squarefree_card
#check simultaneous_coprime_raw_mean
#check even_character_gate
#check base_factored_character_gate
#check conductor_four_silence
#check conductor_four_does_not_descend
#check finite_character_decomposition
#check channel_convergence_from_class_residuals

end NField.Papers.GeneralNeutrality

/-! Additional source-owned analytic and conductor-four conclusions. -/

#check NField.Alignment.ProgressionMertens.real_cutoff_mertens_progression
#check NField.Alignment.CollisionPrimeLimits.squarefree_real_true_channel_limit
#check NField.Alignment.ConductorFourLifts.signedConductorFourLift_gcd
#check NField.Alignment.ConductorFourHundred.signedUnitSawtoothSum_sub_lifts
#check NField.Alignment.ConductorFourHundred.signedUnitSawtoothSum_support
#check NField.Alignment.ConductorFourFloors.unitFloorSum_eq_linear_sub_sawtooth
#check NField.Alignment.ConductorFourFloors.decimal_diagonal_floor_cancellation
#check NField.Alignment.ConductorFourCoefficient.literal_decimal_conductor_four_coefficient
#check NField.Alignment.PeriodicBernoulliDistribution.periodicSawtooth_distribution
#check NField.Alignment.FiniteActivePrimeDecomposition.finite_prime_active_decomposition
