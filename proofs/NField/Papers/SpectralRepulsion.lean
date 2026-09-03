/-
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralRepulsion
import NField.Alignment.CenteredCollisionClosure
import NField.Papers.DoubleTransversality

/-!
# The Spectral Repulsion

Reader-facing theorem map for the Lean companion to
`papers/spectral_repulsion.tex`.

## Checked here

* The concrete all-lag collision table, finite determination, raw and centered
  reflection, reflected fiber means, zero fiber sums, zero total, and the even
  and base-factored character gates are inherited and exported for this title.
* Its zero extension from the unit group to the full residue ring agrees on
  units, vanishes on nonunits, remains odd, and retains zero total.
* The full odd-sector overlap factors exactly into sector occupancy and the
  normalized overlap inside the eligible sector.
* Centered probability masses have zero total.  Lean proves the exact
  one-point and two-point moments of the full finite permutation group, then
  derives mean one and the manuscript's exact variance normalization for the
  uncentered overlap.  The one-label case is pointwise equal to one.
* The additive self-convolution of any finite odd real signal is even, has
  zero total when the signal does, and takes the negative square energy at the
  reflection shift.  Every other shift therefore supplies the exact positive
  compensation.
* On `ZMod N`, the additive transform of an odd real signal is purely
  imaginary.  Its self-convolution transform is its square, hence the negative
  norm square at every frequency.
* Every finite family of reflected additive pairs contributes a negative sum
  of squares and is therefore nonpositive.

## Boundary

The primitive-character conductor classification, the count of eligible odd
primitive characters, and the fact that no eligible character is
self-conjugate are not separately encoded here.  The sector theorem starts
from the resulting full-to-eligible mass relation.

The manuscript's underlap and entropy rows remain finite nfield evidence and
are not recomputed by Lean.

The additive theorem is proved for an arbitrary odd real signal on `ZMod N`
and specialized here to the zero-extended centered collision table.  The
reflected-pair identity is likewise specialized to arbitrary finite families
of residues satisfying `q i = -p i`.  The finite indexing type abstracts the
ordered prime representations; their elementary congruence supplies that
displayed residue relation in the manuscript.  No asymptotic prime statement
or zero-location claim is formalized or asserted.  No manuscript contradiction
appeared in the formalized layer, and no unchecked declaration is used.
-/

namespace NField.Papers.SpectralRepulsion

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.DoubleTransversality
open NField.Alignment.SpectralRepulsion
open NField.Papers.DoubleTransversality

/-! ## Concrete collision-table structure -/

/-- The direct collision deviation is exactly the endpoint-corrected finite
table on every eligible residue progression. -/
theorem exact_finite_determination
    {b ell t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a :=
  NField.Alignment.CenteredCollisionClosure.directAllLagDeviation_eq_allLagTable
    hb2 hell ha halt hcop

/-- The raw finite collision table has exact reflected sum `-1`. -/
theorem raw_collision_table_reflection
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    allLagUnitTable b ell a + allLagUnitTable b ell (-a) = -1 :=
  NField.Papers.DoubleTransversality.exact_raw_reflection hb2 hell a

/-- The means on reflected reduction fibers sum exactly to `-1`. -/
theorem collision_fiber_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 :=
  NField.Alignment.CenteredCollisionClosure.natural_fiber_mean_reflection
    hb2 hell u

/-- Every reduction fiber of the concrete centered table has zero sum. -/
theorem centered_collision_fiber_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
      centeredCollisionTable b ell a = 0 := by
  simpa [centeredCollisionTable,
    NField.Alignment.CollisionTransform.centeredCollisionTransform] using
    (NField.Alignment.CenteredCollisionClosure.natural_centering_fiber_sum_zero
      (b := b) (ell := ell) u)

/-- The manuscript's centered collision table has exactly zero total. -/
theorem centered_collision_table_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a, centeredCollisionTable b ell a = 0 :=
  NField.Papers.DoubleTransversality.centered_collision_table_sum_zero

/-- Fiber centering turns the concrete raw reflection law into exact oddness. -/
theorem centered_collision_table_odd
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTable b ell (-a) = -centeredCollisionTable b ell a :=
  NField.Papers.DoubleTransversality.exact_centered_reflection hb2 hell a

/-- Every even character channel of the centered collision table vanishes. -/
theorem even_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell))
    (heven : χ (-1 : ZMod (allLagModulus b ell)) = 1) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  NField.Papers.DoubleTransversality.even_character_gate hb2 hell χ heven

/-- Every character factored through the coarse base reduction also vanishes. -/
theorem base_factored_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (ψ : UnitClass b → ℂ) (χ : Character (allLagModulus b ell))
    (hfactor : ∀ a, χ a.val = ψ (coarseUnitReduction b ell a)) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  NField.Papers.DoubleTransversality.base_factored_character_gate ψ χ hfactor

/-- The manuscript's centered table, extended by zero to every residue. -/
noncomputable def centered_collision_zero_extension
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (a : ZMod (allLagModulus b ell)) : ℝ :=
  unitZeroExtension (fun u => (centeredCollisionTable b ell u).re) a

/-- The zero extension agrees with the centered table on units. -/
theorem centered_collision_zero_extension_unit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (a : UnitClass (allLagModulus b ell)) :
    centered_collision_zero_extension (b := b) (ell := ell) a.val =
      (centeredCollisionTable b ell a).re :=
  unitZeroExtension_unit (fun u => (centeredCollisionTable b ell u).re) a

/-- The zero extension vanishes on nonunit residues. -/
theorem centered_collision_zero_extension_nonunit
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (a : ZMod (allLagModulus b ell)) (ha : ¬IsUnit a) :
    centered_collision_zero_extension (b := b) (ell := ell) a = 0 :=
  unitZeroExtension_nonunit
    (fun u => (centeredCollisionTable b ell u).re) a ha

/-- The concrete zero extension remains odd. -/
theorem centered_collision_zero_extension_odd
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : ZMod (allLagModulus b ell)) :
    centered_collision_zero_extension (b := b) (ell := ell) (-a) =
      -centered_collision_zero_extension (b := b) (ell := ell) a := by
  apply unitZeroExtension_odd
  intro u
  have h := congrArg Complex.re (exact_centered_reflection hb2 hell u)
  simpa using h

/-- The concrete zero extension retains exact total zero. -/
theorem centered_collision_zero_extension_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a, centered_collision_zero_extension
      (b := b) (ell := ell) a = 0 := by
  rw [show (∑ a, centered_collision_zero_extension
      (b := b) (ell := ell) a) =
      ∑ u, (centeredCollisionTable b ell u).re by
    exact sum_unitZeroExtension
      (fun u => (centeredCollisionTable b ell u).re)]
  have h := congrArg Complex.re
    (centered_collision_table_sum_zero (b := b) (ell := ell))
  simpa using h

/-! ## Sector and relabeling laws -/

/-- Exact factorization of the full odd-sector overlap. -/
theorem exact_sector_factorization
    {α : Type*} [Fintype α]
    (p q qFull : α → ℝ) (η primitiveCount oddCount : ℝ)
    (hq : ∀ i, qFull i = η * q i)
    (hprimitive : primitiveCount ≠ 0) :
    oddCount * sectorOverlap p qFull =
      (oddCount / primitiveCount) * η *
        (primitiveCount * sectorOverlap p q) :=
  sector_factorization p q qFull η primitiveCount oddCount hq hprimitive

/-- Centered relabeling overlap has mean zero under its exact first moment. -/
theorem centered_relabeling_mean
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hfirst : ∀ i,
      uniformAverage (fun ω => centeredMass y (image ω i)) = 0) :
    uniformAverage (centeredRelabelingStatistic x y image) = 0 :=
  centered_relabeling_mean_zero x y image hfirst

/-- The manuscript's uncentered overlap has exact mean one. -/
theorem exact_relabeling_mean_one
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hx : ∑ i, x i = 1)
    (hmass : ∀ ω, ∑ i, y (image ω i) = 1)
    (hfirst : ∀ i,
      uniformAverage (fun ω => centeredMass y (image ω i)) = 0) :
    uniformAverage (relabelingStatistic x y image) = 1 :=
  relabelingStatistic_mean_one x y image hx hmass hfirst

/-- Exact variance forced by the uniform first and two-point moment laws. -/
theorem exact_relabeling_variance
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hmass : ∀ ω, ∑ i, y (image ω i) = 1)
    (hk : 1 < Fintype.card ι)
    (hfirst : ∀ i,
      uniformAverage (fun ω => centeredMass y (image ω i)) = 0)
    (hsecond : ∀ i j,
      uniformAverage (fun ω =>
        centeredMass y (image ω i) * centeredMass y (image ω j)) =
        if i = j then
          (Fintype.card ι : ℝ)⁻¹ * ∑ r, (centeredMass y r) ^ 2
        else
          -((Fintype.card ι : ℝ) *
            (Fintype.card ι - 1 : ℝ))⁻¹ *
              ∑ r, (centeredMass y r) ^ 2) :
    uniformVariance (relabelingStatistic x y image) =
      (Fintype.card ι : ℝ) ^ 2 /
          (Fintype.card ι - 1 : ℝ) *
        (∑ r, (centeredMass x r) ^ 2) *
        (∑ r, (centeredMass y r) ^ 2) :=
  relabelingStatistic_variance x y image hx hy hmass hk hfirst hsecond

/-- Uniform permutation of the labels gives exact mean one. -/
theorem exact_uniform_permutation_mean_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1) :
    uniformAverage (fun π : Equiv.Perm ι =>
      relabelingStatistic x y (fun σ i => σ i) π) = 1 :=
  permutation_relabeling_mean_one x y hx hy

/-- Uniform permutation of more than one label gives the exact manuscript
variance. -/
theorem exact_uniform_permutation_variance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hk : 1 < Fintype.card ι) :
    uniformVariance (fun π : Equiv.Perm ι =>
      relabelingStatistic x y (fun σ i => σ i) π) =
      (Fintype.card ι : ℝ) ^ 2 /
          (Fintype.card ι - 1 : ℝ) *
        (∑ r, (centeredMass x r) ^ 2) *
        (∑ r, (centeredMass y r) ^ 2) :=
  permutation_relabeling_variance x y hx hy hk

/-- With one label, every permutation gives overlap one. -/
theorem exact_uniform_permutation_one_label
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hk : Fintype.card ι = 1) (π : Equiv.Perm ι) :
    relabelingStatistic x y (fun σ i => σ i) π = 1 :=
  permutation_relabeling_eq_one_of_card_one x y hx hy hk π

/-! ## Additive reflection and spectral sign -/

/-- The concrete centered collision self-convolution is even. -/
theorem centered_collision_additive_even
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (t : ZMod (allLagModulus b ell)) :
    additiveSelfConvolution
        (centered_collision_zero_extension (b := b) (ell := ell)) (-t) =
      additiveSelfConvolution
        (centered_collision_zero_extension (b := b) (ell := ell)) t :=
  additiveSelfConvolution_even _
    (centered_collision_zero_extension_odd hb2 hell) t

/-- The concrete zero-extended collision table has the exact negative
reflection well. -/
theorem centered_collision_additive_reflection_well
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    additiveSelfConvolution
        (centered_collision_zero_extension (b := b) (ell := ell)) 0 =
      -(∑ a, (centered_collision_zero_extension
        (b := b) (ell := ell) a) ^ 2) :=
  additiveSelfConvolution_zero _
    (centered_collision_zero_extension_odd hb2 hell)

/-- The concrete zero-extended collision table has zero-total
self-convolution. -/
theorem centered_collision_additive_total_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ t, additiveSelfConvolution
      (centered_collision_zero_extension (b := b) (ell := ell)) t = 0 :=
  additiveSelfConvolution_total_zero _
    centered_collision_zero_extension_sum_zero

/-- The concrete nonzero shifts exactly compensate for the reflection well. -/
theorem centered_collision_additive_compensation
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    ∑ t ∈ Finset.univ.erase 0,
        additiveSelfConvolution
          (centered_collision_zero_extension (b := b) (ell := ell)) t =
      ∑ a, (centered_collision_zero_extension
        (b := b) (ell := ell) a) ^ 2 :=
  additiveSelfConvolution_nonzero_compensation _
    (centered_collision_zero_extension_odd hb2 hell)
    centered_collision_zero_extension_sum_zero

/-- The additive transform of the concrete self-convolution is the square of
the transform of the centered table. -/
theorem centered_collision_additive_transform_square
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (j : ZMod (allLagModulus b ell)) :
    realAdditiveTransform
        (additiveSelfConvolution
          (centered_collision_zero_extension (b := b) (ell := ell))) j =
      (realAdditiveTransform
        (centered_collision_zero_extension (b := b) (ell := ell)) j) ^ 2 :=
  additiveSelfConvolution_transform _ j

/-- The concrete additive spectrum is a negative norm square at every
frequency. -/
theorem centered_collision_additive_spectrum_nonpositive
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (j : ZMod (allLagModulus b ell)) :
    (realAdditiveTransform
      (centered_collision_zero_extension (b := b) (ell := ell)) j) ^ 2 =
        -(Complex.normSq (realAdditiveTransform
          (centered_collision_zero_extension (b := b) (ell := ell)) j) : ℂ) ∧
      ((realAdditiveTransform
        (centered_collision_zero_extension (b := b) (ell := ell)) j) ^ 2).re
          ≤ 0 :=
  additive_reflection_spectrum_nonpositive _
    (centered_collision_zero_extension_odd hb2 hell) j

/-- Every finite family of reflected residues satisfies the manuscript's
negative-square identity for the concrete collision weights. -/
theorem centered_collision_reflected_pair_identity
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {ι : Type*} [Fintype ι]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (p q : ι → ZMod (allLagModulus b ell)) (hpq : ∀ i, q i = -p i) :
    (∑ i, centered_collision_zero_extension (p i) *
      centered_collision_zero_extension (q i)) =
      -(∑ i, (centered_collision_zero_extension (p i)) ^ 2) :=
  reflected_pair_sum _
    (centered_collision_zero_extension_odd hb2 hell) p q hpq

/-- The reflection shift is the exact negative square-energy well. -/
theorem additive_reflection_well
    {G : Type*} [Fintype G] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a) :
    additiveSelfConvolution f 0 = -(∑ a, (f a) ^ 2) :=
  additiveSelfConvolution_zero f hodd

/-- All nonzero shifts exactly compensate for the reflection well. -/
theorem exact_nonzero_shift_compensation
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a)
    (hsum : ∑ a, f a = 0) :
    ∑ t ∈ Finset.univ.erase 0, additiveSelfConvolution f t =
      ∑ a, (f a) ^ 2 :=
  additiveSelfConvolution_nonzero_compensation f hodd hsum

/-- The additive spectrum is the negative norm square at every frequency. -/
theorem additive_spectrum_is_nonpositive
    {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (j : ZMod N) :
    (realAdditiveTransform f j) ^ 2 =
        -(Complex.normSq (realAdditiveTransform f j) : ℂ) ∧
      ((realAdditiveTransform f j) ^ 2).re ≤ 0 :=
  additive_reflection_spectrum_nonpositive f hodd j

/-- A finite reflected-pair ledger is always nonpositive. -/
theorem reflected_pair_obstruction
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a)
    (p q : ι → G) (hpq : ∀ i, q i = -p i) :
    (∑ i, f (p i) * f (q i)) ≤ 0 :=
  reflected_pair_sum_nonpositive f hodd p q hpq

#check exact_finite_determination
#check raw_collision_table_reflection
#check collision_fiber_mean_reflection
#check centered_collision_fiber_sum_zero
#check centered_collision_table_sum_zero
#check centered_collision_table_odd
#check even_character_gate
#check base_factored_character_gate
#check centered_collision_zero_extension_unit
#check centered_collision_zero_extension_nonunit
#check centered_collision_zero_extension_odd
#check centered_collision_zero_extension_sum_zero
#check exact_sector_factorization
#check centered_relabeling_mean
#check exact_relabeling_mean_one
#check exact_relabeling_variance
#check exact_uniform_permutation_mean_one
#check exact_uniform_permutation_variance
#check exact_uniform_permutation_one_label
#check centered_collision_additive_even
#check centered_collision_additive_reflection_well
#check centered_collision_additive_total_zero
#check centered_collision_additive_compensation
#check centered_collision_additive_transform_square
#check centered_collision_additive_spectrum_nonpositive
#check centered_collision_reflected_pair_identity
#check additive_reflection_well
#check exact_nonzero_shift_compensation
#check additive_spectrum_is_nonpositive
#check reflected_pair_obstruction

end NField.Papers.SpectralRepulsion
