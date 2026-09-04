/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CubicEnergyCharacterMoment
import NField.Alignment.PrimeThresholdEnergyNormalization
import NField.Alignment.PrimitiveFloorTransform
import NField.Alignment.SawtoothCharacterExpansion

/-!
# The Cubic Law for Digit-Collision Energy

Reader-facing theorem map for the Lean companion to
`papers/the_cubic_law_for_digit_collision_energy.tex`.

## Fully proved cubic theorem

* The centered sawtooth is odd, its character transform is the generalized
  Bernoulli sum, and primitive carry transforms factor through their signed
  finite boundary.
* The concrete prime-square lag-one boundary is assembled from the first
  digit window.  Every odd character has the exact phase-sensitive flux
  `-2 * chi(p+1) * shortWindowSum`, and the squared magnitude is exactly four
  times the short-window mass.
* Every nonprincipal odd character lifted from the prime level has zero short
  window and zero lag-one boundary flux.
* The actual centered lag-one collision table is reflection-odd, has zero
  total mass, admits only primitive odd active channels at a prime base, and
  satisfies finite Parseval.
* The classical Dedekind sum is defined directly from the centered sawtooth.
  Negation, inversion, common-unit ratio cancellation, the zero sum over all
  unit arguments, and the exact ratio-one value are proved.
* The collision weight is removed exactly by finite reindexing into a
  weight-free double sum.  The diagonal and off-diagonal parts split exactly,
  and the diagonal has the manuscript's closed value.
* Reduction from the prime-square first window to the prime-level unit group
  is an explicit equivalence.  It proves that the complete collision-weighted
  lower-modulus Dedekind correction is exactly zero.
* The carry-table column law and threshold normalization are proved from the
  floor-jump definitions.  The concrete carry energy is then identified
  exactly with the Dedekind collision energy.
* GCD reduction gives the floor-weighted primitive-ratio triangle.
  Rademacher's three-term relation is proved from finite sawtooth sums and
  yields the exact four-way off-diagonal decomposition.
* The coprime Euler mass is proved by an exact Calkin--Wilf telescoping law,
  including a quantitative frontier estimate.
* The Dedekind first moment is proved by finite Fourier inversion.  Finite Abel
  summation gives the surviving smaller-modulus remainder bound, while the
  larger-modulus remainder cancels exactly.
* The diagonal is within `p²` of its one-third cubic pole.  The off-diagonal
  main pole is within `6 p² H_p²` of its two-thirds cubic pole.  The remaining
  terms are bounded explicitly.
* The primitive odd Bernoulli special value is proved from Mathlib's
  analytically continued Dirichlet `L`-function at `s = 1`.  Character
  inversion then gives the exact `L(1)`-weighted window moment.
* The spectral window diagonal and off-diagonal split exactly and obey the
  explicit one-third and two-thirds pole estimates.
* Consequently, for every odd prime `p`, the concrete carry energy satisfies
  `|E_p - p³| ≤ 24 p² H_p²`, and hence also the manuscript-scale bound
  `|E_p - p³| ≤ 96 p² (log p)²`.

Every named lemma, proposition, theorem, and corollary in the manuscript has
a declaration-level theorem map below.  The historical prose, bibliography,
and `O` notation are not themselves Lean objects; every use of `O` in a named
result is represented by an explicit finite bound.
-/

namespace NField.Papers.TheCubicLawForDigitCollisionEnergy

open scoped BigOperators
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionRatioCompression
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CoprimeEulerMass
open NField.Alignment.CubicEnergyCharacterMoment
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindFourierMoment
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarrySpectralBridge
open NField.Alignment.PrimeCarryTableColumnLaw
open NField.Alignment.PrimeThresholdEnergyNormalization
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareDedekindCorrection
open NField.Alignment.PrimeSquareReducedRatio
open NField.Alignment.PrimeSquareSawtoothEnergy
open NField.Alignment.PrimitiveFloorTransform
open NField.Alignment.RademacherThreeTerm
open NField.Alignment.SawtoothCharacterExpansion
open NField.Alignment.TheCollisionSpectrum

/-- Manuscript Lemma `Odd sawtooth expansion`. -/
theorem odd_sawtooth_expansion
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (a : UnitClass q) :
    centeredSawtooth a.val =
      (q.totient : ℂ)⁻¹ * oddSawtoothCharacterSum a :=
  centeredSawtooth_eq_oddCharacterExpansion hq a

/-- Manuscript Proposition `Prime-square imprimitive vanishing`, including
both the first-window sum and its lag-one boundary consequence. -/
theorem prime_square_imprimitive_vanishing
    {p : ℕ} (hp : p.Prime) (ψ : Character p)
    (hne : ψ ≠ 1) (hodd : ψ.Odd) :
    shortWindowSum hp
          (DirichletCharacter.changeLevel (dvd_pow_self p (by omega)) ψ) = 0 ∧
      lagOneBoundaryFlux hp
          (DirichletCharacter.changeLevel (dvd_pow_self p (by omega)) ψ) = 0 :=
  ⟨shortWindowSum_changeLevel_zero hp ψ hne,
    lagOneBoundaryFlux_changeLevel_zero hp ψ hne hodd⟩

/-- Manuscript Lemma `Parseval mass formula`, in the manuscript's normalized
Fourier convention. -/
theorem parseval_mass_formula
    {m : ℕ} [NeZero m] (F : UnitClass m → ℂ) :
    (∑ x : UnitClass m, ‖F x‖ ^ 2) =
      (m.totient : ℝ)⁻¹ *
        ∑ χ : Character m, ‖characterTransform F χ‖ ^ 2 := by
  rw [character_parseval]
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  field_simp [hphi]

/-- Manuscript Lemma `Carry-table column law`, with its exact raw-column and
class-mean statements.  The global square-mean consequence is the theorem
`primeClassMeanSquareCorrection`. -/
theorem carry_table_column_law
    {p s : ℕ} [NeZero p] (hp : p.Prime) (hpodd : p ≠ 2)
    (hspos : 0 < s) (hslt : s < p) :
    (∑ q ∈ Finset.range p, carryThresholdCount p (p * q + s) =
        (((p * (p - 1) / 2 + s : ℕ) : ℤ))) ∧
      ((p : ℚ)⁻¹ *
          ∑ q ∈ Finset.range p,
            (fluctuationTable p (p * q + s) : ℚ) =
        -((p - s : ℕ) : ℚ) / (p : ℚ)) ∧
      (∑ u : UnitClass p,
          ((p - u.val.val : ℕ) : ℝ) ^ 2 / (p : ℝ)) =
        ((p - 1 : ℕ) : ℝ) * ((2 * p - 1 : ℕ) : ℝ) / 6 ∧
      primeCarryEnergy hp =
        primeThresholdVariance hp -
          ((p - 1 : ℕ) : ℝ) * ((2 * p - 1 : ℕ) : ℝ) / 6 :=
  ⟨carryThresholdCount_column_law hp hpodd hspos hslt,
    fluctuationTable_column_mean hp hpodd hspos hslt,
    primeClassMeanSquareCorrection hp,
    primeCarryEnergy_eq_thresholdVariance_sub_classMean hp hpodd⟩

/-- Manuscript Lemma `Primitive floor transform`.  Lean proves the stronger
statement that odd parity is not needed. -/
theorem primitive_floor_transform
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : Character q} (hχ : χ.IsPrimitive) (k : UnitClass q) :
    (∑ a : UnitClass q,
        (((k.val.val * a.val.val) / q : ℕ) : ℂ) * χ⁻¹ a.val) =
      ((k.val.val : ℂ) - χ k.val) * bernoulliOne χ⁻¹ :=
  primitiveFloorTransform hq hχ k

/-- Manuscript Theorem `Lag-one collision factorization`, before dividing by
the finite-group cardinality used in the normalized Fourier coefficient. -/
theorem lag_one_collision_factorization
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (χ : Character (p ^ 2)) (hprim : χ.IsPrimitive) :
    characterTransform (primeCarryCentered hp) χ =
      -(bernoulliOne χ * lagOneBoundaryFlux hp χ⁻¹) :=
  primitive_characterTransform_factorization hp χ hprim

/-- Manuscript Lemma `Carry-table reflection law`, for the raw statistic, the
integer half-centered table, and the class-centered collision function. -/
theorem carry_table_reflection_law
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (a : UnitClass (p ^ 2)) :
    carryThresholdCount p a.val.val +
          carryThresholdCount p (p ^ 2 - a.val.val) = (p : ℤ) ∧
      rawPrimeCarryValue hp a + rawPrimeCarryValue hp (-a) = -1 ∧
      primeHalfCenteredValue hp (-a) = -primeHalfCenteredValue hp a ∧
      primeCarryCentered hp (-a) = -primeCarryCentered hp a :=
  ⟨carryThresholdCount_reflection hp a,
    rawPrimeCarryValue_reflection hp a,
    primeHalfCenteredValue_reflection hp a,
    primeCarryCentered_reflection hp hpodd a⟩

/-- Manuscript Corollary `Lag-one spectral energy formula`. -/
theorem lag_one_spectral_energy_formula
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      4 / ((p ^ 2).totient : ℝ) * bernoulliWindowMoment hp :=
  primeCarryEnergy_eq_bernoulliWindowMoment hp hpodd

/-- Manuscript Theorem `Threshold-energy normalization`, including both exact
normalizations of the raw threshold variance and centered collision energy. -/
theorem threshold_energy_normalization
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeThresholdVariance hp =
        (1 / 4 : ℝ) * primeHalfCenteredSquareMass hp +
          (1 / 4 : ℝ) * (p : ℝ) * ((p - 1 : ℕ) : ℝ) ∧
      primeCarryEnergy hp =
        (1 / 4 : ℝ) * primeHalfCenteredSquareMass hp -
          ((p - 1 : ℕ) : ℝ) * ((p - 2 : ℕ) : ℝ) / 12 :=
  ⟨primeThresholdVariance_eq_halfCentered hp,
    primeCarryEnergy_eq_halfCentered_sub_classMean hp hpodd⟩

/-- Manuscript Theorem `Weighted Dedekind identity`, including exact
cancellation of the lower-modulus correction. -/
theorem weighted_dedekind_identity
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) (hpodd : p ≠ 2) :
    (primeCarryEnergy hp : ℂ) = dedekindCollisionEnergy hp ∧
      weightedLowerDedekindCorrection hp = 0 :=
  ⟨primeCarryEnergy_eq_dedekindCollisionEnergy hp hpodd,
    weightedLowerDedekindCorrection_eq_zero hp hpodd⟩

/-- Manuscript Corollary `Prime-square energy dictionary`: the table energy,
primitive odd Bernoulli moment, and weighted Dedekind energy are the same
finite object. -/
theorem prime_square_energy_dictionary
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
        4 / ((p ^ 2).totient : ℝ) * bernoulliWindowMoment hp ∧
      (primeCarryEnergy hp : ℂ) = dedekindCollisionEnergy hp :=
  ⟨primeCarryEnergy_eq_bernoulliWindowMoment hp hpodd,
    primeCarryEnergy_eq_dedekindCollisionEnergy hp hpodd⟩

/-- Manuscript Lemma `Reduced-ratio invariance`. -/
theorem reduced_ratio_invariance
    {p g k a : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (hgpos : 0 < g) (hkpos : 0 < k) (hapos : 0 < a)
    (hglt : g < p) (hklt : k < p) (halt : a < p)
    (hgklt : g * k < p) (hgalt : g * a < p) :
    dedekindSum ((smallNatUnit hp (g * k))⁻¹ *
        smallNatUnit hp (g * a)) =
      dedekindSum ((smallNatUnit hp k)⁻¹ * smallNatUnit hp a) :=
  dedekindRatio_smallNatUnit_cancel hp hgpos hkpos hapos
    hglt hklt halt hgklt hgalt

/-- Manuscript Lemma `Coprime Euler sum`, represented as convergence of its
canonical finite exhaustion to the exact value one. -/
theorem coprime_euler_sum :
    Filter.Tendsto
      (fun N => ∑ ka ∈ reducedEulerPairs N, pairWeight ka)
      Filter.atTop (nhds 1) :=
  tendsto_reducedEulerPairs_weight_sum_one

/-- Manuscript Lemma `Rademacher reciprocity reduction`. -/
theorem rademacher_reciprocity_reduction
    {p a k : ℕ} [NeZero (p ^ 2)] [NeZero a] [NeZero k]
    (hp : p.Prime)
    (ha : 0 < a) (hk : 0 < k) (hka : k < a) (hap : a < p)
    (hcop : k.Coprime a) :
    dedekindSum ((smallNatUnit hp k)⁻¹ * smallNatUnit hp a) =
      ((reducedRatioElementaryTerm p a k : ℚ) : ℂ) -
        coefficientDedekindTerm a (p ^ 2)
          hcop.symm (smallNatUnit_coprime hp hk (hka.trans hap)).symm -
        coefficientDedekindTerm (p ^ 2) k
          (smallNatUnit_coprime hp ha hap).symm hcop :=
  reducedRatio_dedekindSum_eq_threeTerm hp ha hk hka hap hcop

/-- Manuscript Lemma `Constant Rademacher remainder`, with an explicit
quadratic constant. -/
theorem constant_rademacher_remainder
    {p : ℕ} (hp3 : 3 ≤ p) :
    ‖offDiagonalElementaryRemainder p‖ ≤ 8 * (p : ℝ) ^ 2 :=
  norm_offDiagonalElementaryRemainder_le hp3

/-- Manuscript Lemma `Dedekind first-moment bound`, with an explicit finite
constant and harmonic-square majorant. -/
theorem dedekind_first_moment_bound
    {m : ℕ} [NeZero m] (hm : 0 < m) :
    dedekindFirstMoment m ≤
      (m : ℝ) * (harmonic m : ℝ) ^ 2 / 4 :=
  dedekindFirstMoment_le hm

/-- Manuscript Proposition `Character-moment form`, using Mathlib's
analytically continued Dirichlet `L`-function at one. -/
theorem character_moment_form
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      (4 * (p : ℝ)) /
          (Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ)) *
        lValueWindowMoment hp :=
  primeCarryEnergy_eq_lValueWindowMoment hp hpodd

/-- Manuscript Corollary `L(1)-weighted window moment`, with the paper's
big-O statement replaced by an explicit uniform bound. -/
theorem l_one_weighted_window_moment
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |lValueWindowMoment hp -
        Real.pi ^ 2 / 4 * ((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ 2| ≤
      6 * Real.pi ^ 2 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 :=
  lValueWindowMoment_cubic_bound hp hpodd

/-- Manuscript Proposition `Spectral pole split`, including the exact split
and explicit diagonal and off-diagonal pole bounds. -/
theorem spectral_pole_split
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    (primeCarryEnergy hp : ℂ) =
        spectralWindowDiagonal hp + spectralWindowOffDiagonal hp ∧
      ‖spectralWindowDiagonal hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)‖ ≤ 2 * (p : ℝ) ^ 2 ∧
      ‖spectralWindowOffDiagonal hp -
          (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
        26 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 :=
  ⟨primeCarryEnergy_eq_spectralWindowSplit hp hpodd,
    norm_spectralWindowDiagonal_sub_cubicPole_le hp hpodd,
    norm_spectralWindowOffDiagonal_sub_cubicPole_le hp hpodd⟩

/-- Manuscript Lemma `Lag-one boundary reduction`, including its exact
phase-sensitive and squared-magnitude forms. -/
theorem lag_one_boundary_reduction
    {p : ℕ} (hp : p.Prime) (χ : Character (p ^ 2)) (hodd : χ.Odd) :
    lagOneBoundaryFlux hp χ =
        -2 * χ (lagOneStepUnit p).val * shortWindowSum hp χ ∧
      Complex.normSq (lagOneBoundaryFlux hp χ) =
        4 * Complex.normSq (shortWindowSum hp χ) :=
  ⟨lagOneBoundaryFlux_eq_shortWindow hp χ hodd,
    lagOneBoundaryFlux_normSq hp χ hodd⟩

/-- Manuscript Proposition `Weight-free collision double sum`. -/
theorem weight_free_collision_double_sum
    {p : ℕ} (hp : p.Prime) :
    dedekindCollisionEnergy hp =
      4 * primeSquareCollisionDoubleSum hp :=
  dedekindCollisionEnergy_eq_doubleSum hp

/-- Manuscript Proposition `Reduced-ratio pole split`, with its exact energy
split, closed diagonal, and reduced-ratio off-diagonal formula. -/
theorem reduced_ratio_pole_split
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    dedekindCollisionEnergy hp =
        4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp +
          4 * primeSquareCollisionOffDiagonal hp ∧
      4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp =
        ((p - 1 : ℕ) : ℂ) * (((p ^ 2 : ℕ) : ℂ) - 1) *
          (((p ^ 2 : ℕ) : ℂ) - 2) /
            (3 * ((p ^ 2 : ℕ) : ℂ)) ∧
      4 * primeSquareCollisionOffDiagonal hp =
        8 * ∑ ak ∈ reducedRatioPairs p,
          (((p - 1) / ak.1 : ℕ) : ℂ) *
            dedekindSum
              ((smallNatUnit hp ak.2)⁻¹ * smallNatUnit hp ak.1) :=
  ⟨dedekindCollisionEnergy_poleSplit hp,
    dedekindCollisionEnergy_diagonal_closed hp,
    four_mul_primeSquareCollisionOffDiagonal_eq_reducedRatios hp⟩

/-- Manuscript Proposition `Four-way off-diagonal decomposition`. -/
theorem four_way_off_diagonal_decomposition
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    4 * primeSquareCollisionOffDiagonal hp =
      offDiagonalMain p + offDiagonalElementaryRemainder p +
        offDiagonalModulusA p + offDiagonalModulusK p :=
  four_mul_offDiagonal_eq_fourWay hp

/-- Manuscript Lemma `Off-diagonal main term`, with an explicit finite
harmonic-square error bound. -/
theorem off_diagonal_main_term
    {p : ℕ} (hp3 : 3 ≤ p) :
    ‖offDiagonalMain p - (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
      6 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 :=
  norm_offDiagonalMain_sub_cubicPole_le hp3

/-- Manuscript Lemma `a-modulus cancellation`. -/
theorem a_modulus_cancellation
    {p : ℕ} (hp : p.Prime) : offDiagonalModulusA p = 0 :=
  offDiagonalModulusA_eq_zero hp

/-- Manuscript Proposition `k-modulus remainder bound`, with an explicit
finite constant. -/
theorem k_modulus_remainder_bound
    {p : ℕ} (hp : p.Prime) :
    ‖offDiagonalModulusK p‖ ≤
      8 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 :=
  norm_offDiagonalModulusK_le hp

/-- Manuscript Theorem `Cubic law for digit-collision energy`, including the
full explicit bound and the separate one-third and two-thirds pole bounds. -/
theorem cubic_law_for_digit_collision_energy
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
        24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 ∧
      ‖4 * ((p - 1 : ℕ) : ℂ) * primeSquareDiagonalDedekind hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ 2 ∧
      ‖offDiagonalMain p -
          (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
        6 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 :=
  ⟨primeCarryEnergy_cubic_bound hp hpodd,
    norm_diagonalEnergy_sub_cubicPole_le hp hpodd,
    norm_offDiagonalMain_sub_cubicPole_le (by
      have hp2 := hp.two_le
      omega)⟩

end NField.Papers.TheCubicLawForDigitCollisionEnergy
