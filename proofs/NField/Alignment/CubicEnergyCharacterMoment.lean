/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareCubicEnergy
import NField.Alignment.SawtoothLValue

/-!
# Character moments of the cubic collision energy

This module closes the exact character and Dirichlet `L(1)` forms of the
prime-square carry energy.  The sums run over every character at the ambient
level, with an intrinsic primitive-odd gate.  This avoids choosing an
enumeration of the character group.
-/

namespace NField.Alignment.CubicEnergyCharacterMoment

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionRatioCompression
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindFourierMoment
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarrySpectralBridge
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareDedekindCorrection
open NField.Alignment.PrimeSquareSawtoothEnergy
open NField.Alignment.SawtoothLValue

/-- The primitive-odd generalized-Bernoulli window moment. -/
noncomputable def bernoulliWindowMoment
    {p : ℕ} (hp : p.Prime) : ℝ := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ χ : Character (p ^ 2),
    if χ.IsPrimitive ∧ χ.Odd then
      Complex.normSq (bernoulliOne χ) *
        Complex.normSq (shortWindowSum hp χ)
    else 0

/-- The primitive-odd `L(1)` window moment in the manuscript's character
labeling. -/
noncomputable def lValueWindowMoment
    {p : ℕ} (hp : p.Prime) : ℝ := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ χ : Character (p ^ 2),
    if χ.IsPrimitive ∧ χ.Odd then
      Complex.normSq (DirichletCharacter.LFunction χ 1) *
        Complex.normSq (shortWindowSum hp χ)
    else 0

/-- The same `L(1)` window moment before conjugate-character reindexing. -/
noncomputable def inverseLValueWindowMoment
    {p : ℕ} (hp : p.Prime) : ℝ := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ χ : Character (p ^ 2),
    if χ.IsPrimitive ∧ χ.Odd then
      Complex.normSq (DirichletCharacter.LFunction χ⁻¹ 1) *
        Complex.normSq (shortWindowSum hp χ)
    else 0

/-- Parseval and the primitive-odd gate give the exact Bernoulli moment of
the concrete carry table. -/
theorem primeCarryEnergy_eq_bernoulliWindowMoment
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      4 / ((p ^ 2).totient : ℝ) * bernoulliWindowMoment hp := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let F : UnitClass (p ^ 2) → ℂ := shortWindowSawtoothSignal hp
  have hchannels :
      (∑ χ : Character (p ^ 2), ‖characterTransform F χ‖ ^ 2) =
        bernoulliWindowMoment hp := by
    unfold bernoulliWindowMoment
    apply Finset.sum_congr rfl
    intro χ _
    rcases χ.even_or_odd with heven | hodd
    · have hnotodd : ¬χ.Odd := fun h =>
        χ.not_even_and_odd ⟨heven, h⟩
      have hz := characterTransform_odd_even_zero F
        (shortWindowSawtoothSignal_neg hp) χ heven
      rw [hz]
      simp [hnotodd]
    · by_cases hprim : χ.IsPrimitive
      · have hform := characterTransform_shortWindowSawtoothSignal hp
          (odd_character_ne_one χ hodd)
        rw [Complex.sq_norm, hform, Complex.normSq_mul]
        simp [hprim, hodd]
      · have hshort := shortWindowSum_eq_zero_of_imprimitive_odd
          hp χ hprim hodd
        have hform := characterTransform_shortWindowSawtoothSignal hp
          (odd_character_ne_one χ hodd)
        rw [hform, hshort]
        simp [hprim]
  have hparseval := character_parseval F
  have hmoment :
      bernoulliWindowMoment hp =
        ((p ^ 2).totient : ℝ) *
          ∑ a : UnitClass (p ^ 2), ‖F a‖ ^ 2 :=
    hchannels.symm.trans hparseval
  have henergy := primeCarryEnergy_eq_shortWindow hp hpodd
  rw [henergy, hmoment]
  have htot : ((p ^ 2).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos hp.pos 2)).ne'
  field_simp
  simp [F]

/-- The Bernoulli moment is exactly the inverse-character `L(1)` moment
supplied by the primitive odd special-value formula. -/
theorem bernoulliWindowMoment_eq_inverseLValueMoment
    {p : ℕ} (hp : p.Prime) :
    bernoulliWindowMoment hp =
      (p : ℝ) ^ 2 / Real.pi ^ 2 *
        inverseLValueWindowMoment hp := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold bernoulliWindowMoment inverseLValueWindowMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hgate : χ.IsPrimitive ∧ χ.Odd
  · rw [if_pos hgate, if_pos hgate,
      bernoulliOne_normSq_eq_LFunction
        (by nlinarith [hp.two_le] : 2 ≤ p ^ 2) hgate.1 hgate.2]
    push_cast
    ring
  · rw [if_neg hgate, if_neg hgate]
    ring

/-- Character inversion permutes the primitive odd sector and preserves the
short-window square mass. -/
theorem inverseLValueWindowMoment_eq_lValueWindowMoment
    {p : ℕ} (hp : p.Prime) :
    inverseLValueWindowMoment hp = lValueWindowMoment hp := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let T : Character (p ^ 2) → ℝ := fun χ =>
    if χ.IsPrimitive ∧ χ.Odd then
      Complex.normSq (DirichletCharacter.LFunction χ 1) *
        Complex.normSq (shortWindowSum hp χ)
    else 0
  have hgateStar (χ : Character (p ^ 2)) :
      ((star χ).IsPrimitive ∧ (star χ).Odd) ↔
        (χ.IsPrimitive ∧ χ.Odd) := by
    constructor
    · intro h
      constructor
      · have hinv := CarryBoundarySpectra.inverse_isPrimitive h.1
        simpa [MulChar.star_eq_inv] using hinv
      · change χ (-1) = -1
        have hodd : (star χ) (-1) = -1 := h.2
        rw [MulChar.star_apply] at hodd
        simpa using congrArg star hodd
    · intro h
      constructor
      · simpa [MulChar.star_eq_inv] using
          (CarryBoundarySpectra.inverse_isPrimitive h.1)
      · change (star χ) (-1) = -1
        rw [MulChar.star_apply, h.2]
        simp
  have hshortStar (χ : Character (p ^ 2)) :
      Complex.normSq (shortWindowSum hp (star χ)) =
        Complex.normSq (shortWindowSum hp χ) := by
    rw [show star χ = χ⁻¹ by simp [MulChar.star_eq_inv],
      shortWindowSum_inv hp χ]
    change Complex.normSq ((starRingEnd ℂ) (shortWindowSum hp χ)) = _
    exact Complex.normSq_conj _
  have hterm (χ : Character (p ^ 2)) :
      (if χ.IsPrimitive ∧ χ.Odd then
          Complex.normSq (DirichletCharacter.LFunction χ⁻¹ 1) *
            Complex.normSq (shortWindowSum hp χ)
        else 0) = T (star χ) := by
    by_cases hgate : χ.IsPrimitive ∧ χ.Odd
    · rw [if_pos hgate]
      unfold T
      rw [if_pos ((hgateStar χ).2 hgate), hshortStar]
      simp [MulChar.star_eq_inv]
    · rw [if_neg hgate]
      unfold T
      rw [if_neg (fun hs => hgate ((hgateStar χ).1 hs))]
  have hreindex :
      (∑ χ : Character (p ^ 2), T (star χ)) =
        ∑ χ : Character (p ^ 2), T χ := by
    simpa using (Equiv.sum_comp
      (Equiv.Perm.star : Equiv.Perm (Character (p ^ 2))) T)
  unfold inverseLValueWindowMoment lValueWindowMoment
  calc
    (∑ χ : Character (p ^ 2),
        if χ.IsPrimitive ∧ χ.Odd then
          Complex.normSq (DirichletCharacter.LFunction χ⁻¹ 1) *
            Complex.normSq (shortWindowSum hp χ)
        else 0) = ∑ χ : Character (p ^ 2), T (star χ) := by
          apply Finset.sum_congr rfl
          intro χ _
          exact hterm χ
    _ = ∑ χ : Character (p ^ 2), T χ := hreindex
    _ = ∑ χ : Character (p ^ 2),
        if χ.IsPrimitive ∧ χ.Odd then
          Complex.normSq (DirichletCharacter.LFunction χ 1) *
            Complex.normSq (shortWindowSum hp χ)
        else 0 := by rfl

/-- Exact conversion from the Bernoulli moment to the manuscript's
`L(1)`-weighted window moment. -/
theorem bernoulliWindowMoment_eq_lValueWindowMoment
    {p : ℕ} (hp : p.Prime) :
    bernoulliWindowMoment hp =
      (p : ℝ) ^ 2 / Real.pi ^ 2 * lValueWindowMoment hp := by
  rw [bernoulliWindowMoment_eq_inverseLValueMoment hp,
    inverseLValueWindowMoment_eq_lValueWindowMoment hp]

/-- Exact character-moment form with the coefficient simplified at the
prime-square level. -/
theorem primeCarryEnergy_eq_lValueWindowMoment
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      (4 * (p : ℝ)) /
          (Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ)) *
        lValueWindowMoment hp := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpred0 : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show p - 1 ≠ 0 by
      have := hp.two_le
      omega)
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  rw [primeCarryEnergy_eq_bernoulliWindowMoment hp hpodd,
    bernoulliWindowMoment_eq_lValueWindowMoment hp,
    Nat.totient_prime_pow hp (by decide : 0 < 2)]
  norm_num [pow_two]
  field_simp [hp0, hpred0, hpi]

/-- Solved form of the exact character moment. -/
theorem lValueWindowMoment_eq_primeCarryEnergy
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    lValueWindowMoment hp =
      Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ) /
          (4 * (p : ℝ)) * primeCarryEnergy hp := by
  have h := primeCarryEnergy_eq_lValueWindowMoment hp hpodd
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpred0 : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show p - 1 ≠ 0 by
      have := hp.two_le
      omega)
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  field_simp [hp0, hpred0, hpi] at h ⊢
  nlinarith only [h]

/-- Quantitative form of the manuscript's `L(1)`-weighted window asymptotic.
It implies the displayed `O(p² (log p)²)` statement. -/
theorem lValueWindowMoment_cubic_bound
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |lValueWindowMoment hp -
        Real.pi ^ 2 / 4 * ((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ 2| ≤
      6 * Real.pi ^ 2 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
  rw [lValueWindowMoment_eq_primeCarryEnergy hp hpodd]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfactorNonneg :
      0 ≤ Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ) / (4 * (p : ℝ)) := by
    positivity
  have hrearrange :
      Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ) /
            (4 * (p : ℝ)) * primeCarryEnergy hp -
          Real.pi ^ 2 / 4 * ((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ 2 =
        (Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ) /
            (4 * (p : ℝ))) *
          (primeCarryEnergy hp - (p : ℝ) ^ 3) := by
    field_simp [ne_of_gt hp0]
  rw [hrearrange, abs_mul, abs_of_nonneg hfactorNonneg]
  have hcubic := primeCarryEnergy_cubic_bound hp hpodd
  calc
    (Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ) / (4 * (p : ℝ))) *
        |primeCarryEnergy hp - (p : ℝ) ^ 3| ≤
      (Real.pi ^ 2 * ((p - 1 : ℕ) : ℝ) / (4 * (p : ℝ))) *
        (24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2) := by
          gcongr
    _ ≤ 6 * Real.pi ^ 2 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
      have hpred : (((p - 1 : ℕ) : ℝ)) ≤ p := by
        exact_mod_cast Nat.sub_le p 1
      have hnonneg : 0 ≤ (harmonic p : ℝ) ^ 2 := sq_nonneg _
      field_simp [ne_of_gt hp0]
      nlinarith [sq_nonneg (p : ℝ)]

/-! ## Window diagonal and off-diagonal -/

/-- The diagonal part of the short-window character-square expansion.  Its
kernel is the unit-restricted Dedekind correlation because character
orthogonality runs on the unit group. -/
noncomputable def spectralWindowDiagonal
    {p : ℕ} (hp : p.Prime) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact 4 * ((p - 1 : ℕ) : ℂ) *
    unitDedekindSum (1 : UnitClass (p ^ 2))

/-- The off-diagonal part of the same short-window expansion. -/
noncomputable def spectralWindowOffDiagonal
    {p : ℕ} (hp : p.Prime) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact 4 * collisionOffDiagonal (firstCollisionWindow hp) unitDedekindSum

/-- Exact finite window-diagonal/window-off-diagonal split of the spectral
energy. -/
theorem primeCarryEnergy_eq_spectralWindowSplit
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    (primeCarryEnergy hp : ℂ) =
      spectralWindowDiagonal hp + spectralWindowOffDiagonal hp := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have henergy := primeCarryEnergy_eq_dedekindCollisionEnergy hp hpodd
  rw [dedekindCollisionEnergy_eq_doubleSum hp] at henergy
  have hunit := unitDedekindDoubleSum_eq_full hp hpodd
  rw [← hunit] at henergy
  rw [collisionDoubleSum_diagonal_offDiagonal] at henergy
  rw [firstCollisionWindow_card hp] at henergy
  unfold spectralWindowDiagonal spectralWindowOffDiagonal
  simpa [mul_add, mul_assoc] using henergy

/-- The spectral window diagonal is the full prime-square ratio-one
Dedekind term with the nonunit prime-level term removed. -/
theorem spectralWindowDiagonal_eq_full_sub_lower
    {p : ℕ} (hp : p.Prime) :
    spectralWindowDiagonal hp =
      4 * ((p - 1 : ℕ) : ℂ) *
        (primeSquareDiagonalDedekind hp -
          primeDedekindSum hp (1 : UnitClass p)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hsplit := dedekindSum_eq_unit_add_lower hp
    (1 : UnitClass (p ^ 2))
  have hlower :
      lowerDedekindKernel hp (1 : UnitClass (p ^ 2)) =
        primeDedekindSum hp (1 : UnitClass p) := by
    unfold lowerDedekindKernel
    congr 1
    apply Units.ext
    unfold primeReduction
    simp
  rw [hlower] at hsplit
  unfold spectralWindowDiagonal primeSquareDiagonalDedekind
  rw [show unitDedekindSum (1 : UnitClass (p ^ 2)) =
      dedekindSum (1 : UnitClass (p ^ 2)) -
        primeDedekindSum hp (1 : UnitClass p) by
      linear_combination -hsplit]

/-- The removed prime-level diagonal is quadratically bounded. -/
theorem norm_spectralWindowLowerCorrection_le
    {p : ℕ} (hp : p.Prime) :
    ‖4 * ((p - 1 : ℕ) : ℂ) *
        primeDedekindSum hp (1 : UnitClass p)‖ ≤
      (p : ℝ) ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : 2 ≤ p := hp.two_le
  unfold primeDedekindSum
  rw [dedekindSum_one hp2]
  rw [show
      4 * ((p - 1 : ℕ) : ℂ) *
          ((((p : ℕ) : ℂ) - 1) * (((p : ℕ) : ℂ) - 2) /
            (12 * (p : ℂ))) =
        (((((p - 1 : ℕ) : ℝ) ^ 2 * ((p - 2 : ℕ) : ℝ) /
          (3 * (p : ℝ))) : ℝ) : ℂ) by
            push_cast [Nat.cast_sub (show 1 ≤ p by omega),
              Nat.cast_sub hp2]
            field_simp [show (p : ℂ) ≠ 0 by exact_mod_cast hp.ne_zero]
            ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * p)]
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub hp2]
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  · positivity

/-- Quantitative `O(p²)` bound for the spectral window diagonal. -/
theorem norm_spectralWindowDiagonal_sub_cubicPole_le
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ‖spectralWindowDiagonal hp -
        (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)‖ ≤
      2 * (p : ℝ) ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hdiag := norm_diagonalEnergy_sub_cubicPole_le hp hpodd
  have hlower := norm_spectralWindowLowerCorrection_le hp
  rw [spectralWindowDiagonal_eq_full_sub_lower hp]
  have hrearrange :
      4 * ((p - 1 : ℕ) : ℂ) *
            (primeSquareDiagonalDedekind hp -
              primeDedekindSum hp (1 : UnitClass p)) -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ) =
        (4 * ((p - 1 : ℕ) : ℂ) *
            primeSquareDiagonalDedekind hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)) -
        4 * ((p - 1 : ℕ) : ℂ) *
          primeDedekindSum hp (1 : UnitClass p) := by ring
  rw [hrearrange]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Quantitative `O(p² H_p²)` bound for the spectral window
off-diagonal. -/
theorem norm_spectralWindowOffDiagonal_sub_cubicPole_le
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ‖spectralWindowOffDiagonal hp -
        (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
      26 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
  have hsplit := primeCarryEnergy_eq_spectralWindowSplit hp hpodd
  have hdiag := norm_spectralWindowDiagonal_sub_cubicPole_le hp hpodd
  have hcubicReal := primeCarryEnergy_cubic_bound hp hpodd
  have hcubic :
      ‖(primeCarryEnergy hp : ℂ) -
          (((p : ℝ) ^ 3 : ℝ) : ℂ)‖ ≤
        24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
    rw [show (primeCarryEnergy hp : ℂ) -
        (((p : ℝ) ^ 3 : ℝ) : ℂ) =
      (((primeCarryEnergy hp - (p : ℝ) ^ 3 : ℝ)) : ℂ) by
        push_cast
        ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hcubicReal
  have hoff : spectralWindowOffDiagonal hp =
      (primeCarryEnergy hp : ℂ) - spectralWindowDiagonal hp := by
    linear_combination -hsplit
  rw [hoff]
  have hrearrange :
      (primeCarryEnergy hp : ℂ) - spectralWindowDiagonal hp -
          (((2 / 3 : ℝ) * (p : ℝ) ^ 3 : ℝ) : ℂ) =
        ((primeCarryEnergy hp : ℂ) -
          (((p : ℝ) ^ 3 : ℝ) : ℂ)) -
        (spectralWindowDiagonal hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hrearrange]
  have hHone : (1 : ℝ) ≤ (harmonic p : ℝ) := by
    calc
      (1 : ℝ) = (harmonic 1 : ℝ) := by norm_num [harmonic]
      _ ≤ (harmonic p : ℝ) :=
        harmonic_cast_mono (show 1 ≤ p by exact hp.one_le)
  calc
    ‖((primeCarryEnergy hp : ℂ) -
          (((p : ℝ) ^ 3 : ℝ) : ℂ)) -
        (spectralWindowDiagonal hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ))‖ ≤
      ‖(primeCarryEnergy hp : ℂ) -
          (((p : ℝ) ^ 3 : ℝ) : ℂ)‖ +
        ‖spectralWindowDiagonal hp -
          (((p : ℝ) ^ 3 / 3 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 24 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 +
        2 * (p : ℝ) ^ 2 := by gcongr
    _ ≤ 26 * (p : ℝ) ^ 2 * (harmonic p : ℝ) ^ 2 := by
      have hpnonneg : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg ((harmonic p : ℝ) - 1)]

end NField.Alignment.CubicEnergyCharacterMoment
