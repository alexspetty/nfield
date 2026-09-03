/-
Author: Alexander S. Petty
-/

import NField.Alignment.DeficitLattice
import NField.Alignment.DigitPartitionedField
import NField.Golden.Threshold

/-!
# The coherence decomposition

Reusable formal core for the Lean companion to "The Coherence Decomposition".

The manuscript compares two differently normalized statistics.  This file
keeps that distinction explicit.  It verifies the synchronized pair relation,
the exact pair-class count, the reference, focused, and pairwise formulas and
their limits, the reciprocal-golden gap, and the zero-pairwise-alignment
characterization.
-/

namespace NField.Alignment.CoherenceDecomposition

open Filter
open NField.Alignment
open NField.Alignment.DeficitLattice
open NField.Golden

/-- Equality modulo `p` is preserved and reflected by multiplication by a
cofactor coprime to `p`. -/
theorem mul_mod_eq_mul_mod_iff_of_coprime {p u j k : ℕ}
    (hu : Nat.Coprime p u) :
    (j * u) % p = (k * u) % p ↔ j % p = k % p := by
  constructor
  · intro h
    have hmod : j * u ≡ k * u [MOD p] := by
      simpa [Nat.ModEq] using h
    have hcancel := Nat.ModEq.cancel_right_of_coprime hu.gcd_eq_one hmod
    simpa [Nat.ModEq] using hcancel
  · intro h
    have hmod : j ≡ k [MOD p] := by
      simpa [Nat.ModEq] using h
    have hmul := hmod.mul_right u
    simpa [Nat.ModEq] using hmul

/-- A synchronized pair either consists of two terminating fractions, or of
two nonterminating fractions whose digits agree at the indicated position. -/
def synchronizedPairAlignedAtPosition
    (b p u j k position : ℕ) : Prop :=
  (j % p = 0 ∧ k % p = 0) ∨
    (j % p ≠ 0 ∧ k % p ≠ 0 ∧
      digitAt b p ((j * u) % p) position =
        digitAt b p ((k * u) % p) position)

/-- Under digit partitioning, one synchronized comparison matches exactly
when the two numerators belong to the same residue class. -/
theorem synchronizedPairAlignedAtPosition_iff_same_residue
    {b p u j k position : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hu : Nat.Coprime p u) :
    synchronizedPairAlignedAtPosition b p u j k position ↔
      j % p = k % p := by
  constructor
  · rintro (hzero | hnonzero)
    · exact hzero.1.trans hzero.2.symm
    · rcases hnonzero with ⟨hj0, hk0, hdigit⟩
      have hju0 : (j * u) % p ≠ 0 := by
        intro h
        have hdiv : p ∣ j * u := (Nat.dvd_iff_mod_eq_zero).2 h
        have hjdiv : p ∣ j := hu.dvd_of_dvd_mul_right hdiv
        exact hj0 ((Nat.dvd_iff_mod_eq_zero).1 hjdiv)
      have hku0 : (k * u) % p ≠ 0 := by
        intro h
        have hdiv : p ∣ k * u := (Nat.dvd_iff_mod_eq_zero).2 h
        have hkdiv : p ∣ k := hu.dvd_of_dvd_mul_right hdiv
        exact hk0 ((Nat.dvd_iff_mod_eq_zero).1 hkdiv)
      have hstarts : (j * u) % p = (k * u) % p := by
        by_contra hne
        exact (digitAt_separated hp hpb hdp
          (Nat.pos_of_ne_zero hju0) (Nat.mod_lt _ hp.pos)
          (Nat.pos_of_ne_zero hku0) (Nat.mod_lt _ hp.pos) hne) hdigit
      exact (mul_mod_eq_mul_mod_iff_of_coprime hu).mp hstarts
  · intro hres
    by_cases hj0 : j % p = 0
    · exact Or.inl ⟨hj0, hres ▸ hj0⟩
    · right
      have hk0 : k % p ≠ 0 := by simpa [hres] using hj0
      refine ⟨hj0, hk0, ?_⟩
      have hstarts : (j * u) % p = (k * u) % p :=
        (mul_mod_eq_mul_mod_iff_of_coprime hu).mpr hres
      rw [hstarts]

/-- A pair agrees through a whole positive synchronized window. -/
def fullySynchronizedPairAligned
    (b p u j k length : ℕ) : Prop :=
  ∀ position < length,
    synchronizedPairAlignedAtPosition b p u j k position

/-- Agreement through any positive common window is exactly equality of the
two numerator residue classes. -/
theorem fullySynchronizedPairAligned_iff_same_residue
    {b p u j k length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hu : Nat.Coprime p u)
    (hlength : 0 < length) :
    fullySynchronizedPairAligned b p u j k length ↔ j % p = k % p := by
  constructor
  · intro h
    exact (synchronizedPairAlignedAtPosition_iff_same_residue
      hp hpb hdp hu).mp (h 0 hlength)
  · intro h position hposition
    exact (synchronizedPairAlignedAtPosition_iff_same_residue
      hp hpb hdp hu).mpr h

/-- The rational extension of the number of unordered pairs from a class of
size `x`.  It is used only at nonnegative integer values. -/
def chooseTwoMass (x : ℚ) : ℚ :=
  x * (x - 1) / 2

/-- Pair-score mass from the terminating class of size `m-1` and the `p-1`
nonterminating classes of size `m`. -/
def primeCorePairMass (p m : ℕ) : ℚ :=
  chooseTwoMass ((m : ℚ) - 1) +
    ((p : ℚ) - 1) * chooseTwoMass (m : ℚ)

/-- Total number of distinct unordered pairs among `p*m-1` fractions. -/
def primeCoreTotalPairMass (p m : ℕ) : ℚ :=
  chooseTwoMass ((p : ℚ) * m - 1)

/-- The exact pairwise statistic obtained from the synchronized class count. -/
def pairwiseAlignmentFormula (p m : ℕ) : ℚ :=
  primeCorePairMass p m / primeCoreTotalPairMass p m

/-- Focused alignment is the manuscript's signed residual, not an independent
sampling average. -/
def focusedAlignmentFormula (p m : ℕ) : ℚ :=
  alignmentFormula p m - pairwiseAlignmentFormula p m

/-- The synchronized residue classes have precisely the sizes used in the
pair-count formula. -/
theorem synchronizedClassSizes {p m : ℕ} (hp : 1 < p) :
    terminatingNumeratorCount p m = m - 1 ∧
      ∀ r : ℕ, r < p → residueCount p r m = m := by
  exact ⟨terminatingNumeratorCount_eq (by omega),
    fun r hr => residueCount_eq hr⟩

/-- The two binomial contributions factor as `(m-1)(p*m-2)/2`. -/
theorem primeCorePairMass_eq (p m : ℕ) :
    primeCorePairMass p m =
      (((m : ℚ) - 1) * ((p : ℚ) * m - 2)) / 2 := by
  unfold primeCorePairMass chooseTwoMass
  ring

/-- The pairwise average simplifies to `(m-1)/(p*m-1)`. -/
theorem pairwiseAlignmentFormula_eq {p m : ℕ}
    (hpm : 3 ≤ p * m) :
    pairwiseAlignmentFormula p m =
      ((m : ℚ) - 1) / ((p : ℚ) * m - 1) := by
  rw [pairwiseAlignmentFormula, primeCorePairMass_eq]
  have hpm1 : (p : ℚ) * m - 1 ≠ 0 := by
    have hpmq : (3 : ℚ) ≤ (p : ℚ) * m := by exact_mod_cast hpm
    nlinarith
  have hpm2 : (p : ℚ) * m - 2 ≠ 0 := by
    have : (3 : ℚ) ≤ (p : ℚ) * m := by exact_mod_cast hpm
    nlinarith
  have hpm2' : (p : ℚ) * m - 1 - 1 ≠ 0 := by
    intro h
    apply hpm2
    linarith
  have htotal : primeCoreTotalPairMass p m ≠ 0 := by
    unfold primeCoreTotalPairMass chooseTwoMass
    exact div_ne_zero (mul_ne_zero hpm1 hpm2') (by norm_num)
  apply (div_eq_iff htotal).2
  unfold primeCoreTotalPairMass chooseTwoMass
  rw [show (p : ℚ) * m - 1 - 1 = (p : ℚ) * m - 2 by ring]
  symm
  calc
    (((m : ℚ) - 1) / ((p : ℚ) * m - 1)) *
          ((((p : ℚ) * m - 1) * ((p : ℚ) * m - 2)) / 2) =
        ((((m : ℚ) - 1) / ((p : ℚ) * m - 1)) *
          ((p : ℚ) * m - 1)) * ((p : ℚ) * m - 2) / 2 := by ring
    _ = (((m : ℚ) - 1) * ((p : ℚ) * m - 2)) / 2 := by
      rw [div_mul_cancel₀ _ hpm1]

/-- Subtracting the pairwise background from the reference alignment leaves
exactly the normalized reference residue class. -/
theorem focusedAlignmentFormula_eq {p m : ℕ}
    (hpm : 3 ≤ p * m) :
    focusedAlignmentFormula p m =
      (m : ℚ) / ((p : ℚ) * m - 1) := by
  rw [focusedAlignmentFormula, alignmentFormula,
    pairwiseAlignmentFormula_eq hpm]
  have hden : (p : ℚ) * m - 1 ≠ 0 := by
    have hpmq : (3 : ℚ) ≤ (p : ℚ) * m := by exact_mod_cast hpm
    nlinarith
  field_simp
  ring

/-- Exact three-way coherence decomposition. -/
theorem exactCoherenceDecomposition {p m : ℕ}
    (hpm : 3 ≤ p * m) :
    alignmentFormula p m =
        ((2 : ℚ) * m - 1) / ((p : ℚ) * m - 1) ∧
      focusedAlignmentFormula p m =
        (m : ℚ) / ((p : ℚ) * m - 1) ∧
      pairwiseAlignmentFormula p m =
        ((m : ℚ) - 1) / ((p : ℚ) * m - 1) := by
  exact ⟨rfl, focusedAlignmentFormula_eq hpm,
    pairwiseAlignmentFormula_eq hpm⟩

/-- The inherited reference statistic computed from every synchronized digit
comparison is the closed reference formula used in the decomposition. -/
theorem synchronizedRepetendAlignment_eq_alignmentFormula
    {b p m u length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hu : Nat.Coprime p u)
    (hm : 1 ≤ m) (hlength : 0 < length) :
    synchronizedRepetendAlignment b p m u length = alignmentFormula p m := by
  rw [synchronizedRepetendAlignment_eq hp hpb hdp hu hm hlength]
  unfold alignmentFormula
  have htwo : 1 ≤ 2 * m := by omega
  have hpm : 1 ≤ p * m := by nlinarith [hp.two_le]
  push_cast [Nat.cast_sub htwo, Nat.cast_sub hpm]
  rfl

/-- Real closed form of the focused residual. -/
noncomputable def focusedAlignmentFormulaReal (p m : ℕ) : ℝ :=
  (m : ℝ) / ((p : ℝ) * m - 1)

/-- Real closed form of the pairwise background. -/
noncomputable def pairwiseAlignmentFormulaReal (p m : ℕ) : ℝ :=
  ((m : ℝ) - 1) / ((p : ℝ) * m - 1)

/-- The focused residual tends to `1/p` along every natural scale. -/
theorem focusedAlignmentFormulaReal_tendsto {p : ℕ} (hp : 0 < p) :
    Tendsto (focusedAlignmentFormulaReal p) atTop
      (nhds ((1 : ℝ) / p)) := by
  convert (tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 0 (-1) 1 (d := (p : ℝ)) (by exact_mod_cast hp.ne')) using 1
  funext m
  simp only [focusedAlignmentFormulaReal, sub_eq_add_neg]
  ring

/-- The pairwise background also tends to `1/p`. -/
theorem pairwiseAlignmentFormulaReal_tendsto {p : ℕ} (hp : 0 < p) :
    Tendsto (pairwiseAlignmentFormulaReal p) atTop
      (nhds ((1 : ℝ) / p)) := by
  convert (tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) (-1) (-1) 1 (d := (p : ℝ)) (by exact_mod_cast hp.ne')) using 1
  funext m
  simp only [pairwiseAlignmentFormulaReal, sub_eq_add_neg]
  ring

/-- The inherited reference alignment tends to `2/p`. -/
theorem referenceAlignmentFormulaReal_tendsto {p : ℕ} (hp : 0 < p) :
    Tendsto (alignmentFormulaReal p) atTop
      (nhds ((2 : ℝ) / p)) := by
  convert digitPartitioningAlignmentFormulaReal_tendsto (p := p) hp using 1
  funext m
  unfold alignmentFormulaReal digitPartitioningAlignmentFormulaReal
  ring

/-- The three manuscript limits, packaged with their distinct normalizations. -/
theorem coherenceDecomposition_tendsto {p : ℕ} (hp : 0 < p) :
    Tendsto (alignmentFormulaReal p) atTop (nhds ((2 : ℝ) / p)) ∧
      Tendsto (focusedAlignmentFormulaReal p) atTop (nhds ((1 : ℝ) / p)) ∧
      Tendsto (pairwiseAlignmentFormulaReal p) atTop
        (nhds ((1 : ℝ) / p)) := by
  exact ⟨referenceAlignmentFormulaReal_tendsto hp,
    focusedAlignmentFormulaReal_tendsto hp,
    pairwiseAlignmentFormulaReal_tendsto hp⟩

/-- The reciprocal-golden threshold lies between the focused and reference
limits exactly for the prime cores two and three. -/
theorem reciprocalGolden_between_limits_iff {p : ℕ} (hp : Nat.Prime p) :
    ((1 : ℝ) / p < goldenReciprocal ∧
      goldenReciprocal < (2 : ℝ) / p) ↔ p = 2 ∨ p = 3 := by
  constructor
  · rintro ⟨_, hupper⟩
    by_contra hnot
    push Not at hnot
    have hp5 : 5 ≤ p := by
      have hp2 := hp.two_le
      have hp4 : p ≠ 4 := by
        intro h
        subst p
        norm_num at hp
      omega
    have hle : (2 : ℝ) / p ≤ 2 / 5 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by exact_mod_cast hp5)
    nlinarith [two_fifths_lt_goldenReciprocal]
  · rintro (rfl | rfl)
    · constructor
      · dsimp [goldenReciprocal]
        nlinarith [sqrt_five_gt_two]
      · dsimp [goldenReciprocal]
        nlinarith [sqrt_five_lt_three]
    · constructor
      · nlinarith [two_fifths_lt_goldenReciprocal]
      · exact goldenReciprocal_lt_two_thirds

/-- In the prime-two case the reference formula is identically one. -/
theorem primeTwo_reference_degenerate {m : ℕ} (hm : 1 ≤ m) :
    alignmentFormula 2 m = 1 := by
  unfold alignmentFormula
  have hmq : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hden : (2 : ℚ) * m - 1 ≠ 0 := by nlinarith
  exact div_self hden

/-- For every prime core at least three, the focused residual is at most one
half and therefore strictly below the reciprocal-golden threshold. -/
theorem focusedAlignment_below_golden_of_three_le {p m : ℕ}
    (hp : 3 ≤ p) (hm : 1 ≤ m) :
    focusedAlignmentFormulaReal p m < goldenReciprocal := by
  have hmq : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpq : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) * m - 1 := by nlinarith
  have hhalf : focusedAlignmentFormulaReal p m ≤ (1 : ℝ) / 2 := by
    rw [focusedAlignmentFormulaReal]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hgold : (1 : ℝ) / 2 < goldenReciprocal := by
    dsimp [goldenReciprocal]
    nlinarith [sqrt_five_gt_two]
  exact lt_of_le_of_lt hhalf hgold

/-- The admissible nontrivial prime-two resolutions start at three and their
focused residual is already below the reciprocal-golden threshold. -/
theorem primeTwo_focused_below_golden {m : ℕ} (hm : 3 ≤ m) :
    focusedAlignmentFormulaReal 2 m < goldenReciprocal := by
  have hmq : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : (0 : ℝ) < (2 : ℝ) * m - 1 := by nlinarith
  have hthreeFifths :
      focusedAlignmentFormulaReal 2 m ≤ (3 : ℝ) / 5 := by
    rw [focusedAlignmentFormulaReal]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hgold : (3 : ℝ) / 5 < goldenReciprocal := by
    dsimp [goldenReciprocal]
    nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]
  exact lt_of_le_of_lt hthreeFifths hgold

/-- A supported scale in a base not divisible by two cannot itself be
divisible by two. -/
theorem two_not_dvd_supported {b m : ℕ} (h2b : ¬2 ∣ b)
    (hsupported : Supported b m) : ¬2 ∣ m := by
  intro h2m
  rcases hsupported with ⟨D, hD⟩
  have h2pow : 2 ∣ b ^ D := h2m.trans hD
  exact h2b (Nat.prime_two.dvd_of_dvd_pow h2pow)

/-- The manuscript's hypotheses force every admissible nontrivial supported
prime-two scale to be at least three. -/
theorem primeTwo_supported_scale_ge_three {b m : ℕ}
    (h2b : ¬2 ∣ b) (hsupported : Supported b m) (hproduct : 3 ≤ 2 * m) :
    3 ≤ m := by
  have hm2 : 2 ≤ m := by omega
  have hmne2 : m ≠ 2 := by
    intro hm
    subst m
    exact two_not_dvd_supported h2b hsupported (by norm_num)
  omega

/-- The prime-two finite bound with exactly the manuscript's supported-scale
hypotheses. -/
theorem primeTwo_supported_focused_below_golden {b m : ℕ}
    (h2b : ¬2 ∣ b) (hsupported : Supported b m) (hproduct : 3 ≤ 2 * m) :
    focusedAlignmentFormulaReal 2 m < goldenReciprocal := by
  exact primeTwo_focused_below_golden
    (primeTwo_supported_scale_ge_three h2b hsupported hproduct)

/-- In every defined prime-core formula, the focused residual is nonnegative
and no larger than the inherited reference alignment. -/
theorem focused_nonnegative_and_le_reference {p m : ℕ}
    (hpm : 3 ≤ p * m) :
    0 ≤ focusedAlignmentFormulaReal p m ∧
      focusedAlignmentFormulaReal p m ≤ alignmentFormulaReal p m := by
  have hpmq : (3 : ℝ) ≤ (p : ℝ) * m := by exact_mod_cast hpm
  have hden : (0 : ℝ) < (p : ℝ) * m - 1 := by nlinarith
  have hmq : (0 : ℝ) ≤ m := by positivity
  have hm : 1 ≤ m := by
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      norm_num at hpm
    omega
  have hmq1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  constructor
  · rw [focusedAlignmentFormulaReal]
    positivity
  · rw [focusedAlignmentFormulaReal, alignmentFormulaReal]
    apply div_le_div_of_nonneg_right (by nlinarith) hden.le

/-- At every finite resolution with prime core at least five, both the
reference alignment and focused residual are below the threshold. -/
theorem largePrime_reference_and_focused_below_golden {p m : ℕ}
    (hp : 5 ≤ p) (hm : 1 ≤ m) :
    alignmentFormulaReal p m < goldenReciprocal ∧
      focusedAlignmentFormulaReal p m < goldenReciprocal := by
  exact ⟨large_prime_below_golden hp hm,
    focusedAlignment_below_golden_of_three_le (by omega) hm⟩

/-- The supported clearing depth, synchronized pair classification, residue
class sizes, and exact three-way formulas in one paper-facing certificate. -/
theorem coherenceDecomposition_certificate
    {b p m length : ℕ} (_hb : 2 ≤ b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hle : p ≤ b + 1) (_hm : 1 ≤ m)
    (hsupported : Supported b m) (hpm : 3 ≤ p * m)
    (hlength : 0 < length) :
    ∃ D : ℕ,
      m ∣ b ^ D ∧
      (∀ j k : ℕ,
        fullySynchronizedPairAligned b p (clearingCofactor b m D)
            j k length ↔ j % p = k % p) ∧
      synchronizedRepetendAlignment b p m (clearingCofactor b m D) length =
        alignmentFormula p m ∧
      terminatingNumeratorCount p m = m - 1 ∧
      (∀ r : ℕ, r < p → residueCount p r m = m) ∧
      alignmentFormula p m =
          ((2 : ℚ) * m - 1) / ((p : ℚ) * m - 1) ∧
      focusedAlignmentFormula p m =
          (m : ℚ) / ((p : ℚ) * m - 1) ∧
      pairwiseAlignmentFormula p m =
          ((m : ℚ) - 1) / ((p : ℚ) * m - 1) := by
  rcases hsupported with ⟨D, hD⟩
  have hdp : DigitPartitioning b p :=
    digitPartitioning_of_le hp.pos hpb hle
  have hu : Nat.Coprime p (clearingCofactor b m D) :=
    prime_coprime_clearingCofactor hp hpb hD
  have hsizes := synchronizedClassSizes (m := m) hp.one_lt
  have hformulas := exactCoherenceDecomposition hpm
  exact ⟨D, hD,
    fun j k => fullySynchronizedPairAligned_iff_same_residue
      hp hpb hdp hu hlength,
    synchronizedRepetendAlignment_eq_alignmentFormula
      hp hpb hdp hu _hm hlength,
    hsizes.1, hsizes.2, hformulas.1, hformulas.2.1, hformulas.2.2⟩

/-- Number of matching synchronized positions for one unordered residue pair. -/
def primePairPositionMatchCount
    (b p r s length : ℕ) : ℕ :=
  ((Finset.range length).filter
    (fun position => digitAt b p r position = digitAt b p s position)).card

/-- Total matching-position count over distinct unordered nonzero residue
pairs. -/
def primePairwiseMatchCount (b p length : ℕ) : ℕ :=
  ((Finset.range p).filter (fun r => 0 < r)).sum fun r =>
    ((Finset.range p).filter (fun s => r < s)).sum fun s =>
      primePairPositionMatchCount b p r s length

/-- The actual finite prime pairwise alignment on a positive synchronized
window. -/
def primePairwiseAlignment (b p length : ℕ) : ℚ :=
  (primePairwiseMatchCount b p length : ℚ) /
    (chooseTwoMass ((p : ℚ) - 1) * length)

/-- Digit partitioning forces every distinct residue pair to have zero
matching positions. -/
theorem primePairwiseMatchCount_eq_zero_of_digitPartitioning
    {b p length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) :
    primePairwiseMatchCount b p length = 0 := by
  unfold primePairwiseMatchCount
  apply Finset.sum_eq_zero
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_range] at hr
  apply Finset.sum_eq_zero
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_range] at hs
  unfold primePairPositionMatchCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro position hposition hdigit
  exact (digitAt_separated (j := position) hp hpb hdp hr.2 hr.1
    (hr.2.trans hs.2) hs.1 (Nat.ne_of_lt hs.2)) hdigit

/-- A first-position digit collision contributes positively to every positive
synchronized window. -/
theorem primePairPositionMatchCount_pos_of_first_digit_eq
    {b p r s length : ℕ} (hr : r < p) (hs : s < p)
    (hlength : 0 < length)
    (hdigit : NField.CollisionDefinition.digitBin b p r =
      NField.CollisionDefinition.digitBin b p s) :
    0 < primePairPositionMatchCount b p r s length := by
  unfold primePairPositionMatchCount
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp [digitAt, hlength, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, hdigit]

/-- If the synchronized pairwise match count vanishes on a positive window,
then the first digit is injective on nonzero residues. -/
theorem digitPartitioning_of_primePairwiseMatchCount_eq_zero
    {b p length : ℕ} (hlength : 0 < length)
    (hzero : primePairwiseMatchCount b p length = 0) :
    DigitPartitioning b p := by
  intro r s hr0 hr hs0 hs hdigit
  by_contra hrs
  rcases Nat.lt_trichotomy r s with hrslt | hrseq | hrslt
  · have hrmem : r ∈ (Finset.range p).filter (fun x => 0 < x) := by
      simp [hr, hr0]
    have hsmem : s ∈ (Finset.range p).filter (fun x => r < x) := by
      simp [hs, hrslt]
    have hpos := primePairPositionMatchCount_pos_of_first_digit_eq
      hr hs hlength hdigit
    have hinner : primePairPositionMatchCount b p r s length ≤
        ((Finset.range p).filter (fun x => r < x)).sum
          (fun x => primePairPositionMatchCount b p r x length) := by
      exact Finset.single_le_sum
        (f := fun x => primePairPositionMatchCount b p r x length)
        (fun _ _ => Nat.zero_le _) hsmem
    have houter :
        ((Finset.range p).filter (fun x => r < x)).sum
            (fun x => primePairPositionMatchCount b p r x length) ≤
          primePairwiseMatchCount b p length := by
      unfold primePairwiseMatchCount
      exact Finset.single_le_sum
        (f := fun x =>
          ((Finset.range p).filter (fun y => x < y)).sum
            (fun y => primePairPositionMatchCount b p x y length))
        (fun _ _ => Nat.zero_le _) hrmem
    omega
  · exact hrs hrseq
  · have hsrmem : s ∈ (Finset.range p).filter (fun x => 0 < x) := by
      simp [hs, hs0]
    have hrmem : r ∈ (Finset.range p).filter (fun x => s < x) := by
      simp [hr, hrslt]
    have hpos := primePairPositionMatchCount_pos_of_first_digit_eq
      hs hr hlength hdigit.symm
    have hinner : primePairPositionMatchCount b p s r length ≤
        ((Finset.range p).filter (fun x => s < x)).sum
          (fun x => primePairPositionMatchCount b p s x length) := by
      exact Finset.single_le_sum
        (f := fun x => primePairPositionMatchCount b p s x length)
        (fun _ _ => Nat.zero_le _) hrmem
    have houter :
        ((Finset.range p).filter (fun x => s < x)).sum
            (fun x => primePairPositionMatchCount b p s x length) ≤
          primePairwiseMatchCount b p length := by
      unfold primePairwiseMatchCount
      exact Finset.single_le_sum
        (f := fun x =>
          ((Finset.range p).filter (fun y => x < y)).sum
            (fun y => primePairPositionMatchCount b p x y length))
        (fun _ _ => Nat.zero_le _) hsrmem
    omega

/-- Exact zero-match characterization on every positive synchronized window. -/
theorem primePairwiseMatchCount_eq_zero_iff_digitPartitioning
    {b p length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hlength : 0 < length) :
    primePairwiseMatchCount b p length = 0 ↔ DigitPartitioning b p := by
  exact ⟨digitPartitioning_of_primePairwiseMatchCount_eq_zero hlength,
    primePairwiseMatchCount_eq_zero_of_digitPartitioning hp hpb⟩

/-- The manuscript's zero-pairwise-alignment proposition, proved for every
positive synchronized window and hence for the order-length window it uses. -/
theorem primePairwiseAlignment_eq_zero_iff_digitPartitioning
    {b p length : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpb : ¬p ∣ b) (hlength : 0 < length) :
    primePairwiseAlignment b p length = 0 ↔ DigitPartitioning b p := by
  have hden : chooseTwoMass ((p : ℚ) - 1) * length ≠ 0 := by
    unfold chooseTwoMass
    have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp3
    have hlq : (0 : ℚ) < length := by exact_mod_cast hlength
    have hfirst : (0 : ℚ) < (p : ℚ) - 1 := by nlinarith
    have hsecond : (0 : ℚ) < ((p : ℚ) - 1) - 1 := by nlinarith
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero hfirst.ne' hsecond.ne') (by norm_num)) hlq.ne'
  rw [primePairwiseAlignment, div_eq_zero_iff]
  rw [or_iff_left hden]
  norm_cast
  exact primePairwiseMatchCount_eq_zero_iff_digitPartitioning hp hpb hlength

end NField.Alignment.CoherenceDecomposition
