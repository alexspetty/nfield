/-
Author: Alexander S. Petty
-/

import NField.Alignment.CoherenceDecomposition
import NField.Alignment.SupportedRoughDecomposition

/-!
# Synchronized pairwise alignment

Literal finite sample spaces and arithmetic certificates for synchronized
pairwise alignment.  The definitions below model the distinct unordered
numerator pairs and every digit position in the common window.  The prime-core
formula is therefore derived from the manuscript's finite mean, rather than
introduced as a closed form.
-/

namespace NField.Alignment.SynchronizedPairwiseAlignment

open Filter
open NField.Alignment
open NField.Alignment.CoherenceDecomposition
open NField.Alignment.ThreeTier
open NField.Golden

/-- Positive numerators in the field with denominator `p * m`. -/
noncomputable def positiveNumerators (p m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (p * m)).filter (fun k => 0 < k)

/-- The positive numerators in a fixed residue class modulo `p`. -/
noncomputable def numeratorResidueClass (p m r : ℕ) : Finset ℕ := by
  classical
  exact (positiveNumerators p m).filter (fun k => k % p = r)

/-- Distinct unordered pairs of positive field numerators. -/
noncomputable def numeratorPairs (p m : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (positiveNumerators p m).powersetCard 2

/-- Every member of an unordered pair belongs to one residue class. -/
def PairHasSingleResidue (p : ℕ) (A : Finset ℕ) : Prop :=
  ∀ j ∈ A, ∀ k ∈ A, j % p = k % p

/-- The unordered numerator pairs contained in one residue class. -/
noncomputable def singleResiduePairs (p m : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (numeratorPairs p m).filter (PairHasSingleResidue p)

/-- A two-element numerator set agrees at one synchronized position, with the
terminating and mixed cases built into `synchronizedPairAlignedAtPosition`. -/
def pairAlignedAtPosition
    (b p u : ℕ) (A : Finset ℕ) (position : ℕ) : Prop :=
  ∀ j ∈ A, ∀ k ∈ A,
    synchronizedPairAlignedAtPosition b p u j k position

/-- Equality of two arbitrary rough-residue digit streams at one common
position. -/
def periodicPairMatchAt (b t u r s position : ℕ) : Prop :=
  periodicDigit b t u r position = periodicDigit b t u s position

/-- Number of equal synchronized digits for a pair of rough residues. -/
noncomputable def periodicPairMatchCount
    (b t u r s length : ℕ) : ℕ := by
  classical
  exact ((Finset.range length).filter
    (periodicPairMatchAt b t u r s)).card

/-- Advancing the common multiplier by one base digit advances both residue
streams by one position. -/
theorem periodicPairMatchAt_mul_base (b t u r s position : ℕ) :
    periodicPairMatchAt b t (b * u) r s position ↔
      periodicPairMatchAt b t u r s (position + 1) := by
  simp only [periodicPairMatchAt, periodicDigit, periodicResidue_mul_base]

/-- A complete rough-part period closes the equality pattern for every pair
of residue streams. -/
theorem periodicPairMatchAt_wrap {b t u r s length : ℕ}
    (hperiod : b ^ length % t = 1 % t) :
    periodicPairMatchAt b t u r s length ↔
      periodicPairMatchAt b t u r s 0 := by
  unfold periodicPairMatchAt periodicDigit
  rw [periodicResidue_wrap hperiod, periodicResidue_wrap hperiod]

/-- Rotating both streams through one place preserves their number of matches
on a complete period. -/
theorem periodicPairMatchCount_mul_base {b t u r s length : ℕ}
    (hperiod : b ^ length % t = 1 % t) :
    periodicPairMatchCount b t (b * u) r s length =
      periodicPairMatchCount b t u r s length := by
  classical
  unfold periodicPairMatchCount
  simp only [Finset.card_filter]
  simp_rw [periodicPairMatchAt_mul_base]
  let f : ℕ → ℕ := fun position =>
    if periodicPairMatchAt b t u r s position then 1 else 0
  change (∑ position ∈ Finset.range length, f (position + 1)) =
    ∑ position ∈ Finset.range length, f position
  have hshift := sum_shift_succ f length
  have hwrap : f length = f 0 := by
    unfold f
    rw [if_congr (periodicPairMatchAt_wrap hperiod) rfl rfl]
  omega

/-- Any number of simultaneous base shifts preserves the pair match count. -/
theorem periodicPairMatchCount_mul_base_pow {b t u r s length q : ℕ}
    (hperiod : b ^ length % t = 1 % t) :
    periodicPairMatchCount b t (b ^ q * u) r s length =
      periodicPairMatchCount b t u r s length := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hu : b ^ (q + 1) * u = b * (b ^ q * u) := by
        rw [pow_succ]
        ac_rfl
      rw [hu, periodicPairMatchCount_mul_base hperiod, ih]

/-- Increasing a valid common clearing depth rotates both tails and therefore
leaves every full-window pair score unchanged. -/
theorem periodicPairMatchCount_independent_of_later_clearing_depth
    {b t m D q r s length : ℕ} (hD : m ∣ b ^ D)
    (hperiod : b ^ length % t = 1 % t) :
    periodicPairMatchCount b t (clearingCofactor b m (D + q)) r s length =
      periodicPairMatchCount b t (clearingCofactor b m D) r s length := by
  rw [clearingCofactor_add hD]
  exact periodicPairMatchCount_mul_base_pow hperiod

/-- Literal total digit matches over all distinct unordered pairs and all
positions of one common synchronized window. -/
noncomputable def synchronizedPairMatchCount
    (b p m u length : ℕ) : ℕ := by
  classical
  exact (numeratorPairs p m).sum fun A =>
    ((Finset.range length).filter
      (pairAlignedAtPosition b p u A)).card

/-- Literal synchronized pairwise mean from the manuscript. -/
noncomputable def synchronizedPairwiseMean
    (b p m u length : ℕ) : ℚ :=
  (synchronizedPairMatchCount b p m u length : ℚ) /
    (((numeratorPairs p m).card * length : ℕ) : ℚ)

/-- Reference mean under the manuscript's convention that every member of an
entirely supported field receives score one. -/
noncomputable def allTerminatingReferenceMean (n : ℕ) : ℚ :=
  ((positiveNumerators n 1).sum (fun _ => (1 : ℚ))) /
    (positiveNumerators n 1).card

/-- Pairwise mean under the convention that every distinct unordered pair in
an entirely supported field receives score one. -/
noncomputable def allTerminatingPairwiseMean (n : ℕ) : ℚ :=
  ((numeratorPairs n 1).sum (fun _ => (1 : ℚ))) /
    (numeratorPairs n 1).card

/-- The zero residue class contains exactly the positive multiples of `p`, so
its size is `m - 1`. -/
theorem numeratorResidueClass_zero_card {p m : ℕ} (hp : 0 < p) :
    (numeratorResidueClass p m 0).card = m - 1 := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [numeratorResidueClass, positiveNumerators]
  have hmPos : 0 < m := Nat.pos_of_ne_zero hm
  have hzero : 0 ∈ (Finset.range (p * m)).filter (fun k => k % p = 0) := by
    simp [Nat.mul_pos hp hmPos]
  have hset : numeratorResidueClass p m 0 =
      ((Finset.range (p * m)).filter (fun k => k % p = 0)).erase 0 := by
    ext k
    simp [numeratorResidueClass, positiveNumerators]
    omega
  rw [hset, Finset.card_erase_of_mem hzero]
  rw [← Nat.count_eq_card_filter_range]
  change residueCount p 0 m - 1 = m - 1
  rw [residueCount_eq hp]

/-- Every nonzero residue class below `p` contains exactly `m` positive
numerators. -/
theorem numeratorResidueClass_nonzero_card {p m r : ℕ}
    (hr0 : r ≠ 0) (hr : r < p) :
    (numeratorResidueClass p m r).card = m := by
  classical
  have hset : numeratorResidueClass p m r =
      (Finset.range (p * m)).filter (fun k => k % p = r) := by
    ext k
    simp only [numeratorResidueClass, positiveNumerators,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hkbound, _hkpos⟩, hkmod⟩
      exact ⟨hkbound, hkmod⟩
    · rintro ⟨hkbound, hkmod⟩
      have hk0 : k ≠ 0 := by
        intro h
        subst k
        simp at hkmod
        exact hr0 hkmod.symm
      exact ⟨⟨hkbound, Nat.pos_of_ne_zero hk0⟩, hkmod⟩
  rw [hset]
  rw [← Nat.count_eq_card_filter_range]
  change residueCount p r m = m
  exact residueCount_eq hr

/-- A digit-partitioning prime turns every synchronized pair comparison into
the equality relation on numerator residue classes. -/
theorem pairAlignedAtPosition_iff_singleResidue
    {b p u position : ℕ} {A : Finset ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hu : Nat.Coprime p u) :
    pairAlignedAtPosition b p u A position ↔ PairHasSingleResidue p A := by
  constructor
  · intro h j hj k hk
    exact (synchronizedPairAlignedAtPosition_iff_same_residue
      hp hpb hdp hu).mp (h j hj k hk)
  · intro h j hj k hk
    exact (synchronizedPairAlignedAtPosition_iff_same_residue
      hp hpb hdp hu).mpr (h j hj k hk)

/-- The literal pair match count is the number of single-residue unordered
pairs times the synchronized window length. -/
theorem synchronizedPairMatchCount_eq_singleResiduePairs
    {b p m u length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hu : Nat.Coprime p u) :
    synchronizedPairMatchCount b p m u length =
      (singleResiduePairs p m).card * length := by
  classical
  unfold synchronizedPairMatchCount singleResiduePairs
  simp_rw [Finset.card_filter]
  simp_rw [pairAlignedAtPosition_iff_singleResidue hp hpb hdp hu]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  simp

/-- Pairs coming from two distinct residue classes are disjoint collections. -/
theorem residueClassPairCollections_pairwiseDisjoint (p m : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range p) : Set ℕ)
      (fun r => (numeratorResidueClass p m r).powersetCard 2) := by
  classical
  intro r hr s hs hrs
  change Disjoint
    ((numeratorResidueClass p m r).powersetCard 2)
    ((numeratorResidueClass p m s).powersetCard 2)
  rw [Finset.disjoint_left]
  intro A hAr hAs
  have hAr' := Finset.mem_powersetCard.mp hAr
  have hAs' := Finset.mem_powersetCard.mp hAs
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨k, hk⟩ := hAne
  have hkr := hAr'.1 hk
  have hks := hAs'.1 hk
  have hkr' := (Finset.mem_filter.mp hkr).2
  have hks' := (Finset.mem_filter.mp hks).2
  exact hrs (hkr'.symm.trans hks')

/-- The single-residue pair set is exactly the disjoint union of the
two-element subsets of the individual residue classes. -/
theorem singleResiduePairs_eq_biUnion (p m : ℕ) (hp : 0 < p) :
    singleResiduePairs p m =
      (Finset.range p).biUnion fun r =>
        (numeratorResidueClass p m r).powersetCard 2 := by
  classical
  ext A
  constructor
  · intro hA
    have hA' := Finset.mem_filter.mp hA
    have hpair := Finset.mem_powersetCard.mp hA'.1
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hAne
    let r := j % p
    have hr : r < p := Nat.mod_lt j hp
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_range.mpr hr, ?_⟩
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hpair.2⟩
    intro k hk
    apply Finset.mem_filter.mpr
    exact ⟨hpair.1 hk, (hA'.2 k hk j hj).trans rfl⟩
  · intro hA
    obtain ⟨r, hr, hAr⟩ := Finset.mem_biUnion.mp hA
    have hAr' := Finset.mem_powersetCard.mp hAr
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨fun k hk => (Finset.mem_filter.mp (hAr'.1 hk)).1, hAr'.2⟩
    · intro j hj k hk
      have hjr := (Finset.mem_filter.mp (hAr'.1 hj)).2
      have hkr := (Finset.mem_filter.mp (hAr'.1 hk)).2
      exact hjr.trans hkr.symm

/-- Exact number of distinct unordered pairs whose numerators lie in one
residue class. -/
theorem singleResiduePairs_card {p m : ℕ} (hp : 1 < p) :
    (singleResiduePairs p m).card =
      Nat.choose (m - 1) 2 + (p - 1) * Nat.choose m 2 := by
  classical
  rw [singleResiduePairs_eq_biUnion p m (by omega),
    Finset.card_biUnion (residueClassPairCollections_pairwiseDisjoint p m)]
  simp_rw [Finset.card_powersetCard]
  have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_erase_add _ _ hzero]
  rw [numeratorResidueClass_zero_card (by omega)]
  have hconst : ∀ r ∈ (Finset.range p).erase 0,
      Nat.choose (numeratorResidueClass p m r).card 2 = Nat.choose m 2 := by
    intro r hr
    have hrange := (Finset.mem_erase.mp hr).2
    have hr0 := (Finset.mem_erase.mp hr).1
    rw [numeratorResidueClass_nonzero_card hr0 (Finset.mem_range.mp hrange)]
  rw [Finset.sum_const_nat hconst]
  rw [Finset.card_erase_of_mem hzero, Finset.card_range]
  omega

/-- The complete unordered pair sample space has the expected binomial
cardinality. -/
theorem numeratorPairs_card (p m : ℕ) :
    (numeratorPairs p m).card = Nat.choose (p * m - 1) 2 := by
  classical
  rw [numeratorPairs, Finset.card_powersetCard]
  congr 1
  unfold positiveNumerators
  by_cases hpm : p * m = 0
  · simp [hpm]
  · have hzero : 0 ∈ Finset.range (p * m) := by simp [Nat.pos_of_ne_zero hpm]
    have hset : (Finset.range (p * m)).filter (fun k => 0 < k) =
        (Finset.range (p * m)).erase 0 := by
      ext k
      simp
      omega
    rw [hset, Finset.card_erase_of_mem hzero, Finset.card_range]

/-- The entirely terminating reference sample contains `n-1` fractions. -/
theorem positiveNumerators_card (n : ℕ) :
    (positiveNumerators n 1).card = n - 1 := by
  unfold positiveNumerators
  simp only [Nat.mul_one]
  by_cases hn : n = 0
  · simp [hn]
  · have hzero : 0 ∈ Finset.range n := by simp [Nat.pos_of_ne_zero hn]
    have hset : (Finset.range n).filter (fun k => 0 < k) =
        (Finset.range n).erase 0 := by
      ext k
      simp
      omega
    rw [hset, Finset.card_erase_of_mem hzero, Finset.card_range]

/-- Casting a two-element binomial coefficient to the rationals gives the
usual quadratic pair mass. -/
theorem natCast_choose_two (n : ℕ) :
    ((Nat.choose n 2 : ℕ) : ℚ) = chooseTwoMass n := by
  cases n with
  | zero => norm_num [chooseTwoMass]
  | succ n =>
  rw [Nat.choose_two_right, Nat.cast_div]
  · unfold chooseTwoMass
    push_cast [Nat.cast_sub (by omega : 1 ≤ n + 1)]
    ring
  · exact (Nat.even_mul_pred_self (n + 1)).two_dvd
  · norm_num

/-- The literal synchronized pairwise mean has the manuscript's exact
prime-core value. -/
theorem synchronizedPairwiseMean_eq
    {b p m u length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hu : Nat.Coprime p u)
    (hpm : 3 ≤ p * m) (hlength : 0 < length) :
    synchronizedPairwiseMean b p m u length =
      ((m : ℚ) - 1) / ((p : ℚ) * m - 1) := by
  have hm : 1 ≤ m := by
    have hm0 : m ≠ 0 := by intro h; subst m; norm_num at hpm
    omega
  have hlengthQ : (length : ℚ) ≠ 0 := by exact_mod_cast hlength.ne'
  have hpairCast : ((singleResiduePairs p m).card : ℚ) =
      primeCorePairMass p m := by
    rw [singleResiduePairs_card hp.one_lt]
    push_cast
    rw [natCast_choose_two, natCast_choose_two]
    unfold primeCorePairMass
    push_cast [Nat.cast_sub hm, Nat.cast_sub hp.one_le]
    rfl
  have htotalCast : ((numeratorPairs p m).card : ℚ) =
      primeCoreTotalPairMass p m := by
    rw [numeratorPairs_card, natCast_choose_two]
    unfold primeCoreTotalPairMass
    push_cast [Nat.cast_sub (by omega : 1 ≤ p * m)]
    rfl
  rw [synchronizedPairwiseMean,
    synchronizedPairMatchCount_eq_singleResiduePairs hp hpb hdp hu]
  push_cast
  rw [hpairCast, htotalCast]
  calc
    primeCorePairMass p m * length /
          (primeCoreTotalPairMass p m * length) =
        pairwiseAlignmentFormula p m := by
      unfold pairwiseAlignmentFormula
      field_simp [hlengthQ]
    _ = ((m : ℚ) - 1) / ((p : ℚ) * m - 1) :=
      pairwiseAlignmentFormula_eq hpm

/-- Any two valid clearing depths give the same literal prime-core pairwise
mean. -/
theorem synchronizedPairwiseMean_independent_of_clearing_depth
    {b p m D E length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hD : m ∣ b ^ D) (hE : m ∣ b ^ E)
    (hpm : 3 ≤ p * m) (hlength : 0 < length) :
    synchronizedPairwiseMean b p m (clearingCofactor b m D) length =
      synchronizedPairwiseMean b p m (clearingCofactor b m E) length := by
  rw [synchronizedPairwiseMean_eq hp hpb hdp
      (prime_coprime_clearingCofactor hp hpb hD) hpm hlength,
    synchronizedPairwiseMean_eq hp hpb hdp
      (prime_coprime_clearingCofactor hp hpb hE) hpm hlength]

/-- The exact prime-core reference, pairwise, and focused statistics are
computed from their literal synchronized finite means. -/
theorem literalPrimeCoreDecomposition
    {b p m D length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hD : m ∣ b ^ D)
    (hm : 1 ≤ m) (hpm : 3 ≤ p * m) (hlength : 0 < length) :
    synchronizedRepetendAlignment b p m (clearingCofactor b m D) length =
        ((2 : ℚ) * m - 1) / ((p : ℚ) * m - 1) ∧
      synchronizedPairwiseMean b p m (clearingCofactor b m D) length =
        ((m : ℚ) - 1) / ((p : ℚ) * m - 1) ∧
      synchronizedRepetendAlignment b p m (clearingCofactor b m D) length -
          synchronizedPairwiseMean b p m (clearingCofactor b m D) length =
        (m : ℚ) / ((p : ℚ) * m - 1) := by
  have hu := prime_coprime_clearingCofactor hp hpb hD
  have href := synchronizedRepetendAlignment_eq_alignmentFormula
    hp hpb hdp hu hm hlength
  have hpair := synchronizedPairwiseMean_eq hp hpb hdp hu hpm hlength
  refine ⟨?_, hpair, ?_⟩
  · rw [href]
    rfl
  · rw [href, hpair]
    unfold DeficitLattice.alignmentFormula
    have hden : (p : ℚ) * m - 1 ≠ 0 := by
      have hpmQ : (3 : ℚ) ≤ (p : ℚ) * m := by exact_mod_cast hpm
      nlinarith
    field_simp
    ring

/-- The pairwise term is exactly the normalized terminating contribution to
the reference statistic, while the focused term is the normalized reference
residue class. -/
theorem normalizedClassContributionInterpretation
    {p m : ℕ} (hp : Nat.Prime p) (hm : 1 ≤ m) (hpm : 3 ≤ p * m) :
    ((terminatingNumeratorCount p m : ℕ) : ℚ) /
          (((p * m - 1 : ℕ) : ℚ)) = pairwiseAlignmentFormula p m ∧
      ((residueCount p 1 m : ℕ) : ℚ) /
          (((p * m - 1 : ℕ) : ℚ)) = focusedAlignmentFormula p m := by
  rw [terminatingNumeratorCount_eq hp.pos, residueCount_eq hp.one_lt,
    pairwiseAlignmentFormula_eq hpm, focusedAlignmentFormula_eq hpm]
  push_cast [Nat.cast_sub hm, Nat.cast_sub (by omega : 1 ≤ p * m)]
  exact ⟨rfl, rfl⟩

/-- Supported and rough parts give the manuscript's canonical factorization,
including maximality and uniqueness. -/
theorem canonicalSupportedRoughFactorization {b n : ℕ} (hn : 0 < n) :
    Supported b (supportedPart b n) ∧
      supportedPart b n ∣ n ∧
      roughPart b n * supportedPart b n = n ∧
      Nat.Coprime (roughPart b n) b ∧
      (∀ d : ℕ, Supported b d → d ∣ n → d ≤ supportedPart b n) ∧
      (∀ q s : ℕ, n = q * s → 0 < q → 0 < s → Supported b s →
        Nat.Coprime q b → supportedPart b n = s ∧ roughPart b n = q) := by
  exact ⟨supportedPart_supported hn, supportedPart_dvd hn,
    roughPart_mul_supportedPart hn, roughPart_coprime_base hn,
    fun d hd hdn => supportedDivisor_le_supportedPart hn hd hdn,
    fun q s hqs hq hs hsupported hcop =>
      supported_coprime_decomposition_unique hqs hq hs hsupported hcop⟩

/-- The manuscript's digit-partitioning definition is equivalent to its sharp
prime boundary. -/
theorem digitPartitioningPrime_iff_le_base_succ
    {b p : ℕ} (hb : 2 ≤ b) (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    DigitPartitioning b p ↔ p ≤ b + 1 :=
  digitPartitioning_iff (by omega) hp hpb

/-- The three closed forms tend to the three manuscript limits along every
unbounded sequence of supported scales. -/
theorem supportedScaleLimits
    {b p : ℕ} (hp : Nat.Prime p) {s : ℕ → ℕ}
    (_hsupported : ∀ k, Supported b (s k)) (hs : Tendsto s atTop atTop) :
    Tendsto (fun k => alignmentFormulaReal p (s k)) atTop
        (nhds ((2 : ℝ) / p)) ∧
      Tendsto (fun k => focusedAlignmentFormulaReal p (s k)) atTop
        (nhds ((1 : ℝ) / p)) ∧
      Tendsto (fun k => pairwiseAlignmentFormulaReal p (s k)) atTop
        (nhds ((1 : ℝ) / p)) := by
  exact ⟨(referenceAlignmentFormulaReal_tendsto hp.pos).comp hs,
    (focusedAlignmentFormulaReal_tendsto hp.pos).comp hs,
    (pairwiseAlignmentFormulaReal_tendsto hp.pos).comp hs⟩

/-- Exact finite deficit from the limiting reference alignment. -/
theorem referenceLimit_sub_finite {p m : ℕ} (hp : 3 ≤ p) (hm : 1 ≤ m) :
    (2 : ℝ) / p - alignmentFormulaReal p m =
      (p - 2 : ℝ) / (p * ((p : ℝ) * m - 1)) ∧
      0 < (2 : ℝ) / p - alignmentFormulaReal p m := by
  have hpQ : (0 : ℝ) < p := by positivity
  have hmQ : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpThree : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hproduct : (3 : ℝ) ≤ (p : ℝ) * m := by
    nlinarith [mul_le_mul_of_nonneg_left hmQ hpQ.le]
  have hden : (0 : ℝ) < (p : ℝ) * m - 1 := by nlinarith
  constructor
  · rw [alignmentFormulaReal]
    field_simp
    ring
  · rw [alignmentFormulaReal]
    have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
    rw [sub_pos]
    apply (div_lt_div_iff₀ hden hpQ).2
    nlinarith

/-- Every finite prime-core focused value lies below the reciprocal-golden
threshold, including the admissible prime-two case. -/
theorem focusedAlwaysBelowGolden
    {b p m : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hsupported : Supported b m) (hpm : 3 ≤ p * m) :
    focusedAlignmentFormulaReal p m < goldenReciprocal := by
  by_cases hp2 : p = 2
  · subst p
    exact primeTwo_supported_focused_below_golden hpb hsupported hpm
  · exact focusedAlignment_below_golden_of_three_le
      (by have := hp.two_le; omega) (by
        have hm0 : m ≠ 0 := by intro h; subst m; norm_num at hpm
        omega)

/-- For prime cores at least five, both finite statistics are already below
the reciprocal-golden threshold. -/
theorem largePrimeFiniteThresholdCertificate
    {p m : ℕ} (_hp : Nat.Prime p) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    0 ≤ focusedAlignmentFormulaReal p m ∧
      focusedAlignmentFormulaReal p m ≤ alignmentFormulaReal p m ∧
      alignmentFormulaReal p m < (2 : ℝ) / p ∧
      (2 : ℝ) / p ≤ (2 : ℝ) / 5 ∧
      (2 : ℝ) / 5 < goldenReciprocal := by
  have hpm : 3 ≤ p * m := by nlinarith
  have hbounds := focused_nonnegative_and_le_reference hpm
  have hdeficit := referenceLimit_sub_finite (p := p) (by omega) hm
  refine ⟨hbounds.1, hbounds.2, by linarith, ?_,
    two_fifths_lt_goldenReciprocal⟩
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    (by exact_mod_cast hp5)

/-- The two limiting levels have width exactly `1/p`. -/
theorem limitingGapWidth {p : ℕ} (hp : 0 < p) :
    (2 : ℝ) / p - (1 : ℝ) / p = (1 : ℝ) / p := by
  have hpQ : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  norm_num

/-- The manuscript's structural gap inequality is exactly the upper half of
the reciprocal-golden crossing. -/
theorem gapContributionChangesThreshold_iff {p : ℕ} (hp : 0 < p) :
    (1 : ℝ) / p > goldenReciprocal - (1 : ℝ) / p ↔
      (p : ℝ) < 2 * goldenRatio := by
  rw [goldenReciprocal_eq_inv]
  have hpQ : (0 : ℝ) < p := by exact_mod_cast hp
  have hphi : (0 : ℝ) < goldenRatio := goldenRatio_pos
  constructor
  · intro h
    have hsum : (1 : ℝ) / goldenRatio < 1 / p + 1 / p := by linarith
    have hdouble : (1 : ℝ) / p + 1 / p = 2 / p := by ring
    rw [hdouble] at hsum
    have h' : (1 : ℝ) / goldenRatio < 2 / p := hsum
    have hcross := (div_lt_div_iff₀ hphi hpQ).mp h'
    simpa using hcross
  · intro h
    have hcross : (1 : ℝ) * p < 2 * goldenRatio := by simpa using h
    have h' : (1 : ℝ) / goldenRatio < 2 / p :=
      (div_lt_div_iff₀ hphi hpQ).mpr hcross
    have hdouble : (1 : ℝ) / p + 1 / p = 2 / p := by ring
    have hsum : (1 : ℝ) / goldenRatio < 1 / p + 1 / p := by
      rw [hdouble]
      exact h'
    linarith

/-- The signed residual identity is definitional for arbitrary reference and
pairwise statistics; it makes no positivity assertion. -/
theorem signedResidual_identity (reference pairwise : ℚ) :
    reference = (reference - pairwise) + pairwise := by ring

/-- Under the all-terminating convention the literal reference and unordered
pair means are one and their focused residual is zero. -/
theorem fullyTerminatingStatistics {b n : ℕ} (hn : 3 ≤ n)
    (_hsupported : Supported b n) :
    allTerminatingReferenceMean n = 1 ∧
      allTerminatingPairwiseMean n = 1 ∧
      allTerminatingReferenceMean n - allTerminatingPairwiseMean n = 0 := by
  have hrefCard : (positiveNumerators n 1).card ≠ 0 := by
    rw [positiveNumerators_card]
    omega
  have hpairCard : (numeratorPairs n 1).card ≠ 0 := by
    rw [numeratorPairs_card]
    apply Nat.choose_ne_zero
    omega
  have href : allTerminatingReferenceMean n = 1 := by
    unfold allTerminatingReferenceMean
    simp [hrefCard]
  have hpair : allTerminatingPairwiseMean n = 1 := by
    unfold allTerminatingPairwiseMean
    simp [hpairCard]
  exact ⟨href, hpair, by rw [href, hpair]; norm_num⟩

end NField.Alignment.SynchronizedPairwiseAlignment
