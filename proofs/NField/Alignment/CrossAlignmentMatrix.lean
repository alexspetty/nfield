/-
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Circulant
import NField.Alignment.CoherenceDecomposition

/-!
# The cross-alignment matrix

Reusable formal core for the Lean companion to "The Cross-Alignment Matrix".

The development keeps three logically different layers separate.

* `crossAlignmentGram` records the intrinsic Gram-matrix structure and proves
  Hermitian symmetry and positive semidefiniteness without a spectral
  assumption.
* `orbitMatrix` constructs the synchronized digit matrix of a cyclic word and
  proves that it is circulant by an exact common-clock reindexing.
* `primeCrossAlignmentMatrix` uses the actual long-division digit function and
  proves the manuscript's identity characterization.

The final section contains kernel-free exact certificates for the decimal
words at thirteen and seventeen and an abstract version of the supported-lift
block decomposition.
-/

namespace NField.Alignment.CrossAlignmentMatrix

open scoped BigOperators
open NField.Alignment
open NField.Alignment.CoherenceDecomposition

/-! ## Gram and scalar-recovery identities -/

section Gram

variable {ι E : Type*}
variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The matrix of synchronized feature vectors.  The concrete feature vectors
put terminating fractions on one coordinate and digit-position pairs on
orthogonal coordinates. -/
noncomputable def crossAlignmentGram (v : ι → E) : Matrix ι ι ℝ :=
  Matrix.gram ℝ v

/-- The synchronized matrix is Hermitian because it is a Gram matrix. -/
theorem crossAlignmentGram_isHermitian (v : ι → E) :
    (crossAlignmentGram v).IsHermitian := by
  exact Matrix.isHermitian_gram ℝ v

/-- The synchronized matrix is positive semidefinite because it is a Gram
matrix. -/
theorem crossAlignmentGram_posSemidef [Finite ι] (v : ι → E) :
    Matrix.PosSemidef (crossAlignmentGram v) := by
  exact Matrix.posSemidef_gram ℝ v

/-- Unit feature vectors give the manuscript's unit diagonal. -/
theorem crossAlignmentGram_apply_self (v : ι → E) (i : ι) :
    crossAlignmentGram v i i = ‖v i‖ ^ 2 := by
  simp [crossAlignmentGram, Matrix.gram_apply]

/-- Mean off-diagonal recovery in ordered-pair form.  This is the matrix
identity behind the manuscript's formula for pairwise alignment. -/
theorem sum_all_sub_diagonal
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (∑ i, ∑ j, A i j) - Matrix.trace A =
      ∑ i, ∑ j ∈ Finset.univ.erase i, A i j := by
  classical
  have hsplit :
      (∑ i, ∑ j, A i j) = Matrix.trace A +
        ∑ i, ∑ j ∈ Finset.univ.erase i, A i j := by
    rw [Matrix.trace, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm]
    exact (Finset.sum_erase_add Finset.univ (fun j => A i j)
      (Finset.mem_univ i)).symm
  linarith

end Gram

/-! ## Exact cyclic common-clock reduction -/

section Cyclic

variable {G κ : Type*} [Fintype G] [AddCommGroup G]
variable [DecidableEq κ]

/-- Unnormalized cyclic equality cross-correlation. -/
def crossCorrelation (left right : G → κ) (shift : G) : ℕ :=
  ∑ t : G, if left (t + shift) = right t then 1 else 0

/-- The synchronized digit-match count for orbit phases `r` and `s`. -/
def orbitMatchCount (left right : G → κ) (r s : G) : ℕ :=
  ∑ t : G, if left (t + r) = right (t + s) then 1 else 0

/-- Putting both rows on one cyclic clock converts their comparison into a
cross-correlation depending only on the phase difference. -/
theorem orbitMatchCount_eq_crossCorrelation
    (left right : G → κ) (r s : G) :
    orbitMatchCount left right r s = crossCorrelation left right (r - s) := by
  classical
  unfold orbitMatchCount crossCorrelation
  apply Fintype.sum_equiv (Equiv.addRight s)
  intro t
  change (if left (t + r) = right (t + s) then 1 else 0) =
    if left ((t + s) + (r - s)) = right (t + s) then 1 else 0
  rw [show (t + s) + (r - s) = t + r by abel]

/-- Rational synchronized cross-alignment of two cyclic digit words. -/
def orbitMatrix (left right : G → κ) : Matrix G G ℚ :=
  fun r s => (orbitMatchCount left right r s : ℚ) / Fintype.card G

/-- Every coset-to-coset block is circulant. -/
theorem orbitMatrix_eq_circulant (left right : G → κ) :
    orbitMatrix left right = Matrix.circulant
      (fun shift => (crossCorrelation left right shift : ℚ) / Fintype.card G) := by
  ext r s
  simp only [orbitMatrix, Matrix.circulant_apply]
  rw [orbitMatchCount_eq_crossCorrelation]

/-- Reversing the two words transposes a synchronized orbit block. -/
theorem orbitMatrix_transpose (left right : G → κ) :
    (orbitMatrix left right).transpose = orbitMatrix right left := by
  ext r s
  simp only [Matrix.transpose_apply, orbitMatrix, orbitMatchCount]
  have hsum :
      (∑ t : G, if left (t + s) = right (t + r) then 1 else 0) =
        ∑ t : G, if right (t + r) = left (t + s) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : left (t + s) = right (t + r)
    · rw [if_pos h, if_pos h.symm]
    · have h' : right (t + r) ≠ left (t + s) := Ne.symm h
      rw [if_neg h, if_neg h']
  exact congrArg (fun z : ℕ => (z : ℚ) / Fintype.card G) hsum

variable [Fintype κ]

/-- One-hot position-and-digit feature vector for a cyclic word phase. -/
noncomputable def orbitFeature (word : G → κ) (r : G) :
    EuclideanSpace ℝ (G × κ) :=
  WithLp.toLp 2 fun td => if word (td.1 + r) = td.2 then 1 else 0

/-- The real normalized orbit matrix, now constructed from the manuscript's
concrete one-hot digit feature vectors. -/
noncomputable def orbitMatrixReal (word : G → κ) : Matrix G G ℝ :=
  ((Fintype.card G : ℝ)⁻¹) • Matrix.gram ℝ (orbitFeature word)

/-- The one-hot Gram entry is exactly the unnormalized digit-match count. -/
theorem inner_orbitFeature (word : G → κ) (r s : G) :
    inner ℝ (orbitFeature word r) (orbitFeature word s) =
      orbitMatchCount word word r s := by
  classical
  simp [orbitFeature, orbitMatchCount,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_prod_type]
  congr 1
  ext t
  simp [eq_comm]

/-- Entrywise, the concrete Gram construction is the synchronized match
proportion from the paper. -/
theorem orbitMatrixReal_apply (word : G → κ) (r s : G) :
    orbitMatrixReal word r s =
      (orbitMatchCount word word r s : ℝ) / Fintype.card G := by
  simp [orbitMatrixReal, Matrix.gram_apply, inner_orbitFeature,
    div_eq_inv_mul]

/-- The concrete real Gram matrix has the same circulant description as the
rational count matrix. -/
theorem orbitMatrixReal_eq_circulant (word : G → κ) :
    orbitMatrixReal word = Matrix.circulant
      (fun shift => (crossCorrelation word word shift : ℝ) /
        Fintype.card G) := by
  ext r s
  rw [orbitMatrixReal_apply, Matrix.circulant_apply,
    orbitMatchCount_eq_crossCorrelation]

/-- Every diagonal entry of a nonempty cyclic orbit matrix is one. -/
theorem orbitMatrixReal_diagonal [Nonempty G] (word : G → κ) (r : G) :
    orbitMatrixReal word r r = 1 := by
  rw [orbitMatrixReal_apply]
  simp [orbitMatchCount, Fintype.card_ne_zero]

/-- The concrete synchronized cyclic matrix is positive semidefinite. -/
theorem orbitMatrixReal_posSemidef (word : G → κ) :
    Matrix.PosSemidef (orbitMatrixReal word) := by
  apply (Matrix.posSemidef_gram ℝ (orbitFeature word)).smul
  positivity

end Cyclic

/-! ## Fourier blocks are Gram matrices -/

section FourierGram

variable {a d : Type*} [Fintype d]

/-- The manuscript's small frequency block attached to Fourier coefficients
`X`, including its exact `1 / length` normalization. -/
noncomputable def frequencyGram (length : ℕ)
    (X : a → EuclideanSpace ℂ d) : Matrix a a ℂ :=
  (length : ℂ)⁻¹ • Matrix.gram ℂ X

theorem frequencyGram_isHermitian (length : ℕ)
    (X : a → EuclideanSpace ℂ d) :
    (frequencyGram length X).IsHermitian := by
  apply (Matrix.isHermitian_gram ℂ X).smul
  simp

/-- The quadratic form of a Fourier block is an explicit norm square.  This
is the complex positive-semidefinite statement used in the manuscript. -/
theorem frequencyGram_quadratic_eq_normSq [Fintype a]
    (length : ℕ) (X : a → EuclideanSpace ℂ d) (z : a → ℂ) :
    (dotProduct (star z) (Matrix.mulVec (frequencyGram length X) z)).re =
      (length : ℝ)⁻¹ * ‖∑ i, z i • X i‖ ^ 2 := by
  rw [frequencyGram, Matrix.smul_mulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  have hfactor :
      (∑ x, star z x *
          ((length : ℂ)⁻¹ * (Matrix.gram ℂ X).mulVec z x)) =
        (length : ℂ)⁻¹ *
          ∑ x, star z x * (Matrix.gram ℂ X).mulVec z x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfactor]
  change (((length : ℂ)⁻¹ *
    dotProduct (star z) (Matrix.mulVec (Matrix.gram ℂ X) z))).re = _
  rw [Matrix.star_dotProduct_gram_mulVec]
  rw [inner_self_eq_norm_sq_to_K]
  simp
  left
  rw [← Complex.ofReal_pow]
  exact Complex.ofReal_re _

theorem frequencyGram_quadratic_nonnegative [Fintype a]
    (length : ℕ) (X : a → EuclideanSpace ℂ d) (z : a → ℂ) :
    0 ≤ (dotProduct (star z)
      (Matrix.mulVec (frequencyGram length X) z)).re := by
  rw [frequencyGram_quadratic_eq_normSq]
  positivity

/-- Entrywise form of the frequency Gram matrix. -/
theorem frequencyGram_apply (length : ℕ)
    (X : a → EuclideanSpace ℂ d) (i j : a) :
    frequencyGram length X i j =
      (length : ℂ)⁻¹ *
        ∑ digit, starRingEnd ℂ (X i digit) * X j digit := by
  simp [frequencyGram, Matrix.gram_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

end FourierGram

/-! ## The prime identity characterization -/

/-- Nonzero natural residue representatives below `p`. -/
abbrev PrimeResidue (p : ℕ) := {r : ℕ // 0 < r ∧ r < p}

/-- The actual finite synchronized prime matrix on a positive digit window. -/
def primeCrossAlignmentMatrix (b p length : ℕ) :
    Matrix (PrimeResidue p) (PrimeResidue p) ℚ :=
  fun r s => (primePairPositionMatchCount b p r s length : ℚ) / length

/-- A residue agrees with itself at every synchronized position. -/
theorem primePairPositionMatchCount_self
    (b p length : ℕ) (r : PrimeResidue p) :
    primePairPositionMatchCount b p r r length = length := by
  simp [primePairPositionMatchCount]

/-- Digit partitioning makes the normalized prime matrix the identity. -/
theorem primeCrossAlignmentMatrix_eq_one_of_digitPartitioning
    {b p length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hlength : 0 < length) :
    primeCrossAlignmentMatrix b p length = 1 := by
  classical
  ext r s
  by_cases hrs : r = s
  · subst s
    simp [primeCrossAlignmentMatrix, primePairPositionMatchCount_self,
      hlength.ne']
  · have hval : r.val ≠ s.val := by
      intro h
      exact hrs (Subtype.ext h)
    have hzero : primePairPositionMatchCount b p r s length = 0 := by
      unfold primePairPositionMatchCount
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro position _ hdigit
      exact (digitAt_separated hp hpb hdp r.property.1 r.property.2
        s.property.1 s.property.2 hval) hdigit
    simp [primeCrossAlignmentMatrix, hzero, hrs]

/-- If the normalized prime matrix is the identity, the first digit is
injective on nonzero residues. -/
theorem digitPartitioning_of_primeCrossAlignmentMatrix_eq_one
    {b p length : ℕ} (hlength : 0 < length)
    (hmatrix : primeCrossAlignmentMatrix b p length = 1) :
    DigitPartitioning b p := by
  intro r s hr0 hr hs0 hs hdigit
  by_contra hrs
  let ri : PrimeResidue p := ⟨r, hr0, hr⟩
  let si : PrimeResidue p := ⟨s, hs0, hs⟩
  have hris : ri ≠ si := by
    intro h
    exact hrs (congrArg Subtype.val h)
  have hpositive : 0 < primePairPositionMatchCount b p r s length :=
    primePairPositionMatchCount_pos_of_first_digit_eq hr hs hlength hdigit
  have hoff := congrFun (congrFun hmatrix ri) si
  simp only [primeCrossAlignmentMatrix, Matrix.one_apply, hris, if_false] at hoff
  have hlenq : (length : ℚ) ≠ 0 := by exact_mod_cast hlength.ne'
  have hcountq : (primePairPositionMatchCount b p r s length : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpositive)
  exact hcountq ((div_eq_zero_iff.mp hoff).resolve_right hlenq)

/-- Exact identity-matrix characterization on every positive common clock. -/
theorem primeCrossAlignmentMatrix_eq_one_iff_digitPartitioning
    {b p length : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hlength : 0 < length) :
    primeCrossAlignmentMatrix b p length = 1 ↔ DigitPartitioning b p := by
  exact ⟨digitPartitioning_of_primeCrossAlignmentMatrix_eq_one hlength,
    fun hdp => primeCrossAlignmentMatrix_eq_one_of_digitPartitioning
      hp hpb hdp hlength⟩

/-- The manuscript's three-way prime equivalence. -/
theorem primeCrossAlignmentMatrix_eq_one_iff_le
    {b p length : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hlength : 0 < length) :
    primeCrossAlignmentMatrix b p length = 1 ↔ p ≤ b + 1 := by
  rw [primeCrossAlignmentMatrix_eq_one_iff_digitPartitioning hp hpb hlength,
    digitPartitioning_iff hb hp hpb]

/-! ## Exact decimal word certificates -/

/-- The two length-six decimal orbit words modulo thirteen. -/
def decimalThirteenLeft : Fin 6 → Fin 10 :=
  ![0, 7, 6, 9, 2, 3]

def decimalThirteenRight : Fin 6 → Fin 10 :=
  ![1, 5, 3, 8, 4, 6]

/-- Each thirteen-word has no nontrivial self-match, while the cross-word
match count is two precisely at relative shift three. -/
theorem decimalThirteenCorrelation_certificate :
    (∀ shift : Fin 6,
      crossCorrelation decimalThirteenLeft decimalThirteenLeft shift =
        if shift = 0 then 6 else 0) ∧
    (∀ shift : Fin 6,
      crossCorrelation decimalThirteenRight decimalThirteenRight shift =
        if shift = 0 then 6 else 0) ∧
    (∀ shift : Fin 6,
      crossCorrelation decimalThirteenLeft decimalThirteenRight shift =
        if shift = 3 then 2 else 0) := by
  decide

/-- The reverse cross-correlation has the same half-period support.  Keeping
this as a separate finite certificate lets the matrix theorem below be a
short algebraic consequence of the word-level data. -/
theorem decimalThirteenReverseCorrelation_certificate :
    ∀ shift : Fin 6,
      crossCorrelation decimalThirteenRight decimalThirteenLeft shift =
        if shift = 3 then 2 else 0 := by
  decide

/-- Matrix-level form of the thirteen certificate.  The diagonal blocks are
identities and both cross blocks have value `1/3` exactly at phase difference
three. -/
theorem decimalThirteenOrbitMatrix_certificate :
    orbitMatrix decimalThirteenLeft decimalThirteenLeft = 1 ∧
    orbitMatrix decimalThirteenRight decimalThirteenRight = 1 ∧
    (∀ r s : Fin 6,
      orbitMatrix decimalThirteenLeft decimalThirteenRight r s =
        if r - s = 3 then (1 : ℚ) / 3 else 0) ∧
    (∀ r s : Fin 6,
      orbitMatrix decimalThirteenRight decimalThirteenLeft r s =
        if r - s = 3 then (1 : ℚ) / 3 else 0) := by
  rcases decimalThirteenCorrelation_certificate with ⟨hleft, hright, hcross⟩
  constructor
  · ext r s
    rw [orbitMatrix, orbitMatchCount_eq_crossCorrelation, hleft]
    by_cases hrs : r = s
    · simp [Matrix.one_apply, hrs]
    · have hsub : r - s ≠ 0 := sub_ne_zero.mpr hrs
      simp [hsub, hrs]
  constructor
  · ext r s
    rw [orbitMatrix, orbitMatchCount_eq_crossCorrelation, hright]
    by_cases hrs : r = s
    · simp [Matrix.one_apply, hrs]
    · have hsub : r - s ≠ 0 := sub_ne_zero.mpr hrs
      simp [hsub, hrs]
  constructor
  · intro r s
    rw [orbitMatrix, orbitMatchCount_eq_crossCorrelation, hcross]
    by_cases h : r - s = 3
    · simp [h]
      norm_num
    · simp [h]
  · intro r s
    rw [orbitMatrix, orbitMatchCount_eq_crossCorrelation,
      decimalThirteenReverseCorrelation_certificate]
    by_cases h : r - s = 3
    · simp [h]
      norm_num
    · simp [h]

/-- The full twelve-by-twelve decimal matrix assembled from its two orbit
words. -/
def decimalThirteenMatrix :
    Matrix (Sum (Fin 6) (Fin 6)) (Sum (Fin 6) (Fin 6)) ℚ
  | Sum.inl r, Sum.inl s =>
      orbitMatrix decimalThirteenLeft decimalThirteenLeft r s
  | Sum.inl r, Sum.inr s =>
      orbitMatrix decimalThirteenLeft decimalThirteenRight r s
  | Sum.inr r, Sum.inl s =>
      orbitMatrix decimalThirteenRight decimalThirteenLeft r s
  | Sum.inr r, Sum.inr s =>
      orbitMatrix decimalThirteenRight decimalThirteenRight r s

/-- A six-vector copied to the second coset with relative phase three. -/
def decimalThirteenPlusVector (x : Fin 6 → ℚ) :
    Sum (Fin 6) (Fin 6) → ℚ
  | Sum.inl r => x r
  | Sum.inr r => x (r + 3)

/-- The corresponding antisymmetric coset vector. -/
def decimalThirteenMinusVector (x : Fin 6 → ℚ) :
    Sum (Fin 6) (Fin 6) → ℚ
  | Sum.inl r => x r
  | Sum.inr r => -x (r + 3)

/-- The exact matrix fixture gives the `4/3` eigenvalue on every symmetric
six-dimensional branch. -/
theorem decimalThirteen_plus_eigenvector (x : Fin 6 → ℚ) :
    Matrix.mulVec decimalThirteenMatrix (decimalThirteenPlusVector x) =
      ((4 : ℚ) / 3) • decimalThirteenPlusVector x := by
  funext i
  cases i with
  | inl r =>
      fin_cases r <;>
        simp [decimalThirteenMatrix, decimalThirteenPlusVector,
          Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          orbitMatrix, orbitMatchCount, decimalThirteenLeft,
          decimalThirteenRight, Fin.sum_univ_succ] <;>
        ring
  | inr r =>
      fin_cases r <;>
        simp [decimalThirteenMatrix, decimalThirteenPlusVector,
          Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          orbitMatrix, orbitMatchCount, decimalThirteenLeft,
          decimalThirteenRight, Fin.sum_univ_succ] <;>
        ring

/-- The antisymmetric branch has the exact eigenvalue `2/3`. -/
theorem decimalThirteen_minus_eigenvector (x : Fin 6 → ℚ) :
    Matrix.mulVec decimalThirteenMatrix (decimalThirteenMinusVector x) =
      ((2 : ℚ) / 3) • decimalThirteenMinusVector x := by
  funext i
  cases i with
  | inl r =>
      fin_cases r <;>
        simp [decimalThirteenMatrix, decimalThirteenMinusVector,
          Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          orbitMatrix, orbitMatchCount, decimalThirteenLeft,
          decimalThirteenRight, Fin.sum_univ_succ] <;>
        ring
  | inr r =>
      fin_cases r <;>
        simp [decimalThirteenMatrix, decimalThirteenMinusVector,
          Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          orbitMatrix, orbitMatchCount, decimalThirteenLeft,
          decimalThirteenRight, Fin.sum_univ_succ] <;>
        ring

/-- Both parameterizations retain all six coordinates, so neither eigenbranch
collapses dimension. -/
theorem decimalThirteenPlusVector_injective :
    Function.Injective decimalThirteenPlusVector := by
  intro x y h
  funext r
  exact congrFun h (Sum.inl r)

theorem decimalThirteenMinusVector_injective :
    Function.Injective decimalThirteenMinusVector := by
  intro x y h
  funext r
  exact congrFun h (Sum.inl r)

/-- The primitive-root decimal word modulo seventeen. -/
def decimalSeventeenWord : Fin 16 → Fin 10 :=
  ![0, 5, 8, 8, 2, 3, 5, 2, 9, 4, 1, 1, 7, 6, 4, 7]

/-- Exact autocorrelation data used by the manuscript's seventeen example. -/
theorem decimalSeventeenCorrelation_certificate :
    ∀ shift : Fin 16,
      crossCorrelation decimalSeventeenWord decimalSeventeenWord shift =
        if shift = 0 then 16
        else if shift.val ∈ ([1, 3, 5, 11, 13, 15] : List ℕ) then 2 else 0 := by
  decide

/-- The entire seventeen matrix is determined by this normalized first
column together with the proved circulant reduction. -/
theorem decimalSeventeenOrbitMatrix_column_certificate :
    ∀ shift : Fin 16,
      orbitMatrix decimalSeventeenWord decimalSeventeenWord shift 0 =
        if shift = 0 then 1
        else if shift.val ∈ ([1, 3, 5, 11, 13, 15] : List ℕ)
          then (1 : ℚ) / 8 else 0 := by
  intro shift
  rw [orbitMatrix, orbitMatchCount_eq_crossCorrelation,
    decimalSeventeenCorrelation_certificate]
  simp only [sub_zero]
  by_cases hzero : shift = 0
  · simp [hzero]
  · by_cases hsupport :
        shift.val ∈ ([1, 3, 5, 11, 13, 15] : List ℕ)
    · simp [hzero, hsupport]
      norm_num
    · simp [hzero, hsupport]

/-! ## Supported-lift all-ones blocks -/

/-- Indexing of the terminating block and the `p-1` nonterminating residue
blocks of size `s`. -/
abbrev SupportedBlockIndex (p s : ℕ) :=
  Sum (Fin (s - 1)) (Fin (p - 1) × Fin s)

/-- Exact block matrix from the supported-lift proposition. -/
def supportedBlockMatrix (p s : ℕ) :
    Matrix (SupportedBlockIndex p s) (SupportedBlockIndex p s) ℚ
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inr i, Sum.inr j => if i.1 = j.1 then 1 else 0
  | _, _ => 0

/-- Every supported-lift block has unit diagonal. -/
theorem supportedBlockMatrix_diagonal (p s : ℕ)
    (i : SupportedBlockIndex p s) : supportedBlockMatrix p s i i = 1 := by
  cases i <;> simp [supportedBlockMatrix]

/-- Indicator of the terminating all-ones block. -/
def terminatingBlockVector (p s : ℕ) : SupportedBlockIndex p s → ℚ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- Indicator of one nonterminating residue block. -/
def residueBlockVector (p s : ℕ) (c : Fin (p - 1)) :
    SupportedBlockIndex p s → ℚ
  | Sum.inl _ => 0
  | Sum.inr ci => if ci.1 = c then 1 else 0

/-- The terminating block direction has eigenvalue `s-1`. -/
theorem supportedBlockMatrix_terminating_eigenvector (p s : ℕ) :
    Matrix.mulVec (supportedBlockMatrix p s) (terminatingBlockVector p s) =
      ((s - 1 : ℕ) : ℚ) • terminatingBlockVector p s := by
  funext i
  cases i <;>
    simp [Matrix.mulVec, dotProduct, supportedBlockMatrix,
      terminatingBlockVector, Fintype.sum_sum_type]

/-- Each nonterminating residue-block direction has eigenvalue `s`. -/
theorem supportedBlockMatrix_residue_eigenvector
    (p s : ℕ) (c : Fin (p - 1)) :
    Matrix.mulVec (supportedBlockMatrix p s) (residueBlockVector p s c) =
      (s : ℚ) • residueBlockVector p s c := by
  funext i
  cases i with
  | inl i =>
      simp [Matrix.mulVec, dotProduct, supportedBlockMatrix,
        residueBlockVector, Fintype.sum_sum_type]
  | inr ci =>
      rcases ci with ⟨c', i⟩
      simp only [Matrix.mulVec, dotProduct, supportedBlockMatrix,
        residueBlockVector, Fintype.sum_sum_type, zero_mul,
        Finset.sum_const_zero, zero_add]
      rw [Fintype.sum_prod_type]
      by_cases h : c' = c
      · subst c'
        simp [residueBlockVector]
      · simp [residueBlockVector, h]

/-- A vector with zero sum inside every synchronized block is killed by the
supported-lift matrix.  This is the null-space mechanism behind the stated
zero-eigenvalue multiplicity. -/
theorem supportedBlockMatrix_mulVec_eq_zero
    {p s : ℕ} (v : SupportedBlockIndex p s → ℚ)
    (hterm : ∑ i : Fin (s - 1), v (Sum.inl i) = 0)
    (hclass : ∀ c : Fin (p - 1),
      ∑ i : Fin s, v (Sum.inr (c, i)) = 0) :
    Matrix.mulVec (supportedBlockMatrix p s) v = 0 := by
  funext i
  cases i with
  | inl i =>
      simp [Matrix.mulVec, dotProduct, supportedBlockMatrix, hterm]
  | inr ci =>
      rcases ci with ⟨c, i⟩
      simp only [Matrix.mulVec, dotProduct, supportedBlockMatrix,
        Fintype.sum_sum_type, zero_mul]
      simp only [Finset.sum_const_zero, zero_add]
      rw [Fintype.sum_prod_type]
      simp [hclass]

end NField.Alignment.CrossAlignmentMatrix
