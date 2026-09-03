/-
Author: Alexander S. Petty
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import NField.Alignment.CrossAlignmentMatrix

/-!
# Exact decimal orbit spectra

Title-independent exact spectral certificates for the decimal remainder words
modulo thirteen and seventeen.
-/

namespace NField.Alignment.DecimalOrbitSpectra

open scoped BigOperators
open NField.Alignment.CrossAlignmentMatrix

/-! ## The two complete six-dimensional branches modulo thirteen -/

/-- Symmetric coordinate of an arbitrary vector in the two-coset splitting. -/
def decimalThirteenSymmetricCoordinate
    (v : Sum (Fin 6) (Fin 6) → ℚ) (r : Fin 6) : ℚ :=
  (v (Sum.inl r) + v (Sum.inr (r + 3))) / 2

/-- Antisymmetric coordinate of an arbitrary vector in the two-coset
splitting. -/
def decimalThirteenAntisymmetricCoordinate
    (v : Sum (Fin 6) (Fin 6) → ℚ) (r : Fin 6) : ℚ :=
  (v (Sum.inl r) - v (Sum.inr (r + 3))) / 2

/-- Every twelve-vector is the sum of one symmetric and one antisymmetric
branch vector. -/
theorem decimalThirteen_branch_decomposition
    (v : Sum (Fin 6) (Fin 6) → ℚ) :
    v = decimalThirteenPlusVector (decimalThirteenSymmetricCoordinate v) +
      decimalThirteenMinusVector
        (decimalThirteenAntisymmetricCoordinate v) := by
  funext i
  cases i with
  | inl r =>
      simp [decimalThirteenPlusVector, decimalThirteenMinusVector,
        decimalThirteenSymmetricCoordinate,
        decimalThirteenAntisymmetricCoordinate]
      ring
  | inr r =>
      fin_cases r <;>
        simp [decimalThirteenPlusVector, decimalThirteenMinusVector,
          decimalThirteenSymmetricCoordinate,
          decimalThirteenAntisymmetricCoordinate] <;>
        ring

/-- The two parameterized branches intersect only at zero. -/
theorem decimalThirteen_branches_disjoint
    {x y : Fin 6 → ℚ}
    (h : decimalThirteenPlusVector x = decimalThirteenMinusVector y) :
    x = 0 ∧ y = 0 := by
  have hleft (r : Fin 6) : x r = y r := by
    simpa [decimalThirteenPlusVector, decimalThirteenMinusVector] using
      congrFun h (Sum.inl r)
  have hright (r : Fin 6) : x (r + 3) = -y (r + 3) := by
    simpa [decimalThirteenPlusVector, decimalThirteenMinusVector] using
      congrFun h (Sum.inr r)
  have hxzero : x = 0 := by
    funext r
    show x r = (0 : ℚ)
    have hneg : x r = -y r := by
      have := hright (r + 3)
      fin_cases r <;> simpa using this
    linarith [hleft r]
  constructor
  · exact hxzero
  · funext r
    show y r = (0 : ℚ)
    have hx : x r = 0 := congrFun hxzero r
    rw [← hleft r]
    exact hx

/-- The exact prime-thirteen spectral decomposition.  The two injective
six-parameter branches span the full twelve-dimensional space, have trivial
intersection, and carry eigenvalues `4/3` and `2/3`. -/
theorem decimalThirteenSpectrum_complete :
    (∀ x : Fin 6 → ℚ,
      Matrix.mulVec decimalThirteenMatrix (decimalThirteenPlusVector x) =
        ((4 : ℚ) / 3) • decimalThirteenPlusVector x) ∧
    (∀ x : Fin 6 → ℚ,
      Matrix.mulVec decimalThirteenMatrix (decimalThirteenMinusVector x) =
        ((2 : ℚ) / 3) • decimalThirteenMinusVector x) ∧
    Function.Injective decimalThirteenPlusVector ∧
    Function.Injective decimalThirteenMinusVector ∧
    (∀ v : Sum (Fin 6) (Fin 6) → ℚ,
      v = decimalThirteenPlusVector
          (decimalThirteenSymmetricCoordinate v) +
        decimalThirteenMinusVector
          (decimalThirteenAntisymmetricCoordinate v)) ∧
    (∀ x y : Fin 6 → ℚ,
      decimalThirteenPlusVector x = decimalThirteenMinusVector y →
        x = 0 ∧ y = 0) := by
  exact ⟨decimalThirteen_plus_eigenvector,
    decimalThirteen_minus_eigenvector,
    decimalThirteenPlusVector_injective,
    decimalThirteenMinusVector_injective,
    decimalThirteen_branch_decomposition,
    fun _ _ => decimalThirteen_branches_disjoint⟩

/-! ## The exact harmonic values modulo seventeen -/

/-- The real value produced by the autocorrelation transform at a decimal
frequency modulo seventeen. -/
noncomputable def decimalSeventeenHarmonicValue (j : ℕ) : ℝ :=
  1 + (1 / 4 : ℝ) *
    (Real.cos (Real.pi * j / 8) +
      Real.cos (3 * Real.pi * j / 8) +
      Real.cos (5 * Real.pi * j / 8))

/-- The nine values printed in increasing order. -/
noncomputable def decimalSeventeenOrderedValues : Fin 9 → ℝ :=
  ![(1 : ℝ) / 4,
    1 - (1 / 4 : ℝ) * Real.cos (Real.pi / 8),
    1 - Real.sqrt 2 / 8,
    1 - (1 / 4 : ℝ) * Real.cos (3 * Real.pi / 8),
    1,
    1 + (1 / 4 : ℝ) * Real.cos (3 * Real.pi / 8),
    1 + Real.sqrt 2 / 8,
    1 + (1 / 4 : ℝ) * Real.cos (Real.pi / 8),
    (7 : ℝ) / 4]

/-- The unordered set of the nine printed values. -/
noncomputable def decimalSeventeenDistinctValues : Finset ℝ :=
  Finset.univ.image decimalSeventeenOrderedValues

theorem decimalSeventeenHarmonicValue_zero :
    decimalSeventeenHarmonicValue 0 = (7 : ℝ) / 4 := by
  norm_num [decimalSeventeenHarmonicValue]

theorem decimalSeventeenHarmonicValue_one :
    decimalSeventeenHarmonicValue 1 =
      1 + (1 / 4 : ℝ) * Real.cos (Real.pi / 8) := by
  have h5 : Real.cos (5 * Real.pi / 8) =
      -Real.cos (3 * Real.pi / 8) := by
    rw [show 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 by ring,
      Real.cos_pi_sub]
  ring_nf at h5
  norm_num [decimalSeventeenHarmonicValue]
  ring_nf
  rw [h5]
  ring

theorem decimalSeventeenHarmonicValue_two :
    decimalSeventeenHarmonicValue 2 = 1 - Real.sqrt 2 / 8 := by
  have h3 : Real.cos (3 * Real.pi / 4) =
      -Real.cos (Real.pi / 4) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub]
  have h5 : Real.cos (5 * Real.pi / 4) =
      -Real.cos (Real.pi / 4) := by
    rw [show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring,
      Real.cos_add_pi]
  ring_nf at h3 h5
  have hquarter : Real.cos (Real.pi * (1 / 4)) = Real.sqrt 2 / 2 := by
    rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring,
      Real.cos_pi_div_four]
  norm_num [decimalSeventeenHarmonicValue]
  ring_nf
  rw [h3, h5, hquarter]
  ring

theorem decimalSeventeenHarmonicValue_three :
    decimalSeventeenHarmonicValue 3 =
      1 + (1 / 4 : ℝ) * Real.cos (3 * Real.pi / 8) := by
  have h9 : Real.cos (9 * Real.pi / 8) =
      -Real.cos (Real.pi / 8) := by
    rw [show 9 * Real.pi / 8 = Real.pi / 8 + Real.pi by ring,
      Real.cos_add_pi]
  have h15 : Real.cos (15 * Real.pi / 8) =
      Real.cos (Real.pi / 8) := by
    rw [show 15 * Real.pi / 8 = 2 * Real.pi - Real.pi / 8 by ring,
      Real.cos_two_pi_sub]
  ring_nf at h9 h15
  norm_num [decimalSeventeenHarmonicValue]
  ring_nf
  rw [h9, h15]
  ring

theorem decimalSeventeenHarmonicValue_four :
    decimalSeventeenHarmonicValue 4 = 1 := by
  have h3 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  have h5 : Real.cos (5 * Real.pi / 2) = 0 := by
    rw [show 5 * Real.pi / 2 = Real.pi / 2 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_div_two]
  ring_nf at h3 h5
  have hhalf : Real.cos (Real.pi * (1 / 2)) = 0 := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
  norm_num [decimalSeventeenHarmonicValue]
  ring_nf
  rw [h3, h5, hhalf]
  ring

theorem decimalSeventeenHarmonicValue_five :
    decimalSeventeenHarmonicValue 5 =
      1 - (1 / 4 : ℝ) * Real.cos (3 * Real.pi / 8) := by
  have h5 : Real.cos (5 * Real.pi / 8) =
      -Real.cos (3 * Real.pi / 8) := by
    rw [show 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 by ring,
      Real.cos_pi_sub]
  have h15 : Real.cos (15 * Real.pi / 8) =
      Real.cos (Real.pi / 8) := by
    rw [show 15 * Real.pi / 8 = 2 * Real.pi - Real.pi / 8 by ring,
      Real.cos_two_pi_sub]
  have h25 : Real.cos (25 * Real.pi / 8) =
      -Real.cos (Real.pi / 8) := by
    rw [show 25 * Real.pi / 8 = (Real.pi / 8 + Real.pi) +
        2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_add_pi]
  ring_nf at h5 h15 h25
  norm_num [decimalSeventeenHarmonicValue]
  ring_nf
  rw [h5, h15, h25]
  ring

theorem decimalSeventeenHarmonicValue_six :
    decimalSeventeenHarmonicValue 6 = 1 + Real.sqrt 2 / 8 := by
  have h3 : Real.cos (3 * Real.pi / 4) =
      -Real.cos (Real.pi / 4) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub]
  have h9 : Real.cos (9 * Real.pi / 4) =
      Real.cos (Real.pi / 4) := by
    rw [show 9 * Real.pi / 4 = Real.pi / 4 + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  have h15 : Real.cos (15 * Real.pi / 4) =
      Real.cos (Real.pi / 4) := by
    rw [show 15 * Real.pi / 4 = (2 * Real.pi - Real.pi / 4) +
        2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_two_pi_sub]
  ring_nf at h3 h9 h15
  have hquarter : Real.cos (Real.pi * (1 / 4)) = Real.sqrt 2 / 2 := by
    rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring,
      Real.cos_pi_div_four]
  norm_num [decimalSeventeenHarmonicValue]
  ring_nf
  rw [h3, h9, h15, hquarter]
  ring

theorem decimalSeventeenHarmonicValue_seven :
    decimalSeventeenHarmonicValue 7 =
      1 - (1 / 4 : ℝ) * Real.cos (Real.pi / 8) := by
  have h7 : Real.cos (7 * Real.pi / 8) =
      -Real.cos (Real.pi / 8) := by
    rw [show 7 * Real.pi / 8 = Real.pi - Real.pi / 8 by ring,
      Real.cos_pi_sub]
  have h21 : Real.cos (21 * Real.pi / 8) =
      -Real.cos (3 * Real.pi / 8) := by
    rw [show 21 * Real.pi / 8 = (Real.pi - 3 * Real.pi / 8) +
        2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_sub]
  have h35 : Real.cos (35 * Real.pi / 8) =
      Real.cos (3 * Real.pi / 8) := by
    rw [show 35 * Real.pi / 8 = (3 * Real.pi / 8 + 2 * Real.pi) +
        2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_add_two_pi]
  ring_nf at h7 h21 h35
  have heighth : Real.cos (Real.pi * (1 / 8)) =
      Real.sqrt (2 + Real.sqrt 2) / 2 := by
    rw [show Real.pi * (1 / 8 : ℝ) = Real.pi / 8 by ring,
      Real.cos_pi_div_eight]
  norm_num [decimalSeventeenHarmonicValue]
  ring_nf
  rw [h7, h21, h35, heighth]
  ring

theorem decimalSeventeenHarmonicValue_eight :
    decimalSeventeenHarmonicValue 8 = (1 : ℝ) / 4 := by
  have h3 : Real.cos (3 * Real.pi) = -1 := by
    convert Real.cos_nat_mul_pi 3 using 1 <;> norm_num
  have h5 : Real.cos (5 * Real.pi) = -1 := by
    convert Real.cos_nat_mul_pi 5 using 1 <;> norm_num
  norm_num [decimalSeventeenHarmonicValue, h3, h5, Real.cos_pi]

/-- Conjugate Fourier frequencies carry the same real harmonic value. -/
theorem decimalSeventeenHarmonicValue_sub_sixteen
    (j : ℕ) (hj : j ≤ 16) :
    decimalSeventeenHarmonicValue (16 - j) =
      decimalSeventeenHarmonicValue j := by
  have hcast : (((16 - j : ℕ) : ℝ)) = 16 - (j : ℝ) := by
    norm_num [Nat.cast_sub hj]
  have h1 : Real.cos (Real.pi * (16 - j) / 8) =
      Real.cos (Real.pi * j / 8) := by
    rw [show Real.pi * (16 - (j : ℝ)) / 8 =
        (1 : ℕ) * (2 * Real.pi) - Real.pi * j / 8 by norm_num; ring]
    exact Real.cos_nat_mul_two_pi_sub (Real.pi * j / 8) 1
  have h3 : Real.cos (3 * Real.pi * (16 - j) / 8) =
      Real.cos (3 * Real.pi * j / 8) := by
    rw [show 3 * Real.pi * (16 - (j : ℝ)) / 8 =
        (3 : ℕ) * (2 * Real.pi) - 3 * Real.pi * j / 8 by norm_num; ring]
    exact Real.cos_nat_mul_two_pi_sub (3 * Real.pi * j / 8) 3
  have h5 : Real.cos (5 * Real.pi * (16 - j) / 8) =
      Real.cos (5 * Real.pi * j / 8) := by
    rw [show 5 * Real.pi * (16 - (j : ℝ)) / 8 =
        (5 : ℕ) * (2 * Real.pi) - 5 * Real.pi * j / 8 by norm_num; ring]
    exact Real.cos_nat_mul_two_pi_sub (5 * Real.pi * j / 8) 5
  unfold decimalSeventeenHarmonicValue
  rw [hcast, h1, h3, h5]

/-- The strict cosine inequalities used to separate the nine values. -/
theorem decimalSeventeen_cosine_chain :
    Real.cos (Real.pi / 8) > Real.sqrt 2 / 2 ∧
    Real.sqrt 2 / 2 > Real.cos (3 * Real.pi / 8) ∧
    Real.cos (3 * Real.pi / 8) > 0 := by
  have hp : 0 < Real.pi := Real.pi_pos
  have h18 : Real.pi / 8 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith
  have h14 : Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith
  have h38 : 3 * Real.pi / 8 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith
  have hfirst := Real.strictAntiOn_cos h18 h14 (by linarith)
  have hsecond := Real.strictAntiOn_cos h14 h38 (by linarith)
  rw [Real.cos_pi_div_four] at hfirst hsecond
  have hpositive : 0 < Real.cos (3 * Real.pi / 8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  exact ⟨hfirst, hsecond, hpositive⟩

/-- The printed values are strictly ordered and therefore genuinely distinct. -/
theorem decimalSeventeenOrderedValues_strictMono :
    StrictMono decimalSeventeenOrderedValues := by
  rcases decimalSeventeen_cosine_chain with
    ⟨hfirst, hsecond, hpositive⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp [decimalSeventeenOrderedValues]
  all_goals have hcosle := Real.cos_le_one (Real.pi / 8)
  all_goals simp only [Real.cos_pi_div_eight] at hfirst hcosle
  all_goals linarith

/-- There are exactly nine distinct printed harmonic values. -/
theorem decimalSeventeenDistinctValues_card :
    decimalSeventeenDistinctValues.card = 9 := by
  rw [decimalSeventeenDistinctValues,
    Finset.card_image_of_injective _
      decimalSeventeenOrderedValues_strictMono.injective]
  simp

/-- Assign each of the sixteen Fourier frequencies to its one of nine real
harmonic values. -/
def decimalSeventeenValueIndex : Fin 16 → Fin 9 :=
  ![8, 7, 2, 5, 4, 3, 6, 1, 0, 1, 6, 3, 4, 5, 2, 7]

theorem decimalSeventeenHarmonicValue_nine :
    decimalSeventeenHarmonicValue 9 =
      decimalSeventeenHarmonicValue 7 := by
  simpa using decimalSeventeenHarmonicValue_sub_sixteen 7 (by norm_num)

theorem decimalSeventeenHarmonicValue_ten :
    decimalSeventeenHarmonicValue 10 =
      decimalSeventeenHarmonicValue 6 := by
  simpa using decimalSeventeenHarmonicValue_sub_sixteen 6 (by norm_num)

theorem decimalSeventeenHarmonicValue_eleven :
    decimalSeventeenHarmonicValue 11 =
      decimalSeventeenHarmonicValue 5 := by
  simpa using decimalSeventeenHarmonicValue_sub_sixteen 5 (by norm_num)

theorem decimalSeventeenHarmonicValue_twelve :
    decimalSeventeenHarmonicValue 12 =
      decimalSeventeenHarmonicValue 4 := by
  simpa using decimalSeventeenHarmonicValue_sub_sixteen 4 (by norm_num)

theorem decimalSeventeenHarmonicValue_thirteen :
    decimalSeventeenHarmonicValue 13 =
      decimalSeventeenHarmonicValue 3 := by
  simpa using decimalSeventeenHarmonicValue_sub_sixteen 3 (by norm_num)

theorem decimalSeventeenHarmonicValue_fourteen :
    decimalSeventeenHarmonicValue 14 =
      decimalSeventeenHarmonicValue 2 := by
  simpa using decimalSeventeenHarmonicValue_sub_sixteen 2 (by norm_num)

theorem decimalSeventeenHarmonicValue_fifteen :
    decimalSeventeenHarmonicValue 15 =
      decimalSeventeenHarmonicValue 1 := by
  simpa using decimalSeventeenHarmonicValue_sub_sixteen 1 (by norm_num)

/-- Exact lookup of all sixteen frequencies into the strictly ordered
nine-value table. -/
theorem decimalSeventeenHarmonicValue_eq_ordered (j : Fin 16) :
    decimalSeventeenHarmonicValue j.val =
      decimalSeventeenOrderedValues (decimalSeventeenValueIndex j) := by
  fin_cases j <;>
    simp [decimalSeventeenValueIndex, decimalSeventeenOrderedValues,
      decimalSeventeenHarmonicValue_zero,
      decimalSeventeenHarmonicValue_one,
      decimalSeventeenHarmonicValue_two,
      decimalSeventeenHarmonicValue_three,
      decimalSeventeenHarmonicValue_four,
      decimalSeventeenHarmonicValue_five,
      decimalSeventeenHarmonicValue_six,
      decimalSeventeenHarmonicValue_seven,
      decimalSeventeenHarmonicValue_eight,
      decimalSeventeenHarmonicValue_nine,
      decimalSeventeenHarmonicValue_ten,
      decimalSeventeenHarmonicValue_eleven,
      decimalSeventeenHarmonicValue_twelve,
      decimalSeventeenHarmonicValue_thirteen,
      decimalSeventeenHarmonicValue_fourteen,
      decimalSeventeenHarmonicValue_fifteen]

/-- Every one of the nine values is attained by a frequency from zero through
eight. -/
def decimalSeventeenValueRepresentative : Fin 9 → Fin 16 :=
  ![8, 7, 2, 5, 4, 3, 6, 1, 0]

theorem decimalSeventeenValueRepresentative_rightInverse (i : Fin 9) :
    decimalSeventeenValueIndex (decimalSeventeenValueRepresentative i) = i := by
  fin_cases i <;>
    simp [decimalSeventeenValueIndex, decimalSeventeenValueRepresentative]

/-- The image of all sixteen harmonic frequencies is exactly the printed
nine-value set. -/
theorem decimalSeventeenHarmonicValue_image :
    Finset.univ.image
        (fun j : Fin 16 => decimalSeventeenHarmonicValue j.val) =
      decimalSeventeenDistinctValues := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    rw [decimalSeventeenDistinctValues, Finset.mem_image]
    exact ⟨decimalSeventeenValueIndex j, Finset.mem_univ _,
      (decimalSeventeenHarmonicValue_eq_ordered j).symm⟩
  · intro hx
    rw [decimalSeventeenDistinctValues] at hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨decimalSeventeenValueRepresentative i, Finset.mem_univ _, ?_⟩
    rw [decimalSeventeenHarmonicValue_eq_ordered,
      decimalSeventeenValueRepresentative_rightInverse]

/-- Exact extrema of the sixteen harmonic values. -/
theorem decimalSeventeenHarmonicValue_bounds (j : Fin 16) :
    (1 : ℝ) / 4 ≤ decimalSeventeenHarmonicValue j.val ∧
      decimalSeventeenHarmonicValue j.val ≤ (7 : ℝ) / 4 := by
  rw [decimalSeventeenHarmonicValue_eq_ordered]
  have hmono := decimalSeventeenOrderedValues_strictMono.monotone
  constructor
  · simpa [decimalSeventeenOrderedValues] using
      hmono (Fin.zero_le (decimalSeventeenValueIndex j))
  · simpa [decimalSeventeenOrderedValues] using
      hmono (Fin.le_last (decimalSeventeenValueIndex j))

/-- The lower and upper bounds are both attained. -/
theorem decimalSeventeenHarmonicValue_extrema_attained :
    decimalSeventeenHarmonicValue 8 = (1 : ℝ) / 4 ∧
      decimalSeventeenHarmonicValue 0 = (7 : ℝ) / 4 :=
  ⟨decimalSeventeenHarmonicValue_eight,
    decimalSeventeenHarmonicValue_zero⟩

end NField.Alignment.DecimalOrbitSpectra
