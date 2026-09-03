/-
Author: Alexander S. Petty
-/

import NField.Alignment.CrossAlignmentMatrix
import NField.Alignment.SynchronizedCrossAlignment

/-!
# Scalar recovery from a synchronized cross-alignment matrix

Title-independent bridges from the literal matrix to its off-diagonal and
marked-reference statistics.
-/

namespace NField.Alignment.CrossAlignmentScalarRecovery

open scoped BigOperators
open NField.Alignment
open NField.Alignment.SynchronizedCrossAlignment
open NField.Alignment.ThreeTier

/-- The matrix index carried by the reference numerator one. -/
def referenceNumerator (n : ℕ) (_hn : 2 ≤ n) : ProperNumerator n :=
  ⟨0, by omega⟩

@[simp] theorem numeratorValue_referenceNumerator (n : ℕ) (hn : 2 ≤ n) :
    numeratorValue (referenceNumerator n hn) = 1 := by
  rfl

/-- Reindex a sum over the matrix rows by the represented positive proper
numerators `1, ..., n-1`. -/
theorem sum_properNumerators_eq_Icc
    {M : Type*} [AddCommMonoid M] {n : ℕ} (_hn : 2 ≤ n) (f : ℕ → M) :
    (∑ i : ProperNumerator n, f (numeratorValue i)) =
      ∑ k ∈ Finset.Icc 1 (n - 1), f k := by
  classical
  refine Finset.sum_bij (fun i _hi => numeratorValue i) ?_ ?_ ?_ ?_
  · intro i _hi
    simp only [Finset.mem_Icc, numeratorValue]
    constructor
    · omega
    · have hi := i.isLt
      omega
  · intro i _hi j _hj hij
    apply Fin.ext
    simpa [numeratorValue] using hij
  · intro k hk
    have hkI := Finset.mem_Icc.mp hk
    let i : ProperNumerator n := ⟨k - 1, by omega⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp [i, numeratorValue]
    omega
  · intro i _hi
    rfl

/-- The reference-pair digit count is the numerator-to-reference count used
by synchronized reference alignment. -/
theorem clearedPairMatchCount_reference
    {b q s D L : ℕ} (hn : 2 ≤ q * s)
    (j : ProperNumerator (q * s))
    (hj : ¬q ∣ numeratorValue j) :
    clearedPairMatchCount b (q * s) D L
        (referenceNumerator (q * s) hn) j =
      clearedNumeratorMatchCount b q s (numeratorValue j) D L := by
  classical
  unfold clearedNumeratorMatchCount
  rw [if_neg hj]
  unfold clearedPairMatchCount clearedPairMatchAt clearedMatchAt
  apply congrArg Finset.card
  ext position
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [numeratorValue_referenceNumerator]
  exact and_congr_right (fun _ => eq_comm)

/-- One marked-row matrix entry plus its terminating marker is exactly the
reference match count, before normalization. -/
theorem matrix_entry_plus_marker_eq_reference_count
    {b q s D L : ℕ} (hq : 1 < q) (hn : 2 ≤ q * s) (hL : 0 < L)
    (j : ProperNumerator (q * s)) :
    (L : ℝ) * synchronizedCrossAlignmentMatrix b (q * s) q D L
        (referenceNumerator (q * s) hn) j +
      (if q ∣ numeratorValue j then (L : ℝ) else 0) =
        clearedNumeratorMatchCount b q s (numeratorValue j) D L := by
  have hq1 : q ≠ 1 := by omega
  by_cases hj : q ∣ numeratorValue j
  · simp [synchronizedCrossAlignmentMatrix, clearedNumeratorMatchCount,
      numeratorValue_referenceNumerator, hq1, hj]
  · rw [if_neg hj]
    unfold synchronizedCrossAlignmentMatrix
    simp only [numeratorValue_referenceNumerator, Nat.dvd_one,
      hq1, hj, ↓reduceIte]
    rw [clearedPairMatchCount_reference hn j hj]
    field_simp
    simp

/-- Exactly `s-1` marked rows receive the terminating correction. -/
theorem termination_marker_sum
    {q s L : ℕ} (hq : 0 < q) (hs : 0 < s) (hn : 2 ≤ q * s) :
    (∑ i : ProperNumerator (q * s),
        if q ∣ numeratorValue i then (L : ℝ) else 0) =
      ((s - 1) * L : ℕ) := by
  classical
  rw [sum_properNumerators_eq_Icc (M := ℝ)
    hn
    (fun k => if q ∣ k then (L : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hset :
      (Finset.Icc 1 (q * s - 1)).filter (fun k => q ∣ k) =
        (Finset.Ioc 0 (q * s - 1)).filter (fun k => q ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  rw [pred_mul_div_eq_pred hq hs]
  norm_cast

/-- Summing the literal reference counts over matrix indices reproduces the
manuscript's numerator-by-numerator reference total. -/
theorem reference_count_sum_eq_clearedFieldMatchTotal
    {b q s D L : ℕ} (hn : 2 ≤ q * s) :
    (∑ i : ProperNumerator (q * s),
      clearedNumeratorMatchCount b q s (numeratorValue i) D L) =
        clearedFieldMatchTotal b q s D L := by
  unfold clearedFieldMatchTotal
  exact sum_properNumerators_eq_Icc (M := ℕ) hn
    (fun k => clearedNumeratorMatchCount b q s k D L)

/-- The marked first row recovers literal synchronized reference alignment. -/
theorem reference_alignment_recovery
    {b q s D L : ℕ} (hq : 1 < q) (hs : 0 < s)
    (hn : 2 ≤ q * s) (hL : 0 < L) :
    let A := synchronizedCrossAlignmentMatrix b (q * s) q D L
    let ref := referenceNumerator (q * s) hn
    clearedAlignmentReal b q s D L =
      ((∑ j, A ref j) + (s - 1)) / (q * s - 1) := by
  dsimp only
  have hsum :
      (L : ℝ) *
          (∑ j, synchronizedCrossAlignmentMatrix b (q * s) q D L
            (referenceNumerator (q * s) hn) j) +
        ((s - 1) * L : ℕ) =
          clearedFieldMatchTotal b q s D L := by
    calc
      (L : ℝ) *
            (∑ j, synchronizedCrossAlignmentMatrix b (q * s) q D L
              (referenceNumerator (q * s) hn) j) +
          ((s - 1) * L : ℕ) =
          (∑ j, (L : ℝ) *
            synchronizedCrossAlignmentMatrix b (q * s) q D L
              (referenceNumerator (q * s) hn) j) +
          (∑ j, if q ∣ numeratorValue j then (L : ℝ) else 0) := by
              rw [Finset.mul_sum,
                termination_marker_sum (by omega : 0 < q) hs hn]
      _ =
          ∑ j, ((L : ℝ) *
              synchronizedCrossAlignmentMatrix b (q * s) q D L
                (referenceNumerator (q * s) hn) j +
            if q ∣ numeratorValue j then (L : ℝ) else 0) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ j, (clearedNumeratorMatchCount b q s
            (numeratorValue j) D L : ℝ) := by
              apply Finset.sum_congr rfl
              intro j _hj
              exact matrix_entry_plus_marker_eq_reference_count hq hn hL j
      _ = clearedFieldMatchTotal b q s D L := by
              norm_cast
              exact reference_count_sum_eq_clearedFieldMatchTotal hn
  unfold clearedAlignmentReal
  rw [if_neg (by omega : q ≠ 1)]
  have hden : 0 < q * s - 1 := by omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hdenR : (0 : ℝ) < (q : ℝ) * s - 1 := by nlinarith
  push_cast [Nat.cast_sub (by omega : 1 ≤ q * s),
    Nat.cast_sub (by omega : 1 ≤ s)] at hsum ⊢
  rw [div_eq_div_iff (mul_ne_zero hdenR.ne' hLR.ne') hdenR.ne']
  calc
    (clearedFieldMatchTotal b q s D L : ℝ) * ((q : ℝ) * s - 1) =
        ((L : ℝ) *
          (∑ j, synchronizedCrossAlignmentMatrix b (q * s) q D L
            (referenceNumerator (q * s) hn) j) +
          ((s : ℝ) - 1) * L) * ((q : ℝ) * s - 1) := by rw [hsum]
    _ = ((∑ j, synchronizedCrossAlignmentMatrix b (q * s) q D L
            (referenceNumerator (q * s) hn) j) + ((s : ℝ) - 1)) *
          (((q : ℝ) * s - 1) * L) := by ring

/-- Total matrix mass minus trace is exactly the ordered off-diagonal mass. -/
theorem total_sub_trace_eq_offDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∑ i, ∑ j, A i j) - Matrix.trace A =
      ∑ z ∈ (Finset.univ : Finset ι).offDiag, A z.1 z.2 := by
  have hsplit :
      (∑ i, ∑ j, A i j) = Matrix.trace A +
        ∑ z ∈ (Finset.univ : Finset ι).offDiag, A z.1 z.2 := by
    rw [← Finset.sum_product']
    rw [← Finset.diag_union_offDiag]
    rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
    simp [Matrix.trace]
  linarith

/-- Ordered off-diagonal mass equals twice the strict-upper-triangle mass for
a symmetric matrix. -/
theorem ordered_offDiagonal_sum_eq_two_mul_upper
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) (hsym : A.IsSymm) :
    (∑ z ∈ (Finset.univ : Finset ι).offDiag, A z.1 z.2) =
      2 * ∑ z ∈ (Finset.univ : Finset ι).offDiag with z.1 < z.2,
        A z.1 z.2 := by
  classical
  let upper := (Finset.univ : Finset ι).offDiag.filter
    (fun z => z.1 < z.2)
  let lower := (Finset.univ : Finset ι).offDiag.filter
    (fun z => z.2 < z.1)
  have hdis : Disjoint upper lower := by
    rw [Finset.disjoint_left]
    intro z hzu hzl
    simp only [upper, lower, Finset.mem_filter] at hzu hzl
    exact (lt_asymm hzu.2 hzl.2)
  have hunion : upper ∪ lower = (Finset.univ : Finset ι).offDiag := by
    ext z
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter,
      Finset.mem_offDiag, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩)
      · exact hz
      · exact hz
    · intro hz
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · exact Or.inl ⟨hz, hlt⟩
      · exact Or.inr ⟨hz, hgt⟩
  have hlower :
      (∑ z ∈ lower, A z.1 z.2) = ∑ z ∈ upper, A z.1 z.2 := by
    refine Finset.sum_bij (fun z _hz => (z.2, z.1)) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [lower, upper, Finset.mem_filter, Finset.mem_offDiag,
        Finset.mem_univ, true_and] at hz ⊢
      exact ⟨Ne.symm hz.1, hz.2⟩
    · intro z _hz w _hw hzw
      exact Prod.ext (congrArg Prod.snd hzw) (congrArg Prod.fst hzw)
    · intro z hz
      refine ⟨(z.2, z.1), ?_, rfl⟩
      simp only [upper, lower, Finset.mem_filter, Finset.mem_offDiag,
        Finset.mem_univ, true_and] at hz ⊢
      exact ⟨Ne.symm hz.1, hz.2⟩
    · intro z hz
      exact hsym.apply z.2 z.1
  calc
    (∑ z ∈ (Finset.univ : Finset ι).offDiag, A z.1 z.2) =
        (∑ z ∈ upper, A z.1 z.2) +
          ∑ z ∈ lower, A z.1 z.2 := by
            rw [← hunion, Finset.sum_union hdis]
    _ = 2 * ∑ z ∈ upper, A z.1 z.2 := by rw [hlower]; ring
    _ = 2 * ∑ z ∈ (Finset.univ : Finset ι).offDiag with z.1 < z.2,
        A z.1 z.2 := by rfl

/-- The quadratic form of the all-ones vector is the sum of every matrix
entry.  Combined with trace subtraction, this is the scalar pairwise-recovery
identity used by the synchronized matrix. -/
theorem allOnes_quadratic_eq_total
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    dotProduct (fun _ : ι => (1 : ℝ))
        (Matrix.mulVec A (fun _ : ι => (1 : ℝ))) =
      ∑ i, ∑ j, A i j := by
  simp [dotProduct, Matrix.mulVec]

end NField.Alignment.CrossAlignmentScalarRecovery
