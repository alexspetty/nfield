/-
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindInverseResidueTransform
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Reciprocal-divisor moment bounds

The fixed moments of `sigma_{-1}` are bounded on average.  The proof expands a
moment into divisor tuples, counts their common multiples through the tuple
LCM, and dominates the remaining tuple sum by a convergent `p`-series.
-/

namespace NField.Alignment.ReciprocalDivisorMomentBound

open scoped BigOperators
open NField.Alignment.DedekindInverseResidueTransform

/-- Least common multiple of a finite divisor tuple. -/
def tupleLcm {j : ℕ} (d : Fin j → ℕ) : ℕ :=
  Finset.univ.lcm d

theorem tuple_dvd_tupleLcm {j : ℕ} (d : Fin j → ℕ) (i : Fin j) :
    d i ∣ tupleLcm d := by
  exact Finset.dvd_lcm (Finset.mem_univ i)

theorem tupleLcm_dvd_iff {j : ℕ} (d : Fin j → ℕ) (k : ℕ) :
    tupleLcm d ∣ k ↔ ∀ i, d i ∣ k := by
  rw [tupleLcm, Finset.lcm_dvd_iff]
  simp

theorem tupleLcm_pos {j : ℕ} {d : Fin j → ℕ}
    (hd : ∀ i, 0 < d i) : 0 < tupleLcm d := by
  apply Nat.pos_of_ne_zero
  unfold tupleLcm
  rw [Finset.lcm_ne_zero_iff]
  intro i _hi
  exact (hd i).ne'

/-- Positive integers through `x` divisible by every coordinate of `d`. -/
def commonMultipleSet {j : ℕ} (x : ℕ) (d : Fin j → ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun k => ∀ i, d i ∣ k

theorem mem_commonMultipleSet_iff {j x : ℕ} {d : Fin j → ℕ} {k : ℕ} :
    k ∈ commonMultipleSet x d ↔
      1 ≤ k ∧ k ≤ x ∧ tupleLcm d ∣ k := by
  simp only [commonMultipleSet, Finset.mem_filter, Finset.mem_Icc,
    tupleLcm_dvd_iff]
  tauto

/-- Common multiples are parametrized exactly by multiples of the tuple LCM. -/
theorem card_commonMultipleSet {j x : ℕ} {d : Fin j → ℕ}
    (hd : ∀ i, 0 < d i) :
    (commonMultipleSet x d).card = x / tupleLcm d := by
  let L := tupleLcm d
  have hL : 0 < L := tupleLcm_pos hd
  change (commonMultipleSet x d).card = x / L
  calc
    (commonMultipleSet x d).card = (Finset.Icc 1 (x / L)).card := by
      apply Finset.card_bij (fun k _ => k / L)
      · intro k hk
        have h := mem_commonMultipleSet_iff.mp hk
        have hqpos : 0 < k / L := Nat.div_pos (Nat.le_of_dvd h.1 h.2.2) hL
        have hqle : k / L ≤ x / L := Nat.div_le_div_right h.2.1
        exact Finset.mem_Icc.mpr ⟨hqpos, hqle⟩
      · intro a ha b hb hab
        have ha' := mem_commonMultipleSet_iff.mp ha
        have hb' := mem_commonMultipleSet_iff.mp hb
        calc
          a = L * (a / L) := (Nat.mul_div_cancel' ha'.2.2).symm
          _ = L * (b / L) := by rw [hab]
          _ = b := Nat.mul_div_cancel' hb'.2.2
      · intro q hq
        have hqI := Finset.mem_Icc.mp hq
        refine ⟨L * q, ?_, ?_⟩
        · rw [mem_commonMultipleSet_iff]
          exact ⟨Nat.mul_pos hL hqI.1,
            (by simpa [Nat.mul_comm] using
              (Nat.le_div_iff_mul_le hL).mp hqI.2),
            dvd_mul_right L q⟩
        · rw [Nat.mul_div_cancel_left q hL]
    _ = x / L := by simp

/-- Positive `j`-tuples with every coordinate at most `x`. -/
def positiveTuples (j x : ℕ) : Finset (Fin j → Fin (x + 1)) :=
  Finset.univ.filter fun d => ∀ i, 0 < (d i).val

/-- Reciprocal product attached to a divisor tuple. -/
noncomputable def tupleReciprocalWeight {j x : ℕ}
    (d : Fin j → Fin (x + 1)) : ℝ :=
  ∏ i, ((d i).val : ℝ)⁻¹

theorem prod_ite_zero_eq_ite_forall
    {j : ℕ} (P : Fin j → Prop) [DecidablePred P] (w : Fin j → ℝ) :
    (∏ i, if P i then w i else 0) =
      if (∀ i, P i) then ∏ i, w i else 0 := by
  by_cases hP : ∀ i, P i
  · simp [hP]
  · simp only [hP, if_false]
    push Not at hP
    rcases hP with ⟨i, hi⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem reciprocalDivisorSum_eq_fin_sum
    {k x : ℕ} (hk : 0 < k) (hkx : k ≤ x) :
    reciprocalDivisorSum k =
      ∑ a : Fin (x + 1),
        if 0 < a.val ∧ a.val ∣ k then (a.val : ℝ)⁻¹ else 0 := by
  unfold reciprocalDivisorSum
  let f := fun n : ℕ => if 0 < n ∧ n ∣ k then (n : ℝ)⁻¹ else 0
  calc
    (∑ d ∈ k.divisors, (d : ℝ)⁻¹) =
        ∑ n ∈ Finset.range (x + 1), f n := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext a
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
        constructor
        · intro ha
          exact ⟨Nat.le_of_dvd hk ha.1 |>.trans_lt (Nat.lt_succ_of_le hkx),
            Nat.pos_of_dvd_of_pos ha.1 hk, ha.1⟩
        · intro ha
          exact ⟨ha.2.2, hk.ne'⟩
      · intro a ha
        have hpred := (Finset.mem_filter.mp ha).2
        simp
    _ = ∑ a : Fin (x + 1), f a.val :=
      (Fin.sum_univ_eq_sum_range f (x + 1)).symm

/-- Exact divisor-tuple expansion of one fixed reciprocal-divisor moment. -/
theorem reciprocalDivisorSum_pow_eq_tuple_sum
    {j k x : ℕ} (hk : 0 < k) (hkx : k ≤ x) :
    reciprocalDivisorSum k ^ j =
      ∑ d ∈ positiveTuples j x,
        if (∀ i, (d i).val ∣ k) then tupleReciprocalWeight d else 0 := by
  rw [reciprocalDivisorSum_eq_fin_sum hk hkx]
  rw [Fintype.sum_pow]
  unfold positiveTuples tupleReciprocalWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [prod_ite_zero_eq_ite_forall]
  by_cases hpos : ∀ i, 0 < (d i).val
  · have hall :
        (∀ i, 0 < (d i).val ∧ (d i).val ∣ k) ↔
          ∀ i, (d i).val ∣ k := by
      constructor
      · exact fun h i => (h i).2
      · exact fun h i => ⟨hpos i, h i⟩
    simp [hpos]
  · have hall : ¬(∀ i, 0 < (d i).val ∧ (d i).val ∣ k) := by
      intro h
      exact hpos fun i => (h i).1
    rw [if_neg hall, if_neg hpos]

/-- Expanding the moment and swapping the two finite sums leaves the exact
number of common multiples of each divisor tuple. -/
theorem reciprocalDivisorMomentSum_eq_commonMultiples
    {j x : ℕ} :
    (∑ k ∈ Finset.Icc 1 x, reciprocalDivisorSum k ^ j) =
      ∑ d ∈ positiveTuples j x,
        (((commonMultipleSet x fun i => (d i).val).card : ℕ) : ℝ) *
          tupleReciprocalWeight d := by
  calc
    (∑ k ∈ Finset.Icc 1 x, reciprocalDivisorSum k ^ j) =
        ∑ k ∈ Finset.Icc 1 x,
          ∑ d ∈ positiveTuples j x,
            if (∀ i, (d i).val ∣ k) then tupleReciprocalWeight d else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      exact reciprocalDivisorSum_pow_eq_tuple_sum hkI.1 hkI.2
    _ = ∑ d ∈ positiveTuples j x,
          ∑ k ∈ Finset.Icc 1 x,
            if (∀ i, (d i).val ∣ k) then tupleReciprocalWeight d else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← Finset.sum_filter]
      change
        (∑ k ∈ commonMultipleSet x (fun i => (d i).val),
            tupleReciprocalWeight d) = _
      rw [Finset.sum_const, nsmul_eq_mul]

/-- The moment sum is bounded by `x` times the finite tuple-LCM series. -/
theorem reciprocalDivisorMomentSum_le_tupleLcmSeries
    {j x : ℕ} :
    (∑ k ∈ Finset.Icc 1 x, reciprocalDivisorSum k ^ j) ≤
      (x : ℝ) *
        ∑ d ∈ positiveTuples j x,
          tupleReciprocalWeight d /
            (tupleLcm fun i => (d i).val : ℕ) := by
  rw [reciprocalDivisorMomentSum_eq_commonMultiples]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : ∀ i, 0 < (d i).val :=
    (Finset.mem_filter.mp hd).2
  have hLpos : 0 < tupleLcm (fun i => (d i).val) := tupleLcm_pos hdpos
  rw [card_commonMultipleSet hdpos]
  have hcast :
      ((((x / tupleLcm (fun i => (d i).val) : ℕ) : ℕ) : ℝ)) ≤
        (x : ℝ) / (tupleLcm (fun i => (d i).val) : ℕ) :=
    Nat.cast_div_le
  have hw : 0 ≤ tupleReciprocalWeight d := by
    unfold tupleReciprocalWeight
    positivity
  calc
    (((x / tupleLcm (fun i => (d i).val) : ℕ) : ℕ) : ℝ) *
        tupleReciprocalWeight d ≤
      ((x : ℝ) / (tupleLcm (fun i => (d i).val) : ℕ)) *
        tupleReciprocalWeight d := mul_le_mul_of_nonneg_right hcast hw
    _ = (x : ℝ) *
        (tupleReciprocalWeight d /
          (tupleLcm (fun i => (d i).val) : ℕ)) := by ring

/-- The convergent comparison exponent attached to the `j`th moment. -/
noncomputable def momentPSeriesExponent (j : ℕ) : ℝ :=
  1 + (j : ℝ)⁻¹

theorem one_lt_momentPSeriesExponent {j : ℕ} (hj : 0 < j) :
    (1 : ℝ) < momentPSeriesExponent j := by
  unfold momentPSeriesExponent
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hinv : (0 : ℝ) < (j : ℝ)⁻¹ := inv_pos.mpr hjR
  linarith

/-- The tuple LCM supplies the extra fractional power needed to make every
coordinate summable. -/
theorem tupleReciprocalWeight_div_lcm_le_pseriesProduct
    {j x : ℕ} (hj : 0 < j) {d : Fin j → Fin (x + 1)}
    (hd : d ∈ positiveTuples j x) :
    tupleReciprocalWeight d /
        (tupleLcm fun i => (d i).val : ℕ) ≤
      ∏ i, 1 / ((d i).val : ℝ) ^ momentPSeriesExponent j := by
  have hdpos : ∀ i, 0 < (d i).val := (Finset.mem_filter.mp hd).2
  let L := tupleLcm fun i => (d i).val
  have hLpos : 0 < L := tupleLcm_pos hdpos
  have hjne : j ≠ 0 := hj.ne'
  have hcoord : ∀ i : Fin j, ((d i).val : ℝ) ≤ (L : ℝ) := by
    intro i
    exact_mod_cast Nat.le_of_dvd hLpos
      (tuple_dvd_tupleLcm (fun i => (d i).val) i)
  have hprod :
      (∏ i, ((d i).val : ℝ)) ≤ (L : ℝ) ^ j := by
    calc
      (∏ i, ((d i).val : ℝ)) ≤ ∏ _i : Fin j, (L : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _hi
          positivity
        · intro i _hi
          exact hcoord i
      _ = (L : ℝ) ^ j := by simp
  have hroot :
      (∏ i, ((d i).val : ℝ) ^ ((j : ℝ)⁻¹)) ≤ (L : ℝ) := by
    calc
      (∏ i, ((d i).val : ℝ) ^ ((j : ℝ)⁻¹)) =
          (∏ i, ((d i).val : ℝ)) ^ ((j : ℝ)⁻¹) := by
        exact Real.finsetProd_rpow Finset.univ
          (fun i => ((d i).val : ℝ)) (by intro i _hi; positivity) _
      _ ≤ ((L : ℝ) ^ j) ^ ((j : ℝ)⁻¹) := by
        apply Real.rpow_le_rpow
        · positivity
        · exact hprod
        · positivity
      _ = (L : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hjne
  have hinv :
      (L : ℝ)⁻¹ ≤
        (∏ i, ((d i).val : ℝ) ^ ((j : ℝ)⁻¹))⁻¹ := by
    have hrootpos :
        0 < ∏ i, ((d i).val : ℝ) ^ ((j : ℝ)⁻¹) := by
      apply Finset.prod_pos
      intro i _hi
      exact Real.rpow_pos_of_pos (by exact_mod_cast hdpos i) _
    exact (inv_le_inv₀ (by exact_mod_cast hLpos) hrootpos).2 hroot
  have hweight : 0 ≤ tupleReciprocalWeight d := by
    unfold tupleReciprocalWeight
    positivity
  calc
    tupleReciprocalWeight d / (L : ℕ) =
        tupleReciprocalWeight d * (L : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ tupleReciprocalWeight d *
        (∏ i, ((d i).val : ℝ) ^ ((j : ℝ)⁻¹))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hweight
    _ = ∏ i, 1 / ((d i).val : ℝ) ^ momentPSeriesExponent j := by
      unfold tupleReciprocalWeight momentPSeriesExponent
      rw [← Finset.prod_inv_distrib
        (fun i => ((d i).val : ℝ) ^ ((j : ℝ)⁻¹))]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _hi
      have hi : (0 : ℝ) < (d i).val := by exact_mod_cast hdpos i
      rw [Real.rpow_add hi]
      simp [Real.rpow_one, one_div, mul_comm]

/-- A finite box of separated tuple weights factors as a power of the
one-dimensional partial `p`-series. -/
theorem positiveTuplePSeries_sum_eq_pow (j x : ℕ) :
    (∑ d ∈ positiveTuples j x,
        ∏ i, 1 / ((d i).val : ℝ) ^ momentPSeriesExponent j) =
      (∑ n ∈ Finset.Icc 1 x,
        1 / (n : ℝ) ^ momentPSeriesExponent j) ^ j := by
  let f := fun n : ℕ => 1 / (n : ℝ) ^ momentPSeriesExponent j
  have hbase :
      (∑ a : Fin (x + 1), if 0 < a.val then f a.val else 0) =
        ∑ n ∈ Finset.Icc 1 x, f n := by
    calc
      (∑ a : Fin (x + 1), if 0 < a.val then f a.val else 0) =
          ∑ n ∈ Finset.range (x + 1), if 0 < n then f n else 0 :=
        Fin.sum_univ_eq_sum_range
          (fun n => if 0 < n then f n else 0) (x + 1)
      _ = ∑ n ∈ (Finset.range (x + 1)).filter fun n => 0 < n, f n := by
        rw [Finset.sum_filter]
      _ = ∑ n ∈ Finset.Icc 1 x, f n := by
        apply Finset.sum_congr
        · ext n
          simp
          omega
        · intro n _hn
          rfl
  rw [← hbase, Fintype.sum_pow]
  unfold positiveTuples
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [prod_ite_zero_eq_ite_forall]

/-- The complete tuple comparison is bounded by a finite power of a convergent
`p`-series, independently of the cutoff. -/
theorem tupleLcmSeries_le_pseriesPower
    {j x : ℕ} (hj : 0 < j) :
    (∑ d ∈ positiveTuples j x,
        tupleReciprocalWeight d /
          (tupleLcm fun i => (d i).val : ℕ)) ≤
      (∑' n : ℕ, 1 / (n : ℝ) ^ momentPSeriesExponent j) ^ j := by
  calc
    (∑ d ∈ positiveTuples j x,
        tupleReciprocalWeight d /
          (tupleLcm fun i => (d i).val : ℕ)) ≤
      ∑ d ∈ positiveTuples j x,
        ∏ i, 1 / ((d i).val : ℝ) ^ momentPSeriesExponent j := by
      apply Finset.sum_le_sum
      intro d hd
      exact tupleReciprocalWeight_div_lcm_le_pseriesProduct hj hd
    _ = (∑ n ∈ Finset.Icc 1 x,
        1 / (n : ℝ) ^ momentPSeriesExponent j) ^ j :=
      positiveTuplePSeries_sum_eq_pow j x
    _ ≤ (∑' n : ℕ,
        1 / (n : ℝ) ^ momentPSeriesExponent j) ^ j := by
      apply pow_le_pow_left₀
      · positivity
      · apply Summable.sum_le_tsum (Finset.Icc 1 x)
        · intro n _hn
          positivity
        · exact Real.summable_one_div_nat_rpow.mpr
            (one_lt_momentPSeriesExponent hj)

/-- Manuscript Lemma `Bounded reciprocal-divisor moments`, proved for every
fixed positive moment with an explicit convergent `p`-series majorant. -/
theorem bounded_reciprocal_divisor_moments :
    BoundedReciprocalDivisorMoments := by
  intro j hj
  let C :=
    (∑' n : ℕ, 1 / (n : ℝ) ^ momentPSeriesExponent j) ^ j
  have hbaseNonneg :
      0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ momentPSeriesExponent j :=
    tsum_nonneg fun n => by positivity
  refine ⟨C, pow_nonneg hbaseNonneg j, ?_⟩
  intro x
  calc
    (∑ k ∈ Finset.Icc 1 x, reciprocalDivisorSum k ^ j) ≤
        (x : ℝ) *
          ∑ d ∈ positiveTuples j x,
            tupleReciprocalWeight d /
              (tupleLcm fun i => (d i).val : ℕ) :=
      reciprocalDivisorMomentSum_le_tupleLcmSeries
    _ ≤ (x : ℝ) * C := by
      apply mul_le_mul_of_nonneg_left
        (tupleLcmSeries_le_pseriesPower hj)
      positivity
    _ = C * x := by ring

end NField.Alignment.ReciprocalDivisorMomentBound
