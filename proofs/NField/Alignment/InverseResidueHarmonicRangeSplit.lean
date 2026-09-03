/-
Author: Alexander S. Petty
-/

import NField.Alignment.InverseResiduePrefixCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The inverse-residue harmonic range split

Finite Abel-summation lemmas for the three ranges in the inverse-residue
harmonic series.  The source-level Korolev and Weil--Estermann estimates stay
separate from the elementary deductions made from them.
-/

namespace NField.Alignment.InverseResidueHarmonicRangeSplit

open scoped BigOperators
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.DedekindReciprocity
open NField.Alignment.InverseResiduePrefixCompletion

/-- A concrete logarithm-versus-power comparison used by both cutoff
admissibility and the final envelope estimate. -/
theorem loglog_pow_sixteen_le_log_rpow_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      Real.rpow (Real.log (Real.log (q : ℝ))) 16 ≤
        Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (16 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 10)).comp_tendsto
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun q : ℕ => (q : ℝ))
            Filter.atTop Filter.atTop))
  have hbound := hreal.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, Filter.eventually_ge_atTop 3] with q hbound hq
  have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hloglogq0 : 0 ≤ Real.log (Real.log (q : ℝ)) := by
    apply Real.log_nonneg
    have hlogThree : (1 : ℝ) ≤ Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hlogThree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  simp only [Function.comp_apply, one_mul, Real.norm_eq_abs] at hbound
  rw [abs_of_nonneg (Real.rpow_nonneg hloglogq0 _),
    abs_of_nonneg (Real.rpow_nonneg hlogq0 _)] at hbound
  exact hbound

/-- Every fixed log-log power up to sixteen is eventually bounded by the
one-tenth power of the outer logarithm. -/
theorem loglog_rpow_le_log_rpow_tenth_eventually
    {a : ℝ} (ha : a ≤ 16) :
    ∀ᶠ q : ℕ in Filter.atTop,
      Real.rpow (Real.log (Real.log (q : ℝ))) a ≤
        Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) := by
  have htendLogLog : Filter.Tendsto
      (fun q : ℕ => Real.log (Real.log (q : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun q : ℕ => (q : ℝ))
            Filter.atTop Filter.atTop))
  filter_upwards [loglog_pow_sixteen_le_log_rpow_eventually,
    htendLogLog.eventually_ge_atTop 1] with q hpower hbase
  exact (Real.rpow_le_rpow_of_exponent_le hbase ha).trans hpower

/-- A fixed real power of `log log q` is eventually bounded by any positive
real power of `log q`. -/
theorem loglog_rpow_le_log_rpow_eventually
    (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ q : ℕ in Filter.atTop,
      Real.rpow (Real.log (Real.log (q : ℝ))) a ≤
        Real.rpow (Real.log (q : ℝ)) s := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop a hs).comp_tendsto
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun q : ℕ => (q : ℝ))
            Filter.atTop Filter.atTop))
  have hbound := hreal.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, Filter.eventually_ge_atTop 3] with q hbound hq
  have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hloglogq0 : 0 ≤ Real.log (Real.log (q : ℝ)) := by
    apply Real.log_nonneg
    have hlogThree : (1 : ℝ) ≤ Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hlogThree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  simp only [Function.comp_apply, one_mul, Real.norm_eq_abs] at hbound
  rw [abs_of_nonneg (Real.rpow_nonneg hloglogq0 _),
    abs_of_nonneg (Real.rpow_nonneg hlogq0 _)] at hbound
  exact hbound

/-- The centered rational sawtooth has absolute value at most one half. -/
theorem abs_rationalSawtooth_le_half
    {x q : ℕ} (hq : 0 < q) :
    |rationalSawtooth x q| ≤ (1 / 2 : ℚ) := by
  unfold rationalSawtooth
  by_cases hx : x % q = 0
  · simp [hx]
  · rw [if_neg hx, abs_le]
    have hmodPos : 0 < x % q := Nat.pos_of_ne_zero hx
    have hmodLt : x % q < q := Nat.mod_lt x hq
    have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
    constructor
    · apply (le_sub_iff_add_le).2
      rw [show -(1 / 2 : ℚ) + 1 / 2 = 0 by ring]
      exact div_nonneg (by exact_mod_cast hmodPos.le) hqQ.le
    · apply (sub_le_iff_le_add).2
      rw [show (1 / 2 : ℚ) + 1 / 2 = 1 by ring]
      exact (div_le_one hqQ).2 (by exact_mod_cast hmodLt.le)

/-- Every inverse-residue coefficient has norm at most one half. -/
theorem norm_inverseSawCoefficient_le_half
    {q r n : ℕ} (hq : 0 < q) :
    ‖inverseSawCoefficient q r n‖ ≤ (1 / 2 : ℝ) := by
  by_cases hn : n.Coprime q
  · rw [inverseSawCoefficient_eq_rationalSawtooth hq hn]
    norm_cast
    have hbound := abs_rationalSawtooth_le_half
      (x := r * inverseResidue n q) hq
    have hcast :
        ((|rationalSawtooth (r * inverseResidue n q) q| : ℚ) : ℝ) ≤
          (((1 / 2 : ℚ) : ℝ)) := Rat.cast_le.mpr hbound
    norm_num at hcast ⊢
    exact hcast
  · unfold inverseSawCoefficient
    rw [dif_neg hq.ne', dif_neg hn]
    norm_num

/-- The initial range costs at most half of the corresponding harmonic
number.  This is the manuscript's elementary `O(log Y)` estimate with an
explicit constant. -/
theorem norm_inverseSawPartial_le_half_harmonic
    {q r N : ℕ} (hq : 0 < q) :
    ‖inverseSawPartial q r N‖ ≤
      (1 / 2 : ℝ) * (harmonic N : ℝ) := by
  rw [inverseSawPartial_eq_Icc]
  calc
    ‖∑ n ∈ Finset.Icc 1 N,
        (((n : ℝ)⁻¹) • inverseSawCoefficient q r n)‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖((n : ℝ)⁻¹) • inverseSawCoefficient q r n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        (n : ℝ)⁻¹ * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (norm_inverseSawCoefficient_le_half hq) (by positivity)
    _ = (1 / 2 : ℝ) * (harmonic N : ℝ) := by
      rw [show (∑ n ∈ Finset.Icc 1 N,
          (n : ℝ)⁻¹ * (1 / 2 : ℝ)) =
          (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring]
      rw [harmonic_eq_sum_Icc]
      push_cast
      congr 2

/-- The unweighted shifted coefficient prefix is the real prefix used in the
Korolev and completion statements. -/
theorem shiftedCoefficientPrefix_eq_inverseResiduePrefix
    {q r X : ℕ} (hq : 0 < q) :
    (∑ n ∈ Finset.range X, inverseSawCoefficient q r (n + 1)) =
      ((inverseResiduePrefix q r X : ℝ) : ℂ) := by
  rw [inverseResiduePrefix_cast_eq_inverseSawCoefficient hq]
  rw [show Finset.Icc 1 X = Finset.Ico 1 (X + 1) by
    ext n
    simp]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _hn
  congr 1
  omega

/-- A completed-prefix estimate with a fixed source constant controls every
unweighted coefficient prefix, including prefixes extending through
arbitrarily many complete periods. -/
theorem norm_shiftedCoefficientPrefix_le_of_completion_constant
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ q r X,
      2 ≤ q → r.Coprime q → 1 ≤ X → X ≤ q →
      |inverseResiduePrefix q r X| ≤
        C * (q : ℝ).sqrt * q.divisors.card *
          reciprocalSqrtDivisorSum q * (Real.log (2 * q)) ^ 2)
    {q r N : ℕ} (hq : 2 ≤ q) (hr : r.Coprime q) :
    ‖∑ n ∈ Finset.range N,
        inverseSawCoefficient q r (n + 1)‖ ≤
      C * (q : ℝ).sqrt * q.divisors.card *
        reciprocalSqrtDivisorSum q * (Real.log (2 * q)) ^ 2 := by
  let g : ℕ → ℂ := fun n => inverseSawCoefficient q r (n + 1)
  have hqpos : 0 < q := by omega
  have hperiod : Function.Periodic g q := by
    intro n
    unfold g
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      inverseSawCoefficient_add_period q r (n + 1)
  have hzero : (∑ n ∈ Finset.range q, g n) = 0 :=
    sum_shifted_inverseSawCoefficient_period_eq_zero hqpos
  have hdecomp := periodic_sum_range_mul_add
    g hperiod (N / q) (N % q)
  rw [Nat.div_add_mod'] at hdecomp
  rw [hdecomp, hzero, nsmul_zero, zero_add]
  by_cases hrem : N % q = 0
  · simp [hrem]
    have hsigma : 0 ≤ reciprocalSqrtDivisorSum q := by
      unfold reciprocalSqrtDivisorSum
      positivity
    positivity
  · rw [shiftedCoefficientPrefix_eq_inverseResiduePrefix hqpos]
    rw [show ‖((inverseResiduePrefix q r (N % q) : ℝ) : ℂ)‖ =
        |inverseResiduePrefix q r (N % q)| by simp]
    exact hbound q r (N % q) hq hr
      (Nat.one_le_iff_ne_zero.mpr hrem)
      (Nat.le_of_lt (Nat.mod_lt N hqpos))

/-- Existential wrapper around the fixed-constant completed-prefix bound. -/
theorem norm_shiftedCoefficientPrefix_le_of_completion
    (hcompletion : CompletedInversePrefixEstimate)
    {q r N : ℕ} (hq : 2 ≤ q) (hr : r.Coprime q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∑ n ∈ Finset.range N,
          inverseSawCoefficient q r (n + 1)‖ ≤
        C * (q : ℝ).sqrt * q.divisors.card *
          reciprocalSqrtDivisorSum q * (Real.log (2 * q)) ^ 2 := by
  rcases hcompletion with ⟨C, hC, hbound⟩
  exact ⟨C, hC,
    norm_shiftedCoefficientPrefix_le_of_completion_constant
      hC hbound hq hr⟩

/-- Abel summation for a reciprocal-weighted segment.  A uniform bound on
the unweighted shifted prefixes costs exactly the reciprocal of the first
index, up to the explicit factor two. -/
theorem norm_inverseSawSegment_le_of_prefix
    {q r s t : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hprefix : ∀ N,
      ‖∑ n ∈ Finset.range N,
          inverseSawCoefficient q r (n + 1)‖ ≤ M) :
    ‖∑ n ∈ Finset.Ico s t, inverseSawTerm q r (n + 1)‖ ≤
      2 * ((s + 1 : ℕ) : ℝ)⁻¹ * M := by
  let w : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  let g : ℕ → ℂ := fun n => inverseSawCoefficient q r (n + 1)
  have hw0 : ∀ n, 0 ≤ w n := by
    intro n
    unfold w
    positivity
  have hw : Antitone w := by
    intro a b hab
    unfold w
    rw [inv_eq_one_div, inv_eq_one_div]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hab 1
  have habel := norm_antitone_weighted_sum_le
    w g hw0 hw M hM hprefix (s := s) (t := t)
  simpa [w, g, inverseSawTerm] using habel

/-- Abel summation when the unweighted prefix grows at most linearly.  This
is the exact finite mechanism behind the logarithmic cost of Korolev's
middle range. -/
theorem norm_inverseSawSegment_le_of_linear_prefix
    {q r s t : ℕ} {C : ℝ} (hC : 0 ≤ C) (hst : s < t)
    (hprefix : ∀ N, s ≤ N → N ≤ t →
      ‖∑ n ∈ Finset.range N,
          inverseSawCoefficient q r (n + 1)‖ ≤ C * (N : ℝ)) :
    ‖∑ n ∈ Finset.Ico s t, inverseSawTerm q r (n + 1)‖ ≤
      C * (2 + (harmonic t : ℝ)) := by
  let w : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  let g : ℕ → ℂ := fun n => inverseSawCoefficient q r (n + 1)
  let G : ℕ → ℂ := fun n => ∑ i ∈ Finset.range n, g i
  have hw0 : ∀ n, 0 ≤ w n := by
    intro n
    unfold w
    positivity
  have hwanti : Antitone w := by
    intro a b hab
    unfold w
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hlast : s ≤ t - 1 := Nat.le_sub_one_of_lt hst
  have hGlast : ‖G t‖ ≤ C * (t : ℝ) := by
    exact hprefix t (Nat.le_of_lt hst) (le_refl t)
  have hGs : ‖G s‖ ≤ C * (s : ℝ) := by
    exact hprefix s (le_refl s) (Nat.le_of_lt hst)
  have hboundaryTop : ‖w (t - 1) • G t‖ ≤ C := by
    have htpos : 0 < t := by omega
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 (t - 1))]
    calc
      w (t - 1) * ‖G t‖ ≤ w (t - 1) * (C * (t : ℝ)) := by
        gcongr
      _ = C := by
        unfold w
        rw [show t - 1 + 1 = t by omega]
        field_simp [show (t : ℝ) ≠ 0 by exact_mod_cast htpos.ne']
  have hboundaryBot : ‖w s • G s‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 s)]
    calc
      w s * ‖G s‖ ≤ w s * (C * (s : ℝ)) := by
        gcongr
      _ ≤ C := by
        unfold w
        have hsle : (s : ℝ) ≤ (s + 1 : ℕ) := by exact_mod_cast Nat.le_succ s
        have hden : (0 : ℝ) < (s + 1 : ℕ) := by positivity
        calc
          ((s + 1 : ℕ) : ℝ)⁻¹ * (C * (s : ℝ)) =
              C * ((s : ℝ) / (s + 1 : ℕ)) := by
                rw [inv_eq_one_div]
                ring
          _ ≤ C * 1 := by
            gcongr
            exact (div_le_one hden).2 hsle
          _ = C := mul_one C
  have hinterior :
      ‖∑ i ∈ Finset.Ico s (t - 1),
          (w (i + 1) - w i) • G (i + 1)‖ ≤
        C * (harmonic t : ℝ) := by
    calc
      ‖∑ i ∈ Finset.Ico s (t - 1),
          (w (i + 1) - w i) • G (i + 1)‖ ≤
          ∑ i ∈ Finset.Ico s (t - 1),
            ‖(w (i + 1) - w i) • G (i + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.Ico s (t - 1), C * w i := by
        apply Finset.sum_le_sum
        intro i hi
        have hiI := Finset.mem_Ico.mp hi
        have hiRange : s ≤ i + 1 ∧ i + 1 ≤ t := by omega
        have hGi := hprefix (i + 1) hiRange.1 hiRange.2
        have hdiff : w (i + 1) ≤ w i := hwanti (Nat.le_succ i)
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr hdiff), neg_sub]
        calc
          (w i - w (i + 1)) * ‖G (i + 1)‖ ≤
              (w i - w (i + 1)) * (C * ((i + 1 : ℕ) : ℝ)) := by
                gcongr
          _ = C * w (i + 1) := by
            unfold w
            have hi1 : (((i + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
            have hi2 : (((i + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
            push_cast
            field_simp [hi1, hi2]
            ring
          _ ≤ C * w i := by
            exact mul_le_mul_of_nonneg_left hdiff hC
      _ ≤ ∑ i ∈ Finset.range t, C * (((i + 1 : ℕ) : ℝ))⁻¹ := by
        unfold w
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          have hiI := Finset.mem_Ico.mp hi
          simp only [Finset.mem_range]
          omega
        · intro i hi _hsmall
          exact mul_nonneg hC (by positivity)
      _ = C * (harmonic t : ℝ) := by
        rw [← Finset.mul_sum]
        rw [show (∑ i ∈ Finset.range t,
            (((i + 1 : ℕ) : ℝ))⁻¹) =
            ∑ n ∈ Finset.Icc 1 t, (n : ℝ)⁻¹ by
          rw [show Finset.Icc 1 t = Finset.Ico 1 (t + 1) by
            ext n
            simp]
          rw [Finset.sum_Ico_eq_sum_range]
          simp [Nat.add_comm]]
        rw [harmonic_eq_sum_Icc]
        push_cast
        congr 2
  have hsum :
      (∑ n ∈ Finset.Ico s t, inverseSawTerm q r (n + 1)) =
        ∑ n ∈ Finset.Ico s t, w n • g n := by
    apply Finset.sum_congr rfl
    intro n _hn
    simp [w, g, inverseSawTerm]
  rw [hsum, Finset.sum_Ico_by_parts w g hst]
  change ‖w (t - 1) • G t - w s • G s -
      ∑ i ∈ Finset.Ico s (t - 1),
        (w (i + 1) - w i) • G (i + 1)‖ ≤ _
  calc
    _ ≤ ‖w (t - 1) • G t‖ + ‖w s • G s‖ +
        ‖∑ i ∈ Finset.Ico s (t - 1),
          (w (i + 1) - w i) • G (i + 1)‖ := by
      calc
        _ ≤ ‖w (t - 1) • G t - w s • G s‖ +
            ‖∑ i ∈ Finset.Ico s (t - 1),
              (w (i + 1) - w i) • G (i + 1)‖ := norm_sub_le _ _
        _ ≤ (‖w (t - 1) • G t‖ + ‖w s • G s‖) +
            ‖∑ i ∈ Finset.Ico s (t - 1),
              (w (i + 1) - w i) • G (i + 1)‖ := by
                gcongr
                exact norm_sub_le (w (t - 1) • G t) (w s • G s)
        _ = _ := by ring
    _ ≤ C + C + C * (harmonic t : ℝ) := by gcongr
    _ = C * (2 + (harmonic t : ℝ)) := by ring

/-- The logarithmic factor in Korolev's estimate decreases with the prefix
length once the logarithm is positive. -/
theorem korolevPrefixDecay_antitone
    {q Y X : ℕ} (hq : 3 ≤ q) (hY : 2 ≤ Y) (hYX : Y ≤ X) :
    korolevPrefixDecay q X ≤ korolevPrefixDecay q Y := by
  unfold korolevPrefixDecay
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast hY)
  have hlogMono : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hYX)
  have hpow :
      Real.rpow (Real.log (X : ℝ)) (-5 / 24 : ℝ) ≤
        Real.rpow (Real.log (Y : ℝ)) (-5 / 24 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlogY hlogMono (by norm_num)
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hloglogq : 0 ≤ Real.log (Real.log (q : ℝ)) := by
    apply Real.log_nonneg
    have hlogThree : (1 : ℝ) ≤ Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hlogThree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hqOne : 0 ≤ Real.rpow (Real.log (q : ℝ)) (1 / 6 : ℝ) :=
    Real.rpow_nonneg hlogq _
  have hqTwo :
      0 ≤ Real.rpow (Real.log (Real.log (q : ℝ))) (49 / 24 : ℝ) :=
    Real.rpow_nonneg hloglogq _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow hqOne) hqTwo

/-- The exact finite middle-range conclusion obtained from Korolev's
published prefix estimate by Abel summation. -/
def KorolevMiddleHarmonicEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ (q r Y U : ℕ),
    threshold ≤ q → 3 ≤ q → r.Coprime q → 2 ≤ Y → Y < U →
      korolevLowerRange q ≤ (Y : ℝ) →
      (U : ℝ) ≤ korolevUpperRange q →
      ‖∑ n ∈ Finset.Ico Y U, inverseSawTerm q r (n + 1)‖ ≤
        C * korolevPrefixDecay q Y *
          (2 + (harmonic U : ℝ))

theorem korolevMiddleHarmonicEstimate
    (hKorolev : KorolevInverseFractionRangeEstimate) :
    KorolevMiddleHarmonicEstimate := by
  rcases hKorolev with ⟨C, hC, threshold, hsource⟩
  refine ⟨C, hC, threshold, ?_⟩
  intro q r Y U hthreshold hq hr hY hYU hLower hUpper
  have hqpos : 0 < q := by omega
  have hdecay : 0 ≤ korolevPrefixDecay q Y := by
    unfold korolevPrefixDecay
    have hlogY0 : 0 ≤ Real.log (Y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
    have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have hloglogq0 : 0 ≤ Real.log (Real.log (q : ℝ)) := by
      apply Real.log_nonneg
      have hlogThree : (1 : ℝ) ≤ Real.log 3 := by
        nlinarith [Real.log_three_gt_d9]
      exact hlogThree.trans
        (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hlogY0 _)
        (Real.rpow_nonneg hlogq0 _))
      (Real.rpow_nonneg hloglogq0 _)
  apply norm_inverseSawSegment_le_of_linear_prefix
    (mul_nonneg hC hdecay) hYU
  intro X hYX hXU
  have hLowerX : korolevLowerRange q ≤ (X : ℝ) :=
    hLower.trans (by exact_mod_cast hYX)
  have hUpperX : (X : ℝ) ≤ korolevUpperRange q :=
    (show (X : ℝ) ≤ (U : ℝ) by exact_mod_cast hXU).trans hUpper
  have hsourceX := hsource q r X hthreshold hr hLowerX hUpperX
  have hdecayX := korolevPrefixDecay_antitone hq hY hYX
  rw [shiftedCoefficientPrefix_eq_inverseResiduePrefix hqpos]
  rw [show ‖((inverseResiduePrefix q r X : ℝ) : ℂ)‖ =
      |inverseResiduePrefix q r X| by simp]
  calc
    |inverseResiduePrefix q r X| ≤
        C * (X : ℝ) * korolevPrefixDecay q X := hsourceX
    _ ≤ (C * korolevPrefixDecay q Y) * (X : ℝ) := by
      have hXR : 0 ≤ (X : ℝ) := by positivity
      have hCX : 0 ≤ C * (X : ℝ) := mul_nonneg hC hXR
      calc
        C * (X : ℝ) * korolevPrefixDecay q X ≤
            C * (X : ℝ) * korolevPrefixDecay q Y :=
          mul_le_mul_of_nonneg_left hdecayX hCX
        _ = (C * korolevPrefixDecay q Y) * (X : ℝ) := by ring

/-- The modulus-dependent envelope supplied by completed inverse prefixes. -/
noncomputable def completedInversePrefixScale (q : ℕ) : ℝ :=
  (q : ℝ).sqrt * q.divisors.card * reciprocalSqrtDivisorSum q *
    (Real.log (2 * q)) ^ 2

/-- Completion plus periodic zero mean controls the entire harmonic tail,
not only the first modulus block. -/
def CompletedInverseHarmonicTailEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q r U N,
    2 ≤ q → r.Coprime q →
      ‖∑ n ∈ Finset.Ico U N, inverseSawTerm q r (n + 1)‖ ≤
        2 * ((U + 1 : ℕ) : ℝ)⁻¹ *
          (C * completedInversePrefixScale q)

theorem completedInverseHarmonicTailEstimate
    (hcompletion : CompletedInversePrefixEstimate) :
    CompletedInverseHarmonicTailEstimate := by
  rcases hcompletion with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro q r U N hq hr
  have hsigma : 0 ≤ reciprocalSqrtDivisorSum q := by
    unfold reciprocalSqrtDivisorSum
    positivity
  have hscale : 0 ≤ completedInversePrefixScale q := by
    unfold completedInversePrefixScale
    positivity
  apply norm_inverseSawSegment_le_of_prefix (mul_nonneg hC hscale)
  intro X
  have hprefix := norm_shiftedCoefficientPrefix_le_of_completion_constant
    hC hbound (N := X) hq hr
  unfold completedInversePrefixScale
  convert hprefix using 1
  all_goals ring

/-- Splitting an ordered inverse-saw partial sum at a finite index. -/
theorem inverseSawPartial_add_segment
    {q r A N : ℕ} (hAN : A ≤ N) :
    inverseSawPartial q r N =
      inverseSawPartial q r A +
        ∑ n ∈ Finset.Ico A N, inverseSawTerm q r (n + 1) := by
  unfold inverseSawPartial
  rw [Finset.sum_Ico_eq_sub _ hAN]
  abel

/-- Abstract three-range assembly.  It records exactly which finite estimate
is used below, without hiding any analytic source input. -/
theorem norm_inverseSawPartial_le_threeRange
    {q r Y U : ℕ} {low middle tail : ℝ}
    (hYU : Y ≤ U) (_hlow0 : 0 ≤ low)
    (hmiddle0 : 0 ≤ middle) (htail0 : 0 ≤ tail)
    (hlow : ∀ N, N ≤ Y → ‖inverseSawPartial q r N‖ ≤ low)
    (hmiddle : ∀ N, Y < N → N ≤ U →
      ‖∑ n ∈ Finset.Ico Y N, inverseSawTerm q r (n + 1)‖ ≤
        middle)
    (htail : ∀ N, U < N →
      ‖∑ n ∈ Finset.Ico U N, inverseSawTerm q r (n + 1)‖ ≤
        tail) :
    ∀ N, ‖inverseSawPartial q r N‖ ≤ low + middle + tail := by
  intro N
  by_cases hNY : N ≤ Y
  · exact (hlow N hNY).trans (by linarith)
  have hYN : Y < N := Nat.lt_of_not_ge hNY
  by_cases hNU : N ≤ U
  · rw [inverseSawPartial_add_segment (Nat.le_of_lt hYN)]
    calc
      ‖inverseSawPartial q r Y +
          ∑ n ∈ Finset.Ico Y N, inverseSawTerm q r (n + 1)‖ ≤
          ‖inverseSawPartial q r Y‖ +
            ‖∑ n ∈ Finset.Ico Y N,
              inverseSawTerm q r (n + 1)‖ := norm_add_le _ _
      _ ≤ low + middle := by
        gcongr
        · exact hlow Y (le_refl Y)
        · exact hmiddle N hYN hNU
      _ ≤ low + middle + tail := by linarith
  · have hUN : U < N := Nat.lt_of_not_ge hNU
    rw [inverseSawPartial_add_segment (Nat.le_of_lt hUN)]
    have hYU' : Y < U ∨ Y = U := Nat.lt_or_eq_of_le hYU
    have hpartialU : ‖inverseSawPartial q r U‖ ≤ low + middle := by
      rcases hYU' with hYUstrict | hYUeq
      · rw [inverseSawPartial_add_segment (Nat.le_of_lt hYUstrict)]
        calc
          ‖inverseSawPartial q r Y +
              ∑ n ∈ Finset.Ico Y U,
                inverseSawTerm q r (n + 1)‖ ≤
              ‖inverseSawPartial q r Y‖ +
                ‖∑ n ∈ Finset.Ico Y U,
                  inverseSawTerm q r (n + 1)‖ := norm_add_le _ _
          _ ≤ low + middle := by
            gcongr
            · exact hlow Y (le_refl Y)
            · exact hmiddle U hYUstrict (le_refl U)
      · exact (hlow U (by omega)).trans (by linarith)
    calc
      ‖inverseSawPartial q r U +
          ∑ n ∈ Finset.Ico U N, inverseSawTerm q r (n + 1)‖ ≤
          ‖inverseSawPartial q r U‖ +
            ‖∑ n ∈ Finset.Ico U N,
              inverseSawTerm q r (n + 1)‖ := norm_add_le _ _
      _ ≤ (low + middle) + tail := by
        exact add_le_add hpartialU (htail N hUN)
      _ = low + middle + tail := by ring

/-- The finite three-range envelope before choosing the asymptotic cutoffs. -/
noncomputable def inverseSawThreeRangeEnvelope
    (korolevConstant completionConstant : ℝ) (q Y U : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (harmonic Y : ℝ) +
    korolevConstant * korolevPrefixDecay q Y *
      (2 + (harmonic U : ℝ)) +
    2 * ((U + 1 : ℕ) : ℝ)⁻¹ *
      (completionConstant * completedInversePrefixScale q)

/-- Korolev on the middle range and Weil--Estermann completion on the upper
range give the exact three-range finite bound for every partial sum. -/
def InverseSawThreeRangeEstimate : Prop :=
  ∃ korolevConstant completionConstant : ℝ,
    0 ≤ korolevConstant ∧ 0 ≤ completionConstant ∧
      ∃ threshold : ℕ, ∀ (q r Y U N : ℕ),
        threshold ≤ q → 3 ≤ q → r.Coprime q →
          2 ≤ Y → Y < U →
          korolevLowerRange q ≤ (Y : ℝ) →
          (U : ℝ) ≤ korolevUpperRange q →
          ‖inverseSawPartial q r N‖ ≤
            inverseSawThreeRangeEnvelope
              korolevConstant completionConstant q Y U

theorem inverseSawThreeRangeEstimate
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : CompletedInversePrefixEstimate) :
    InverseSawThreeRangeEstimate := by
  rcases korolevMiddleHarmonicEstimate hKorolev with
    ⟨Cₖ, hCₖ, threshold, hmiddle⟩
  rcases completedInverseHarmonicTailEstimate hcompletion with
    ⟨Cₑ, hCₑ, htail⟩
  refine ⟨Cₖ, Cₑ, hCₖ, hCₑ, threshold, ?_⟩
  intro q r Y U N hthreshold hq hr hY hYU hLower hUpper
  have hqpos : 0 < q := by omega
  have harmonic_nonneg (X : ℕ) : 0 ≤ (harmonic X : ℝ) := by
    have hQ : (0 : ℚ) ≤ harmonic X := by
      unfold harmonic
      positivity
    exact_mod_cast hQ
  have hlow0 : 0 ≤ (1 / 2 : ℝ) * (harmonic Y : ℝ) := by
    exact mul_nonneg (by norm_num) (harmonic_nonneg Y)
  have hdecay : 0 ≤ korolevPrefixDecay q Y := by
    unfold korolevPrefixDecay
    have hlogY0 : 0 ≤ Real.log (Y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
    have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have hloglogq0 : 0 ≤ Real.log (Real.log (q : ℝ)) := by
      apply Real.log_nonneg
      have hlogThree : (1 : ℝ) ≤ Real.log 3 := by
        nlinarith [Real.log_three_gt_d9]
      exact hlogThree.trans
        (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hlogY0 _)
        (Real.rpow_nonneg hlogq0 _))
      (Real.rpow_nonneg hloglogq0 _)
  have hmiddle0 :
      0 ≤ Cₖ * korolevPrefixDecay q Y *
        (2 + (harmonic U : ℝ)) := by
    exact mul_nonneg (mul_nonneg hCₖ hdecay)
      (by linarith [harmonic_nonneg U])
  have hcompletedScale : 0 ≤ completedInversePrefixScale q := by
    have hsigma : 0 ≤ reciprocalSqrtDivisorSum q := by
      unfold reciprocalSqrtDivisorSum
      positivity
    unfold completedInversePrefixScale
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) hsigma)
      (sq_nonneg _)
  have htail0 :
      0 ≤ 2 * ((U + 1 : ℕ) : ℝ)⁻¹ *
        (Cₑ * completedInversePrefixScale q) := by positivity
  have hlow : ∀ X, X ≤ Y →
      ‖inverseSawPartial q r X‖ ≤
        (1 / 2 : ℝ) * (harmonic Y : ℝ) := by
    intro X hXY
    calc
      ‖inverseSawPartial q r X‖ ≤
          (1 / 2 : ℝ) * (harmonic X : ℝ) :=
        norm_inverseSawPartial_le_half_harmonic hqpos
      _ ≤ (1 / 2 : ℝ) * (harmonic Y : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (NField.Alignment.DedekindFourierMoment.harmonic_cast_mono hXY)
          (by norm_num)
  have hmiddle' : ∀ X, Y < X → X ≤ U →
      ‖∑ n ∈ Finset.Ico Y X,
          inverseSawTerm q r (n + 1)‖ ≤
        Cₖ * korolevPrefixDecay q Y *
          (2 + (harmonic U : ℝ)) := by
    intro X hYX hXU
    have hUpperX : (X : ℝ) ≤ korolevUpperRange q :=
      (show (X : ℝ) ≤ (U : ℝ) by exact_mod_cast hXU).trans hUpper
    have hm := hmiddle q r Y X hthreshold hq hr hY hYX hLower hUpperX
    calc
      ‖∑ n ∈ Finset.Ico Y X,
          inverseSawTerm q r (n + 1)‖ ≤
          Cₖ * korolevPrefixDecay q Y *
            (2 + (harmonic X : ℝ)) := hm
      _ ≤ Cₖ * korolevPrefixDecay q Y *
          (2 + (harmonic U : ℝ)) := by
        have hH : 2 + (harmonic X : ℝ) ≤
            2 + (harmonic U : ℝ) := by
          linarith [NField.Alignment.DedekindFourierMoment.harmonic_cast_mono hXU]
        exact mul_le_mul_of_nonneg_left
          hH (mul_nonneg hCₖ hdecay)
  have htail' : ∀ X, U < X →
      ‖∑ n ∈ Finset.Ico U X,
          inverseSawTerm q r (n + 1)‖ ≤
        2 * ((U + 1 : ℕ) : ℝ)⁻¹ *
          (Cₑ * completedInversePrefixScale q) := by
    intro X _hUX
    exact htail q r U X (by omega) hr
  have hthree := norm_inverseSawPartial_le_threeRange
    (q := q) (r := r) (Y := Y) (U := U)
    (low := (1 / 2 : ℝ) * (harmonic Y : ℝ))
    (middle := Cₖ * korolevPrefixDecay q Y *
      (2 + (harmonic U : ℝ)))
    (tail := 2 * ((U + 1 : ℕ) : ℝ)⁻¹ *
      (Cₑ * completedInversePrefixScale q))
    (Nat.le_of_lt hYU) hlow0 hmiddle0 htail0 hlow hmiddle' htail' N
  simpa [inverseSawThreeRangeEnvelope] using hthree

/-! ## Concrete cutoff selection -/

/-- A convenient natural cutoff lying just above the lower end of Korolev's
range.  The exponent `9/10` leaves room above the published `4/5` exponent
and below the completion boundary. -/
noncomputable def inverseSawLowerCutoff (q : ℕ) : ℕ :=
  Nat.ceil (Real.exp
    (Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ)))

/-- The largest natural prefix below Korolev's `q^(4/7)` upper edge. -/
noncomputable def inverseSawUpperCutoff (q : ℕ) : ℕ :=
  Nat.floor (Real.rpow (q : ℝ) (4 / 7 : ℝ))

/-- The published lower-range exponent is eventually below the convenient
nine-tenths power of `log q`. -/
theorem korolevLowerExponent_le_convenient_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      Real.rpow (Real.log (q : ℝ)) (4 / 5 : ℝ) *
          Real.rpow (Real.log (Real.log (q : ℝ))) (73 / 5 : ℝ) ≤
        Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ) := by
  filter_upwards [
    loglog_rpow_le_log_rpow_tenth_eventually
      (show (73 / 5 : ℝ) ≤ 16 by norm_num),
    Filter.eventually_ge_atTop 3] with q hloglog hq
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  calc
    Real.rpow (Real.log (q : ℝ)) (4 / 5 : ℝ) *
        Real.rpow (Real.log (Real.log (q : ℝ))) (73 / 5 : ℝ) ≤
      Real.rpow (Real.log (q : ℝ)) (4 / 5 : ℝ) *
        Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hloglog
            (Real.rpow_nonneg hlogqPos.le _)
    _ = Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ) := by
      calc
        _ = Real.rpow (Real.log (q : ℝ))
            ((4 / 5 : ℝ) + (1 / 10 : ℝ)) :=
          (Real.rpow_add hlogqPos _ _).symm
        _ = _ := by norm_num

/-- The natural lower cutoff is inside Korolev's published range. -/
theorem korolevLowerRange_le_lowerCutoff_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      korolevLowerRange q ≤ (inverseSawLowerCutoff q : ℝ) := by
  filter_upwards [korolevLowerExponent_le_convenient_eventually] with q hq
  unfold korolevLowerRange inverseSawLowerCutoff
  exact (Real.exp_le_exp.mpr hq).trans (Nat.le_ceil _)

/-- The natural upper cutoff stays below the published upper range. -/
theorem upperCutoff_le_korolevUpperRange (q : ℕ) :
    (inverseSawUpperCutoff q : ℝ) ≤ korolevUpperRange q := by
  unfold inverseSawUpperCutoff korolevUpperRange
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

/-- The two natural cutoffs are eventually nonempty and correctly ordered. -/
theorem lowerCutoff_lt_upperCutoff_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      2 ≤ inverseSawLowerCutoff q ∧
        inverseSawLowerCutoff q < inverseSawUpperCutoff q := by
  have htendLog : Filter.Tendsto (fun q : ℕ => Real.log (q : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun q : ℕ => (q : ℝ))
          Filter.atTop Filter.atTop)
  have htendLogTenth : Filter.Tendsto
      (fun q : ℕ => Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      htendLog
  have htendHalf : Filter.Tendsto
      (fun q : ℕ => Real.rpow (q : ℝ) (1 / 2 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun q : ℕ => (q : ℝ))
          Filter.atTop Filter.atTop)
  have htendFourteenth : Filter.Tendsto
      (fun q : ℕ => Real.rpow (q : ℝ) (1 / 14 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 14)).comp
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun q : ℕ => (q : ℝ))
          Filter.atTop Filter.atTop)
  filter_upwards [Filter.eventually_ge_atTop 3,
    htendLogTenth.eventually_ge_atTop 2,
    htendHalf.eventually_ge_atTop 1,
    htendFourteenth.eventually_ge_atTop 3] with
      q hq hlogTenth hhalf hfourteenth
  have hqR : (0 : ℝ) < q := by positivity
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  let B := Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ)
  have hBnonneg : 0 ≤ B := Real.rpow_nonneg hlogqPos.le _
  have hfactorization :
      B * Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) =
        Real.log (q : ℝ) := by
    dsimp [B]
    calc
      Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ) *
          Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) =
        Real.rpow (Real.log (q : ℝ))
          ((9 / 10 : ℝ) + (1 / 10 : ℝ)) :=
        (Real.rpow_add hlogqPos _ _).symm
      _ = Real.log (q : ℝ) := by norm_num
  have hBhalf : B ≤ Real.log (q : ℝ) / 2 := by
    have hmul : 2 * B ≤
        Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) * B :=
      mul_le_mul_of_nonneg_right hlogTenth hBnonneg
    have hfactorization' :
        Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) * B =
          Real.log (q : ℝ) := by simpa [mul_comm] using hfactorization
    rw [hfactorization'] at hmul
    linarith
  have hexpB : Real.exp B ≤ Real.rpow (q : ℝ) (1 / 2 : ℝ) := by
    have hrpowHalf : Real.rpow (q : ℝ) (1 / 2 : ℝ) =
        Real.exp (Real.log (q : ℝ) * (1 / 2 : ℝ)) :=
      Real.rpow_def_of_pos hqR _
    rw [hrpowHalf]
    apply (Real.exp_le_exp).2
    nlinarith
  have hupperFactor :
      Real.rpow (q : ℝ) (4 / 7 : ℝ) =
        Real.rpow (q : ℝ) (1 / 2 : ℝ) *
          Real.rpow (q : ℝ) (1 / 14 : ℝ) := by
    calc
      _ = Real.rpow (q : ℝ)
          ((1 / 2 : ℝ) + (1 / 14 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hqR _ _
  have hupperLarge :
      Real.rpow (q : ℝ) (1 / 2 : ℝ) + 2 ≤
        Real.rpow (q : ℝ) (4 / 7 : ℝ) := by
    rw [hupperFactor]
    have hmul := mul_le_mul_of_nonneg_left hfourteenth
      (Real.rpow_nonneg hqR.le (1 / 2 : ℝ))
    nlinarith
  have hceil : (inverseSawLowerCutoff q : ℝ) < Real.exp B + 1 := by
    unfold inverseSawLowerCutoff
    exact Nat.ceil_lt_add_one (Real.exp_nonneg B)
  have hlowerTwo : 2 ≤ inverseSawLowerCutoff q := by
    have hexpTwo : (2 : ℝ) < Real.exp B := by
      have hB : 1 ≤ B := by
        have hlogOne : 1 ≤ Real.log (q : ℝ) := by
          have : (1 : ℝ) ≤ Real.log 3 := by
            nlinarith [Real.log_three_gt_d9]
          exact this.trans
            (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
        exact Real.one_le_rpow hlogOne (by norm_num)
      calc
        (2 : ℝ) < Real.exp 1 := by
          simpa using Real.exp_one_gt_two
        _ ≤ Real.exp B := Real.exp_le_exp.mpr hB
    have hceilBase := Nat.le_ceil (Real.exp B)
    exact_mod_cast (show (2 : ℝ) ≤ (inverseSawLowerCutoff q : ℝ) from
      hexpTwo.le.trans hceilBase)
  have hcastSuccessor :
      ((inverseSawLowerCutoff q + 1 : ℕ) : ℝ) ≤
        Real.rpow (q : ℝ) (4 / 7 : ℝ) := by
    push_cast
    linarith
  have hsuccessorFloor :
      inverseSawLowerCutoff q + 1 ≤ inverseSawUpperCutoff q := by
    unfold inverseSawUpperCutoff
    exact Nat.le_floor hcastSuccessor
  exact ⟨hlowerTwo, by omega⟩

/-- Replacing `log log q` by the paper's everywhere-positive
`log log (3q)` changes the eventual scale by at most a factor two. -/
theorem loglog_three_mul_le_two_loglog_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      0 < Real.log (Real.log (3 * (q : ℝ))) ∧
        Real.log (Real.log (3 * (q : ℝ))) ≤
          2 * Real.log (Real.log (q : ℝ)) := by
  have htendLogLog : Filter.Tendsto
      (fun q : ℕ => Real.log (Real.log (q : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun q : ℕ => (q : ℝ))
            Filter.atTop Filter.atTop))
  filter_upwards [Filter.eventually_ge_atTop 3,
    htendLogLog.eventually_ge_atTop (Real.log 2)] with q hq hloglog
  have hqR : (0 : ℝ) < q := by positivity
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogThreeLe : Real.log 3 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hlog3q : Real.log (3 * (q : ℝ)) ≤
      2 * Real.log (q : ℝ) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hqR.ne']
    linarith
  have hdenPos : 0 < Real.log (Real.log (3 * (q : ℝ))) := by
    apply Real.log_pos
    have harg : Real.exp 1 < 3 * (q : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * (q : ℝ) := by exact_mod_cast (show 3 ≤ 3 * q by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity)).2 harg
  refine ⟨hdenPos, ?_⟩
  have hlog3qPos : 0 < Real.log (3 * (q : ℝ)) :=
    Real.log_pos (by
      have : (1 : ℝ) < 3 * (q : ℝ) := by exact_mod_cast (show 1 < 3 * q by omega)
      exact this)
  have hlogBound : Real.log (Real.log (3 * (q : ℝ))) ≤
      Real.log (2 * Real.log (q : ℝ)) :=
    Real.log_le_log hlog3qPos hlog3q
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogqPos.ne'] at hlogBound
  linarith

/-- The complete initial-range contribution at the chosen lower cutoff is
bounded by the paper's logarithmic-over-log-log scale. -/
theorem lowerCutoffHarmonic_le_scale_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      (1 / 2 : ℝ) * (harmonic (inverseSawLowerCutoff q) : ℝ) ≤
        4 * inverseResidueHarmonicScale q := by
  filter_upwards [Filter.eventually_ge_atTop 3,
    lowerCutoff_lt_upperCutoff_eventually,
    loglog_three_mul_le_two_loglog_eventually,
    loglog_rpow_le_log_rpow_eventually 1
      (show (0 : ℝ) < 1 / 10 by norm_num)] with
      q hq hcutoffs hdenCompare hloglogPower
  have hqR : (0 : ℝ) < q := by positivity
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogqOne : 1 ≤ Real.log (q : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hthree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hlogqGtOne : 1 < Real.log (q : ℝ) := by
    have hthree : (1 : ℝ) < Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hthree.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hloglogqPos : 0 < Real.log (Real.log (q : ℝ)) :=
    Real.log_pos hlogqGtOne
  have hloglogq0 : 0 ≤ Real.log (Real.log (q : ℝ)) :=
    hloglogqPos.le
  have hloglogLe : Real.log (Real.log (q : ℝ)) ≤
      Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) := by
    simpa using hloglogPower
  let B := Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ)
  have hB0 : 0 ≤ B := Real.rpow_nonneg hlogqPos.le _
  have hB1 : 1 ≤ B := Real.one_le_rpow hlogqOne (by norm_num)
  have hfactorization :
      B * Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) =
        Real.log (q : ℝ) := by
    dsimp [B]
    calc
      Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ) *
          Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ) =
        Real.rpow (Real.log (q : ℝ))
          ((9 / 10 : ℝ) + (1 / 10 : ℝ)) :=
        (Real.rpow_add hlogqPos _ _).symm
      _ = Real.log (q : ℝ) := by norm_num
  let den := Real.log (Real.log (3 * (q : ℝ)))
  have hdenPos : 0 < den := hdenCompare.1
  have hBden : B * den ≤ 2 * Real.log (q : ℝ) := by
    calc
      B * den ≤ B * (2 * Real.log (Real.log (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hdenCompare.2 hB0
      _ ≤ B * (2 * Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ)) := by
        gcongr
      _ = 2 *
          (B * Real.rpow (Real.log (q : ℝ)) (1 / 10 : ℝ)) := by ring
      _ = 2 * Real.log (q : ℝ) := by rw [hfactorization]
  have hBscale : B ≤ 2 * inverseResidueHarmonicScale q := by
    unfold inverseResidueHarmonicScale
    dsimp [den] at hdenPos hBden ⊢
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hdenPos).2
    have hlogMono : Real.log (q : ℝ) ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_le_log hqR (by nlinarith)
    nlinarith
  let Y := inverseSawLowerCutoff q
  have hYtwo : 2 ≤ Y := hcutoffs.1
  have hceil : (Y : ℝ) < Real.exp B + 1 := by
    unfold Y inverseSawLowerCutoff
    exact Nat.ceil_lt_add_one (Real.exp_nonneg B)
  have hexpOne : 1 ≤ Real.exp B := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hB0
  have hYbound : (Y : ℝ) ≤ 2 * Real.exp B := by
    linarith
  have hlogY : Real.log (Y : ℝ) ≤ Real.log 2 + B := by
    calc
      Real.log (Y : ℝ) ≤ Real.log (2 * Real.exp B) :=
        Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) hYbound
      _ = Real.log 2 + B := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero B),
          Real.log_exp]
  have hHq := harmonic_le_one_add_log Y
  have hH : (harmonic Y : ℝ) ≤ 1 + Real.log (Y : ℝ) := by
    exact_mod_cast hHq
  have hHtoB : (harmonic Y : ℝ) ≤ 3 * B := by
    have hlogTwo : Real.log 2 ≤ 1 := by
      linarith [Real.log_two_lt_d9]
    linarith
  change (1 / 2 : ℝ) * (harmonic Y : ℝ) ≤ _
  calc
    (1 / 2 : ℝ) * (harmonic Y : ℝ) ≤ (1 / 2 : ℝ) * (3 * B) := by
      gcongr
    _ ≤ 4 * inverseResidueHarmonicScale q := by linarith

/-- At the convenient lower cutoff, Korolev's decay factor has already
gained one full inverse `log log q`. -/
theorem lowerCutoffDecay_mul_loglog_le_one_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      korolevPrefixDecay q (inverseSawLowerCutoff q) *
          Real.log (Real.log (q : ℝ)) ≤ 1 := by
  filter_upwards [Filter.eventually_ge_atTop 3,
    loglog_rpow_le_log_rpow_eventually (73 / 24 : ℝ)
      (show (0 : ℝ) < 1 / 48 by norm_num)] with q hq hpower
  have hqR : (0 : ℝ) < q := by positivity
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogqOne : 1 ≤ Real.log (q : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hthree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hlogqGtOne : 1 < Real.log (q : ℝ) := by
    have hthree : (1 : ℝ) < Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hthree.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hloglogqPos : 0 < Real.log (Real.log (q : ℝ)) :=
    Real.log_pos hlogqGtOne
  have hloglogq0 : 0 ≤ Real.log (Real.log (q : ℝ)) :=
    hloglogqPos.le
  let B := Real.rpow (Real.log (q : ℝ)) (9 / 10 : ℝ)
  have hBpos : 0 < B := Real.rpow_pos_of_pos hlogqPos _
  have hceil : Real.exp B ≤ (inverseSawLowerCutoff q : ℝ) := by
    unfold inverseSawLowerCutoff
    exact Nat.le_ceil _
  have hYpos : 0 < (inverseSawLowerCutoff q : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos B) hceil
  have hlogY : B ≤ Real.log (inverseSawLowerCutoff q : ℝ) := by
    rw [← Real.log_exp B]
    exact Real.log_le_log (Real.exp_pos B) hceil
  have hnegative :
      Real.rpow (Real.log (inverseSawLowerCutoff q : ℝ))
          (-5 / 24 : ℝ) ≤ Real.rpow B (-5 / 24 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hBpos hlogY (by norm_num)
  have hrewrite :
      Real.rpow B (-5 / 24 : ℝ) *
            Real.rpow (Real.log (q : ℝ)) (1 / 6 : ℝ) *
          Real.rpow (Real.log (Real.log (q : ℝ))) (49 / 24 : ℝ) *
            Real.log (Real.log (q : ℝ)) =
        Real.rpow (Real.log (q : ℝ)) (-1 / 48 : ℝ) *
          Real.rpow (Real.log (Real.log (q : ℝ))) (73 / 24 : ℝ) := by
    have hBpow :
        Real.rpow B (-5 / 24 : ℝ) =
          Real.rpow (Real.log (q : ℝ))
            ((9 / 10 : ℝ) * (-5 / 24 : ℝ)) := by
      dsimp [B]
      exact (Real.rpow_mul hlogqPos.le _ _).symm
    have hloglogCombine :
        Real.rpow (Real.log (Real.log (q : ℝ))) (49 / 24 : ℝ) *
            Real.log (Real.log (q : ℝ)) =
          Real.rpow (Real.log (Real.log (q : ℝ))) (73 / 24 : ℝ) := by
      calc
        _ = Real.rpow (Real.log (Real.log (q : ℝ))) (49 / 24 : ℝ) *
            Real.rpow (Real.log (Real.log (q : ℝ))) 1 := by
              congr 1
              exact (Real.rpow_one _).symm
        _ = Real.rpow (Real.log (Real.log (q : ℝ)))
            ((49 / 24 : ℝ) + 1) :=
              (Real.rpow_add hloglogqPos _ _).symm
        _ = _ := by norm_num
    have hlogqCombine :
        Real.rpow (Real.log (q : ℝ))
              ((9 / 10 : ℝ) * (-5 / 24 : ℝ)) *
            Real.rpow (Real.log (q : ℝ)) (1 / 6 : ℝ) =
          Real.rpow (Real.log (q : ℝ)) (-1 / 48 : ℝ) := by
      calc
        _ = Real.rpow (Real.log (q : ℝ))
            ((9 / 10 : ℝ) * (-5 / 24 : ℝ) + 1 / 6) :=
              (Real.rpow_add hlogqPos _ _).symm
        _ = _ := by norm_num
    calc
      _ =
          (Real.rpow B (-5 / 24 : ℝ) *
            Real.rpow (Real.log (q : ℝ)) (1 / 6 : ℝ)) *
          (Real.rpow (Real.log (Real.log (q : ℝ))) (49 / 24 : ℝ) *
            Real.log (Real.log (q : ℝ))) := by ring
      _ = _ := by rw [hBpow, hlogqCombine, hloglogCombine]
  have hinvPower :
      Real.rpow (Real.log (q : ℝ)) (-1 / 48 : ℝ) *
          Real.rpow (Real.log (Real.log (q : ℝ))) (73 / 24 : ℝ) ≤ 1 := by
    have hnonneg := Real.rpow_nonneg hlogqPos.le (-1 / 48 : ℝ)
    calc
      _ ≤ Real.rpow (Real.log (q : ℝ)) (-1 / 48 : ℝ) *
          Real.rpow (Real.log (q : ℝ)) (1 / 48 : ℝ) :=
        mul_le_mul_of_nonneg_left hpower hnonneg
      _ = Real.rpow (Real.log (q : ℝ))
          ((-1 / 48 : ℝ) + (1 / 48 : ℝ)) :=
        (Real.rpow_add hlogqPos _ _).symm
      _ = 1 := by norm_num
  unfold korolevPrefixDecay
  calc
    Real.rpow (Real.log (inverseSawLowerCutoff q : ℝ)) (-5 / 24 : ℝ) *
          Real.rpow (Real.log (q : ℝ)) (1 / 6 : ℝ) *
        Real.rpow (Real.log (Real.log (q : ℝ))) (49 / 24 : ℝ) *
          Real.log (Real.log (q : ℝ)) ≤
      Real.rpow B (-5 / 24 : ℝ) *
          Real.rpow (Real.log (q : ℝ)) (1 / 6 : ℝ) *
        Real.rpow (Real.log (Real.log (q : ℝ))) (49 / 24 : ℝ) *
          Real.log (Real.log (q : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hnegative
                  (Real.rpow_nonneg hlogqPos.le _))
                (Real.rpow_nonneg hloglogq0 _))
              hloglogq0
    _ = Real.rpow (Real.log (q : ℝ)) (-1 / 48 : ℝ) *
          Real.rpow (Real.log (Real.log (q : ℝ))) (73 / 24 : ℝ) :=
      hrewrite
    _ ≤ 1 := hinvPower

/-- The Abel harmonic factor at the upper cutoff is at most a fixed multiple
of `log q`. -/
theorem upperCutoffHarmonic_le_log_eventually :
    ∀ᶠ q : ℕ in Filter.atTop,
      2 + (harmonic (inverseSawUpperCutoff q) : ℝ) ≤
        4 * Real.log (q : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 3,
    lowerCutoff_lt_upperCutoff_eventually] with q hq hcutoffs
  let U := inverseSawUpperCutoff q
  have hUpos : 0 < U := by dsimp [U]; omega
  have hqR : (0 : ℝ) < q := by positivity
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hUbound : (U : ℝ) ≤ Real.rpow (q : ℝ) (4 / 7 : ℝ) := by
    dsimp [U]
    exact upperCutoff_le_korolevUpperRange q
  have hpowPos : 0 < Real.rpow (q : ℝ) (4 / 7 : ℝ) :=
    Real.rpow_pos_of_pos hqR _
  have hlogU : Real.log (U : ℝ) ≤ (4 / 7 : ℝ) * Real.log (q : ℝ) := by
    calc
      Real.log (U : ℝ) ≤
          Real.log (Real.rpow (q : ℝ) (4 / 7 : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hUpos) hUbound
      _ = (4 / 7 : ℝ) * Real.log (q : ℝ) := by
        exact Real.log_rpow hqR _
  have hHq := harmonic_le_one_add_log U
  have hH : (harmonic U : ℝ) ≤ 1 + Real.log (U : ℝ) := by
    exact_mod_cast hHq
  change 2 + (harmonic U : ℝ) ≤ _
  have hlogqOne : 1 ≤ Real.log (q : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hthree.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  linarith

/-- The entire Korolev middle-range contribution at the concrete cutoffs is
bounded by the manuscript's scale. -/
theorem middleCutoffContribution_le_scale_eventually
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ q : ℕ in Filter.atTop,
      C * korolevPrefixDecay q (inverseSawLowerCutoff q) *
          (2 + (harmonic (inverseSawUpperCutoff q) : ℝ)) ≤
        8 * C * inverseResidueHarmonicScale q := by
  filter_upwards [Filter.eventually_ge_atTop 3,
    lowerCutoff_lt_upperCutoff_eventually,
    lowerCutoffDecay_mul_loglog_le_one_eventually,
    upperCutoffHarmonic_le_log_eventually,
    loglog_three_mul_le_two_loglog_eventually] with
      q hq hcutoffs hdecayProduct hHarmonic hdenCompare
  let decay := korolevPrefixDecay q (inverseSawLowerCutoff q)
  let ell := Real.log (Real.log (q : ℝ))
  let den := Real.log (Real.log (3 * (q : ℝ)))
  have hqR : (0 : ℝ) < q := by positivity
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlogqGtOne : 1 < Real.log (q : ℝ) := by
    have hthree : (1 : ℝ) < Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hthree.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hellPos : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos hlogqGtOne
  have hdenPos : 0 < den := hdenCompare.1
  have hdecay0 : 0 ≤ decay := by
    dsimp [decay]
    unfold korolevPrefixDecay
    have hYpos : 0 < Real.log (inverseSawLowerCutoff q : ℝ) :=
      Real.log_pos (by exact_mod_cast hcutoffs.1)
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hYpos.le _)
        (Real.rpow_nonneg hlogqPos.le _))
      (Real.rpow_nonneg hellPos.le _)
  have hdecay : decay ≤ 1 / ell := by
    apply (le_div_iff₀ hellPos).2
    dsimp [decay, ell]
    simpa [mul_comm] using hdecayProduct
  have hlogScale : Real.log (q : ℝ) / ell ≤
      2 * inverseResidueHarmonicScale q := by
    unfold inverseResidueHarmonicScale
    dsimp [ell, den] at hdenPos ⊢
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by exact hellPos) hdenPos).2
    have hlogMono : Real.log (q : ℝ) ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_le_log hqR (by nlinarith)
    have hdenLe : Real.log (Real.log (3 * (q : ℝ))) ≤
        2 * Real.log (Real.log (q : ℝ)) := hdenCompare.2
    nlinarith
  have hH0 : 0 ≤ 2 + (harmonic (inverseSawUpperCutoff q) : ℝ) := by
    have hQ : (0 : ℚ) ≤ harmonic (inverseSawUpperCutoff q) := by
      unfold harmonic
      positivity
    have hR : (0 : ℝ) ≤ (harmonic (inverseSawUpperCutoff q) : ℝ) := by
      exact_mod_cast hQ
    linarith
  calc
    C * decay * (2 + (harmonic (inverseSawUpperCutoff q) : ℝ)) ≤
        C * (1 / ell) * (4 * Real.log (q : ℝ)) := by
          gcongr
    _ = 4 * C * (Real.log (q : ℝ) / ell) := by ring
    _ ≤ 4 * C * (2 * inverseResidueHarmonicScale q) := by
      exact mul_le_mul_of_nonneg_left hlogScale (mul_nonneg (by norm_num) hC)
    _ = 8 * C * inverseResidueHarmonicScale q := by ring

/-- The standard subpower divisor estimates used after completion, stated at
one fixed exponent sufficient for the manuscript's `q^(4/7)` cutoff.  This is
the source-level consequence of the classical divisor bounds, not the target
inverse-harmonic estimate. -/
def StandardCompletedPrefixDivisorGrowth : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ q,
    threshold ≤ q →
      completedInversePrefixScale q ≤
        C * Real.rpow (q : ℝ) (15 / 28 : ℝ)

/-- The paper's harmonic scale is bounded below by one half.  This lets the
bounded completion tail be absorbed without changing its displayed scale. -/
theorem one_half_le_inverseResidueHarmonicScale
    {q : ℕ} (hq : 2 ≤ q) :
    (1 / 2 : ℝ) ≤ inverseResidueHarmonicScale q := by
  unfold inverseResidueHarmonicScale
  have hqR : (0 : ℝ) < q := by positivity
  have hnumPos : 0 < Real.log (2 * (q : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * q by omega))
  have hlog3qGtOne : 1 < Real.log (3 * (q : ℝ)) := by
    have harg : Real.exp 1 < 3 * (q : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * (q : ℝ) := by exact_mod_cast (show 3 ≤ 3 * q by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity)).2 harg
  have hdenPos : 0 < Real.log (Real.log (3 * (q : ℝ))) :=
    Real.log_pos hlog3qGtOne
  have hdenLeLog3q : Real.log (Real.log (3 * (q : ℝ))) ≤
      Real.log (3 * (q : ℝ)) := by
    have hraw := Real.log_le_sub_one_of_pos
      (show 0 < Real.log (3 * (q : ℝ)) from hlog3qGtOne.trans' (by norm_num))
    linarith
  have hlog3qLe : Real.log (3 * (q : ℝ)) ≤
      2 * Real.log (2 * (q : ℝ)) := by
    have harg : 3 * (q : ℝ) ≤ (2 * (q : ℝ)) ^ 2 := by
      nlinarith [show (2 : ℝ) ≤ q by exact_mod_cast hq]
    calc
      Real.log (3 * (q : ℝ)) ≤ Real.log ((2 * (q : ℝ)) ^ 2) :=
        Real.log_le_log (by positivity) harg
      _ = 2 * Real.log (2 * (q : ℝ)) := by
        rw [Real.log_pow]
        norm_num
  apply (le_div_iff₀ hdenPos).2
  nlinarith

/-- Completion and the standard divisor growth estimate make the entire upper
tail bounded, hence bounded by the manuscript's positive harmonic scale. -/
theorem upperCutoffTail_le_scale_eventually
    (completionConstant divisorConstant : ℝ)
    (hcompletionConstant : 0 ≤ completionConstant)
    (hdivisorConstant : 0 ≤ divisorConstant)
    (threshold : ℕ)
    (hdivisor : ∀ q, threshold ≤ q →
      completedInversePrefixScale q ≤
        divisorConstant * Real.rpow (q : ℝ) (15 / 28 : ℝ)) :
    ∀ᶠ q : ℕ in Filter.atTop,
      2 * ((inverseSawUpperCutoff q + 1 : ℕ) : ℝ)⁻¹ *
          (completionConstant * completedInversePrefixScale q) ≤
        4 * completionConstant * divisorConstant *
          inverseResidueHarmonicScale q := by
  filter_upwards [Filter.eventually_ge_atTop (max 2 threshold)] with q hq
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hthreshold : threshold ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (0 : ℝ) < q := by positivity
  let Q := Real.rpow (q : ℝ) (4 / 7 : ℝ)
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hqR _
  have hfloor : Q < (inverseSawUpperCutoff q + 1 : ℕ) := by
    unfold inverseSawUpperCutoff
    dsimp [Q]
    simpa [Q, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one
        (Real.rpow (q : ℝ) (4 / 7 : ℝ)))
  have hinv : (((inverseSawUpperCutoff q + 1 : ℕ) : ℝ))⁻¹ ≤ Q⁻¹ := by
    exact (inv_le_inv₀ (by positivity) hQpos).2 hfloor.le
  have hscale0 : 0 ≤ completedInversePrefixScale q := by
    unfold completedInversePrefixScale reciprocalSqrtDivisorSum
    positivity
  have hpower0 : 0 ≤ Real.rpow (q : ℝ) (15 / 28 : ℝ) :=
    Real.rpow_nonneg hqR.le _
  have hdecay : Q⁻¹ * Real.rpow (q : ℝ) (15 / 28 : ℝ) ≤ 1 := by
    have hrewrite : Q⁻¹ * Real.rpow (q : ℝ) (15 / 28 : ℝ) =
        Real.rpow (q : ℝ) (-1 / 28 : ℝ) := by
      dsimp [Q]
      rw [← Real.rpow_neg hqR.le]
      rw [← Real.rpow_add hqR]
      congr 1
      norm_num
    rw [hrewrite]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ q by omega)) (by norm_num)
  have hbounded :
      2 * (((inverseSawUpperCutoff q + 1 : ℕ) : ℝ))⁻¹ *
          (completionConstant * completedInversePrefixScale q) ≤
        2 * completionConstant * divisorConstant := by
    calc
      _ ≤ 2 * Q⁻¹ *
          (completionConstant * completedInversePrefixScale q) := by
            gcongr
      _ ≤ 2 * Q⁻¹ *
          (completionConstant *
            (divisorConstant * Real.rpow (q : ℝ) (15 / 28 : ℝ))) := by
            gcongr
            exact hdivisor q hthreshold
      _ = 2 * completionConstant * divisorConstant *
          (Q⁻¹ * Real.rpow (q : ℝ) (15 / 28 : ℝ)) := by ring
      _ ≤ 2 * completionConstant * divisorConstant * 1 := by
        exact mul_le_mul_of_nonneg_left hdecay
          (mul_nonneg (mul_nonneg (by norm_num) hcompletionConstant)
            hdivisorConstant)
      _ = 2 * completionConstant * divisorConstant := by ring
  have hscaleLower := one_half_le_inverseResidueHarmonicScale hq2
  calc
    _ ≤ 2 * completionConstant * divisorConstant := hbounded
    _ ≤ 4 * completionConstant * divisorConstant *
        inverseResidueHarmonicScale q := by
      have hnonneg := mul_nonneg hcompletionConstant hdivisorConstant
      nlinarith

/-- The source Korolev estimate, completed prefixes, and standard divisor
growth imply the desired bound for every partial sum at every sufficiently
large modulus. -/
theorem inverseSawPartial_le_own_scale_eventually
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : CompletedInversePrefixEstimate)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ q : ℕ in Filter.atTop, ∀ r N,
        r.Coprime q →
          ‖inverseSawPartial q r N‖ ≤
            C * inverseResidueHarmonicScale q := by
  rcases inverseSawThreeRangeEstimate hKorolev hcompletion with
    ⟨Cₖ, Cₑ, hCₖ, hCₑ, sourceThreshold, hthree⟩
  rcases hdivisorGrowth with
    ⟨Cdivisor, hCdivisor, divisorThreshold, hdivisor⟩
  let C := 4 + 8 * Cₖ + 4 * Cₑ * Cdivisor
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max 3 sourceThreshold),
    lowerCutoff_lt_upperCutoff_eventually,
    korolevLowerRange_le_lowerCutoff_eventually,
    lowerCutoffHarmonic_le_scale_eventually,
    middleCutoffContribution_le_scale_eventually Cₖ hCₖ,
    upperCutoffTail_le_scale_eventually Cₑ Cdivisor hCₑ hCdivisor
      divisorThreshold hdivisor] with
      q hq hcutoffs hLower hlow hmiddle htail
  intro r N hr
  have hq3 : 3 ≤ q := le_trans (le_max_left _ _) hq
  have hsource : sourceThreshold ≤ q :=
    le_trans (le_max_right _ _) hq
  have hbound := hthree q r
    (inverseSawLowerCutoff q) (inverseSawUpperCutoff q) N
    hsource hq3 hr hcutoffs.1 hcutoffs.2 hLower
    (upperCutoff_le_korolevUpperRange q)
  have hscale0 : 0 ≤ inverseResidueHarmonicScale q :=
    inverseResidueHarmonicScale_nonneg (by omega)
  unfold inverseSawThreeRangeEnvelope at hbound
  dsimp [C]
  linarith

/-- The finite exceptional moduli are absorbed with the completed-prefix
bound.  Thus the three source inputs prove the pointwise partial-sum estimate
for every modulus. -/
def PointwiseInverseSawPartialHarmonicEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q r N,
    2 ≤ q → r.Coprime q →
      ‖inverseSawPartial q r N‖ ≤
        C * inverseResidueHarmonicScale q

theorem pointwiseInverseSawPartialHarmonicEstimate
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : CompletedInversePrefixEstimate)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth) :
    PointwiseInverseSawPartialHarmonicEstimate := by
  rcases inverseSawPartial_le_own_scale_eventually
      hKorolev hcompletion hdivisorGrowth with
    ⟨Clarge, hClarge, heventual⟩
  rcases Filter.eventually_atTop.1 heventual with
    ⟨threshold, hlarge⟩
  rcases completedInverseHarmonicTailEstimate hcompletion with
    ⟨Ccompletion, hCcompletion, htail⟩
  let exceptionalMass :=
    ∑ q ∈ Finset.range threshold, completedInversePrefixScale q
  have hexceptionalMass : 0 ≤ exceptionalMass := by
    dsimp [exceptionalMass]
    apply Finset.sum_nonneg
    intro q _hq
    unfold completedInversePrefixScale reciprocalSqrtDivisorSum
    positivity
  let C := Clarge + 4 * Ccompletion * exceptionalMass
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q r N hq hr
  have htarget0 : 0 ≤ inverseResidueHarmonicScale q :=
    inverseResidueHarmonicScale_nonneg hq
  by_cases hthreshold : threshold ≤ q
  · have hmain := hlarge q hthreshold r N hr
    exact hmain.trans (by
      dsimp [C]
      nlinarith [mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCcompletion)
        hexceptionalMass])
  · have hqRange : q ∈ Finset.range threshold :=
      Finset.mem_range.mpr (Nat.lt_of_not_ge hthreshold)
    have hscale0 : 0 ≤ completedInversePrefixScale q := by
      unfold completedInversePrefixScale reciprocalSqrtDivisorSum
      positivity
    have hscaleExceptional : completedInversePrefixScale q ≤
        exceptionalMass := by
      dsimp [exceptionalMass]
      exact Finset.single_le_sum
        (fun x _hx => by
          unfold completedInversePrefixScale reciprocalSqrtDivisorSum
          positivity) hqRange
    have htailBound := htail q r 0 N hq hr
    have hpartial : ‖inverseSawPartial q r N‖ ≤
        2 * Ccompletion * completedInversePrefixScale q := by
      simpa [inverseSawPartial, Nat.add_comm, mul_assoc] using htailBound
    have hfinite : ‖inverseSawPartial q r N‖ ≤
        2 * Ccompletion * exceptionalMass := by
      calc
        _ ≤ 2 * Ccompletion * completedInversePrefixScale q := hpartial
        _ ≤ 2 * Ccompletion * exceptionalMass := by gcongr
    have hscaleLower := one_half_le_inverseResidueHarmonicScale hq
    calc
      ‖inverseSawPartial q r N‖ ≤
          2 * Ccompletion * exceptionalMass := hfinite
      _ ≤ (4 * Ccompletion * exceptionalMass) *
          inverseResidueHarmonicScale q := by
            have hfactor0 := mul_nonneg hCcompletion hexceptionalMass
            nlinarith
      _ ≤ C * inverseResidueHarmonicScale q := by
        dsimp [C]
        nlinarith

/-! ## Uniformity in an ambient modulus -/

/-- Real interpolation of the displayed inverse-residue harmonic scale. -/
noncomputable def inverseResidueHarmonicScaleReal (x : ℝ) : ℝ :=
  Real.log (2 * x) / Real.log (Real.log (3 * x))

/-- The exact derivative of the real harmonic-scale interpolation away from
its logarithmic singularities. -/
noncomputable def inverseResidueHarmonicScaleRealDerivative (x : ℝ) : ℝ :=
  (Real.log (Real.log (3 * x)) -
      Real.log (2 * x) / Real.log (3 * x)) /
    (x * (Real.log (Real.log (3 * x))) ^ 2)

theorem hasDerivAt_inverseResidueHarmonicScaleReal
    {x : ℝ} (hx : 0 < x)
    (hlog3x : Real.log (3 * x) ≠ 0)
    (hloglog3x : Real.log (Real.log (3 * x)) ≠ 0) :
    HasDerivAt inverseResidueHarmonicScaleReal
      (inverseResidueHarmonicScaleRealDerivative x) x := by
  have htwo : (x * 2 : ℝ) ≠ 0 := by positivity
  have hthree : (x * 3 : ℝ) ≠ 0 := by positivity
  have hnum := ((hasDerivAt_id x).mul_const 2).log htwo
  have hinner := ((hasDerivAt_id x).mul_const 3).log hthree
  have hlog3x' : Real.log (x * 3) ≠ 0 := by simpa [mul_comm] using hlog3x
  have hloglog3x' : Real.log (Real.log (x * 3)) ≠ 0 := by
    simpa [mul_comm] using hloglog3x
  have hden := hinner.log hlog3x'
  have hquot := hnum.div hden hloglog3x'
  have hderivative :
      (2 * 1 / (2 * x) * Real.log (Real.log (3 * x)) -
          Real.log (2 * x) *
            (3 * 1 / (3 * x) / Real.log (3 * x))) /
          Real.log (Real.log (3 * x)) ^ 2 =
        inverseResidueHarmonicScaleRealDerivative x := by
    unfold inverseResidueHarmonicScaleRealDerivative
    field_simp [hx.ne', hlog3x, hloglog3x]
  rw [← hderivative]
  convert hquot using 1
  · ext
    rfl
  · apply Module.ext'
    intro r y
    rfl
  · ext y
    simp only [inverseResidueHarmonicScaleReal, Function.id_def,
      Pi.div_apply, mul_comm]
  · simp only [Function.id_def, mul_comm]

/-- Beyond the intrinsic double-exponential threshold, the real interpolation
of `log(2x)/log log(3x)` is monotone. -/
theorem inverseResidueHarmonicScaleReal_monotoneOn :
    MonotoneOn inverseResidueHarmonicScaleReal
      (Set.Ici (Real.exp (Real.exp 1) / 3)) := by
  let A := Real.exp (Real.exp 1) / 3
  have hApos : 0 < A := by dsimp [A]; positivity
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici A)
  · intro x hx
    change A ≤ x at hx
    have hxpos : 0 < x := hApos.trans_le hx
    have h3bound : Real.exp (Real.exp 1) ≤ 3 * x := by
      calc
        Real.exp (Real.exp 1) = 3 * A := by dsimp [A]; ring
        _ ≤ 3 * x := mul_le_mul_of_nonneg_left hx (by norm_num)
    have hlog3xPos : 0 < Real.log (3 * x) := by
      apply Real.log_pos
      have hone : 1 < Real.exp (Real.exp 1) :=
        Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
      exact hone.trans_le h3bound
    have hloglog3xPos : 0 < Real.log (Real.log (3 * x)) := by
      apply Real.log_pos
      have hexp : Real.exp 1 ≤ Real.log (3 * x) := by
        rw [← Real.log_exp (Real.exp 1)]
        exact Real.log_le_log (Real.exp_pos _) h3bound
      exact (show (1 : ℝ) < Real.exp 1 by
        exact Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hexp
    exact (hasDerivAt_inverseResidueHarmonicScaleReal hxpos
      hlog3xPos.ne' hloglog3xPos.ne').continuousAt.continuousWithinAt
  · intro x hx
    have hxA : A < x := by
      simp only [interior_Ici, Set.mem_Ioi] at hx
      exact hx
    have hxpos : 0 < x := hApos.trans hxA
    have h3bound : Real.exp (Real.exp 1) ≤ 3 * x := by
      dsimp [A] at hxA
      nlinarith
    have hlog3xLower : Real.exp 1 ≤ Real.log (3 * x) := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) h3bound
    have hlog3xPos : 0 < Real.log (3 * x) :=
      (Real.exp_pos 1).trans_le hlog3xLower
    have hloglog3xPos : 0 < Real.log (Real.log (3 * x)) :=
      Real.log_pos ((show (1 : ℝ) < Real.exp 1 by
        exact Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hlog3xLower)
    exact (hasDerivAt_inverseResidueHarmonicScaleReal hxpos
      hlog3xPos.ne' hloglog3xPos.ne').hasDerivWithinAt
  · intro x hx
    have hxA : A < x := by
      simp only [interior_Ici, Set.mem_Ioi] at hx
      exact hx
    have hxpos : 0 < x := hApos.trans hxA
    have h3bound : Real.exp (Real.exp 1) ≤ 3 * x := by
      dsimp [A] at hxA
      nlinarith
    have hlog3xLower : Real.exp 1 ≤ Real.log (3 * x) := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) h3bound
    have hlog3xPos : 0 < Real.log (3 * x) :=
      (Real.exp_pos 1).trans_le hlog3xLower
    have hloglog3xOne : 1 ≤ Real.log (Real.log (3 * x)) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hlog3xLower
    have hloglog3xPos : 0 < Real.log (Real.log (3 * x)) := by linarith
    have hnumLe : Real.log (2 * x) ≤ Real.log (3 * x) := by
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hratioLe : Real.log (2 * x) / Real.log (3 * x) ≤ 1 :=
      (div_le_one hlog3xPos).2 hnumLe
    have hnumerator : 0 ≤ Real.log (Real.log (3 * x)) -
        Real.log (2 * x) / Real.log (3 * x) := by linarith
    unfold inverseResidueHarmonicScaleRealDerivative
    exact div_nonneg hnumerator (by positivity)

/-- The displayed natural-modulus scale is the restriction of its real
interpolation. -/
theorem inverseResidueHarmonicScale_eq_real (q : ℕ) :
    inverseResidueHarmonicScale q =
      inverseResidueHarmonicScaleReal (q : ℝ) := by
  rfl

theorem inverseResidueHarmonicScale_nonneg_all (q : ℕ) :
    0 ≤ inverseResidueHarmonicScale q := by
  by_cases hq : 2 ≤ q
  · exact inverseResidueHarmonicScale_nonneg hq
  · have hqsmall : q = 0 ∨ q = 1 := by omega
    rcases hqsmall with rfl | rfl
    · norm_num [inverseResidueHarmonicScale]
    · unfold inverseResidueHarmonicScale
      apply div_nonneg
      · exact Real.log_nonneg (by norm_num)
      · apply Real.log_nonneg
        simpa using (show (1 : ℝ) ≤ Real.log 3 by
          nlinarith [Real.log_three_gt_d9])

/-- Uniform comparison with an ambient modulus.  Eventual monotonicity handles
the large moduli and the finite initial segment is absorbed explicitly. -/
def AmbientInverseResidueHarmonicScaleComparison : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ K q,
    2 ≤ q → q ≤ K →
      inverseResidueHarmonicScale q ≤
        C * inverseResidueHarmonicScale K

theorem ambientInverseResidueHarmonicScaleComparison :
    AmbientInverseResidueHarmonicScaleComparison := by
  let A := Real.exp (Real.exp 1) / 3
  let threshold := Nat.ceil A
  let exceptionalMass :=
    ∑ q ∈ Finset.range threshold, inverseResidueHarmonicScale q
  have hexceptionalMass : 0 ≤ exceptionalMass := by
    dsimp [exceptionalMass]
    apply Finset.sum_nonneg
    intro q _hq
    exact inverseResidueHarmonicScale_nonneg_all q
  let C := 1 + 2 * exceptionalMass
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro K q hq hqK
  have hK : 2 ≤ K := hq.trans hqK
  have hscaleK0 : 0 ≤ inverseResidueHarmonicScale K :=
    inverseResidueHarmonicScale_nonneg hK
  by_cases hlarge : threshold ≤ q
  · have hAq : A ≤ (q : ℝ) := by
      calc
        A ≤ (threshold : ℝ) := by
          dsimp [threshold]
          exact Nat.le_ceil A
        _ ≤ (q : ℝ) := by exact_mod_cast hlarge
    have hAK : A ≤ (K : ℝ) :=
      hAq.trans (by exact_mod_cast hqK)
    have hmono := inverseResidueHarmonicScaleReal_monotoneOn
      hAq hAK (by exact_mod_cast hqK)
    have hmonoNat : inverseResidueHarmonicScale q ≤
        inverseResidueHarmonicScale K := by
      rw [inverseResidueHarmonicScale_eq_real,
        inverseResidueHarmonicScale_eq_real]
      exact hmono
    calc
      inverseResidueHarmonicScale q ≤
          inverseResidueHarmonicScale K := hmonoNat
      _ ≤ C * inverseResidueHarmonicScale K := by
        dsimp [C]
        nlinarith
  · have hqRange : q ∈ Finset.range threshold :=
      Finset.mem_range.mpr (Nat.lt_of_not_ge hlarge)
    have hqTerm0 : 0 ≤ inverseResidueHarmonicScale q :=
      inverseResidueHarmonicScale_nonneg hq
    have hqExceptional : inverseResidueHarmonicScale q ≤
        exceptionalMass := by
      dsimp [exceptionalMass]
      exact Finset.single_le_sum
        (fun x _hx => inverseResidueHarmonicScale_nonneg_all x) hqRange
    have hscaleLower := one_half_le_inverseResidueHarmonicScale hK
    calc
      inverseResidueHarmonicScale q ≤ exceptionalMass := hqExceptional
      _ ≤ 2 * exceptionalMass * inverseResidueHarmonicScale K := by
        nlinarith
      _ ≤ C * inverseResidueHarmonicScale K := by
        dsimp [C]
        nlinarith

/-- The manuscript's uniform finite partial-sum estimate, now derived from the
three source inputs instead of accepted as a manuscript-specific hypothesis. -/
theorem uniformInverseSawPartialHarmonicEstimate
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : CompletedInversePrefixEstimate)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth) :
    UniformInverseSawPartialHarmonicEstimate := by
  rcases pointwiseInverseSawPartialHarmonicEstimate
      hKorolev hcompletion hdivisorGrowth with
    ⟨Cpoint, hCpoint, hpoint⟩
  rcases ambientInverseResidueHarmonicScaleComparison with
    ⟨Cambient, hCambient, hambient⟩
  refine ⟨Cpoint * Cambient, mul_nonneg hCpoint hCambient, ?_⟩
  intro K q r N hq hqK hr
  calc
    ‖inverseSawPartial q r N‖ ≤
        Cpoint * inverseResidueHarmonicScale q := hpoint q r N hq hr
    _ ≤ Cpoint *
        (Cambient * inverseResidueHarmonicScale K) :=
      mul_le_mul_of_nonneg_left (hambient K q hq hqK) hCpoint
    _ = (Cpoint * Cambient) * inverseResidueHarmonicScale K := by ring

end NField.Alignment.InverseResidueHarmonicRangeSplit
