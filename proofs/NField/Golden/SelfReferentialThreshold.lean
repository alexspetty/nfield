/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Golden.Threshold
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Self-referential alignment thresholds

This module formalizes the reciprocal-square closure attached to the exact
one-digit alignment formula.  It is organized around the mathematical object,
not around a paper number.  The reader-facing paper manifest imports these
results and records their correspondence with the manuscript.
-/

namespace NField.Golden

open Polynomial

/-- The critical real resolution at which the one-digit alignment formula
equals a threshold `tau`. -/
noncomputable def criticalResolution (τ : ℝ) (p : ℕ) : ℝ :=
  (1 - τ) / (2 - (p : ℝ) * τ)

/-- The cubic forced by reciprocal-square closure. -/
def selfReferentialCubicValue (p : ℕ) (τ : ℝ) : ℝ :=
  τ ^ 3 - τ ^ 2 - (p : ℝ) * τ + 2

/-- The same cubic as a polynomial over the rationals. -/
noncomputable def selfReferentialCubic (p : ℕ) : ℚ[X] :=
  X ^ 3 - X ^ 2 - C (p : ℚ) * X + C 2

/-- Integral model used to apply the rational-root theorem without changing
the manuscript's polynomial. -/
noncomputable def selfReferentialCubicInt (p : ℕ) : ℤ[X] :=
  X ^ 3 - X ^ 2 - C (p : ℤ) * X + C 2

theorem selfReferentialCubic_eval (p : ℕ) (τ : ℚ) :
    (selfReferentialCubic p).eval τ =
      τ ^ 3 - τ ^ 2 - (p : ℚ) * τ + 2 := by
  simp [selfReferentialCubic]

theorem selfReferentialCubic_aeval_real (p : ℕ) (τ : ℝ) :
    aeval τ (selfReferentialCubic p) = selfReferentialCubicValue p τ := by
  simp [selfReferentialCubic, selfReferentialCubicValue, aeval_def]

theorem selfReferentialCubic_monic (p : ℕ) :
    (selfReferentialCubic p).Monic := by
  rw [selfReferentialCubic]
  monicity <;> norm_num

theorem selfReferentialCubic_natDegree (p : ℕ) :
    (selfReferentialCubic p).natDegree = 3 := by
  rw [selfReferentialCubic]
  compute_degree <;> norm_num

theorem selfReferentialCubicInt_monic (p : ℕ) :
    (selfReferentialCubicInt p).Monic := by
  rw [selfReferentialCubicInt]
  monicity <;> norm_num

theorem selfReferentialCubicInt_map (p : ℕ) :
    (selfReferentialCubicInt p).map (algebraMap ℤ ℚ) =
      selfReferentialCubic p := by
  ext n
  simp [selfReferentialCubicInt, selfReferentialCubic]
  exact congrArg (fun q : ℚ[X] => q.coeff n)
    (C_eq_natCast (R := ℚ) 2).symm

/-- Solving the alignment equation gives the displayed critical resolution. -/
theorem alignment_eq_threshold_iff_criticalResolution
    {p : ℕ} {m τ : ℝ} (hden : 2 - (p : ℝ) * τ ≠ 0)
    (halignDen : (p : ℝ) * m - 1 ≠ 0) :
    (2 * m - 1) / ((p : ℝ) * m - 1) = τ ↔
      m = criticalResolution τ p := by
  constructor
  · intro h
    rw [div_eq_iff halignDen] at h
    apply (eq_div_iff hden).2
    nlinarith
  · intro h
    have hlinear : m * (2 - (p : ℝ) * τ) = 1 - τ :=
      (eq_div_iff hden).mp h
    rw [div_eq_iff halignDen]
    nlinarith

/-- Under the manuscript's domain hypotheses, reciprocal-square closure is
equivalent to the self-referential cubic equation. -/
theorem criticalResolution_eq_reciprocal_sq_iff
    {p : ℕ} {τ : ℝ} (hτ : 0 < τ) (hrange : τ < 2 / (p : ℝ))
    (hp : 0 < p) :
    criticalResolution τ p = 1 / τ ^ 2 ↔
      selfReferentialCubicValue p τ = 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcritical : 0 < 2 - (p : ℝ) * τ := by
    apply (sub_pos).2
    simpa [mul_comm] using (lt_div_iff₀ hpR).mp hrange
  have hτsq : τ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hτ)
  unfold criticalResolution selfReferentialCubicValue
  rw [div_eq_div_iff (ne_of_gt hcritical) hτsq]
  constructor <;> intro h <;> nlinarith

theorem selfReferentialCubicValue_zero (p : ℕ) :
    selfReferentialCubicValue p 0 = 2 := by
  simp [selfReferentialCubicValue]

theorem selfReferentialCubicValue_one (p : ℕ) :
    selfReferentialCubicValue p 1 = 2 - p := by
  simp [selfReferentialCubicValue]
  ring

theorem selfReferentialCubicValue_two_div
    {p : ℕ} (hp : 0 < p) :
    selfReferentialCubicValue p (2 / (p : ℝ)) =
      4 * (2 - (p : ℝ)) / (p : ℝ) ^ 3 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  rw [selfReferentialCubicValue]
  field_simp
  ring

/-- On `[0,1]`, the self-referential cubic is strictly decreasing for
`p >= 3`. -/
theorem selfReferentialCubicValue_strictAntiOn {p : ℕ} (hp : 3 ≤ p) :
    StrictAntiOn (selfReferentialCubicValue p) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hy2 : y ^ 2 ≤ y := by nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
  have hxyLe : x * y ≤ x := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.2)]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hbracket :
      y ^ 2 + y * x + x ^ 2 - (y + x) - (p : ℝ) < 0 := by
    nlinarith
  have hfactor :
      selfReferentialCubicValue p y - selfReferentialCubicValue p x =
        (y - x) * (y ^ 2 + y * x + x ^ 2 - (y + x) - (p : ℝ)) := by
    unfold selfReferentialCubicValue
    ring
  have hproduct :
      (y - x) * (y ^ 2 + y * x + x ^ 2 - (y + x) - (p : ℝ)) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hbracket
  linarith

/-- Every integer `p >= 3` has exactly one reciprocal-square cubic root in
`(0,1)`, and that root lies in the sharper interval `(0,2/p)`. -/
theorem exists_unique_selfReferential_root {p : ℕ} (hp : 3 ≤ p) :
    ∃! τ : ℝ, τ ∈ Set.Ioo 0 1 ∧ selfReferentialCubicValue p τ = 0 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hcontinuous : Continuous (selfReferentialCubicValue p) := by
    unfold selfReferentialCubicValue
    fun_prop
  have hzeroMem : (0 : ℝ) ∈ Set.Icc
      (selfReferentialCubicValue p 1) (selfReferentialCubicValue p 0) := by
    constructor
    · rw [selfReferentialCubicValue_one]
      linarith
    · rw [selfReferentialCubicValue_zero]
      norm_num
  have himage : (0 : ℝ) ∈
      selfReferentialCubicValue p '' Set.Icc 0 1 :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
      hcontinuous.continuousOn hzeroMem
  rcases himage with ⟨τ, hτmem, hτzero⟩
  have hτopen : τ ∈ Set.Ioo (0 : ℝ) 1 := by
    rcases hτmem with ⟨hτ0, hτ1⟩
    constructor
    · apply lt_of_le_of_ne hτ0
      intro h
      subst τ
      norm_num [selfReferentialCubicValue] at hτzero
    · apply lt_of_le_of_ne hτ1
      intro h
      subst τ
      rw [selfReferentialCubicValue_one] at hτzero
      nlinarith
  refine ⟨τ, ⟨hτopen, hτzero⟩, ?_⟩
  intro σ hσ
  rcases hσ with ⟨hσmem, hσzero⟩
  by_contra hne
  have hanti := selfReferentialCubicValue_strictAntiOn hp
  rcases lt_or_gt_of_ne hne with hτσ | hστ
  · have := hanti ⟨hσmem.1.le, hσmem.2.le⟩
        ⟨hτopen.1.le, hτopen.2.le⟩ hτσ
    rw [hσzero, hτzero] at this
    exact (lt_irrefl 0 this)
  · have := hanti ⟨hτopen.1.le, hτopen.2.le⟩
        ⟨hσmem.1.le, hσmem.2.le⟩ hστ
    rw [hτzero, hσzero] at this
    exact (lt_irrefl 0 this)

/-- The unique root is below the alignment limit `2/p`, so its critical
resolution is positive. -/
theorem selfReferential_root_lt_two_div
    {p : ℕ} (hp : 3 ≤ p) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo 0 1)
    (hroot : selfReferentialCubicValue p τ = 0) :
    τ < 2 / (p : ℝ) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have htwoPos : 0 < 2 / (p : ℝ) := div_pos (by norm_num) hpR
  have htwoLeOne : 2 / (p : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hpR).2
    norm_num
    exact_mod_cast (show 2 ≤ p by omega)
  have hvalueNeg : selfReferentialCubicValue p (2 / (p : ℝ)) < 0 := by
    rw [selfReferentialCubicValue_two_div hp0]
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
    exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  by_contra hnot
  have hle : 2 / (p : ℝ) ≤ τ := le_of_not_gt hnot
  have hanti := selfReferentialCubicValue_strictAntiOn hp
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst τ
    linarith
  · have hcomp := hanti ⟨htwoPos.le, htwoLeOne⟩
        ⟨hτ.1.le, hτ.2.le⟩ hlt
    linarith

theorem selfReferential_root_criticalResolution_pos
    {p : ℕ} (hp : 3 ≤ p) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo 0 1)
    (hroot : selfReferentialCubicValue p τ = 0) :
    0 < criticalResolution τ p := by
  have hrange := selfReferential_root_lt_two_div hp hτ hroot
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  unfold criticalResolution
  exact div_pos (sub_pos.mpr hτ.2)
    (sub_pos.mpr (by simpa [mul_comm] using (lt_div_iff₀ hpR).mp hrange))

/-- The degenerate prime-two cubic has no root in the admissible open unit
interval. -/
theorem prime_two_no_selfReferential_root {τ : ℝ}
    (hτ : τ ∈ Set.Ioo 0 1) :
    selfReferentialCubicValue 2 τ ≠ 0 := by
  have hfactor : selfReferentialCubicValue 2 τ =
      (τ - 1) * (τ ^ 2 - 2) := by
    unfold selfReferentialCubicValue
    ring
  have hfirst : τ - 1 < 0 := sub_neg.mpr hτ.2
  have hτsq : τ ^ 2 < 1 := by
    nlinarith [mul_pos hτ.1 (sub_pos.mpr hτ.2)]
  have hsecond : τ ^ 2 - 2 < 0 := by linarith
  rw [hfactor]
  exact ne_of_gt (mul_pos_of_neg_of_neg hfirst hsecond)

/-- The three exceptional rational factorizations. -/
theorem selfReferentialCubic_two_factorization :
    selfReferentialCubic 2 = (X - 1) * (X ^ 2 - 2) := by
  simp only [selfReferentialCubic, Nat.cast_ofNat, C_ofNat]
  ring

theorem selfReferentialCubic_three_factorization :
    selfReferentialCubic 3 = (X - 2) * (X ^ 2 + X - 1) := by
  simp only [selfReferentialCubic, Nat.cast_ofNat, C_ofNat]
  ring

theorem selfReferentialCubic_five_factorization :
    selfReferentialCubic 5 = (X + 2) * (X ^ 2 - 3 * X + 1) := by
  simp only [selfReferentialCubic, Nat.cast_ofNat, C_ofNat]
  ring

/-- The four rational-root candidates evaluate exactly as in the manuscript. -/
theorem selfReferentialCubic_candidate_values (p : ℕ) :
    (selfReferentialCubic p).eval 1 = 2 - p ∧
    (selfReferentialCubic p).eval (-1) = p ∧
    (selfReferentialCubic p).eval 2 = 6 - 2 * p ∧
      (selfReferentialCubic p).eval (-2) = 2 * p - 10 := by
  repeat' apply And.intro
  all_goals norm_num [selfReferentialCubic_eval]
  all_goals ring

/-- For `p >= 7`, the cubic has no rational root. -/
theorem selfReferentialCubic_no_rational_root {p : ℕ} (hp : 7 ≤ p) :
    ∀ τ : ℚ, ¬(selfReferentialCubic p).IsRoot τ := by
  intro τ hroot
  have hmapped :
      ((selfReferentialCubicInt p).map (algebraMap ℤ ℚ)).eval τ = 0 := by
    rw [selfReferentialCubicInt_map]
    exact hroot
  have hintegralRoot : aeval τ (selfReferentialCubicInt p) = 0 := by
    simpa [aeval_def, eval_map] using hmapped
  obtain ⟨z, hτz, hzdiv⟩ :=
    exists_integer_of_is_root_of_monic
      (selfReferentialCubicInt_monic p) hintegralRoot
  have hconstant : (selfReferentialCubicInt p).coeff 0 = 2 := by
    simp [selfReferentialCubicInt]
  rw [hconstant] at hzdiv
  have hzabs : z.natAbs ≤ 2 :=
    Int.natAbs_le_of_dvd_ne_zero hzdiv (by norm_num)
  have hzsq : z * z ≤ 4 := by
    have := (Int.natAbs_le_iff_mul_self_le (a := z) (b := 2)).mp
      (by simpa using hzabs)
    norm_num at this ⊢
    exact this
  have hzlower : (-2 : ℤ) ≤ z := by nlinarith
  have hzupper : z ≤ (2 : ℤ) := by nlinarith
  subst τ
  have hrootEval :
      ((z : ℚ) ^ 3 - (z : ℚ) ^ 2 - (p : ℚ) * z + 2) = 0 := by
    simpa [selfReferentialCubic_eval] using hroot
  interval_cases z <;> norm_num at hrootEval
  all_goals
    have hpQ : (7 : ℚ) ≤ p := by exact_mod_cast hp
    linarith

/-- The manuscript's cubic is irreducible over the rationals for every
`p >= 7`. -/
theorem selfReferentialCubic_irreducible {p : ℕ} (hp : 7 ≤ p) :
    Irreducible (selfReferentialCubic p) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [selfReferentialCubic_natDegree]
    simp
  · exact selfReferentialCubic_no_rational_root hp

/-- For a prime parameter, rational factorization occurs exactly at
`2`, `3`, and `5`. -/
theorem selfReferentialCubic_reducible_iff_prime_exception
    {p : ℕ} (hp : p.Prime) :
    ¬Irreducible (selfReferentialCubic p) ↔
      p = 2 ∨ p = 3 ∨ p = 5 := by
  constructor
  · intro hred
    by_contra hexception
    push Not at hexception
    have hp7 : 7 ≤ p := by
      have hp2 := hp.two_le
      have hp4 : p ≠ 4 := by
        intro h
        subst p
        norm_num at hp
      have hp6 : p ≠ 6 := by
        intro h
        subst p
        norm_num at hp
      omega
    exact hred (selfReferentialCubic_irreducible hp7)
  · intro hexception
    rcases hexception with rfl | rfl | rfl
    · rw [selfReferentialCubic_two_factorization]
      have hleft : ¬IsUnit (X - 1 : ℚ[X]) := by
        refine not_isUnit_of_natDegree_pos _ ?_
        have hdegree : (X - 1 : ℚ[X]).natDegree = 1 := by
          compute_degree
          all_goals norm_num
        omega
      have hright : ¬IsUnit (X ^ 2 - 2 : ℚ[X]) := by
        refine not_isUnit_of_natDegree_pos _ ?_
        have hdegree : (X ^ 2 - 2 : ℚ[X]).natDegree = 2 := by
          compute_degree
          all_goals norm_num
        omega
      intro hirr
      rcases of_irreducible_mul hirr with hunit | hunit
      · exact hleft hunit
      · exact hright hunit
    · rw [selfReferentialCubic_three_factorization]
      have hleft : ¬IsUnit (X - 2 : ℚ[X]) := by
        refine not_isUnit_of_natDegree_pos _ ?_
        have hdegree : (X - 2 : ℚ[X]).natDegree = 1 := by
          compute_degree
          all_goals norm_num
        omega
      have hright : ¬IsUnit (X ^ 2 + X - 1 : ℚ[X]) := by
        refine not_isUnit_of_natDegree_pos _ ?_
        have hdegree : (X ^ 2 + X - 1 : ℚ[X]).natDegree = 2 := by
          compute_degree
          all_goals norm_num
        omega
      intro hirr
      rcases of_irreducible_mul hirr with hunit | hunit
      · exact hleft hunit
      · exact hright hunit
    · rw [selfReferentialCubic_five_factorization]
      have hleft : ¬IsUnit (X + 2 : ℚ[X]) := by
        refine not_isUnit_of_natDegree_pos _ ?_
        have hdegree : (X + 2 : ℚ[X]).natDegree = 1 := by
          compute_degree
          all_goals norm_num
        omega
      have hright : ¬IsUnit (X ^ 2 - 3 * X + 1 : ℚ[X]) := by
        refine not_isUnit_of_natDegree_pos _ ?_
        have hdegree : (X ^ 2 - 3 * X + 1 : ℚ[X]).natDegree = 2 := by
          compute_degree
          all_goals norm_num
        omega
      intro hirr
      rcases of_irreducible_mul hirr with hunit | hunit
      · exact hleft hunit
      · exact hright hunit

/-- The reciprocal golden ratio satisfies its exact quadratic equation. -/
theorem goldenReciprocal_quadratic :
    goldenReciprocal ^ 2 + goldenReciprocal - 1 = 0 := by
  dsimp [goldenReciprocal]
  nlinarith [sqrt_five_sq]

theorem goldenReciprocal_pos : 0 < goldenReciprocal := by
  linarith [two_fifths_lt_goldenReciprocal]

theorem goldenReciprocal_lt_one : goldenReciprocal < 1 := by
  linarith [goldenReciprocal_lt_two_thirds]

theorem goldenReciprocal_sq_closed_form :
    goldenReciprocal ^ 2 = (3 - Real.sqrt 5) / 2 := by
  dsimp [goldenReciprocal]
  nlinarith [sqrt_five_sq]

theorem goldenReciprocal_sq_eq_goldenRatio_inv_sq :
    goldenReciprocal ^ 2 = 1 / goldenRatio ^ 2 := by
  rw [goldenReciprocal_eq_inv]
  field_simp [goldenRatio_pos.ne']

theorem sqrt_five_gt_eleven_fifths :
    (11 : ℝ) / 5 < Real.sqrt 5 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

theorem goldenReciprocal_sq_lt_two_fifths :
    goldenReciprocal ^ 2 < (2 : ℝ) / 5 := by
  rw [goldenReciprocal_sq_closed_form]
  linarith [sqrt_five_gt_eleven_fifths]

theorem goldenReciprocal_selfReferential_root :
    selfReferentialCubicValue 3 goldenReciprocal = 0 := by
  rw [show selfReferentialCubicValue 3 goldenReciprocal =
      (goldenReciprocal - 2) *
        (goldenReciprocal ^ 2 + goldenReciprocal - 1) by
    unfold selfReferentialCubicValue
    ring]
  rw [goldenReciprocal_quadratic, mul_zero]

theorem goldenReciprocal_sq_selfReferential_root :
    selfReferentialCubicValue 5 (goldenReciprocal ^ 2) = 0 := by
  have hquadratic :
      (goldenReciprocal ^ 2) ^ 2 - 3 * goldenReciprocal ^ 2 + 1 = 0 := by
    calc
      (goldenReciprocal ^ 2) ^ 2 - 3 * goldenReciprocal ^ 2 + 1 =
          (goldenReciprocal ^ 2 + goldenReciprocal - 1) *
            (goldenReciprocal ^ 2 - goldenReciprocal - 1) := by ring
      _ = 0 := by rw [goldenReciprocal_quadratic, zero_mul]
  rw [show selfReferentialCubicValue 5 (goldenReciprocal ^ 2) =
      (goldenReciprocal ^ 2 + 2) *
        ((goldenReciprocal ^ 2) ^ 2 - 3 * goldenReciprocal ^ 2 + 1) by
    unfold selfReferentialCubicValue
    ring]
  rw [hquadratic, mul_zero]

/-- The unique admissible root for `p=3` is the reciprocal golden ratio. -/
theorem selfReferential_root_three_eq_goldenReciprocal
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1)
    (hroot : selfReferentialCubicValue 3 τ = 0) :
    τ = goldenReciprocal := by
  have hgold : goldenReciprocal ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨goldenReciprocal_pos, goldenReciprocal_lt_one⟩
  exact (exists_unique_selfReferential_root (p := 3) (by norm_num)).unique
    ⟨hτ, hroot⟩ ⟨hgold, goldenReciprocal_selfReferential_root⟩

/-- The unique admissible root for `p=5` is the square of the reciprocal
golden ratio. -/
theorem selfReferential_root_five_eq_goldenReciprocal_sq
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 1)
    (hroot : selfReferentialCubicValue 5 τ = 0) :
    τ = goldenReciprocal ^ 2 := by
  have hsqPos : 0 < goldenReciprocal ^ 2 := sq_pos_of_pos goldenReciprocal_pos
  have hsqOne : goldenReciprocal ^ 2 < 1 := by
    nlinarith [mul_pos goldenReciprocal_pos
      (sub_pos.mpr goldenReciprocal_lt_one)]
  exact (exists_unique_selfReferential_root (p := 5) (by norm_num)).unique
    ⟨hτ, hroot⟩
    ⟨⟨hsqPos, hsqOne⟩, goldenReciprocal_sq_selfReferential_root⟩

/-- Among prime parameters, the reciprocal-square root lies in the separating
window exactly for `p=3`, where it is `1/phi`. -/
theorem selfReferential_root_in_separating_window_iff
    {p : ℕ} (hp : p.Prime) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo 0 1)
    (hroot : selfReferentialCubicValue p τ = 0) :
    τ ∈ Set.Ioo ((2 : ℝ) / 5) (2 / 3) ↔
      p = 3 ∧ τ = goldenReciprocal := by
  constructor
  · intro hwindow
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      have hfactor : selfReferentialCubicValue 2 τ =
          (τ - 1) * (τ ^ 2 - 2) := by
        unfold selfReferentialCubicValue
        ring
      have hfirst : τ - 1 < 0 := sub_neg.mpr hτ.2
      have hτsq : τ ^ 2 < 1 := by
        nlinarith [mul_pos hτ.1 (sub_pos.mpr hτ.2)]
      have hsecond : τ ^ 2 - 2 < 0 := by linarith
      rw [hfactor] at hroot
      have : 0 < (τ - 1) * (τ ^ 2 - 2) := mul_pos_of_neg_of_neg hfirst hsecond
      linarith
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hpIsThree : p = 3 := by
      by_contra hpne3
      have hp5 : 5 ≤ p := by
        have hp4 : p ≠ 4 := by
          intro hp4
          subst p
          norm_num at hp
        omega
      have hlimit := selfReferential_root_lt_two_div hp3 hτ hroot
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have hpRpos : (0 : ℝ) < p := by positivity
      have hle : (2 : ℝ) / p ≤ 2 / 5 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
      norm_num at hwindow hle
      linarith
    subst p
    exact ⟨rfl, selfReferential_root_three_eq_goldenReciprocal hτ hroot⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨two_fifths_lt_goldenReciprocal,
      goldenReciprocal_lt_two_thirds⟩

/-- A root of an irreducible higher-prime cubic cannot satisfy any nonzero
rational polynomial of degree at most two.  This is the precise algebraic
content of being a cubic irrational outside every quadratic field. -/
theorem selfReferential_root_has_no_quadratic_rational_relation
    {p : ℕ} (hp : 7 ≤ p) {τ : ℝ}
    (hroot : selfReferentialCubicValue p τ = 0) :
    ¬∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 2 ∧ aeval τ q = 0 := by
  intro hrelation
  rcases hrelation with ⟨q, hqne, hqdegree, hqroot⟩
  have hcubicRoot : aeval τ (selfReferentialCubic p) = 0 := by
    rw [selfReferentialCubic_aeval_real]
    exact hroot
  have hminpoly : selfReferentialCubic p = minpoly ℚ τ :=
    minpoly.eq_of_irreducible_of_monic
      (selfReferentialCubic_irreducible hp) hcubicRoot
      (selfReferentialCubic_monic p)
  have hdvd : minpoly ℚ τ ∣ q := minpoly.dvd ℚ τ hqroot
  rw [← hminpoly] at hdvd
  have hdegree := natDegree_le_of_dvd hdvd hqne
  rw [selfReferentialCubic_natDegree] at hdegree
  omega

/-- A higher-prime self-referential root has the displayed cubic itself as
its rational minimal polynomial. -/
theorem selfReferential_root_minpoly_eq_cubic
    {p : ℕ} (hp : 7 ≤ p) {τ : ℝ}
    (hroot : selfReferentialCubicValue p τ = 0) :
    minpoly ℚ τ = selfReferentialCubic p := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
    (selfReferentialCubic_irreducible hp)
  · rw [selfReferentialCubic_aeval_real]
    exact hroot
  · exact selfReferentialCubic_monic p

/-- Consequently every higher-prime self-referential threshold has algebraic
degree exactly three over the rationals. -/
theorem selfReferential_root_minpoly_natDegree
    {p : ℕ} (hp : 7 ≤ p) {τ : ℝ}
    (hroot : selfReferentialCubicValue p τ = 0) :
    (minpoly ℚ τ).natDegree = 3 := by
  rw [selfReferential_root_minpoly_eq_cubic hp hroot,
    selfReferentialCubic_natDegree]

/-- The reciprocal-golden minimal polynomial. -/
noncomputable def goldenReciprocalPolynomial : ℚ[X] :=
  X ^ 2 + X - 1

noncomputable def goldenReciprocalPolynomialInt : ℤ[X] :=
  X ^ 2 + X - 1

theorem goldenReciprocalPolynomial_monic :
    goldenReciprocalPolynomial.Monic := by
  rw [goldenReciprocalPolynomial]
  monicity
  all_goals norm_num

theorem goldenReciprocalPolynomial_natDegree :
    goldenReciprocalPolynomial.natDegree = 2 := by
  rw [goldenReciprocalPolynomial]
  compute_degree
  all_goals norm_num

theorem goldenReciprocalPolynomialInt_monic :
    goldenReciprocalPolynomialInt.Monic := by
  rw [goldenReciprocalPolynomialInt]
  monicity
  all_goals norm_num

theorem goldenReciprocalPolynomialInt_map :
    goldenReciprocalPolynomialInt.map (algebraMap ℤ ℚ) =
      goldenReciprocalPolynomial := by
  ext n
  simp [goldenReciprocalPolynomialInt, goldenReciprocalPolynomial]

theorem goldenReciprocalPolynomial_aeval :
    aeval goldenReciprocal goldenReciprocalPolynomial = 0 := by
  simp [goldenReciprocalPolynomial, aeval_def]
  exact goldenReciprocal_quadratic

theorem goldenReciprocalPolynomial_no_rational_root :
    ∀ τ : ℚ, ¬goldenReciprocalPolynomial.IsRoot τ := by
  intro τ hroot
  have hmapped :
      (goldenReciprocalPolynomialInt.map (algebraMap ℤ ℚ)).eval τ = 0 := by
    rw [goldenReciprocalPolynomialInt_map]
    exact hroot
  have hintegralRoot : aeval τ goldenReciprocalPolynomialInt = 0 := by
    simpa [aeval_def, eval_map] using hmapped
  obtain ⟨z, hτz, hzdiv⟩ :=
    exists_integer_of_is_root_of_monic
      goldenReciprocalPolynomialInt_monic hintegralRoot
  have hconstant : goldenReciprocalPolynomialInt.coeff 0 = -1 := by
    simp [goldenReciprocalPolynomialInt]
  rw [hconstant] at hzdiv
  have hzabs : z.natAbs ≤ 1 :=
    Int.natAbs_le_of_dvd_ne_zero hzdiv (by norm_num)
  have hzsq : z * z ≤ 1 := by
    have := (Int.natAbs_le_iff_mul_self_le (a := z) (b := 1)).mp
      (by simpa using hzabs)
    norm_num at this ⊢
    exact this
  have hzlower : (-1 : ℤ) ≤ z := by nlinarith
  have hzupper : z ≤ (1 : ℤ) := by nlinarith
  subst τ
  have hrootEval : (z : ℚ) ^ 2 + z - 1 = 0 := by
    simpa [goldenReciprocalPolynomial, IsRoot] using hroot
  interval_cases z <;> norm_num at hrootEval

theorem goldenReciprocalPolynomial_irreducible :
    Irreducible goldenReciprocalPolynomial := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [goldenReciprocalPolynomial_natDegree]
    simp
  · exact goldenReciprocalPolynomial_no_rational_root

theorem goldenReciprocalPolynomial_eq_minpoly :
    goldenReciprocalPolynomial = minpoly ℚ goldenReciprocal :=
  minpoly.eq_of_irreducible_of_monic
    goldenReciprocalPolynomial_irreducible
    goldenReciprocalPolynomial_aeval
    goldenReciprocalPolynomial_monic

/-- The reciprocal-golden minimal polynomial divides the cubic exactly when
the parameter is three. -/
theorem goldenReciprocalPolynomial_dvd_selfReferentialCubic_iff (p : ℕ) :
    goldenReciprocalPolynomial ∣ selfReferentialCubic p ↔ p = 3 := by
  constructor
  · intro hdvd
    rcases hdvd with ⟨q, hq⟩
    have hcubicRoot : aeval goldenReciprocal (selfReferentialCubic p) = 0 := by
      rw [hq, map_mul, goldenReciprocalPolynomial_aeval, zero_mul]
    rw [selfReferentialCubic_aeval_real] at hcubicRoot
    have hidentity : selfReferentialCubicValue p goldenReciprocal =
        (goldenReciprocal - 2) *
          (goldenReciprocal ^ 2 + goldenReciprocal - 1) +
            (3 - (p : ℝ)) * goldenReciprocal := by
      unfold selfReferentialCubicValue
      ring
    rw [hidentity, goldenReciprocal_quadratic, mul_zero, zero_add] at hcubicRoot
    have hgoldne : goldenReciprocal ≠ 0 := ne_of_gt goldenReciprocal_pos
    have hcoefficient : 3 - (p : ℝ) = 0 :=
      (mul_eq_zero.mp hcubicRoot).resolve_right hgoldne
    exact_mod_cast (show (p : ℝ) = 3 by linarith)
  · rintro rfl
    rw [selfReferentialCubic_three_factorization]
    exact dvd_mul_left goldenReciprocalPolynomial (X - 2)

/-- Exact polynomial division by the reciprocal-golden minimal polynomial.
The remainder coefficient is `3-p`. -/
theorem goldenReciprocalPolynomial_division (p : ℕ) :
    selfReferentialCubic p =
      (X - 2) * goldenReciprocalPolynomial + C ((3 : ℚ) - p) * X := by
  simp only [selfReferentialCubic, goldenReciprocalPolynomial]
  rw [map_sub]
  simp only [C_ofNat]
  ring

/-- The fourth-power identity carrying coefficient three. -/
theorem goldenReciprocal_fourth_power :
    goldenReciprocal ^ 4 = 2 - 3 * goldenReciprocal := by
  have hquadratic := goldenReciprocal_quadratic
  nlinarith [sq_nonneg (goldenReciprocal ^ 2 + goldenReciprocal - 1)]

end NField.Golden
