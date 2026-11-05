/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OneDigitModulus
import NField.Golden.Threshold
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Rational rigidity at the golden scale

Reusable theorem objects for the weighted one-digit profile.  The finite score,
its real interpolant, the Fibonacci coordinate identity, and both the rational
and real classifications are kept independent of any manuscript title.
-/

namespace NField.Golden

open Filter NField.Alignment

/-- Weighted mass of the terminating and reference residue blocks. -/
noncomputable def weightedReferenceMass (q m : ℕ) (lambda : ℝ) : ℝ :=
  lambda * terminatingNumeratorCount q m + matchingNumeratorCount q m

/-- Finite weighted score over the positive numerator rows below `q*m`. -/
noncomputable def weightedReferenceScore (q m : ℕ) (lambda : ℝ) : ℝ :=
  weightedReferenceMass q m lambda / ((q * m - 1 : ℕ) : ℝ)

/-- The block counts give the exact numerator in the manuscript. -/
theorem weightedReferenceMass_eq {q m : ℕ} (hq : 1 < q) (lambda : ℝ) :
    weightedReferenceMass q m lambda =
      lambda * ((m - 1 : ℕ) : ℝ) + (m : ℝ) := by
  rw [weightedReferenceMass, terminatingNumeratorCount_eq (by omega),
    matchingNumeratorCount_eq hq]

/-- Exact finite weighted-score formula. -/
theorem weightedReferenceScore_eq {q m : ℕ} (hq : 1 < q) (lambda : ℝ) :
    weightedReferenceScore q m lambda =
      (lambda * ((m - 1 : ℕ) : ℝ) + (m : ℝ)) /
        ((q * m - 1 : ℕ) : ℝ) := by
  rw [weightedReferenceScore, weightedReferenceMass_eq hq]

/-- A rational weight is exactly the ordinary marked-copy proportion in a
finite replication of every numerator row. -/
theorem finiteReplicationProportion_eq {q m a d : ℕ}
    (hq : 1 < q) (hm : 1 ≤ m) (hd : 0 < d) :
    (((a : ℝ) * ((m - 1 : ℕ) : ℝ) + (d : ℝ) * (m : ℝ)) /
        ((d : ℝ) * ((q * m - 1 : ℕ) : ℝ))) =
      weightedReferenceScore q m ((a : ℝ) / (d : ℝ)) := by
  rw [weightedReferenceScore_eq hq]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hrows : 0 < q * m - 1 := by
    have : 2 ≤ q * m := Nat.mul_le_mul hq hm
    omega
  have hrowsR : (((q * m - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hrows)
  field_simp [hdR, hrowsR]

/-- Real interpolation of the finite weighted profile. -/
noncomputable def weightedReferenceInterpolant
    (q : ℕ) (lambda x : ℝ) : ℝ :=
  (((lambda + 1) * x) - lambda) / ((q : ℝ) * x - 1)

/-- The real interpolant agrees with the finite score at positive integer
resolutions. -/
theorem weightedReferenceScore_eq_interpolant {q m : ℕ}
    (hq : 1 < q) (hm : 1 ≤ m) (lambda : ℝ) :
    weightedReferenceScore q m lambda =
      weightedReferenceInterpolant q lambda m := by
  rw [weightedReferenceScore_eq hq]
  unfold weightedReferenceInterpolant
  have hqm : 1 ≤ q * m := Nat.mul_pos (by omega) (by omega)
  push_cast [Nat.cast_sub hm, Nat.cast_sub hqm]
  ring

/-- Exact derivative of the weighted interpolant away from its pole. -/
theorem weightedReferenceInterpolant_deriv_eq {q : ℕ} {lambda x : ℝ}
    (hden : (q : ℝ) * x - 1 ≠ 0) :
    deriv (weightedReferenceInterpolant q lambda) x =
      (lambda * ((q : ℝ) - 1) - 1) / ((q : ℝ) * x - 1) ^ 2 := by
  change deriv
      (fun y : ℝ => (((lambda + 1) * y) - lambda) /
        ((q : ℝ) * y - 1)) x = _
  have hraw :=
    ((((hasDerivAt_id x).const_mul (lambda + 1)).sub_const lambda).div
      (((hasDerivAt_id x).const_mul (q : ℝ)).sub_const 1) hden)
  have halgebra :
      ((lambda + 1) * ((q : ℝ) * x - 1) -
          (((lambda + 1) * x) - lambda) * (q : ℝ)) /
          ((q : ℝ) * x - 1) ^ 2 =
        (lambda * ((q : ℝ) - 1) - 1) /
          ((q : ℝ) * x - 1) ^ 2 := by
    congr 1
    ring
  have hderiv := hraw.deriv
  simp only [id_eq, mul_one] at hderiv
  rw [halgebra] at hderiv
  exact hderiv

/-- Algebraic decomposition into the limiting value and its exact correction. -/
theorem weightedReferenceInterpolant_correction {q : ℕ} (hq : 0 < q)
    (lambda x : ℝ) (hden : (q : ℝ) * x - 1 ≠ 0) :
    weightedReferenceInterpolant q lambda x =
      (lambda + 1) / (q : ℝ) +
        (1 - lambda * ((q : ℝ) - 1)) /
          ((q : ℝ) * ((q : ℝ) * x - 1)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  let d : ℝ := (q : ℝ) * x - 1
  let N : ℝ := (lambda + 1) * x - lambda
  let L : ℝ := lambda + 1
  let R : ℝ := 1 - lambda * ((q : ℝ) - 1)
  have hd : d ≠ 0 := by simpa [d] using hden
  have hid : (q : ℝ) * N = L * d + R := by
    simp [N, L, d, R]
    ring
  change N / d = L / (q : ℝ) + R / ((q : ℝ) * d)
  calc
    N / d = ((q : ℝ) * N) / ((q : ℝ) * d) := by
      field_simp [hqR, hd]
    _ = (L * d + R) / ((q : ℝ) * d) := by rw [hid]
    _ = L / (q : ℝ) + R / ((q : ℝ) * d) := by
      field_simp [hqR, hd]

/-- The interpolated profile tends to `(1 + lambda)/q`. -/
theorem weightedReferenceInterpolant_tendsto (q : ℕ) (hq : 0 < q)
    (lambda : ℝ) :
    Tendsto (weightedReferenceInterpolant q lambda) atTop
      (nhds ((lambda + 1) / (q : ℝ))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlinear : Tendsto (fun x : ℝ => (q : ℝ) * x - 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1)
      (Filter.tendsto_id.const_mul_atTop hqR)
  have hdenprod : Tendsto
      (fun x : ℝ => (q : ℝ) * ((q : ℝ) * x - 1)) atTop atTop :=
    hlinear.const_mul_atTop hqR
  have hcorrection : Tendsto
      (fun x : ℝ =>
        (1 - lambda * ((q : ℝ) - 1)) /
          ((q : ℝ) * ((q : ℝ) * x - 1)))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hdenprod
  have hconstant : Tendsto
      (fun _ : ℝ => (lambda + 1) / (q : ℝ)) atTop
      (nhds ((lambda + 1) / (q : ℝ))) := tendsto_const_nhds
  have hsum := hconstant.add hcorrection
  have hevent :
      (fun x : ℝ =>
        (lambda + 1) / (q : ℝ) +
          (1 - lambda * ((q : ℝ) - 1)) /
            ((q : ℝ) * ((q : ℝ) * x - 1))) =ᶠ[atTop]
        weightedReferenceInterpolant q lambda := by
    filter_upwards [eventually_gt_atTop (1 / (q : ℝ))] with x hx
    have hx' : (1 : ℝ) < x * (q : ℝ) :=
      (div_lt_iff₀ hqR).mp hx
    have hden : (q : ℝ) * x - 1 ≠ 0 := by
      nlinarith
    exact (weightedReferenceInterpolant_correction hq lambda x hden).symm
  simpa only [add_zero] using hsum.congr' hevent

/-- The reciprocal golden ratio satisfies its quadratic relation. -/
theorem goldenReciprocal_quadratic_weighted :
    goldenReciprocal ^ 2 + goldenReciprocal - 1 = 0 := by
  dsimp [goldenReciprocal]
  nlinarith [sqrt_five_sq]

/-- Positivity and the unit upper bound for the reciprocal golden ratio. -/
theorem goldenReciprocal_unit_interval :
    goldenReciprocal ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · linarith [two_fifths_lt_goldenReciprocal]
  · linarith [goldenReciprocal_lt_two_thirds]

/-- The exact rational window used to exclude exponent one. -/
theorem goldenReciprocal_three_fifths_bound :
    (3 : ℝ) / 5 < goldenReciprocal := by
  dsimp [goldenReciprocal]
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- The reciprocal golden ratio is irrational. -/
theorem goldenReciprocal_irrational : Irrational goldenReciprocal := by
  have h := Real.goldenConj_irrational.neg
  convert h using 1
  simp [Real.goldenConj, goldenReciprocal]
  ring

/-- Fibonacci coordinates of every positive power of the reciprocal golden
ratio. -/
theorem goldenReciprocal_power_fibonacci (n : ℕ) :
    goldenReciprocal ^ (n + 1) =
      (-1 : ℝ) ^ n *
        ((Nat.fib (n + 1) : ℝ) * goldenReciprocal - (Nat.fib n : ℝ)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        goldenReciprocal ^ (n.succ + 1) =
            goldenReciprocal ^ (n + 1) * goldenReciprocal := by
              rw [show n.succ + 1 = (n + 1) + 1 by omega, pow_succ]
        _ = (-1 : ℝ) ^ n *
              ((Nat.fib (n + 1) : ℝ) * goldenReciprocal -
                (Nat.fib n : ℝ)) * goldenReciprocal := by rw [ih]
        _ = (-1 : ℝ) ^ n.succ *
              ((Nat.fib (n.succ + 1) : ℝ) * goldenReciprocal -
                (Nat.fib n.succ : ℝ)) := by
              rw [show n.succ + 1 = n + 2 by omega, Nat.fib_add_two]
              push_cast
              rw [pow_succ]
              have hmul : goldenReciprocal * goldenReciprocal =
                  1 - goldenReciprocal := by
                nlinarith [goldenReciprocal_quadratic_weighted]
              ring_nf
              rw [sq, hmul]
              simp [Nat.succ_eq_add_one, Nat.add_comm]
              ring

/-- Rational coordinates in the basis `{1, goldenReciprocal}` are unique. -/
theorem goldenReciprocal_rational_coordinates {a c : ℚ}
    (h : (a : ℝ) * goldenReciprocal + (c : ℝ) = 0) :
    a = 0 ∧ c = 0 := by
  by_cases ha : a = 0
  · subst a
    simp only [Rat.cast_zero, zero_mul, zero_add, Rat.cast_eq_zero] at h
    exact ⟨rfl, h⟩
  · have haR : (a : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ha
    have htau : goldenReciprocal = ((-c / a : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_neg]
      apply (eq_div_iff haR).2
      nlinarith
    exact False.elim (goldenReciprocal_irrational.ne_rat (-c / a) htau)

/-- The equation obtained by evaluating the interpolant at a reciprocal golden
power. -/
noncomputable def goldenPowerEquation (q r : ℕ) (lambda : ℝ) : ℝ :=
  goldenReciprocal ^ (r + 1) - lambda * goldenReciprocal ^ r -
    (q : ℝ) * goldenReciprocal + lambda + 1

/-- Equality with the reciprocal golden ratio is equivalent to the displayed
power equation. -/
theorem weightedInterpolant_goldenPower_iff {q r : ℕ} {lambda : ℝ}
    (hq : 2 ≤ q) (hr : 1 ≤ r) :
    weightedReferenceInterpolant q lambda
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      goldenPowerEquation q r lambda = 0 := by
  have htau := goldenReciprocal_unit_interval
  have hpowpos : 0 < goldenReciprocal ^ r := pow_pos htau.1 r
  have hpowlt : goldenReciprocal ^ r < 1 := by
    exact pow_lt_one₀ htau.1.le htau.2 (by omega)
  have hinv : 1 < (goldenReciprocal ^ r)⁻¹ := (one_lt_inv₀ hpowpos).2 hpowlt
  have hden :
      (q : ℝ) * (goldenReciprocal ^ r)⁻¹ - 1 ≠ 0 := by
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hpowne : goldenReciprocal ^ r ≠ 0 := ne_of_gt hpowpos
  unfold weightedReferenceInterpolant goldenPowerEquation
  rw [div_eq_iff hden]
  constructor
  · intro h
    have hscaled := congrArg
      (fun z : ℝ => z * goldenReciprocal ^ r) h
    field_simp [hpowne] at hscaled
    rw [pow_succ]
    nlinarith
  · intro h
    have hcross :
        lambda + 1 - lambda * goldenReciprocal ^ r =
          goldenReciprocal * ((q : ℝ) - goldenReciprocal ^ r) := by
      rw [pow_succ] at h
      nlinarith
    field_simp [hpowne]
    nlinarith


/-- Rational coefficient of `goldenReciprocal` in the power equation. -/
def rationalGoldenCoefficientA (q r : ℕ) (lambda : ℚ) : ℚ :=
  (-1 : ℚ) ^ r * (Nat.fib (r + 1) + lambda * Nat.fib r) - q

/-- Rational constant coefficient in the power equation. -/
def rationalGoldenCoefficientB (r : ℕ) (lambda : ℚ) : ℚ :=
  (-1 : ℚ) ^ (r + 1) *
      (Nat.fib r + lambda * Nat.fib (r - 1)) + lambda + 1

/-- The power equation in the rational basis `{goldenReciprocal, 1}`. -/
theorem goldenPowerEquation_rational_coordinates {q r : ℕ} {lambda : ℚ}
    (hr : 1 ≤ r) :
    goldenPowerEquation q r (lambda : ℝ) =
      (rationalGoldenCoefficientA q r lambda : ℝ) * goldenReciprocal +
        (rationalGoldenCoefficientB r lambda : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 1 + n = n + 1 by omega]
  unfold goldenPowerEquation
  rw [goldenReciprocal_power_fibonacci (n + 1),
    goldenReciprocal_power_fibonacci n]
  simp only [rationalGoldenCoefficientA,
    rationalGoldenCoefficientB]
  push_cast
  ring

/-- A vanishing power equation with rational weight forces both Fibonacci
coordinates to vanish. -/
theorem goldenPowerEquation_zero_iff_rational_coordinates
    {q r : ℕ} {lambda : ℚ} (hr : 1 ≤ r) :
    goldenPowerEquation q r (lambda : ℝ) = 0 ↔
      rationalGoldenCoefficientA q r lambda = 0 ∧
        rationalGoldenCoefficientB r lambda = 0 := by
  rw [goldenPowerEquation_rational_coordinates hr]
  constructor
  · intro h
    exact goldenReciprocal_rational_coordinates h
  · rintro ⟨hA, hB⟩
    rw [hA, hB]
    norm_num


/-- The constant Fibonacci coordinate is positive at every odd exponent. -/
theorem rationalGoldenCoefficientB_pos_of_odd {r : ℕ} {lambda : ℚ}
    (hr : 1 ≤ r) (hodd : Odd r) (hlambda : 0 ≤ lambda) :
    0 < rationalGoldenCoefficientB r lambda := by
  unfold rationalGoldenCoefficientB
  rw [hodd.add_one.neg_one_pow, one_mul]
  have hfibNat : 0 < Nat.fib r := Nat.fib_pos.mpr (by omega)
  have hfib : (0 : ℚ) < Nat.fib r := by exact_mod_cast hfibNat
  have hprev : (0 : ℚ) ≤ Nat.fib (r - 1) := by positivity
  nlinarith [mul_nonneg hlambda hprev]

/-- From exponent four onward, the constant Fibonacci coordinate is negative
at every even exponent. -/
theorem rationalGoldenCoefficientB_neg_of_even_four_le
    {r : ℕ} {lambda : ℚ} (hr : 4 ≤ r) (heven : Even r)
    (hlambda : 0 ≤ lambda) :
    rationalGoldenCoefficientB r lambda < 0 := by
  unfold rationalGoldenCoefficientB
  rw [heven.add_one.neg_one_pow, neg_one_mul]
  have hfrNat : 3 ≤ Nat.fib r := by
    have hmono := Nat.fib_mono hr
    norm_num at hmono ⊢
    exact hmono
  have hrprev : 3 ≤ r - 1 := by omega
  have hprevNat : 2 ≤ Nat.fib (r - 1) := by
    have hmono := Nat.fib_mono hrprev
    norm_num at hmono ⊢
    exact hmono
  have hfr : (3 : ℚ) ≤ Nat.fib r := by exact_mod_cast hfrNat
  have hprev : (2 : ℚ) ≤ Nat.fib (r - 1) := by exact_mod_cast hprevNat
  have hfactor : (Nat.fib (r - 1) : ℚ) - 1 ≥ 0 := by nlinarith
  nlinarith [mul_nonneg hlambda hfactor]

/-- Rational weights collapse the two real golden branches to their square
endpoints. -/
theorem goldenPowerEquation_rational_classification
    {q r : ℕ} {lambda : ℚ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    goldenPowerEquation q r (lambda : ℝ) = 0 ↔
      (q = 2 ∧ lambda = 0 ∧ r = 2) ∨
        (q = 3 ∧ lambda = 1 ∧ r = 2) := by
  constructor
  · intro heq
    have hcoords :=
      (goldenPowerEquation_zero_iff_rational_coordinates hr).mp heq
    rcases Nat.even_or_odd r with heven | hodd
    · by_cases hr2 : r = 2
      · subst r
        have hA := hcoords.1
        norm_num [rationalGoldenCoefficientA] at hA
        have hqUpper : q ≤ 3 := by
          have hqR : (q : ℚ) = 2 + lambda := by nlinarith
          have : (q : ℚ) ≤ 3 := by nlinarith
          exact_mod_cast this
        interval_cases q
        · left
          constructor
          · rfl
          constructor
          · norm_num at hA ⊢
            linarith
          · rfl
        · right
          constructor
          · rfl
          constructor
          · norm_num at hA ⊢
            linarith
          · rfl
      · have hr4 : 4 ≤ r := by
          rcases heven with ⟨k, hk⟩
          omega
        have hneg := rationalGoldenCoefficientB_neg_of_even_four_le
          hr4 heven hlambda0
        rw [hcoords.2] at hneg
        exact (lt_irrefl 0 hneg).elim
    · have hpos := rationalGoldenCoefficientB_pos_of_odd
        hr hodd hlambda0
      rw [hcoords.2] at hpos
      exact (lt_irrefl 0 hpos).elim
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · norm_num [goldenPowerEquation]
      nlinarith [goldenReciprocal_quadratic_weighted]
    · norm_num [goldenPowerEquation]
      nlinarith [goldenReciprocal_quadratic_weighted]

/-- Interpolant form of the complete rational classification. -/
theorem weightedInterpolant_rational_classification
    {q r : ℕ} {lambda : ℚ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    weightedReferenceInterpolant q (lambda : ℝ)
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      (q = 2 ∧ lambda = 0 ∧ r = 2) ∨
        (q = 3 ∧ lambda = 1 ∧ r = 2) := by
  rw [weightedInterpolant_goldenPower_iff hq hr]
  exact goldenPowerEquation_rational_classification hq hr hlambda0 hlambda1


/-- The cubic and fourth powers used at the real branch endpoints. -/
theorem goldenReciprocal_third_power :
    goldenReciprocal ^ 3 = 2 * goldenReciprocal - 1 := by
  have hquad := goldenReciprocal_quadratic_weighted
  calc
    goldenReciprocal ^ 3 =
        goldenReciprocal * goldenReciprocal ^ 2 := by ring
    _ = goldenReciprocal * (1 - goldenReciprocal) := by
      congr 1
      nlinarith
    _ = 2 * goldenReciprocal - 1 := by nlinarith

 theorem goldenReciprocal_fourth_power_weighted :
    goldenReciprocal ^ 4 = 2 - 3 * goldenReciprocal := by
  nlinarith [goldenReciprocal_third_power,
    goldenReciprocal_quadratic_weighted]

/-- Difference identity behind the admissible real-weight window. -/
theorem goldenReciprocal_power_difference (r : ℕ) :
    goldenReciprocal ^ (r + 1) - goldenReciprocal ^ r =
      -goldenReciprocal ^ (r + 2) := by
  have hquad : goldenReciprocal ^ 2 = 1 - goldenReciprocal := by
    nlinarith [goldenReciprocal_quadratic_weighted]
  rw [show goldenReciprocal ^ (r + 1) =
      goldenReciprocal ^ r * goldenReciprocal by rw [pow_succ],
    show goldenReciprocal ^ (r + 2) =
      goldenReciprocal ^ r * goldenReciprocal ^ 2 by
        rw [← pow_add]]
  rw [hquad]
  ring

/-- The unique real weight obtained by solving the golden power equation. -/
noncomputable def goldenRealWeight (q r : ℕ) : ℝ :=
  ((q : ℝ) * goldenReciprocal - 1 - goldenReciprocal ^ (r + 1)) /
    (1 - goldenReciprocal ^ r)

/-- Solving the power equation for a real weight. -/
theorem goldenPowerEquation_zero_iff_realWeight {q r : ℕ} {lambda : ℝ}
    (hr : 1 ≤ r) :
    goldenPowerEquation q r lambda = 0 ↔ lambda = goldenRealWeight q r := by
  have htau := goldenReciprocal_unit_interval
  have hpowlt : goldenReciprocal ^ r < 1 :=
    pow_lt_one₀ htau.1.le htau.2 (by omega)
  have hden : 1 - goldenReciprocal ^ r ≠ 0 := by nlinarith
  unfold goldenPowerEquation goldenRealWeight
  rw [eq_div_iff hden]
  rw [pow_succ]
  constructor <;> intro h <;> nlinarith

/-- A real weight lies in the unit interval exactly on the displayed golden
window. -/
theorem goldenRealWeight_mem_unitInterval_iff_window {q r : ℕ}
    (hr : 1 ≤ r) :
    goldenRealWeight q r ∈ Set.Icc (0 : ℝ) 1 ↔
      1 + goldenReciprocal ^ (r + 1) ≤
          (q : ℝ) * goldenReciprocal ∧
        (q : ℝ) * goldenReciprocal ≤
          2 - goldenReciprocal ^ (r + 2) := by
  have htau := goldenReciprocal_unit_interval
  have hpowlt : goldenReciprocal ^ r < 1 :=
    pow_lt_one₀ htau.1.le htau.2 (by omega)
  have hden : 0 < 1 - goldenReciprocal ^ r := by nlinarith
  have hdiff := goldenReciprocal_power_difference r
  unfold goldenRealWeight
  constructor
  · rintro ⟨hlower, hupper⟩
    have hlower' := (le_div_iff₀ hden).mp hlower
    have hupper' := (div_le_iff₀ hden).mp hupper
    constructor <;> nlinarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · apply (le_div_iff₀ hden).2
      nlinarith
    · apply (div_le_iff₀ hden).2
      nlinarith

/-- Powers decrease as their exponents increase on the reciprocal-golden unit
interval. -/
theorem goldenReciprocal_pow_antitone {m n : ℕ} (hmn : m ≤ n) :
    goldenReciprocal ^ n ≤ goldenReciprocal ^ m := by
  exact pow_le_pow_of_le_one goldenReciprocal_unit_interval.1.le
    goldenReciprocal_unit_interval.2.le hmn

/-- The admissible real-weight window contains exactly moduli two and three
from exponent two onward. -/
theorem golden_window_classification {q r : ℕ} (hq : 2 ≤ q) (hr : 1 ≤ r) :
    (1 + goldenReciprocal ^ (r + 1) ≤
        (q : ℝ) * goldenReciprocal ∧
      (q : ℝ) * goldenReciprocal ≤
        2 - goldenReciprocal ^ (r + 2)) ↔
      (q = 2 ∨ q = 3) ∧ 2 ≤ r := by
  constructor
  · rintro ⟨hlower, hupper⟩
    have hqUpper : q ≤ 3 := by
      by_contra hnot
      have hq4 : 4 ≤ q := by omega
      have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq4
      have htau := goldenReciprocal_three_fifths_bound
      have hleft : 2 < (q : ℝ) * goldenReciprocal := by
        nlinarith [goldenReciprocal_unit_interval.1]
      have hpowpos : 0 < goldenReciprocal ^ (r + 2) :=
        pow_pos goldenReciprocal_unit_interval.1 _
      nlinarith
    have hqCases : q = 2 ∨ q = 3 := by omega
    constructor
    · exact hqCases
    · by_contra hnot
      have hr1 : r = 1 := by omega
      subst r
      rcases hqCases with rfl | rfl
      · have htau := goldenReciprocal_lt_two_thirds
        norm_num [goldenReciprocal_quadratic_weighted] at hlower
        nlinarith [goldenReciprocal_quadratic_weighted]
      · have htau := goldenReciprocal_three_fifths_bound
        norm_num [goldenReciprocal_third_power] at hupper
        nlinarith [goldenReciprocal_third_power]
  · rintro ⟨hqCases, hr2⟩
    have htau := goldenReciprocal_unit_interval
    rcases hqCases with rfl | rfl
    · norm_num only [Nat.cast_ofNat] at *
      have hpow3 : goldenReciprocal ^ (r + 1) ≤
          goldenReciprocal ^ 3 :=
        goldenReciprocal_pow_antitone (by omega)
      have hpow4 : goldenReciprocal ^ (r + 2) ≤
          goldenReciprocal ^ 4 :=
        goldenReciprocal_pow_antitone (by omega)
      constructor
      · nlinarith [goldenReciprocal_third_power]
      · nlinarith [goldenReciprocal_fourth_power_weighted, htau.1]
    · norm_num only [Nat.cast_ofNat] at *
      have hpow2 : goldenReciprocal ^ (r + 1) ≤
          goldenReciprocal ^ 2 :=
        goldenReciprocal_pow_antitone (by omega)
      have hpow4 : goldenReciprocal ^ (r + 2) ≤
          goldenReciprocal ^ 4 :=
        goldenReciprocal_pow_antitone (by omega)
      constructor
      · nlinarith [goldenReciprocal_quadratic_weighted,
          goldenReciprocal_unit_interval.1]
      · nlinarith [goldenReciprocal_fourth_power_weighted]

/-- Complete real-weight classification of the reciprocal-golden equation. -/
theorem weightedInterpolant_real_classification
    {q r : ℕ} {lambda : ℝ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    weightedReferenceInterpolant q lambda
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      (q = 2 ∨ q = 3) ∧ 2 ≤ r ∧ lambda = goldenRealWeight q r := by
  rw [weightedInterpolant_goldenPower_iff hq hr,
    goldenPowerEquation_zero_iff_realWeight hr]
  constructor
  · intro hlambdaEq
    have hweightMem : goldenRealWeight q r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [← hlambdaEq] using hlambda
    have hwindow :=
      (goldenRealWeight_mem_unitInterval_iff_window hr).mp hweightMem
    exact ⟨(golden_window_classification hq hr).mp hwindow |>.1,
      (golden_window_classification hq hr).mp hwindow |>.2, hlambdaEq⟩
  · rintro ⟨_, _, hlambdaEq⟩
    exact hlambdaEq


/-- Every later admissible branch weight is irrational. -/
theorem goldenRealWeight_irrational {q r : ℕ}
    (hq : q = 2 ∨ q = 3) (hr : 3 ≤ r) :
    Irrational (goldenRealWeight q r) := by
  have hqLower : 2 ≤ q := by rcases hq with rfl | rfl <;> norm_num
  have hrOne : 1 ≤ r := by omega
  have hwindow := (golden_window_classification hqLower hrOne).mpr
    ⟨hq, by omega⟩
  have hweightMem :=
    (goldenRealWeight_mem_unitInterval_iff_window hrOne).mpr hwindow
  intro hrat
  rcases hrat with ⟨lambda, hlambda⟩
  have hlambda0 : 0 ≤ lambda := by
    have : (0 : ℝ) ≤ (lambda : ℝ) := by
      rw [hlambda]
      exact hweightMem.1
    exact_mod_cast this
  have hlambda1 : lambda ≤ 1 := by
    have : (lambda : ℝ) ≤ 1 := by
      rw [hlambda]
      exact hweightMem.2
    exact_mod_cast this
  have heq : goldenPowerEquation q r (lambda : ℝ) = 0 :=
    (goldenPowerEquation_zero_iff_realWeight hrOne).2 hlambda
  have hclass := (goldenPowerEquation_rational_classification
    hqLower hrOne hlambda0 hlambda1).mp heq
  rcases hclass with ⟨_, _, hr2⟩ | ⟨_, _, hr2⟩ <;> omega

/-- The two rational branch endpoints. -/
theorem goldenRealWeight_square_endpoints :
    goldenRealWeight 2 2 = 0 ∧ goldenRealWeight 3 2 = 1 := by
  constructor
  · symm
    apply (goldenPowerEquation_zero_iff_realWeight
      (q := 2) (r := 2) (lambda := (0 : ℝ)) (by norm_num)).mp
    norm_num [goldenPowerEquation]
    nlinarith [goldenReciprocal_quadratic_weighted]
  · symm
    apply (goldenPowerEquation_zero_iff_realWeight
      (q := 3) (r := 2) (lambda := (1 : ℝ)) (by norm_num)).mp
    norm_num [goldenPowerEquation]
    nlinarith [goldenReciprocal_quadratic_weighted]

/-- First irrational values on the two real branches. -/
theorem goldenRealWeight_first_later_values :
    goldenRealWeight 2 3 = goldenReciprocal ^ 3 / 2 ∧
      goldenRealWeight 3 3 = 3 * goldenReciprocal / 2 := by
  constructor
  · symm
    apply (goldenPowerEquation_zero_iff_realWeight
      (q := 2) (r := 3) (lambda := goldenReciprocal ^ 3 / 2)
      (by norm_num)).mp
    unfold goldenPowerEquation
    nlinarith [goldenReciprocal_third_power,
      goldenReciprocal_fourth_power_weighted,
      goldenReciprocal_quadratic_weighted]
  · symm
    apply (goldenPowerEquation_zero_iff_realWeight
      (q := 3) (r := 3) (lambda := 3 * goldenReciprocal / 2)
      (by norm_num)).mp
    unfold goldenPowerEquation
    nlinarith [goldenReciprocal_third_power,
      goldenReciprocal_fourth_power_weighted,
      goldenReciprocal_quadratic_weighted]

/-- Exact step difference along a real-weight branch. -/
theorem goldenRealWeight_step_difference (q r : ℕ) (hr : 1 ≤ r) :
    goldenRealWeight q (r + 1) - goldenRealWeight q r =
      ((goldenReciprocal ^ (r + 1) - goldenReciprocal ^ r) *
          (((q : ℝ) - 1) * goldenReciprocal - 1)) /
        ((1 - goldenReciprocal ^ (r + 1)) *
          (1 - goldenReciprocal ^ r)) := by
  have htau := goldenReciprocal_unit_interval
  have hdenR : 1 - goldenReciprocal ^ r ≠ 0 := by
    have hlt := pow_lt_one₀ htau.1.le htau.2 (by omega : r ≠ 0)
    nlinarith
  have hdenS : 1 - goldenReciprocal ^ (r + 1) ≠ 0 := by
    have hlt := pow_lt_one₀ htau.1.le htau.2 (by omega : r + 1 ≠ 0)
    nlinarith
  unfold goldenRealWeight
  rw [show r + 1 + 1 = r + 2 by omega]
  field_simp [hdenR, hdenS]
  rw [pow_succ (a := goldenReciprocal) (n := r + 1),
    pow_succ (a := goldenReciprocal) (n := r)]
  ring

/-- The modulus-two branch rises and the modulus-three branch falls. -/
theorem goldenRealWeight_branch_directions {r : ℕ} (hr : 2 ≤ r) :
    goldenRealWeight 2 r < goldenRealWeight 2 (r + 1) ∧
      goldenRealWeight 3 (r + 1) < goldenRealWeight 3 r := by
  have htau := goldenReciprocal_unit_interval
  have hpowrPos : 0 < goldenReciprocal ^ r := pow_pos htau.1 _
  have hpowSuccLt : goldenReciprocal ^ (r + 1) < goldenReciprocal ^ r := by
    rw [pow_succ]
    exact mul_lt_of_lt_one_right hpowrPos htau.2
  have hdenR : 0 < 1 - goldenReciprocal ^ r := by
    have hlt := pow_lt_one₀ htau.1.le htau.2 (by omega : r ≠ 0)
    nlinarith
  have hdenS : 0 < 1 - goldenReciprocal ^ (r + 1) := by
    have hlt := pow_lt_one₀ htau.1.le htau.2 (by omega : r + 1 ≠ 0)
    nlinarith
  constructor
  · rw [← sub_pos, goldenRealWeight_step_difference 2 r (by omega)]
    norm_num only [Nat.cast_ofNat]
    apply div_pos
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr hpowSuccLt)
        (by simpa using (sub_neg.mpr htau.2))
    · exact mul_pos hdenS hdenR
  · rw [← sub_pos]
    have hstep := goldenRealWeight_step_difference 3 r (by omega)
    have hfactor : 0 < 2 * goldenReciprocal - 1 := by
      nlinarith [goldenReciprocal_three_fifths_bound]
    have hnum :
        (goldenReciprocal ^ (r + 1) - goldenReciprocal ^ r) *
          (2 * goldenReciprocal - 1) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hpowSuccLt) hfactor
    have hfrac :
        ((goldenReciprocal ^ (r + 1) - goldenReciprocal ^ r) *
            (2 * goldenReciprocal - 1)) /
          ((1 - goldenReciprocal ^ (r + 1)) *
            (1 - goldenReciprocal ^ r)) < 0 :=
      div_neg_of_neg_of_pos hnum (mul_pos hdenS hdenR)
    norm_num only [Nat.cast_ofNat] at hstep
    nlinarith

/-- Each real branch converges to its open-end weight. -/
theorem goldenRealWeight_tendsto (q : ℕ) :
    Tendsto (goldenRealWeight q) atTop
      (nhds ((q : ℝ) * goldenReciprocal - 1)) := by
  have htau := goldenReciprocal_unit_interval
  have hpow : Tendsto (fun r : ℕ => goldenReciprocal ^ r) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one htau.1.le htau.2
  have hpowSucc : Tendsto
      (fun r : ℕ => goldenReciprocal ^ (r + 1)) atTop (nhds 0) := by
    simpa only [pow_succ, zero_mul] using hpow.mul_const goldenReciprocal
  have hconstant : Tendsto
      (fun _ : ℕ => (q : ℝ) * goldenReciprocal - 1) atTop
      (nhds ((q : ℝ) * goldenReciprocal - 1)) := tendsto_const_nhds
  have hnum : Tendsto
      (fun r : ℕ =>
        (q : ℝ) * goldenReciprocal - 1 - goldenReciprocal ^ (r + 1))
      atTop (nhds ((q : ℝ) * goldenReciprocal - 1)) := by
    simpa only [sub_zero] using hconstant.sub hpowSucc
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hden : Tendsto (fun r : ℕ => 1 - goldenReciprocal ^ r)
      atTop (nhds 1) := by
    simpa only [sub_zero] using hone.sub hpow
  change Tendsto
    ((fun r : ℕ =>
        (q : ℝ) * goldenReciprocal - 1 - goldenReciprocal ^ (r + 1)) /
      (fun r : ℕ => 1 - goldenReciprocal ^ r)) atTop
    (nhds ((q : ℝ) * goldenReciprocal - 1))
  simpa only [div_one] using
    hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)

/-- Endpoint limits displayed for the two branches. -/
theorem goldenRealWeight_branch_limits :
    Tendsto (goldenRealWeight 2) atTop
        (nhds (goldenReciprocal ^ 3)) ∧
      Tendsto (goldenRealWeight 3) atTop
        (nhds (3 * goldenReciprocal - 1)) := by
  constructor
  · simpa [goldenReciprocal_third_power] using goldenRealWeight_tendsto 2
  · simpa using goldenRealWeight_tendsto 3

end NField.Golden
