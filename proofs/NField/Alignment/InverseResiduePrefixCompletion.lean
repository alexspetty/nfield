/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindInverseResidueTransform

/-!
# Completion of inverse-residue prefixes

The finite Fourier identity is proved on the manuscript's actual centered
inverse-residue prefix.  The published Weil--Estermann estimate enters only
as a bound for the incomplete inverse additive character sum.  The remaining
cotangent-frequency envelope is stated separately, so neither source input is
the completed-prefix conclusion that this module derives.
-/

namespace NField.Alignment.InverseResiduePrefixCompletion

open scoped BigOperators ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.DedekindFourierMoment
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.DedekindReciprocity

/-- The incomplete inverse additive character sum occurring after finite
Fourier inversion of the centered sawtooth. -/
noncomputable def inverseAdditivePrefix
    (q : ℕ) [NeZero q] (r X : ℕ) (j : ZMod q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    if hn : n.Coprime q then
      ZMod.stdAddChar
        (j * ((r : ZMod q) * (ZMod.unitOfCoprime n hn)⁻¹.val))
    else 0

/-- The real prefix is exactly the corresponding sum of intrinsic centered
inverse-residue coefficients. -/
theorem inverseResiduePrefix_cast_eq_inverseSawCoefficient
    {q r X : ℕ} (hq : 0 < q) :
    ((inverseResiduePrefix q r X : ℝ) : ℂ) =
      ∑ n ∈ Finset.Icc 1 X, inverseSawCoefficient q r n := by
  unfold inverseResiduePrefix
  push_cast
  apply Finset.sum_congr rfl
  intro n _hnmem
  by_cases hn : n.Coprime q
  · rw [if_pos hn, inverseSawCoefficient_eq_rationalSawtooth hq hn]
    norm_cast
  · rw [if_neg hn]
    simp [inverseSawCoefficient, hq.ne', hn]

/-- Exact finite Fourier inversion of the incomplete inverse-residue prefix. -/
theorem inverseResiduePrefix_fourier
    {q r X : ℕ} (hq : 0 < q) :
    letI : NeZero q := ⟨hq.ne'⟩
    ((inverseResiduePrefix q r X : ℝ) : ℂ) =
      (q : ℂ)⁻¹ * ∑ j : ZMod q,
        inverseAdditivePrefix q r X j *
          ZMod.dft (centeredSawtooth : ZMod q → ℂ) j := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [inverseResiduePrefix_cast_eq_inverseSawCoefficient hq]
  have hterm (n : ℕ) :
      inverseSawCoefficient q r n =
        (q : ℂ)⁻¹ * ∑ j : ZMod q,
          (if hn : n.Coprime q then
            ZMod.stdAddChar
              (j * ((r : ZMod q) * (ZMod.unitOfCoprime n hn)⁻¹.val))
          else 0) *
            ZMod.dft (centeredSawtooth : ZMod q → ℂ) j := by
    by_cases hn : n.Coprime q
    · unfold inverseSawCoefficient
      rw [dif_neg hq.ne', dif_pos hn]
      rw [centeredSawtooth_fourier_inversion]
      apply congrArg ((q : ℂ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro j _hj
      rw [dif_pos hn]
    · have hnonunit : ¬IsUnit (n : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]
        simpa using hn
      rw [inverseSawCoefficient_eq_residue]
      simp [residueInverseSawCoefficient, hnonunit, hn]
  calc
    (∑ n ∈ Finset.Icc 1 X, inverseSawCoefficient q r n) =
        ∑ n ∈ Finset.Icc 1 X,
          ((q : ℂ)⁻¹ * ∑ j : ZMod q,
            (if hn : n.Coprime q then
              ZMod.stdAddChar
                (j * ((r : ZMod q) *
                  (ZMod.unitOfCoprime n hn)⁻¹.val))
            else 0) *
              ZMod.dft (centeredSawtooth : ZMod q → ℂ) j) := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact hterm n
    _ = (q : ℂ)⁻¹ * ∑ j : ZMod q,
        inverseAdditivePrefix q r X j *
          ZMod.dft (centeredSawtooth : ZMod q → ℂ) j := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      unfold inverseAdditivePrefix
      rw [Finset.sum_mul]

/-- The published incomplete Kloosterman estimate at every nonzero Fourier
frequency.  This is the Weil--Estermann source input. -/
def WeilEstermannInversePrefixEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q (hq : 2 ≤ q),
    letI : NeZero q := ⟨by omega⟩
    ∀ r X (j : ZMod q), r.Coprime q → 1 ≤ X → X ≤ q → j ≠ 0 →
      ‖inverseAdditivePrefix q r X j‖ ≤
        C * (q : ℝ).sqrt * q.divisors.card *
          ((j.val.gcd q : ℕ) : ℝ).sqrt * Real.log (2 * q)

/-- The elementary cotangent-frequency grouping used after the
Weil--Estermann bound.  It is kept separate from the Kloosterman source and
from the completed-prefix conclusion. -/
def CotangentGcdFrequencyEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q (hq : 2 ≤ q),
    letI : NeZero q := ⟨by omega⟩
    (∑ j : ZMod q, if j = 0 then 0 else
      ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
        ((j.val.gcd q : ℕ) : ℝ).sqrt) ≤
      C * (q : ℝ) * Real.log (2 * q) * reciprocalSqrtDivisorSum q

set_option maxHeartbeats 800000 in
/-- The cotangent-frequency grouping is elementary and needs no external
certificate.  Grouping a nonzero frequency by `gcd(j,q)` cancels one square
root of the gcd against the scaled circular distance. -/
theorem cotangentGcdFrequencyEstimate : CotangentGcdFrequencyEstimate := by
  refine ⟨1, by norm_num, ?_⟩
  intro q hq
  letI : NeZero q := ⟨by omega⟩
  let w : ℕ → ℝ := fun n =>
    if n = 0 then 0 else
      ‖sawtoothFourier q n‖ * (((n.gcd q : ℕ) : ℝ).sqrt)
  have hzmod :
      (∑ j : ZMod q, if j = 0 then 0 else
        ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
          ((j.val.gcd q : ℕ) : ℝ).sqrt) =
        ∑ n ∈ Finset.Ico 1 q,
          ‖sawtoothFourier q n‖ * ((n.gcd q : ℕ) : ℝ).sqrt := by
    calc
      (∑ j : ZMod q, if j = 0 then 0 else
          ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
            ((j.val.gcd q : ℕ) : ℝ).sqrt) =
          ∑ n : Fin q, w n.val := by
            rw [← (ZMod.finEquiv q).toEquiv.sum_comp]
            apply Finset.sum_congr rfl
            intro n _hn
            have hcoe : ((ZMod.finEquiv q).toEquiv n : ZMod q) =
                (n.val : ZMod q) := by
              simpa using
                NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast n
            rw [hcoe]
            have hval : (n.val : ZMod q).val = n.val := by
              rw [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt]
            rw [hval]
            unfold w
            by_cases hn : n.val = 0
            · simp [hn]
            · have hcastne : (n.val : ZMod q) ≠ 0 := by
                intro hzero
                have hzeroVal := congrArg ZMod.val hzero
                apply hn
                simpa [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt] using hzeroVal
              rw [if_neg hn, if_neg hcastne]
              rw [norm_dft_centeredSawtooth_eq]
              rw [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt]
      _ = ∑ n ∈ Finset.range q, w n :=
        Fin.sum_univ_eq_sum_range w q
      _ = ∑ n ∈ Finset.Ico 1 q,
          ‖sawtoothFourier q n‖ * ((n.gcd q : ℕ) : ℝ).sqrt := by
        rw [NField.Alignment.DedekindReciprocity.sum_range_eq_sum_Ico_one
          w (by omega)]
        · apply Finset.sum_congr rfl
          intro n hn
          have hnI := Finset.mem_Ico.mp hn
          have hn0 : n ≠ 0 := by omega
          simp [w, hn0]
        · simp [w]
  rw [hzmod]
  rw [sum_Ico_gcd_unit_reindex hq]
  have hinner : ∀ g ∈ q.divisors.filter (fun g => 2 ≤ q / g),
      (∑ u ∈ (Finset.Ico 1 (q / g)).filter
          (fun u => u.Coprime (q / g)),
        ‖sawtoothFourier q (g * u)‖ *
          ((((g * u).gcd q : ℕ) : ℝ).sqrt)) ≤
        (q : ℝ) / (2 * (g : ℝ).sqrt) * (harmonic q : ℝ) := by
    intro g hg
    have hgdiv : g ∣ q :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
    have hgpos : 0 < g :=
      Nat.pos_of_mem_divisors (Finset.mem_filter.mp hg).1
    have hQ2 : 2 ≤ q / g := (Finset.mem_filter.mp hg).2
    have hqfactor : q = g * (q / g) := (Nat.mul_div_cancel' hgdiv).symm
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hsqrtg : (0 : ℝ) < (g : ℝ).sqrt := Real.sqrt_pos.2 hgR
    have hpoint : ∀ u ∈ (Finset.Ico 1 (q / g)).filter
        (fun u => u.Coprime (q / g)),
        ‖sawtoothFourier q (g * u)‖ *
            ((((g * u).gcd q : ℕ) : ℝ).sqrt) ≤
          (q : ℝ) / (4 * (g : ℝ).sqrt) *
            (1 / (circularDistance (q / g) u : ℝ)) := by
      intro u hu
      have huI := Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1
      have hcop := (Finset.mem_filter.mp hu).2
      have hguPos : 0 < g * u := Nat.mul_pos hgpos huI.1
      have hguLt : g * u < q := by
        rw [hqfactor]
        exact (Nat.mul_lt_mul_left hgpos).2 huI.2
      have hgcd : (g * u).gcd q = g := by
        rw [hqfactor, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
      have hdistNat : circularDistance q (g * u) =
          g * circularDistance (q / g) u := by
        conv_lhs => rw [hqfactor]
        exact circularDistance_mul_left (Nat.le_of_lt huI.2)
      have hdistPos : (0 : ℝ) < circularDistance (q / g) u := by
        exact_mod_cast circularDistance_pos huI.1 huI.2
      have hfourier := norm_sawtoothFourier_le
        (by omega : 0 < q) hguPos hguLt
      rw [hdistNat] at hfourier
      rw [hgcd]
      have hsquare : (g : ℝ).sqrt * (g : ℝ).sqrt = (g : ℝ) :=
        Real.mul_self_sqrt hgR.le
      calc
        ‖sawtoothFourier q (g * u)‖ * (g : ℝ).sqrt ≤
            ((q : ℝ) /
              (4 * ((g * circularDistance (q / g) u : ℕ) : ℝ))) *
                (g : ℝ).sqrt := by gcongr
        _ = (q : ℝ) / (4 * (g : ℝ).sqrt) *
              (1 / (circularDistance (q / g) u : ℝ)) := by
          push_cast
          field_simp [hgR.ne', hsqrtg.ne', hdistPos.ne']
          rw [pow_two]
          exact hsquare
    calc
      (∑ u ∈ (Finset.Ico 1 (q / g)).filter
          (fun u => u.Coprime (q / g)),
          ‖sawtoothFourier q (g * u)‖ *
            ((((g * u).gcd q : ℕ) : ℝ).sqrt)) ≤
        ∑ u ∈ (Finset.Ico 1 (q / g)).filter
          (fun u => u.Coprime (q / g)),
          (q : ℝ) / (4 * (g : ℝ).sqrt) *
            (1 / (circularDistance (q / g) u : ℝ)) := by
              exact Finset.sum_le_sum fun u hu => hpoint u hu
      _ ≤ ∑ u ∈ Finset.Ico 1 (q / g),
          (q : ℝ) / (4 * (g : ℝ).sqrt) *
            (1 / (circularDistance (q / g) u : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro u _huBig _huSmall
          positivity
      _ = (q : ℝ) / (4 * (g : ℝ).sqrt) *
          (∑ u ∈ Finset.Ico 1 (q / g),
            1 / (circularDistance (q / g) u : ℝ)) := by
            rw [Finset.mul_sum]
      _ ≤ (q : ℝ) / (4 * (g : ℝ).sqrt) *
          (2 * (harmonic (q / g) : ℝ)) := by
            gcongr
            exact circularReciprocal_sum_le_harmonic (by omega)
      _ ≤ (q : ℝ) / (4 * (g : ℝ).sqrt) *
          (2 * (harmonic q : ℝ)) := by
            gcongr
            exact_mod_cast harmonic_cast_mono (Nat.div_le_self q g)
      _ = (q : ℝ) / (2 * (g : ℝ).sqrt) *
          (harmonic q : ℝ) := by ring
  calc
    (∑ g ∈ q.divisors.filter (fun g => 2 ≤ q / g),
        ∑ u ∈ (Finset.Ico 1 (q / g)).filter
          (fun u => u.Coprime (q / g)),
          ‖sawtoothFourier q (g * u)‖ *
            ((((g * u).gcd q : ℕ) : ℝ).sqrt)) ≤
      ∑ g ∈ q.divisors.filter (fun g => 2 ≤ q / g),
        (q : ℝ) / (2 * (g : ℝ).sqrt) * (harmonic q : ℝ) := by
          exact Finset.sum_le_sum fun g hg => hinner g hg
    _ ≤ ∑ g ∈ q.divisors,
        (q : ℝ) / (2 * (g : ℝ).sqrt) * (harmonic q : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro g hg _hnot
      have hgpos := Nat.pos_of_mem_divisors hg
      have hsqrt : (0 : ℝ) < (g : ℝ).sqrt := by positivity
      have hH0 : (0 : ℝ) ≤ (harmonic q : ℝ) := by
        exact_mod_cast (show (0 : ℚ) ≤ harmonic q by
          unfold harmonic
          positivity)
      exact mul_nonneg (div_nonneg (by positivity) (by positivity)) hH0
    _ = (q : ℝ) / 2 * (harmonic q : ℝ) *
        reciprocalSqrtDivisorSum q := by
      unfold reciprocalSqrtDivisorSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      have hgpos : (0 : ℝ) < g := by
        exact_mod_cast Nat.pos_of_mem_divisors hg
      field_simp [Real.sqrt_ne_zero'.mpr hgpos]
    _ ≤ (q : ℝ) * Real.log (2 * q) * reciprocalSqrtDivisorSum q := by
      have hH := harmonic_le_one_add_log q
      have hHreal : (harmonic q : ℝ) ≤ 1 + Real.log q := by exact_mod_cast hH
      have hlogMul : Real.log (2 * (q : ℝ)) =
          Real.log 2 + Real.log q := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      have hlogBound : 1 + Real.log (q : ℝ) ≤
          2 * Real.log (2 * (q : ℝ)) := by
        rw [hlogMul]
        have hqLog : Real.log 2 ≤ Real.log (q : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hq)
        have htwo : (1 : ℝ) ≤ 2 * Real.log 2 := by
          nlinarith [Real.log_two_gt_d9]
        linarith
      have hsigma : 0 ≤ reciprocalSqrtDivisorSum q := by
        unfold reciprocalSqrtDivisorSum
        positivity
      have hqnonneg : (0 : ℝ) ≤ q := by positivity
      have hhalf : (harmonic q : ℝ) / 2 ≤ Real.log (2 * q) := by
        linarith
      calc
        (q : ℝ) / 2 * (harmonic q : ℝ) *
            reciprocalSqrtDivisorSum q =
          ((q : ℝ) * reciprocalSqrtDivisorSum q) *
            ((harmonic q : ℝ) / 2) := by ring
        _ ≤ ((q : ℝ) * reciprocalSqrtDivisorSum q) *
            Real.log (2 * q) := by gcongr
        _ = (q : ℝ) * Real.log (2 * q) *
            reciprocalSqrtDivisorSum q := by ring
    _ = 1 * (q : ℝ) * Real.log (2 * q) *
        reciprocalSqrtDivisorSum q := by ring

/-- The sole published source estimate used by completion.  The frequency
grouping is proved internally above. -/
def WeilEstermannCompletionInputs : Prop :=
  WeilEstermannInversePrefixEstimate

/-- Finite Fourier inversion and the two source estimates imply the exact
completed-prefix envelope printed in the manuscript. -/
theorem completed_inverse_prefixes
    (hsource : WeilEstermannCompletionInputs) :
    CompletedInversePrefixEstimate := by
  rcases hsource with ⟨C₁, hC₁, hKloosterman⟩
  rcases cotangentGcdFrequencyEstimate with ⟨C₂, hC₂, hfrequency⟩
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro q r X hq hr hX hXq
  letI : NeZero q := ⟨by omega⟩
  have hqR : (0 : ℝ) < q := by positivity
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  have hzero :
      ZMod.dft (centeredSawtooth : ZMod q → ℂ) 0 = 0 := by
    calc
      ZMod.dft (centeredSawtooth : ZMod q → ℂ) 0 =
          sawtoothFourier q 0 := by
            simpa using (sawtoothFourier_eq_dft (m := q) (n := 0)).symm
      _ = 0 := sawtoothFourier_zero (by omega)
  have hterm : ∀ j : ZMod q,
      ‖inverseAdditivePrefix q r X j *
          ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ ≤
        C₁ * (q : ℝ).sqrt * q.divisors.card * Real.log (2 * q) *
          (if j = 0 then 0 else
            ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
              ((j.val.gcd q : ℕ) : ℝ).sqrt) := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [hzero]
    · rw [if_neg hj, norm_mul]
      have hjbound := hKloosterman q hq r X j hr hX hXq hj
      calc
        ‖inverseAdditivePrefix q r X j‖ *
            ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ ≤
          (C₁ * (q : ℝ).sqrt * q.divisors.card *
              ((j.val.gcd q : ℕ) : ℝ).sqrt * Real.log (2 * q)) *
            ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ := by
              gcongr
        _ = C₁ * (q : ℝ).sqrt * q.divisors.card * Real.log (2 * q) *
            (‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
              ((j.val.gcd q : ℕ) : ℝ).sqrt) := by ring
  rw [show |inverseResiduePrefix q r X| =
      ‖((inverseResiduePrefix q r X : ℝ) : ℂ)‖ by simp]
  rw [inverseResiduePrefix_fourier (r := r) (X := X) (by omega)]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ *
        ‖∑ j : ZMod q, inverseAdditivePrefix q r X j *
          ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ ≤
      (q : ℝ)⁻¹ * ∑ j : ZMod q,
        ‖inverseAdditivePrefix q r X j *
          ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ (q : ℝ)⁻¹ * ∑ j : ZMod q,
        C₁ * (q : ℝ).sqrt * q.divisors.card * Real.log (2 * q) *
          (if j = 0 then 0 else
            ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
              ((j.val.gcd q : ℕ) : ℝ).sqrt) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum fun j _hj => hterm j
          · positivity
    _ = (q : ℝ)⁻¹ *
        (C₁ * (q : ℝ).sqrt * q.divisors.card * Real.log (2 * q)) *
          (∑ j : ZMod q, if j = 0 then 0 else
            ‖ZMod.dft (centeredSawtooth : ZMod q → ℂ) j‖ *
              ((j.val.gcd q : ℕ) : ℝ).sqrt) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ (q : ℝ)⁻¹ *
        (C₁ * (q : ℝ).sqrt * q.divisors.card * Real.log (2 * q)) *
          (C₂ * (q : ℝ) * Real.log (2 * q) *
            reciprocalSqrtDivisorSum q) := by
        apply mul_le_mul_of_nonneg_left (hfrequency q hq)
        exact mul_nonneg (inv_nonneg.mpr hqR.le)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hC₁ (Real.sqrt_nonneg _)) (by positivity)) hlog)
    _ = (C₁ * C₂) * (q : ℝ).sqrt * q.divisors.card *
        reciprocalSqrtDivisorSum q * (Real.log (2 * q)) ^ 2 := by
      field_simp [hqR.ne']

end NField.Alignment.InverseResiduePrefixCompletion
