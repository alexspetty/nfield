/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExactSamplingReservoirBridge
import NField.Alignment.PrimeSecondaryCoefficient
import NField.Alignment.DedekindCarrierFourierBound
import NField.Alignment.ReciprocalDivisorMomentBound

/-!
# Prime carrier damping transfer

The exact Rademacher bridge is converted into a concrete estimate for the
actual sampling defect.  The elementary reciprocal reservoir is bounded
directly; the only input to the strict saving is therefore a bound for the
actual lower-modulus reservoir.
-/

namespace NField.Alignment.PrimeCarrierDamping

open scoped BigOperators
open NField.Alignment.ExactSamplingReservoirBridge
open NField.Alignment.PrimeSquareReducedRatio
open NField.Alignment.PrimeSecondaryCoefficient
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.DedekindCarrierFourierBound
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.ReciprocalDivisorMomentBound

/-- A uniform bound restricted to prime indices. -/
def PrimeUniformBound (f scale : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime → |f p| ≤ C * scale p

theorem elementaryRatioReservoir_nonneg (p : ℕ) :
    0 ≤ elementaryRatioReservoir p := by
  unfold elementaryRatioReservoir
  positivity

/-- A deliberately coarse polynomial bound sufficient to show that the
elementary term in the exact bridge is uniformly bounded after division by
`p^4`. -/
theorem elementaryRatioReservoir_le
    {p : ℕ} (hp : p.Prime) :
    elementaryRatioReservoir p ≤ 2 * (p : ℝ) ^ 4 := by
  have hpR : 0 ≤ (p : ℝ) := by positivity
  have hpoint : ∀ ak ∈ reducedRatioPairs p,
      (((p - 1) / ak.1 : ℕ) : ℝ) *
          ((ak.1 : ℝ) / (ak.2 : ℝ) + (ak.2 : ℝ) / (ak.1 : ℝ)) ≤
        2 * (p : ℝ) ^ 2 := by
    intro ak hak
    have h := hak
    simp [reducedRatioPairs] at h
    have ha0 : (0 : ℝ) < ak.1 := by exact_mod_cast h.2.1
    have hk0 : (0 : ℝ) < ak.2 := by exact_mod_cast h.2.2.1
    have haP : (ak.1 : ℝ) ≤ p := by exact_mod_cast (Nat.le_of_lt h.1.1)
    have hkA : (ak.2 : ℝ) ≤ ak.1 := by
      exact_mod_cast (Nat.le_of_lt h.2.2.2.1)
    have hMnat : (p - 1) / ak.1 ≤ p :=
      (Nat.div_le_self (p - 1) ak.1).trans (Nat.sub_le p 1)
    have hM : ((((p - 1) / ak.1 : ℕ) : ℝ)) ≤ p := by
      exact_mod_cast hMnat
    have hratio1 : (ak.1 : ℝ) / (ak.2 : ℝ) ≤ p := by
      apply (div_le_iff₀ hk0).2
      have hkOne : (1 : ℝ) ≤ ak.2 := by exact_mod_cast h.2.2.1
      calc
        (ak.1 : ℝ) ≤ p := haP
        _ = (p : ℝ) * 1 := by ring
        _ ≤ (p : ℝ) * ak.2 :=
          mul_le_mul_of_nonneg_left hkOne hpR
    have hratio2 : (ak.2 : ℝ) / (ak.1 : ℝ) ≤ 1 := by
      exact (div_le_one ha0).2 hkA
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hM0 : (0 : ℝ) ≤ (((p - 1) / ak.1 : ℕ) : ℝ) := by positivity
    have hratios0 : 0 ≤
        (ak.1 : ℝ) / (ak.2 : ℝ) + (ak.2 : ℝ) / (ak.1 : ℝ) := by
      positivity
    calc
      (((p - 1) / ak.1 : ℕ) : ℝ) *
          ((ak.1 : ℝ) / (ak.2 : ℝ) + (ak.2 : ℝ) / (ak.1 : ℝ)) ≤
        (p : ℝ) * ((p : ℝ) + 1) := by nlinarith
      _ ≤ 2 * (p : ℝ) ^ 2 := by nlinarith
  unfold elementaryRatioReservoir
  calc
    (∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℝ) *
          ((ak.1 : ℝ) / (ak.2 : ℝ) +
            (ak.2 : ℝ) / (ak.1 : ℝ))) ≤
      ∑ _ak ∈ reducedRatioPairs p, 2 * (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro ak hak
        exact hpoint ak hak
    _ = (reducedRatioPairs p).card * (2 * (p : ℝ) ^ 2) := by simp
    _ ≤ (p ^ 2 : ℕ) * (2 * (p : ℝ) ^ 2) := by
      gcongr
      unfold reducedRatioPairs
      exact (Finset.card_filter_le _ _).trans_eq (by simp [pow_two])
    _ = 2 * (p : ℝ) ^ 4 := by
      push_cast
      ring

/-- Exact bridge estimate with the lower-modulus reservoir left visible. -/
theorem samplingDefect_le_lowerReservoir
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |samplingDefect hp| ≤
      3 + |lowerModulusReservoir p| / (p : ℝ) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hX0 := elementaryRatioReservoir_nonneg p
  have hX := elementaryRatioReservoir_le hp
  have hformula := exact_sampling_reservoir_bridge hp hpodd
  rw [hformula]
  have hfirst :
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hpR)).2
    gcongr
    exact_mod_cast Nat.sub_le p 1
  have hcorrection :
      (2 / (3 * (p : ℝ) ^ 4) : ℝ) *
          (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p) ≤ 2 := by
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hpm : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    have hp2 : (p : ℝ) ≤ (p : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((p : ℝ) - 1)]
    have hp4 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((p : ℝ) ^ 2 - 1)]
    have hpTo4 : (p : ℝ) ≤ (p : ℝ) ^ 4 := hp2.trans hp4
    rw [show
      (2 / (3 * (p : ℝ) ^ 4) : ℝ) *
          (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p) =
        (2 * (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p)) /
          (3 * (p : ℝ) ^ 4) by ring]
    apply (div_le_iff₀ (show 0 < 3 * (p : ℝ) ^ 4 by positivity)).2
    nlinarith
  have hfirst0 : 0 ≤
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 := by positivity
  have hcorrection0 : 0 ≤
      (2 / (3 * (p : ℝ) ^ 4) : ℝ) *
        (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p) := by positivity
  let x := ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2
  let y := (2 / (3 * (p : ℝ) ^ 4) : ℝ) *
    (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p)
  let z := lowerModulusReservoir p / (p : ℝ) ^ 2
  change |x - y - z| ≤ 3 + |lowerModulusReservoir p| / (p : ℝ) ^ 2
  calc
    |x - y - z| ≤ |x - y| + |z| := abs_sub _ _
    _ ≤ (|x| + |y|) + |z| := by
      have hxy := add_le_add_right (abs_sub x y) |z|
      simpa [add_comm, add_left_comm, add_assoc] using hxy
    _ = ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        (2 / (3 * (p : ℝ) ^ 4) : ℝ) *
          (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p) +
        |lowerModulusReservoir p| / (p : ℝ) ^ 2 := by
      dsimp [x, y, z]
      rw [abs_of_nonneg hfirst0, abs_of_nonneg hcorrection0, abs_div,
        abs_of_pos (sq_pos_of_pos hpR)]
    _ ≤ 3 + |lowerModulusReservoir p| / (p : ℝ) ^ 2 := by
      linarith

/-- The corresponding normalized sampling scale. -/
noncomputable def strictCarrierSamplingScale (p : ℕ) : ℝ :=
  if 2 ≤ p then inverseResidueHarmonicScale p * (harmonic p : ℝ) else 0

/-- The exact harmonic form of the strict reservoir scale. -/
noncomputable def strictCarrierReservoirScale (p : ℕ) : ℝ :=
  (p : ℝ) ^ 2 * strictCarrierSamplingScale p

theorem strictCarrierSamplingScale_nonneg (p : ℕ) :
    0 ≤ strictCarrierSamplingScale p := by
  unfold strictCarrierSamplingScale
  split_ifs with hp
  · have hH : (0 : ℝ) ≤ (harmonic p : ℝ) := by
      exact_mod_cast (show (0 : ℚ) ≤ harmonic p by
        unfold harmonic
        positivity)
    exact mul_nonneg (inverseResidueHarmonicScale_nonneg hp) hH
  · exact le_rfl

theorem strictCarrierSamplingScale_nonneg_of_prime
    {p : ℕ} (_hp : p.Prime) : 0 ≤ strictCarrierSamplingScale p := by
  exact strictCarrierSamplingScale_nonneg p

/-- The literal logarithmic scale printed in the all-prime theorem. -/
noncomputable def logarithmicCarrierSamplingScale (p : ℕ) : ℝ :=
  if 2 ≤ p then
    Real.log (2 * p) ^ 2 / Real.log (Real.log (3 * p))
  else 0

noncomputable def logarithmicCarrierReservoirScale (p : ℕ) : ℝ :=
  (p : ℝ) ^ 2 * logarithmicCarrierSamplingScale p

theorem logarithmicCarrierSamplingScale_nonneg (p : ℕ) :
    0 ≤ logarithmicCarrierSamplingScale p := by
  unfold logarithmicCarrierSamplingScale
  split_ifs with hp
  · have hden : 0 < Real.log (Real.log (3 * p)) := by
      have hthree : (1 : ℝ) < Real.log (3 * p) := by
        have harg : Real.exp 1 < 3 * (p : ℝ) := by
          calc
            Real.exp 1 < 3 := Real.exp_one_lt_three
            _ ≤ 3 * (p : ℝ) := by
              exact_mod_cast (show 3 ≤ 3 * p by omega)
        exact (Real.lt_log_iff_exp_lt (by positivity)).2 harg
      exact Real.log_pos hthree
    exact div_nonneg (sq_nonneg _) hden.le
  · exact le_rfl

theorem strictCarrierSamplingScale_le_logarithmic (p : ℕ) :
    strictCarrierSamplingScale p ≤
      2 * logarithmicCarrierSamplingScale p := by
  by_cases hp : 2 ≤ p
  · rw [strictCarrierSamplingScale, if_pos hp,
      logarithmicCarrierSamplingScale, if_pos hp]
    have hden : 0 < Real.log (Real.log (3 * p)) := by
      have hthree : (1 : ℝ) < Real.log (3 * p) := by
        have harg : Real.exp 1 < 3 * (p : ℝ) := by
          calc
            Real.exp 1 < 3 := Real.exp_one_lt_three
            _ ≤ 3 * (p : ℝ) := by
              exact_mod_cast (show 3 ≤ 3 * p by omega)
        exact (Real.lt_log_iff_exp_lt (by positivity)).2 harg
      exact Real.log_pos hthree
    have hlogOne : (1 : ℝ) ≤ Real.log (2 * p) := by
      apply (Real.le_log_iff_exp_le (by positivity)).2
      calc
        Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
        _ ≤ 2 * (p : ℝ) := by exact_mod_cast (show 3 ≤ 2 * p by omega)
    have hlogMono : Real.log (p : ℝ) ≤ Real.log (2 * p) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < p by omega)
      · exact_mod_cast (show p ≤ 2 * p by omega)
    have hH := harmonic_le_one_add_log p
    have hHReal : (harmonic p : ℝ) ≤ 1 + Real.log p := by
      exact_mod_cast hH
    have hHbound : (harmonic p : ℝ) ≤ 2 * Real.log (2 * p) := by
      linarith
    have hscale : 0 ≤ inverseResidueHarmonicScale p :=
      inverseResidueHarmonicScale_nonneg hp
    calc
      inverseResidueHarmonicScale p * (harmonic p : ℝ) ≤
          inverseResidueHarmonicScale p * (2 * Real.log (2 * p)) :=
        mul_le_mul_of_nonneg_left hHbound hscale
      _ = 2 * (Real.log (2 * p) ^ 2 /
          Real.log (Real.log (3 * p))) := by
        unfold inverseResidueHarmonicScale
        field_simp [hden.ne']
  · rw [strictCarrierSamplingScale, if_neg hp,
      logarithmicCarrierSamplingScale, if_neg hp]
    norm_num

theorem strictCarrierReservoirScale_le_logarithmic (p : ℕ) :
    strictCarrierReservoirScale p ≤
      2 * logarithmicCarrierReservoirScale p := by
  unfold strictCarrierReservoirScale logarithmicCarrierReservoirScale
  have hp2 : (0 : ℝ) ≤ (p : ℝ) ^ 2 := sq_nonneg _
  calc
    (p : ℝ) ^ 2 * strictCarrierSamplingScale p ≤
        (p : ℝ) ^ 2 * (2 * logarithmicCarrierSamplingScale p) :=
      mul_le_mul_of_nonneg_left
        (strictCarrierSamplingScale_le_logarithmic p) hp2
    _ = 2 * ((p : ℝ) ^ 2 * logarithmicCarrierSamplingScale p) := by ring

set_option maxHeartbeats 800000 in
/-- One actual prime carrier inherits the additive-transform saving, including
the exact floor weight and all divisor costs. -/
theorem norm_modulusKSlice_le_of_ambient_inverse_estimate
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    {C : ℝ} (hC : 0 ≤ C)
    (hKorolev : ∀ K q r, 2 ≤ q → q ≤ K → r.Coprime q →
      ‖inverseSawSeries q r‖ ≤ C * inverseResidueHarmonicScale K) :
    ‖modulusKSlice p k‖ ≤
      2 * C * (p : ℝ) * inverseResidueHarmonicScale p *
        (harmonic p : ℝ) * reciprocalDivisorSum k ^ 3 := by
  have hPk : (p ^ 2).Coprime k :=
    (smallNatUnit_coprime hp (by omega : 0 < k) hkp).symm
  letI : NeZero k := ⟨by omega⟩
  let β : (ZMod k)ˣ := ZMod.unitOfCoprime (p ^ 2) hPk
  have hscale : 0 ≤ inverseResidueHarmonicScale p :=
    inverseResidueHarmonicScale_nonneg hp.two_le
  have hsigma : 0 ≤ reciprocalDivisorSum k ^ 3 :=
    pow_nonneg (reciprocalDivisorSum_nonneg k) 3
  let U := C * inverseResidueHarmonicScale p * reciprocalDivisorSum k ^ 3
  have hU : 0 ≤ U := by
    dsimp [U]
    exact mul_nonneg (mul_nonneg hC hscale) hsigma
  have htransform : ∀ t,
      ‖unitDedekindTransform k t‖ / (k : ℝ) ≤ U := by
    intro t
    exact norm_unitDedekindTransform_div_le_of_ambient_unit_bound
      (A := p) hk (Nat.le_of_lt hkp) inverseResidueHarmonicScale
        hC hscale (fun Q u hQ hQp hu => hKorolev p Q u hQ hQp hu)
  have habel :=
    norm_floorWeighted_residueDedekindSequence_le_of_transform
      hk hkp β hU htransform
  have hfloorNat : ((p - 1) / (k + 1)) * k ≤ p := by
    calc
      ((p - 1) / (k + 1)) * k ≤
          ((p - 1) / (k + 1)) * (k + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ k)
      _ ≤ p - 1 := Nat.div_mul_le_self _ _
      _ ≤ p := Nat.sub_le _ _
  have hfloor :
      ((((p - 1) / (k + 1) : ℕ) : ℝ) * (k : ℝ)) ≤ (p : ℝ) := by
    exact_mod_cast hfloorNat
  have hHmono := NField.Alignment.DedekindFourierMoment.harmonic_cast_mono
    (Nat.le_of_lt hkp)
  have hHk : (0 : ℝ) ≤ (harmonic k : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic k by
      unfold harmonic
      positivity)
  rw [modulusKSlice, dif_neg (by omega : k ≠ 0), dif_pos ⟨hk, hPk⟩]
  calc
    ‖∑ a ∈ Finset.Ico (k + 1) p,
        (((p - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      2 * (((p - 1) / (k + 1) : ℕ) : ℝ) *
        ((k : ℝ) * U * (harmonic k : ℝ)) := habel
    _ = 2 * ((((p - 1) / (k + 1) : ℕ) : ℝ) * (k : ℝ)) *
        U * (harmonic k : ℝ) := by ring
    _ ≤ 2 * (p : ℝ) * U * (harmonic p : ℝ) := by
      gcongr
    _ = 2 * C * (p : ℝ) * inverseResidueHarmonicScale p *
        (harmonic p : ℝ) * reciprocalDivisorSum k ^ 3 := by
      dsimp [U]
      ring

/-- The paper's full lower-modulus reservoir bound is assembled from the
source-level inverse-fraction estimate and the proved reciprocal-divisor
moment. -/
theorem lowerModulusReservoir_strict_bound
    (hKorolev : KorolevAmbientInverseResidueEstimate) :
    PrimeUniformBound lowerModulusReservoir strictCarrierReservoirScale := by
  rcases hKorolev with ⟨C, hC, hKorolev⟩
  rcases bounded_reciprocal_divisor_moments 3 (by omega) with
    ⟨M, hM, hmoment⟩
  refine ⟨16 * C * M, by positivity, ?_⟩
  intro p hp
  have hpR : (0 : ℝ) ≤ p := by positivity
  have hscale : 0 ≤ inverseResidueHarmonicScale p :=
    inverseResidueHarmonicScale_nonneg hp.two_le
  have hH : (0 : ℝ) ≤ (harmonic p : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic p by
      unfold harmonic
      positivity)
  have hpoint : ∀ k ∈ Finset.range p,
      ‖modulusKSlice p k‖ ≤
        2 * C * (p : ℝ) * inverseResidueHarmonicScale p *
          (harmonic p : ℝ) * reciprocalDivisorSum k ^ 3 := by
    intro k hkp
    have hRhs0 : 0 ≤
        2 * C * (p : ℝ) * inverseResidueHarmonicScale p *
          (harmonic p : ℝ) * reciprocalDivisorSum k ^ 3 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hC) hpR) hscale) hH)
        (pow_nonneg (reciprocalDivisorSum_nonneg k) 3)
    by_cases hk : 2 ≤ k
    · exact norm_modulusKSlice_le_of_ambient_inverse_estimate
        hp hk (Finset.mem_range.mp hkp) hC hKorolev
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simpa [modulusKSlice] using hRhs0
      · simpa [modulusKSlice] using hRhs0
  have hsumMoment :
      (∑ k ∈ Finset.range p, reciprocalDivisorSum k ^ 3) ≤ M * p := by
    rw [NField.Alignment.DedekindReciprocity.sum_range_eq_sum_Ico_one
      (fun k => reciprocalDivisorSum k ^ 3) hp.pos]
    · exact (Finset.sum_le_sum_of_subset_of_nonneg
        (show Finset.Ico 1 p ⊆ Finset.Icc 1 p by
          intro k hk
          simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
          omega)
        (fun k _hkBig _hkSmall =>
          pow_nonneg (reciprocalDivisorSum_nonneg k) 3)).trans (hmoment p)
    · simp [reciprocalDivisorSum]
  have hslices := offDiagonalModulusK_eq_slices hp
  have hoff : ‖offDiagonalModulusK p‖ ≤
      16 * C * M * strictCarrierReservoirScale p := by
    rw [hslices, norm_mul]
    norm_num
    calc
      8 * ‖∑ k ∈ Finset.range p, modulusKSlice p k‖ ≤
        8 * ∑ k ∈ Finset.range p, ‖modulusKSlice p k‖ := by
          gcongr
          exact norm_sum_le _ _
      _ ≤ 8 * ∑ k ∈ Finset.range p,
          (2 * C * (p : ℝ) * inverseResidueHarmonicScale p *
            (harmonic p : ℝ) * reciprocalDivisorSum k ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum fun k hk => hpoint k hk
      _ = 16 * C * (p : ℝ) * inverseResidueHarmonicScale p *
          (harmonic p : ℝ) *
            (∑ k ∈ Finset.range p, reciprocalDivisorSum k ^ 3) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ 16 * C * (p : ℝ) * inverseResidueHarmonicScale p *
          (harmonic p : ℝ) * (M * p) := by
          gcongr
      _ = 16 * C * M * strictCarrierReservoirScale p := by
          simp [strictCarrierReservoirScale, strictCarrierSamplingScale,
            hp.two_le]
          ring
  unfold lowerModulusReservoir
  calc
    |(offDiagonalModulusK p).re| ≤ ‖offDiagonalModulusK p‖ :=
      Complex.abs_re_le_norm _
    _ ≤ 16 * C * M * strictCarrierReservoirScale p := hoff

/-- The all-prime sampling estimate derived from an actual lower-reservoir
estimate and the exact bridge. -/
theorem all_prime_carrier_damping
    (reservoirScale samplingScale : ℕ → ℝ)
    (hreservoir : PrimeUniformBound lowerModulusReservoir reservoirScale)
    (hscale : ∀ p, 0 ≤ samplingScale p)
    (hscaleLink : ∀ p, reservoirScale p ≤
      (p : ℝ) ^ 2 * samplingScale p) :
    PrimeUniformBound lowerModulusReservoir reservoirScale ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime → p ≠ 2 →
        |primeSamplingDefect p| ≤ C * (1 + samplingScale p) := by
  refine ⟨hreservoir, ?_⟩
  rcases hreservoir with ⟨C, hC, hR⟩
  refine ⟨max 3 C, le_max_of_le_left (by norm_num), ?_⟩
  intro p hp hpodd
  rw [primeSamplingDefect, dif_pos hp]
  have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpR : 0 < (p : ℝ) ^ 2 := sq_pos_of_ne_zero hpR0
  calc
    |samplingDefect hp| ≤
        3 + |lowerModulusReservoir p| / (p : ℝ) ^ 2 :=
      samplingDefect_le_lowerReservoir hp hpodd
    _ ≤ 3 + C * samplingScale p := by
      have hbound := hR p hp
      have hlink := hscaleLink p
      have hCmul : C * reservoirScale p ≤
          C * ((p : ℝ) ^ 2 * samplingScale p) := by gcongr
      have hdiv : |lowerModulusReservoir p| / (p : ℝ) ^ 2 ≤
          C * samplingScale p := by
        apply (div_le_iff₀ hpR).2
        calc
          |lowerModulusReservoir p| ≤ C * reservoirScale p := hbound
          _ ≤ C * ((p : ℝ) ^ 2 * samplingScale p) := hCmul
          _ = C * samplingScale p * (p : ℝ) ^ 2 := by ring
      linarith
    _ ≤ max 3 C * (1 + samplingScale p) := by
      have hs := hscale p
      have h3 : (3 : ℝ) ≤ max 3 C := le_max_left _ _
      have hCm : C ≤ max 3 C := le_max_right _ _
      nlinarith

/-- The literal all-prime damping theorem, with every internal Fourier, Abel,
divisor-average, and reservoir-transfer step discharged. -/
theorem all_prime_carrier_damping_from_analytic_inputs
    (hKorolev : KorolevAmbientInverseResidueEstimate) :
    PrimeUniformBound lowerModulusReservoir logarithmicCarrierReservoirScale ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime → p ≠ 2 →
        |primeSamplingDefect p| ≤
          C * (1 + logarithmicCarrierSamplingScale p) := by
  have hstrict := lowerModulusReservoir_strict_bound hKorolev
  have hlogReservoir :
      PrimeUniformBound lowerModulusReservoir logarithmicCarrierReservoirScale := by
    rcases hstrict with ⟨C, hC, hbound⟩
    refine ⟨2 * C, by positivity, ?_⟩
    intro p hp
    calc
      |lowerModulusReservoir p| ≤ C * strictCarrierReservoirScale p :=
        hbound p hp
      _ ≤ C * (2 * logarithmicCarrierReservoirScale p) := by
        exact mul_le_mul_of_nonneg_left
          (strictCarrierReservoirScale_le_logarithmic p) hC
      _ = (2 * C) * logarithmicCarrierReservoirScale p := by ring
  have hstrictConclusion := all_prime_carrier_damping
    strictCarrierReservoirScale strictCarrierSamplingScale hstrict
    strictCarrierSamplingScale_nonneg
    (fun p => by unfold strictCarrierReservoirScale; exact le_rfl)
  rcases hstrictConclusion.2 with ⟨C, hC, hbound⟩
  refine ⟨hlogReservoir, 2 * C, by positivity, ?_⟩
  intro p hp hpodd
  have hlog0 := logarithmicCarrierSamplingScale_nonneg p
  have hcomp := strictCarrierSamplingScale_le_logarithmic p
  calc
    |primeSamplingDefect p| ≤ C * (1 + strictCarrierSamplingScale p) :=
      hbound p hp hpodd
    _ ≤ C * (1 + 2 * logarithmicCarrierSamplingScale p) := by
      gcongr
    _ ≤ (2 * C) * (1 + logarithmicCarrierSamplingScale p) := by
      nlinarith

/-- The strict sampling estimate in the exact all-prime form consumed by the
finite secondary-coefficient transfer.  The analytic carrier theorem is
stated for odd primes; the single prime `2` is absorbed into the uniform
constant rather than hidden in an eventual qualifier. -/
theorem primeSamplingDefect_strict_bound_from_analytic_inputs
    (hKorolev : KorolevAmbientInverseResidueEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime →
      |primeSamplingDefect p| ≤ C * primeStrictSamplingScale p := by
  rcases (all_prime_carrier_damping_from_analytic_inputs hKorolev).2 with
    ⟨C, hC, hbound⟩
  let C' : ℝ := max C |primeSamplingDefect 2|
  refine ⟨C', le_max_of_le_left hC, ?_⟩
  intro p hp
  have hlog0 : 0 ≤ logarithmicCarrierSamplingScale p :=
    logarithmicCarrierSamplingScale_nonneg p
  have hscale : primeStrictSamplingScale p =
      1 + logarithmicCarrierSamplingScale p := by
    simp [primeStrictSamplingScale, logarithmicCarrierSamplingScale,
      hp.two_le]
  rw [hscale]
  by_cases hpTwo : p = 2
  · subst p
    have hC' : 0 ≤ C' := le_max_of_le_left hC
    have hvalue : |primeSamplingDefect 2| ≤ C' := le_max_right _ _
    have hscaleOne : (1 : ℝ) ≤
        1 + logarithmicCarrierSamplingScale 2 := by
      have := logarithmicCarrierSamplingScale_nonneg 2
      linarith
    nlinarith
  · have hC_le : C ≤ C' := le_max_left _ _
    have hscale0 : 0 ≤ 1 + logarithmicCarrierSamplingScale p := by
      linarith
    exact (hbound p hp hpTwo).trans
      (mul_le_mul_of_nonneg_right hC_le hscale0)

end NField.Alignment.PrimeCarrierDamping
