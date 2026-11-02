/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralRepulsion
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Finite magnitude decorrelation

Probability inequalities for uniform finite magnitude samples. The short-sum
asymptotic estimate is not an axiom in this module. It will be an explicit
input to the limiting deduction.
-/

namespace NField.Alignment.FiniteMagnitudeDecorrelation

open scoped BigOperators Topology
open Filter
open NField.Alignment.SpectralRepulsion

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def magnitudeMoment (p : ℝ) (X : ι → ℝ) : ℝ :=
  uniformAverage (fun i => (X i) ^ p)

noncomputable def magnitudeCovariance (X Y : ι → ℝ) : ℝ :=
  uniformAverage (fun i => X i * Y i) - uniformAverage X * uniformAverage Y

noncomputable def magnitudeCorrelation (X Y : ι → ℝ) : ℝ :=
  magnitudeCovariance X Y / Real.sqrt (uniformVariance X * uniformVariance Y)

omit [Nonempty ι] in
theorem average_nonneg {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ uniformAverage f := by
  unfold uniformAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => hf i)

omit [Nonempty ι] in
theorem average_mono {f g : ι → ℝ} (hfg : ∀ i, f i ≤ g i) :
    uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hfg i)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem average_const (c : ℝ) :
    uniformAverage (fun _ : ι => c) = c := by
  have h := uniformAverage_mul_left c (fun _ : ι => (1 : ℝ))
  simpa [uniformAverage_one] using h

omit [Nonempty ι] in
theorem average_sub (f g : ι → ℝ) :
    uniformAverage (fun i => f i - g i) =
      uniformAverage f - uniformAverage g := by
  unfold uniformAverage
  rw [Finset.sum_sub_distrib]
  ring

omit [Nonempty ι] in
theorem average_cauchy_sq (f g : ι → ℝ) :
    uniformAverage (fun i => f i * g i) ^ 2 ≤
      uniformAverage (fun i => f i ^ 2) *
        uniformAverage (fun i => g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hs := mul_le_mul_of_nonneg_left h
    (sq_nonneg ((Fintype.card ι : ℝ)⁻¹))
  unfold uniformAverage
  convert hs using 1 <;> first | rfl | ring

theorem average_sq_le (f : ι → ℝ) :
    uniformAverage f ^ 2 ≤ uniformAverage (fun i => f i ^ 2) := by
  simpa [average_const] using average_cauchy_sq f (fun _ => 1)

theorem variance_eq_second_sub_square (f : ι → ℝ) :
    uniformVariance f =
      uniformAverage (fun i => f i ^ 2) - uniformAverage f ^ 2 := by
  unfold uniformVariance
  have heq : (fun i => (f i - uniformAverage f) ^ 2) =
      (fun i => f i ^ 2 - (2 * uniformAverage f) * f i +
        uniformAverage f ^ 2) := by funext i; ring
  rw [heq, uniformAverage_add, average_sub,
    uniformAverage_mul_left, average_const]
  ring

omit [Nonempty ι] in
theorem variance_nonneg (f : ι → ℝ) : 0 ≤ uniformVariance f :=
  average_nonneg (fun _ => sq_nonneg _)

theorem correlation_from_first_moments (X Y : ι → ℝ)
    (hX : uniformAverage (fun i => X i ^ 2) = 1)
    (ν : ℝ) (hY : uniformAverage (fun i => Y i ^ 2) = ν) :
    magnitudeCorrelation X Y =
      (uniformAverage (fun i => X i * Y i) -
        uniformAverage X * uniformAverage Y) /
      Real.sqrt ((1 - uniformAverage X ^ 2) *
        (ν - uniformAverage Y ^ 2)) := by
  simp only [magnitudeCorrelation, magnitudeCovariance,
    variance_eq_second_sub_square, hX, hY]

theorem twist_forces_variance (Y Z : ι → ℝ) (ν : ℝ) (hν : 0 < ν)
    (hsecond : uniformAverage (fun i => Y i ^ 2) = ν)
    (hzero : uniformAverage Z = 0)
    (hbound : ∀ i, |Z i| ≤ 1)
    (htwist : uniformAverage (fun i => Y i ^ 2 * Z i) = ν / 2) :
    ν / 16 ≤ uniformVariance Y := by
  let c := uniformAverage Y
  have hc : c ^ 2 ≤ ν := by simpa [c, hsecond] using average_sq_le Y
  have hfactor : uniformAverage (fun i => (Y i - c) * ((Y i + c) * Z i)) =
      ν / 2 := by
    have heq : (fun i => (Y i - c) * ((Y i + c) * Z i)) =
        (fun i => Y i ^ 2 * Z i - c ^ 2 * Z i) := by funext i; ring
    rw [heq, average_sub, uniformAverage_mul_left, htwist, hzero]
    ring
  have hplus : uniformAverage (fun i => (Y i + c) ^ 2) = ν + 3 * c ^ 2 := by
    have heq : (fun i => (Y i + c) ^ 2) =
        (fun i => Y i ^ 2 + (2 * c) * Y i + c ^ 2) := by funext i; ring
    rw [heq, uniformAverage_add, uniformAverage_add,
      uniformAverage_mul_left, average_const, hsecond]
    dsimp [c]
    ring
  have hboundSq : uniformAverage (fun i => ((Y i + c) * Z i) ^ 2) ≤
      ν + 3 * c ^ 2 := by
    rw [← hplus]
    apply average_mono
    intro i
    have hz : Z i ^ 2 ≤ 1 := by
      have hz' := hbound i
      rw [abs_le] at hz'
      nlinarith [sq_nonneg (Z i - 1), sq_nonneg (Z i + 1)]
    simpa [mul_pow] using mul_le_mul_of_nonneg_left hz (sq_nonneg (Y i + c))
  have hCS := average_cauchy_sq (fun i => Y i - c) (fun i => (Y i + c) * Z i)
  rw [hfactor] at hCS
  have hv : 0 ≤ uniformVariance Y := variance_nonneg Y
  have hCS' : (ν / 2) ^ 2 ≤ uniformVariance Y * (4 * ν) :=
    hCS.trans ((mul_le_mul_of_nonneg_left hboundSq hv).trans
      (mul_le_mul_of_nonneg_left (by nlinarith : ν + 3 * c ^ 2 ≤ 4 * ν) hv))
  by_contra h
  have hlt : 0 < ν / 16 - uniformVariance Y := by linarith
  nlinarith [mul_pos hν hlt]

omit [Nonempty ι] in
theorem moment_nonneg (p : ℝ) (X : ι → ℝ) (hX : ∀ i, 0 ≤ X i) :
    0 ≤ magnitudeMoment p X :=
  average_nonneg (fun i => Real.rpow_nonneg (hX i) p)

theorem average_holder_three_halves (X Y : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) :
    uniformAverage (fun i => X i * Y i) ≤
      magnitudeMoment (3/2) X ^ (2/3 : ℝ) *
        magnitudeMoment 3 Y ^ (1/3 : ℝ) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hN (f : ι → ℝ) :
      ∑ i, f i = (Fintype.card ι : ℝ) * uniformAverage f := by
    unfold uniformAverage
    field_simp
  have hpq : (3/2 : ℝ).HolderConjugate 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) hpq (fun i _ => hX i) (fun i _ => hY i)
  simp only [show (1 / (3/2) : ℝ) = 2/3 by norm_num] at h
  rw [hN (fun i => X i * Y i), hN (fun i => (X i) ^ (3/2 : ℝ)),
    hN (fun i => (Y i) ^ (3 : ℝ))] at h
  change (Fintype.card ι : ℝ) * uniformAverage (fun i => X i * Y i) ≤
    ((Fintype.card ι : ℝ) * magnitudeMoment (3/2) X) ^ (2/3 : ℝ) *
    ((Fintype.card ι : ℝ) * magnitudeMoment 3 Y) ^ (1/3 : ℝ) at h
  rw [Real.mul_rpow hn.le (moment_nonneg (3/2) X hX),
    Real.mul_rpow hn.le (moment_nonneg 3 Y hY)] at h
  have hpow : (Fintype.card ι : ℝ) ^ (2/3 : ℝ) *
      (Fintype.card ι : ℝ) ^ (1/3 : ℝ) = (Fintype.card ι : ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    _ ≤ _ := h
    _ = _ := by
      unfold magnitudeMoment
      rw [show (Fintype.card ι : ℝ) ^ (2/3 : ℝ) *
          uniformAverage (fun i => X i ^ (3/2 : ℝ)) ^ (2/3 : ℝ) *
          ((Fintype.card ι : ℝ) ^ (1/3 : ℝ) *
          uniformAverage (fun i => Y i ^ (3 : ℝ)) ^ (1/3 : ℝ)) =
          ((Fintype.card ι : ℝ) ^ (2/3 : ℝ) *
          (Fintype.card ι : ℝ) ^ (1/3 : ℝ)) *
          (uniformAverage (fun i => X i ^ (3/2 : ℝ)) ^ (2/3 : ℝ) *
          uniformAverage (fun i => Y i ^ (3 : ℝ)) ^ (1/3 : ℝ)) by ring]
      rw [hpow]

theorem mean_le_fractional_moment (X : ι → ℝ) (hX : ∀ i, 0 ≤ X i) :
    uniformAverage X ≤ magnitudeMoment (3/2) X ^ (2/3 : ℝ) := by
  simpa [magnitudeMoment, average_const] using
    average_holder_three_halves X (fun _ => 1) hX (fun _ => by norm_num)

theorem covariance_bound (X Y : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (ν M : ℝ) (hsecond : uniformAverage (fun i => Y i ^ 2) = ν)
    (hthird : magnitudeMoment 3 Y ≤ M) :
    |magnitudeCovariance X Y| ≤
      (M ^ (1/3 : ℝ) + Real.sqrt ν) *
        magnitudeMoment (3/2) X ^ (2/3 : ℝ) := by
  have ha := mean_le_fractional_moment X hX
  have hc : uniformAverage Y ≤ Real.sqrt ν :=
    Real.le_sqrt_of_sq_le (hsecond ▸ average_sq_le Y)
  have hH := Real.rpow_nonneg (moment_nonneg (3/2) X hX) (2/3 : ℝ)
  have hd := (average_holder_three_halves X Y hX hY).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (moment_nonneg 3 Y hY) hthird (by norm_num)) hH)
  have hac := mul_le_mul ha hc (average_nonneg hY) hH
  have ha0 := average_nonneg hX
  have hc0 := average_nonneg hY
  have hd0 := average_nonneg (fun i => mul_nonneg (hX i) (hY i))
  unfold magnitudeCovariance
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg ha0 hc0]

theorem fractional_power_square {H : ℝ} (hH : 0 ≤ H) :
    (H ^ (2/3 : ℝ)) ^ 2 = H ^ (4/3 : ℝ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hH]
  norm_num

theorem variance_lower_from_fractional (X : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i)
    (hsecond : uniformAverage (fun i => X i ^ 2) = 1) :
    1 - magnitudeMoment (3/2) X ^ (4/3 : ℝ) ≤ uniformVariance X := by
  have ha := mean_le_fractional_moment X hX
  have ha0 := average_nonneg hX
  have hh0 := Real.rpow_nonneg (moment_nonneg (3/2) X hX) (2/3 : ℝ)
  have hs : uniformAverage X ^ 2 ≤ (magnitudeMoment (3/2) X ^ (2/3 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ ha0 ha 2
  rw [fractional_power_square (moment_nonneg (3/2) X hX)] at hs
  rw [variance_eq_second_sub_square, hsecond]
  linarith

theorem fractional_correlation_bound (X Y : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (ν M v : ℝ) (hv : 0 < v)
    (hXsecond : uniformAverage (fun i => X i ^ 2) = 1)
    (hYsecond : uniformAverage (fun i => Y i ^ 2) = ν)
    (hthird : magnitudeMoment 3 Y ≤ M)
    (hvariance : v ≤ uniformVariance Y)
    (hsmall : magnitudeMoment (3/2) X < 1) :
    |magnitudeCorrelation X Y| ≤
      ((M ^ (1/3 : ℝ) + Real.sqrt ν) *
        magnitudeMoment (3/2) X ^ (2/3 : ℝ)) /
      Real.sqrt (v * (1 - magnitudeMoment (3/2) X ^ (4/3 : ℝ))) := by
  let H := magnitudeMoment (3/2) X
  have hH : 0 ≤ H := moment_nonneg (3/2) X hX
  have hgap : 0 < 1 - H ^ (4/3 : ℝ) := by
    exact sub_pos.mpr (Real.rpow_lt_one hH hsmall (by norm_num))
  have hVX := variance_lower_from_fractional X hX hXsecond
  have hden : Real.sqrt (v * (1 - H ^ (4/3 : ℝ))) ≤
      Real.sqrt (uniformVariance X * uniformVariance Y) := by
    apply Real.sqrt_le_sqrt
    calc
      v * (1 - H ^ (4/3 : ℝ)) ≤ uniformVariance Y * uniformVariance X :=
        mul_le_mul hvariance hVX hgap.le (variance_nonneg Y)
      _ = _ := mul_comm _ _
  have hdenpos : 0 < Real.sqrt (v * (1 - H ^ (4/3 : ℝ))) :=
    Real.sqrt_pos.mpr (mul_pos hv hgap)
  have hnum := covariance_bound X Y hX hY ν M hYsecond hthird
  have hM : 0 ≤ M := (moment_nonneg 3 Y hY).trans hthird
  have hupper : 0 ≤ (M ^ (1/3 : ℝ) + Real.sqrt ν) * H ^ (2/3 : ℝ) :=
    mul_nonneg (add_nonneg (Real.rpow_nonneg hM _) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hH _)
  unfold magnitudeCorrelation
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right hnum (hdenpos.le.trans hden)).trans
    (div_le_div_of_nonneg_left hupper hdenpos hden)

/-- A checked limit deduction from the explicit fractional-moment bound.
No character-sum asymptotic is asserted by this general theorem. -/
theorem correlation_tendsto_zero_of_bound
    {α : Type*} {l : Filter α} (H r : α → ℝ) (C v : ℝ) (hv : 0 < v)
    (hH : Tendsto H l (𝓝 0))
    (hbound : ∀ᶠ a in l, |r a| ≤
      C * (H a) ^ (2/3 : ℝ) /
        Real.sqrt (v * (1 - (H a) ^ (4/3 : ℝ)))) :
    Tendsto r l (𝓝 0) := by
  have htwo := hH.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 2/3)
  have hfour := hH.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 4/3)
  have hden : Tendsto
      (fun a => Real.sqrt (v * (1 - (H a) ^ (4/3 : ℝ)))) l
      (𝓝 (Real.sqrt v)) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub hfour)).sqrt using 1
    norm_num
  have hratio : Tendsto (fun a =>
      C * (H a) ^ (2/3 : ℝ) /
        Real.sqrt (v * (1 - (H a) ^ (4/3 : ℝ)))) l (𝓝 0) := by
    convert
      ((tendsto_const_nhds : Tendsto (fun _ : α => C) l (𝓝 C)).mul htwo).div hden
        (ne_of_gt (Real.sqrt_pos.mpr hv)) using 1 <;>
      first | rfl | norm_num
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbound) hratio

noncomputable def tailFraction (X : ι → ℝ) (ε : ℝ) : ℝ :=
  uniformAverage (fun i => if ε < X i then 1 else 0)

noncomputable def lowerSquareMass (X : ι → ℝ) (ε : ℝ) : ℝ :=
  uniformAverage (fun i => if X i ≤ ε then X i ^ 2 else 0)

noncomputable def upperSquareMass (X : ι → ℝ) (ε : ℝ) : ℝ :=
  uniformAverage (fun i => if ε < X i then X i ^ 2 else 0)

omit [Nonempty ι] in
theorem tail_fraction_nonneg (X : ι → ℝ) (ε : ℝ) :
    0 ≤ tailFraction X ε := by
  apply average_nonneg
  intro i
  split_ifs <;> norm_num

omit [Nonempty ι] in
theorem tail_fraction_bound (X : ι → ℝ) (hX : ∀ i, 0 ≤ X i)
    (ε : ℝ) (hε : 0 < ε) :
    tailFraction X ε ≤ magnitudeMoment (3/2) X / ε ^ (3/2 : ℝ) := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hε _)).mpr
  unfold tailFraction magnitudeMoment
  rw [mul_comm, ← uniformAverage_mul_left]
  apply average_mono
  intro i
  by_cases hi : ε < X i
  · simp only [if_pos hi, mul_one]
    exact Real.rpow_le_rpow hε.le hi.le (by norm_num)
  · simp only [if_neg hi, mul_zero]
    exact Real.rpow_nonneg (hX i) _

omit [Nonempty ι] in
theorem lower_square_mass_nonneg (X : ι → ℝ) (ε : ℝ) :
    0 ≤ lowerSquareMass X ε := by
  apply average_nonneg
  intro i
  split_ifs <;> positivity

omit [Nonempty ι] in
theorem lower_square_mass_bound (X : ι → ℝ) (hX : ∀ i, 0 ≤ X i)
    (ε : ℝ) (hε : 0 < ε) :
    lowerSquareMass X ε ≤ ε ^ (1/2 : ℝ) * magnitudeMoment (3/2) X := by
  unfold lowerSquareMass magnitudeMoment
  rw [← uniformAverage_mul_left]
  apply average_mono
  intro i
  by_cases hi : X i ≤ ε
  · rw [if_pos hi]
    by_cases hz : X i = 0
    · simp [hz]
    have hp : 0 < X i := lt_of_le_of_ne (hX i) (Ne.symm hz)
    calc
      X i ^ 2 = X i ^ (1/2 : ℝ) * X i ^ (3/2 : ℝ) := by
        rw [← Real.rpow_add hp]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hX i) hi (by norm_num))
        (Real.rpow_nonneg (hX i) _)
  · rw [if_neg hi]
    exact mul_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg (hX i) _)

omit [Nonempty ι] in
theorem square_mass_split (X : ι → ℝ) (ε : ℝ) :
    upperSquareMass X ε + lowerSquareMass X ε =
      uniformAverage (fun i => X i ^ 2) := by
  unfold upperSquareMass lowerSquareMass
  rw [← uniformAverage_add]
  congr 1
  funext i
  by_cases hi : ε < X i
  · simp [hi, not_le.mpr hi]
  · simp [hi, le_of_not_gt hi]

section VaryingFamily

variable {α : Type*} {κ : α → Type*}
  [∀ a, Fintype (κ a)] [∀ a, Nonempty (κ a)] {l : Filter α}

/-- The full correlation deduction for a varying finite family. The
fractional-moment limit and uniform L-magnitude bounds are explicit inputs,
not new axioms or conclusions assumed as hypotheses. -/
theorem correlation_limit_from_moments
    (X Y : (a : α) → κ a → ℝ)
    (hX : ∀ a i, 0 ≤ X a i) (hY : ∀ a i, 0 ≤ Y a i)
    (V M v : ℝ) (hv : 0 < v)
    (hXsecond : ∀ a, uniformAverage (fun i => X a i ^ 2) = 1)
    (hYsecond : ∀ a, uniformAverage (fun i => Y a i ^ 2) ≤ V)
    (hthird : ∀ a, magnitudeMoment 3 (Y a) ≤ M)
    (hvariance : ∀ a, v ≤ uniformVariance (Y a))
    (hH : Tendsto (fun a => magnitudeMoment (3/2) (X a)) l (𝓝 0)) :
    Tendsto (fun a => magnitudeCorrelation (X a) (Y a)) l (𝓝 0) := by
  apply correlation_tendsto_zero_of_bound
    (fun a => magnitudeMoment (3/2) (X a)) _
    (M ^ (1/3 : ℝ) + Real.sqrt V) v hv hH
  have hsmall : ∀ᶠ a in l, magnitudeMoment (3/2) (X a) < 1 :=
    hH.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall] with a ha
  have h := fractional_correlation_bound (X a) (Y a) (hX a) (hY a)
    (uniformAverage (fun i => Y a i ^ 2)) M v hv (hXsecond a)
    rfl (hthird a) (hvariance a) ha
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (add_le_add (le_refl _) (Real.sqrt_le_sqrt (hYsecond a)))
    (Real.rpow_nonneg (moment_nonneg (3/2) (X a) (hX a)) _)

omit [∀ a, Nonempty (κ a)] in
theorem tail_fraction_tendsto_zero
    (X : (a : α) → κ a → ℝ) (hX : ∀ a i, 0 ≤ X a i)
    (ε : ℝ) (hε : 0 < ε)
    (hH : Tendsto (fun a => magnitudeMoment (3/2) (X a)) l (𝓝 0)) :
    Tendsto (fun a => tailFraction (X a) ε) l (𝓝 0) := by
  have hb : Tendsto (fun a => magnitudeMoment (3/2) (X a) /
      ε ^ (3/2 : ℝ)) l (𝓝 0) := by
    simpa using hH.div_const (ε ^ (3/2 : ℝ))
  exact squeeze_zero (fun a => tail_fraction_nonneg (X a) ε)
    (fun a => tail_fraction_bound (X a) (hX a) ε hε) hb

omit [∀ a, Nonempty (κ a)] in
theorem lower_square_mass_tendsto_zero
    (X : (a : α) → κ a → ℝ) (hX : ∀ a i, 0 ≤ X a i)
    (ε : ℝ) (hε : 0 < ε)
    (hH : Tendsto (fun a => magnitudeMoment (3/2) (X a)) l (𝓝 0)) :
    Tendsto (fun a => lowerSquareMass (X a) ε) l (𝓝 0) := by
  have hb : Tendsto (fun a => ε ^ (1/2 : ℝ) *
      magnitudeMoment (3/2) (X a)) l (𝓝 0) := by
    simpa using hH.const_mul (ε ^ (1/2 : ℝ))
  exact squeeze_zero (fun a => lower_square_mass_nonneg (X a) ε)
    (fun a => lower_square_mass_bound (X a) (hX a) ε hε) hb

omit [∀ a, Nonempty (κ a)] in
theorem upper_square_mass_tendsto_one
    (X : (a : α) → κ a → ℝ) (hX : ∀ a i, 0 ≤ X a i)
    (hsecond : ∀ a, uniformAverage (fun i => X a i ^ 2) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hH : Tendsto (fun a => magnitudeMoment (3/2) (X a)) l (𝓝 0)) :
    Tendsto (fun a => upperSquareMass (X a) ε) l (𝓝 1) := by
  have hlow := lower_square_mass_tendsto_zero X hX ε hε hH
  have heq : (fun a => upperSquareMass (X a) ε) =
      (fun a => 1 - lowerSquareMass (X a) ε) := by
    funext a
    have h := square_mass_split (X a) ε
    rw [hsecond a] at h
    linarith
  rw [heq]
  simpa using tendsto_const_nhds.sub hlow

end VaryingFamily

end NField.Alignment.FiniteMagnitudeDecorrelation
