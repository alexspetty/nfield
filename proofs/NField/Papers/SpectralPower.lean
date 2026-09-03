/-
Author: Alexander S. Petty
-/

import NField.Alignment.FloorDigitSpectralModel
import NField.Alignment.IntervalSineKernel

/-!
# The Spectral Power of the Digit Function

Reader-facing theorem map for the Lean companion to
`papers/spectral_power.tex`.

## Checked here

* The long-division digit function is encoded intrinsically as one coordinate
  for each digit, with residue zero omitted.
* The zero Fourier mode is exactly the ordered same-bin collision mass.
* The additive collision profile transforms exactly into spectral power, and
  inverse DFT recovers the profile with the manuscript's normalization.
* Parseval gives total power `p * (p - 1)` for the intrinsic prime word.
* Translation changes an interval coefficient only by a unit phase.  The
  interval coefficient is an exact finite geometric sum and, away from zero
  frequency, the exact geometric quotient.
* The floor-arithmetic bridge proves that every intrinsic prime digit bin is
  the required cyclic interval and has one of the two quotient/remainder
  lengths.  The exact two-kernel spectral formula therefore applies directly
  to the manuscript's digit word.
* The complex interval quotient is converted to the printed real sine ratio.
* Short intrinsic intervals give the exact sum of two triangular profiles.
* Spectral flatness is equivalent to digit partitioning and hence, under the
  manuscript's hypotheses, to `p ≤ b + 1`.  The constant value is `p - 1`.
* Exact certificates check every decimal-prime-thirteen bin size, its zero
  mode and collision profile, and the flat base-eight/base-ten contrast modulo
  seven with multiplicative orders one and six.

The reusable additions extend the cumulative Lean stack.  They do not reorder
its dependency structure to imitate the manuscript chronology.
-/

namespace NField.Papers.SpectralPower

open scoped BigOperators
open ZMod
open NField.Alignment
open NField.Alignment.SpectralPower

/-- The zero mode of the intrinsic prime digit word is the original
bin-population square sum. -/
theorem zero_mode_collision_mass {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    spectralPower (primeDigitWord b p hb hp) 0 =
      (digitBinSquareSum b p : ℂ) :=
  prime_spectralPower_zero hb hp

/-- Exact additive correlation theorem for the intrinsic digit encoding. -/
theorem additive_collision_transform {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (k : ZMod p) :
    𝓕 (fun h =>
      (additiveCollision (primeDigitWord b p hb hp) h : ℂ)) k =
        spectralPower (primeDigitWord b p hb hp) k :=
  dft_additiveCollision (primeDigitWord b p hb hp) k

/-- Fourier inversion with the exact `1 / p` normalization. -/
theorem additive_collision_inversion {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (h : ZMod p) :
    (additiveCollision (primeDigitWord b p hb hp) h : ℂ) =
      (p : ℂ)⁻¹ * ∑ k : ZMod p,
        stdAddChar (k * h) * spectralPower (primeDigitWord b p hb hp) k := by
  have hinverse := congrFun
    (inverseDFT_spectralPower (primeDigitWord b p hb hp)) h
  rw [ZMod.invDFT_apply] at hinverse
  simpa [smul_eq_mul] using hinverse.symm

/-- The manuscript's multiplicative comparison count, written as the exact
double indicator sum over digit labels and residues. -/
theorem multiplicative_collision_definition {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) (g : ZMod N) :
    multiplicativeCollisionCount word g =
      ∑ d : Fin κ, ∑ r : ZMod N,
        if word r = some d ∧ word (g * r) = some d then 1 else 0 :=
  multiplicativeCollisionCount_eq_indicator_sum word g

/-- Parseval's total-power identity for the intrinsic prime digit word. -/
theorem parseval_total_power {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    ∑ k, spectralPower (primeDigitWord b p hb hp) k =
      (p * (p - 1) : ℕ) :=
  prime_total_spectralPower hb hp

/-- Exact nonzero-frequency geometric quotient for a consecutive interval. -/
theorem interval_geometric_quotient (p n : ℕ) [NeZero p]
    {k : ZMod p} (hk : k ≠ 0) :
    intervalFourier p n k =
      ((stdAddChar (-k)) ^ n - 1) / (stdAddChar (-k) - 1) :=
  intervalFourier_eq_geom_quotient p n hk

/-- The interval transform in the exact real sine form printed in the
manuscript. -/
theorem interval_sine_quotient (p n : ℕ) [NeZero p]
    {k : ZMod p} (hk : k ≠ 0) :
    ‖intervalFourier p n k‖ =
      |Real.sin (Real.pi * (k.val : ℝ) * n / p)| /
        |Real.sin (Real.pi * (k.val : ℝ) / p)| :=
  intervalFourier_norm_eq_sine_quotient p n hk

/-- Every intrinsic digit bin is the exact consecutive boundary interval used
by the manuscript. -/
theorem consecutive_prime_digit_bins {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (d : Fin b) :
    binSet (primeDigitWord b p hb hp) d =
      (Finset.Ico (max 1 (digitBinBoundary b p d.val))
        (digitBinBoundary b p (d.val + 1))).image
          (fun x : ℕ => (x : ZMod p)) :=
  primeDigitWord_binSet_eq_boundary_image hb hp d

/-- The two intrinsic bin lengths and their exact multiplicities. -/
theorem intrinsic_two_bin_lengths {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    (∀ d, (binSet (primeDigitWord b p hb hp) d).card = (p - 1) / b ∨
      (binSet (primeDigitWord b p hb hp) d).card = (p - 1) / b + 1) ∧
    (Finset.univ.filter fun d : Fin b =>
      (binSet (primeDigitWord b p hb hp) d).card = (p - 1) / b).card =
        b - (p - 1) % b ∧
    (Finset.univ.filter fun d : Fin b =>
      (binSet (primeDigitWord b p hb hp) d).card = (p - 1) / b + 1).card =
        (p - 1) % b := by
  have model := primeDigitWord_twoLengthIntervalModel hb hp
  exact ⟨model.length_cases, model.small_count, model.large_count⟩

/-- The exact nonzero-frequency spectral-power formula for the intrinsic digit
word, in the manuscript's real sine-square notation. -/
theorem intrinsic_spectral_power_formula {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p]
    {k : ZMod p} (hk : k ≠ 0) :
    spectralPower (primeDigitWord b p hb hp) k =
      (((b - (p - 1) % b : ℕ) : ℝ) *
          (Real.sin (Real.pi * (k.val : ℝ) *
              (((p - 1) / b : ℕ) : ℝ) / p) ^ 2 /
            Real.sin (Real.pi * (k.val : ℝ) / p) ^ 2) +
        (((p - 1) % b : ℕ) : ℝ) *
          (Real.sin (Real.pi * (k.val : ℝ) *
              ((((p - 1) / b + 1 : ℕ)) : ℝ) / p) ^ 2 /
            Real.sin (Real.pi * (k.val : ℝ) / p) ^ 2) : ℝ) := by
  rw [prime_spectralPower_eq_two_interval_kernels hb hp k,
    intervalPower_eq_sine_sq_div_sq p ((p - 1) / b) hk,
    intervalPower_eq_sine_sq_div_sq p ((p - 1) / b + 1) hk]
  push_cast
  rfl

/-- Closed zero-frequency formula for the intrinsic digit word. -/
theorem intrinsic_spectral_power_zero {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    spectralPower (primeDigitWord b p hb hp) 0 =
      (b * ((p - 1) / b) ^ 2 +
        ((p - 1) % b) * (2 * ((p - 1) / b) + 1) : ℕ) :=
  prime_spectralPower_zero_closed hb hp

/-- Exact intrinsic triangular additive-collision profile. -/
theorem intrinsic_triangular_collision_profile {b p : ℕ}
    (hb : 2 ≤ b) (hp : 0 < p) [NeZero p] (h : ZMod p) :
    additiveCollision (primeDigitWord b p (by omega) hp) h =
      (b - (p - 1) % b) * ((p - 1) / b - circularDistance p h) +
        (p - 1) % b * ((p - 1) / b + 1 - circularDistance p h) :=
  prime_additiveCollision_eq_two_triangles hb hp h

/-- Bijections of the digit labels leave every spectral-power value fixed. -/
theorem digit_relabeling_invariance {N b : ℕ} [NeZero N]
    (e : Fin b ≃ Fin b) (word : ZMod N → Option (Fin b)) (k : ZMod N) :
    spectralPower (relabelWord e word) k = spectralPower word k :=
  spectralPower_relabelWord e word k

/-- The two-length count is forced by the total mass. -/
theorem two_length_bin_count {b q ρ : ℕ}
    (n : Fin b → ℕ)
    (hlength : ∀ d, n d = q ∨ n d = q + 1)
    (htotal : ∑ d, n d = b * q + ρ) :
    (Finset.univ.filter fun d : Fin b => n d = q).card = b - ρ ∧
      (Finset.univ.filter fun d : Fin b => n d = q + 1).card = ρ :=
  two_length_count_certificate n hlength htotal

/-- The manuscript's two-kernel spectral formula from explicit cyclic
interval data. -/
theorem two_length_spectral_formula {p b q ρ : ℕ} [NeZero p]
    (word : ZMod p → Option (Fin b))
    (hlength : ∀ d, (binSet word d).card = q ∨
      (binSet word d).card = q + 1)
    (htotal : ∑ d, (binSet word d).card = b * q + ρ)
    (hshort : ∀ d, (binSet word d).card ≤ p)
    (hinterval : ∀ d,
      IsCyclicInterval (binSet word d) (binSet word d).card)
    (k : ZMod p) :
    spectralPower word k =
      (b - ρ : ℕ) * intervalPower p q k +
        (ρ : ℕ) * intervalPower p (q + 1) k :=
  spectralPower_eq_two_interval_kernels_of_cyclicIntervals
    word hlength htotal hshort hinterval k

/-- Exact triangular overlap law from the manuscript's short two-length
interval model. -/
theorem triangular_collision_profile {p b q ρ : ℕ} [NeZero p]
    (word : ZMod p → Option (Fin b))
    (model : ShortTwoLengthIntervalModel word q ρ) (h : ZMod p) :
    additiveCollision word h =
      (b - ρ) * (q - circularDistance p h) +
        ρ * (q + 1 - circularDistance p h) :=
  additiveCollision_eq_two_triangles word model h

/-- The exact flatness boundary for prime digit words. -/
theorem flatness_criterion {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p] :
    SpectralFlat (primeDigitWord b p hb hp.pos) ↔ p ≤ b + 1 :=
  prime_spectralFlat_iff_le hb hp hpb

/-- Exact cosine rewrite printed for the nonzero decimal-prime-thirteen
frequencies. -/
theorem decimal_thirteen_nonzero_power {k : ZMod 13} (hk : k ≠ 0) :
    spectralPower decimalThirteenDigitWord k =
      (((8 : ℝ) + 8 *
        Real.cos (Real.pi * (k.val : ℝ) / 13) ^ 2 : ℝ) : ℂ) := by
  let x : ℝ := Real.pi * (k.val : ℝ) / 13
  have hxpos : 0 < x := by
    dsimp [x]
    have hkpos : 0 < k.val := ZMod.val_pos.mpr hk
    positivity
  have hxlt : x < Real.pi := by
    have hkltR : (k.val : ℝ) < 13 := by exact_mod_cast k.val_lt
    have hfrac : (k.val : ℝ) / 13 < 1 :=
      (div_lt_one (by norm_num : (0 : ℝ) < 13)).2 hkltR
    calc
      x = Real.pi * ((k.val : ℝ) / 13) := by dsimp [x]; ring
      _ < Real.pi * 1 := mul_lt_mul_of_pos_left hfrac Real.pi_pos
      _ = Real.pi := by ring
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxpos hxlt)
  have hformula := intrinsic_spectral_power_formula
    (b := 10) (p := 13) (by norm_num) (by norm_num) hk
  norm_num [decimalThirteenDigitWord] at hformula ⊢
  let y : ℂ := (x : ℂ)
  have hy : y = (Real.pi : ℂ) * ((k.cast : ℝ) : ℂ) / 13 := by
    dsimp [y, x]
    push_cast
    rfl
  have hy2 : (Real.pi : ℂ) * ((k.cast : ℝ) : ℂ) * 2 / 13 = 2 * y := by
    rw [hy]
    ring
  rw [← hy] at hformula ⊢
  rw [hy2] at hformula
  have hsinC : Complex.sin y ≠ 0 := by
    rw [show y = (x : ℂ) by rfl, ← Complex.ofReal_sin]
    exact_mod_cast hsin
  rw [Complex.sin_two_mul] at hformula
  apply hformula.trans
  field_simp
  ring

/-- The decimal cosine-square sum over the nonzero residue classes. -/
private lemma decimal_thirteen_cosine_subtype_sum :
    (∑ k : {k : ZMod 13 // k ≠ 0},
      Real.cos (Real.pi * (k.val.val : ℝ) / 13) ^ 2) = (11 : ℝ) / 2 := by
  have hsum := prime_total_spectralPower
    (b := 10) (p := 13) (by norm_num) (by norm_num)
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun k : ZMod 13 =>
      spectralPower (primeDigitWord 10 13 (by norm_num) (by norm_num)) k) 0]
    at hsum
  norm_num [decimalThirteenDigitWord] at hsum
  have hzero :
      spectralPower (primeDigitWord 10 13 (by norm_num) (by norm_num)) 0 = 16 := by
    simpa using prime_spectralPower_zero_closed
      (b := 10) (p := 13) (by norm_num) (by norm_num)
  rw [hzero] at hsum
  have hnonzero (i : {k : ZMod 13 // k ≠ 0}) :
      spectralPower (primeDigitWord 10 13 (by norm_num) (by norm_num)) i =
        (((8 : ℝ) + 8 *
          Real.cos (Real.pi * (i.val.val : ℝ) / 13) ^ 2 : ℝ) : ℂ) := by
    simpa [decimalThirteenDigitWord] using
      decimal_thirteen_nonzero_power i.property
  simp_rw [hnonzero] at hsum
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.re_sum, Complex.ofReal_re] at hre
  have hcard : Fintype.card {k : ZMod 13 // k ≠ 0} = 12 := by
    rw [Fintype.card_subtype_compl (fun k : ZMod 13 => k = 0),
      ZMod.card]
    norm_num
  rw [Finset.sum_add_distrib, Finset.sum_const] at hre
  simp only [Finset.card_univ, hcard, nsmul_eq_mul] at hre
  norm_num at hre
  rw [← Finset.mul_sum] at hre
  simp only [ZMod.cast_eq_val] at hre
  linarith

/-- The exact natural-indexed cosine-square sum printed in the decimal
prime-thirteen calculation. -/
theorem decimal_thirteen_cosine_sum :
    (∑ k ∈ Finset.Icc (1 : ℕ) 12,
      Real.cos (Real.pi * (k : ℝ) / 13) ^ 2) = (11 : ℝ) / 2 := by
  classical
  have hreindex :
      (∑ k ∈ Finset.Icc (1 : ℕ) 12,
        Real.cos (Real.pi * (k : ℝ) / 13) ^ 2) =
      ∑ z : {z : ZMod 13 // z ≠ 0},
        Real.cos (Real.pi * (z.val.val : ℝ) / 13) ^ 2 := by
    apply Finset.sum_bij
      (fun a ha =>
        ⟨(a : ZMod 13), by
          intro hzero
          have hdvd : 13 ∣ a :=
            (ZMod.natCast_eq_zero_iff a 13).mp hzero
          obtain ⟨c, hc⟩ := hdvd
          have haIcc := Finset.mem_Icc.mp ha
          omega⟩)
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ heq
      have ha₁Icc := Finset.mem_Icc.mp ha₁
      have ha₂Icc := Finset.mem_Icc.mp ha₂
      have hzmod : (a₁ : ZMod 13) = (a₂ : ZMod 13) :=
        congrArg Subtype.val heq
      have hval := congrArg ZMod.val hzmod
      have ha₁lt : a₁ < 13 := by omega
      have ha₂lt : a₂ < 13 := by omega
      simpa [ZMod.val_cast_of_lt ha₁lt,
        ZMod.val_cast_of_lt ha₂lt] using hval
    · intro z hz
      have hzlt : z.val.val < 13 := z.val.val_lt
      refine ⟨z.val.val, Finset.mem_Icc.mpr
        ⟨ZMod.val_pos.mpr z.property, by omega⟩, ?_⟩
      apply Subtype.ext
      exact ZMod.natCast_zmod_val z.val
    · intro a ha
      have haIcc := Finset.mem_Icc.mp ha
      have halt : a < 13 := by omega
      rw [ZMod.val_cast_of_lt halt]
  rw [hreindex, decimal_thirteen_cosine_subtype_sum]

/-- Exact finite data printed in the decimal-prime-thirteen section. -/
theorem decimal_thirteen_certificate :
    decimalThirteenBinSizes = [1, 1, 1, 2, 1, 1, 2, 1, 1, 1] ∧
      binSquareMass decimalThirteenDigitWord = 16 ∧
      spectralPower decimalThirteenDigitWord 0 = 16 ∧
      decimalThirteenCollisionProfile =
        [12, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] ∧
      (∑ k, spectralPower decimalThirteenDigitWord k) = 156 := by
  refine ⟨decimalThirteenBinSizes_certificate,
    decimalThirteenBinSquareMass_certificate,
    decimalThirteenSpectralPower_zero,
    decimalThirteenCollisionProfile_certificate, ?_⟩
  simpa [decimalThirteenDigitWord] using prime_total_spectralPower
    (b := 10) (p := 13) (by norm_num) (by norm_num)

/-- Same flat additive spectrum, different multiplicative orbit orders. -/
theorem magnitude_boundary_certificate :
    SpectralFlat (primeDigitWord 8 7 (by norm_num) (by norm_num)) ∧
      SpectralFlat (primeDigitWord 10 7 (by norm_num) (by norm_num)) ∧
      orderOf (8 : ZMod 7) = 1 ∧ orderOf (10 : ZMod 7) = 6 := by
  exact ⟨baseEightAndTen_modSeven_flat.1,
    baseEightAndTen_modSeven_flat.2,
    baseEightAndTen_modSeven_orders⟩

-- Intrinsic encoding and collision mass.
#check primeDigitWord
#check primeDigitWord_bin_card
#check spectralPower_zero
#check prime_spectralPower_zero
#check zero_mode_collision_mass

-- Additive collision transform, inversion, and Parseval.
#check dft_setOverlap
#check dft_additiveCollision
#check inverseDFT_spectralPower
#check total_spectralPower
#check additive_collision_transform
#check additive_collision_inversion
#check multiplicative_collision_definition
#check parseval_total_power

-- Interval and two-length structure.
#check setFourier_translate
#check setFourier_power_translate
#check intervalFourier_eq_geom
#check intervalFourier_eq_geom_quotient
#check interval_sine_quotient
#check primeDigitWord_binSet_eq_boundary_image
#check consecutive_prime_digit_bins
#check intrinsic_two_bin_lengths
#check intrinsic_spectral_power_formula
#check intrinsic_spectral_power_zero
#check intrinsic_triangular_collision_profile
#check spectralPower_relabelWord
#check digit_relabeling_invariance
#check two_length_count_certificate
#check spectralPower_eq_two_interval_kernels_of_cyclicIntervals
#check additiveCollision_eq_two_triangles
#check interval_geometric_quotient
#check two_length_bin_count
#check two_length_spectral_formula
#check triangular_collision_profile

-- Flatness and exact examples.
#check spectralFlat_value
#check prime_spectralFlat_iff_digitPartitioning
#check prime_spectralFlat_iff_le
#check flatness_criterion
#check decimal_thirteen_nonzero_power
#check decimal_thirteen_cosine_sum
#check decimal_thirteen_certificate
#check magnitude_boundary_certificate

end NField.Papers.SpectralPower
