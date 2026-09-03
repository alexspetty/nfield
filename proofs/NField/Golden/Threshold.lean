/-
Author: Alexander S. Petty
-/

import NField.Alignment.OneDigitPrime

/-!
Exact real inequalities behind the threshold in
"Three and the Golden Ratio."
-/

namespace NField.Golden

open NField.Alignment

/-- The golden ratio. -/
noncomputable def goldenRatio : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- The reciprocal golden ratio, written in its conjugate closed form. -/
noncomputable def goldenReciprocal : ℝ :=
  (Real.sqrt 5 - 1) / 2

/-- The real-valued closed form of the one-digit alignment formula. -/
noncomputable def alignmentFormulaReal (p m : ℕ) : ℝ :=
  (2 * (m : ℝ) - 1) / (p * (m : ℝ) - 1)

theorem sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 := by
  norm_num

theorem sqrt_five_gt_two : 2 < Real.sqrt 5 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

theorem sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

theorem sqrt_five_lt_seven_thirds : Real.sqrt 5 < (7 : ℝ) / 3 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

theorem sqrt_five_lt_nine_fourths : Real.sqrt 5 < (9 : ℝ) / 4 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- The two closed forms really are multiplicative inverses. -/
theorem goldenRatio_mul_goldenReciprocal :
    goldenRatio * goldenReciprocal = 1 := by
  dsimp [goldenRatio, goldenReciprocal]
  nlinarith [sqrt_five_sq]

theorem goldenRatio_pos : 0 < goldenRatio := by
  dsimp [goldenRatio]
  positivity

theorem goldenReciprocal_eq_inv :
    goldenReciprocal = 1 / goldenRatio := by
  apply (eq_div_iff goldenRatio_pos.ne').2
  nlinarith [goldenRatio_mul_goldenReciprocal]

/-- Exact bounds used to turn the real threshold into an integer threshold. -/
theorem goldenRatio_sq_gt_two : (2 : ℝ) < goldenRatio ^ 2 := by
  dsimp [goldenRatio]
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

theorem goldenRatio_sq_lt_three : goldenRatio ^ 2 < (3 : ℝ) := by
  dsimp [goldenRatio]
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5, sqrt_five_lt_three]

/-- The reciprocal golden ratio lies strictly inside the paper's threshold window. -/
theorem two_fifths_lt_goldenReciprocal :
    (2 : ℝ) / 5 < goldenReciprocal := by
  dsimp [goldenReciprocal]
  nlinarith [sqrt_five_gt_two]

theorem goldenReciprocal_lt_two_thirds :
    goldenReciprocal < (2 : ℝ) / 3 := by
  dsimp [goldenReciprocal]
  nlinarith [sqrt_five_lt_seven_thirds]

/-- The rational count formula and its real closed form agree. -/
theorem oneDigitAlignment_cast_eq {p m : ℕ} (hp : Nat.Prime p) (hm : 1 ≤ m) :
    ((oneDigitAlignment p m : ℚ) : ℝ) = alignmentFormulaReal p m := by
  rw [oneDigitAlignment_eq hp]
  have h2m : 1 ≤ 2 * m := by omega
  have hpmPos : 0 < p * m := Nat.mul_pos hp.pos (by omega)
  have hpm : 1 ≤ p * m := hpmPos
  push_cast [Nat.cast_sub h2m, Nat.cast_sub hpm]
  rfl

/-- For integers, being above `phi^2` is exactly being at least three. -/
theorem nat_ge_goldenRatio_sq_iff (m : ℕ) :
    (m : ℝ) ≥ goldenRatio ^ 2 ↔ 3 ≤ m := by
  constructor
  · intro h
    by_contra hn
    have hmle : m ≤ 2 := by omega
    have hmReal : (m : ℝ) ≤ 2 := by exact_mod_cast hmle
    nlinarith [goldenRatio_sq_gt_two]
  · intro h
    have hmReal : (3 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith [goldenRatio_sq_lt_three]

/-- The exact golden threshold for the prime-three alignment formula. -/
theorem prime_three_golden_threshold {m : ℕ} (hm : 1 ≤ m) :
    alignmentFormulaReal 3 m ≥ goldenReciprocal ↔ 3 ≤ m := by
  have hs2 : (Real.sqrt 5) ^ 2 = 5 := sqrt_five_sq
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  constructor
  · intro h
    by_contra hn
    have hmle : m ≤ 2 := by omega
    interval_cases m <;>
      norm_num [alignmentFormulaReal, goldenReciprocal] at h ⊢ <;>
      nlinarith
  · intro hm3
    rw [alignmentFormulaReal, goldenReciprocal]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden).2
    have hm3Real : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    nlinarith [sqrt_five_lt_three]

/-- The paper's displayed `phi^2` criterion, followed by its integer form. -/
theorem prime_three_golden_threshold_full {m : ℕ} (hm : 1 ≤ m) :
    alignmentFormulaReal 3 m ≥ goldenReciprocal ↔
      (m : ℝ) ≥ goldenRatio ^ 2 := by
  rw [prime_three_golden_threshold hm, nat_ge_goldenRatio_sq_iff]

/-- No equality occurs at the integer threshold: `m ≥ 3` is strictly above it. -/
theorem prime_three_strict_golden_threshold {m : ℕ} (hm : 1 ≤ m) :
    alignmentFormulaReal 3 m > goldenReciprocal ↔ 3 ≤ m := by
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  constructor
  · intro h
    exact (prime_three_golden_threshold hm).mp (le_of_lt h)
  · intro hm3
    rw [alignmentFormulaReal, goldenReciprocal]
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden).2
    have hm3Real : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    nlinarith [sqrt_five_lt_nine_fourths]

/-- Primes at least five never reach the reciprocal-golden threshold. -/
theorem large_prime_below_golden {p m : ℕ} (hp : 5 ≤ p) (hm : 1 ≤ m) :
    alignmentFormulaReal p m < goldenReciprocal := by
  have hpReal : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (p : ℝ) * m - 1 := by nlinarith
  have hupper : alignmentFormulaReal p m < (2 : ℝ) / p := by
    rw [alignmentFormulaReal,
      div_lt_div_iff₀ hden (by positivity : (0 : ℝ) < p)]
    nlinarith
  have hpPos : (0 : ℝ) < p := by positivity
  have hle : (2 : ℝ) / p ≤ 2 / 5 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpReal
  exact lt_of_lt_of_le hupper (le_of_lt (lt_of_le_of_lt hle
    two_fifths_lt_goldenReciprocal))

/-- The stronger bound used for the whole separating threshold window. -/
theorem large_prime_below_two_fifths {p m : ℕ} (hp : 5 ≤ p) (hm : 1 ≤ m) :
    alignmentFormulaReal p m < (2 : ℝ) / 5 := by
  have hpReal : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (p : ℝ) * m - 1 := by nlinarith
  have hupper : alignmentFormulaReal p m < (2 : ℝ) / p := by
    rw [alignmentFormulaReal,
      div_lt_div_iff₀ hden (by positivity : (0 : ℝ) < p)]
    nlinarith
  have hle : (2 : ℝ) / p ≤ 2 / 5 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpReal
  exact lt_of_lt_of_le hupper hle

/-- Among primes, some positive resolution crosses the threshold exactly for 2 or 3. -/
theorem prime_golden_selection {p : ℕ} (hp : Nat.Prime p) :
    (∃ m : ℕ, 1 ≤ m ∧
      alignmentFormulaReal p m ≥ goldenReciprocal) ↔ p = 2 ∨ p = 3 := by
  constructor
  · rintro ⟨m, hm, halign⟩
    by_contra hnot
    push Not at hnot
    have hp5 : 5 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      have hpne4 : p ≠ 4 := by
        intro hp4
        subst p
        norm_num at hp
      omega
    exact (not_lt_of_ge halign) (large_prime_below_golden hp5 hm)
  · intro h
    rcases h with rfl | rfl
    · refine ⟨1, by norm_num, ?_⟩
      norm_num [alignmentFormulaReal, goldenReciprocal]
      nlinarith [sqrt_five_lt_three]
    · refine ⟨3, by norm_num, ?_⟩
      exact (prime_three_golden_threshold (by norm_num)).2 (by norm_num)

/--
The base-supported version of prime selection.  For prime three, `m=b` is the
explicit supported witness; for prime two, `m=1` is the degenerate witness.
-/
theorem supported_prime_golden_selection {b p : ℕ} (hp : Nat.Prime p)
    (hb : 2 ≤ b) (hpb : ¬p ∣ b) (hmod : b % p = 1) :
    (∃ m : ℕ, 1 ≤ m ∧ Supported b m ∧
      alignmentFormulaReal p m ≥ goldenReciprocal) ↔ p = 2 ∨ p = 3 := by
  constructor
  · rintro ⟨m, hm, _, halign⟩
    exact (prime_golden_selection hp).mp ⟨m, hm, halign⟩
  · intro h
    rcases h with rfl | rfl
    · refine ⟨1, by norm_num, supported_one b, ?_⟩
      norm_num [alignmentFormulaReal, goldenReciprocal]
      nlinarith [sqrt_five_lt_three]
    · have hb3 : 3 ≤ b := by
        omega
      refine ⟨b, by omega, supported_self b, ?_⟩
      exact (prime_three_golden_threshold (by omega)).2 hb3

/-- Supported powers of any base at least two eventually cross every threshold below `2/3`. -/
theorem exists_supported_prime_three_crossing {b : ℕ} (hb : 2 ≤ b)
    {t : ℝ} (ht : t < (2 : ℝ) / 3) :
    ∃ m : ℕ, 1 ≤ m ∧ Supported b m ∧
      t ≤ alignmentFormulaReal 3 m := by
  have hcoef : 0 < 2 - 3 * t := by linarith
  let x : ℝ := (1 - t) / (2 - 3 * t)
  have hbReal : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  obtain ⟨D, hD⟩ := pow_unbounded_of_one_lt x hbReal
  refine ⟨b ^ D, Nat.one_le_pow D b (by omega), supported_pow b D, ?_⟩
  have hmReal : x < ((b ^ D : ℕ) : ℝ) := by simpa using hD
  have hmNat : 1 ≤ b ^ D := Nat.one_le_pow D b (by omega)
  have hmOne : (1 : ℝ) ≤ (b ^ D : ℕ) := by exact_mod_cast hmNat
  have hden : 0 < (3 : ℝ) * (b ^ D : ℕ) - 1 := by nlinarith
  rw [alignmentFormulaReal]
  apply (le_div_iff₀ hden).2
  dsimp [x] at hmReal
  have hmain : 1 - t < ((b ^ D : ℕ) : ℝ) * (2 - 3 * t) :=
    (div_lt_iff₀ hcoef).mp hmReal
  nlinarith

/-- Every threshold strictly between `2/5` and `2/3` selects the same primes. -/
theorem supported_prime_threshold_window {b p : ℕ} (hp : Nat.Prime p)
    (hb : 2 ≤ b) (hpb : ¬p ∣ b) (hmod : b % p = 1)
    {t : ℝ} (htLower : (2 : ℝ) / 5 < t) (htUpper : t < (2 : ℝ) / 3) :
    (∃ m : ℕ, 1 ≤ m ∧ Supported b m ∧
      t ≤ alignmentFormulaReal p m) ↔ p = 2 ∨ p = 3 := by
  constructor
  · rintro ⟨m, hm, _, halign⟩
    by_contra hnot
    push Not at hnot
    have hp5 : 5 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      have hpne4 : p ≠ 4 := by
        intro hp4
        subst p
        norm_num at hp
      omega
    have hbelow := large_prime_below_two_fifths hp5 hm
    linarith
  · intro h
    rcases h with rfl | rfl
    · refine ⟨1, by norm_num, supported_one b, ?_⟩
      norm_num [alignmentFormulaReal]
      linarith
    · exact exists_supported_prime_three_crossing hb htUpper

/-- A base-10 supported resolution cannot equal three. -/
theorem base_ten_supported_ne_three {m : ℕ} (hm : Supported 10 m) : m ≠ 3 := by
  rintro rfl
  rcases hm with ⟨D, hD⟩
  have hthreePow : 3 ∣ 10 ^ D := hD
  have hthreeTen : 3 ∣ 10 := Nat.prime_three.dvd_of_dvd_pow hthreePow
  norm_num at hthreeTen

/-- The base-10 classification: the first supported crossing is `m=4`. -/
theorem base_ten_supported_golden_threshold {m : ℕ} (hmPos : 1 ≤ m)
    (hm : Supported 10 m) :
    alignmentFormulaReal 3 m > goldenReciprocal ↔ 4 ≤ m := by
  rw [prime_three_strict_golden_threshold hmPos]
  constructor
  · intro hm3
    have hmne : m ≠ 3 := base_ten_supported_ne_three hm
    omega
  · omega

/-- The first base-10 supported crossing has the paper's exact value `7/11`. -/
theorem first_base_ten_crossing_value :
    alignmentFormulaReal 3 4 = (7 : ℝ) / 11 := by
  norm_num [alignmentFormulaReal]

end NField.Golden
