/-
Author: Alexander S. Petty
-/

import NField.Alignment.CanonicalSynchronizedAlignment
import NField.Alignment.DigitPartitioningClassification

/-!
# Canonical three-tier classification

The synchronized complement bound is lifted from supplied factors to the
canonical supported and rough parts of an arbitrary positive denominator.
-/

namespace NField.Alignment

open Filter NField.Golden NField.Alignment.ThreeTier

theorem canonicalClearingCofactor_coprime {b n D : ℕ} (hn : 0 < n)
    (hD : supportedPart b n ∣ b ^ D) :
    Nat.Coprime (roughPart b n) (clearingCofactor b (supportedPart b n) D) :=
  ((roughPart_coprime_base (b := b) hn).pow_right D).of_dvd_right
    (Nat.div_dvd_of_dvd hD)

/-- The arbitrary-denominator alignment is exactly the already grouped
rough-residue statistic. -/
theorem canonicalSynchronizedAlignmentReal_eq_roughAlignment
    {b n D : ℕ} (hn : 0 < n)
    (hD : supportedPart b n ∣ b ^ D) :
    canonicalSynchronizedAlignmentReal b n D hn =
      canonicalRoughAlignmentReal b (roughPart b n) (supportedPart b n)
        (clearingCofactor b (supportedPart b n) D)
        (canonicalAlignmentPeriod b n hn) := by
  unfold canonicalSynchronizedAlignmentReal
  exact clearedAlignmentReal_eq_canonicalRoughAlignmentReal
    (roughPart_pos hn) (supportedPart_pos hn) hD

/-- A supported denominator has canonical alignment one. -/
theorem supportedDenominator_canonicalAlignment_eq_one
    {b n D : ℕ} (hn : 0 < n) (hnSupported : Supported b n)
    (hD : supportedPart b n ∣ b ^ D) :
    canonicalSynchronizedAlignmentReal b n D hn = 1 := by
  rw [canonicalSynchronizedAlignmentReal_eq_roughAlignment hn hD,
    (roughPart_eq_one_iff_supported hn).mpr hnSupported,
    canonicalRoughAlignmentReal_eq_one_of_rough_one]

/-- The exact synchronized formula for every supported three-core family. -/
theorem threeCoreAlignmentFormula {b m D : ℕ}
    (hb : 2 ≤ b) (h3b : ¬3 ∣ b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedAlignmentReal b 3 m D
        (coprimeBasePeriod b 3
          (Nat.prime_three.coprime_iff_not_dvd.mpr h3b)) =
      alignmentFormulaReal 3 m := by
  have hcop : Nat.Coprime 3 b :=
    Nat.prime_three.coprime_iff_not_dvd.mpr h3b
  rw [clearedAlignmentReal_eq_canonicalRoughAlignmentReal (by norm_num) hm hD,
    canonicalRoughAlignmentReal, if_neg (by norm_num)]
  have hformula := synchronizedCompositeAlignmentReal_eq_digitPartitioningFormula
    Nat.prime_three h3b
      (digitPartitioning_of_le (by norm_num) h3b (by omega))
      ((hcop.pow_right D).of_dvd_right (Nat.div_dvd_of_dvd hD)) hm
      (coprimeBasePeriod_pos hcop)
  change synchronizedCompositeAlignmentReal b 3 m (b ^ D / m)
    (coprimeBasePeriod b 3 hcop) = alignmentFormulaReal 3 m
  exact hformula

/-- The exact finite complement upper bound on the canonical decomposition. -/
theorem canonicalSynchronizedAlignmentReal_upper_bound
    {b n D : ℕ} (hb : 0 < b) (hbeven : Even b) (hn : 0 < n)
    (hD : supportedPart b n ∣ b ^ D) (ht : roughPart b n ≠ 1) :
    canonicalSynchronizedAlignmentReal b n D hn ≤
        finiteComplementBoundReal (roughPart b n) (supportedPart b n) ∧
      finiteComplementBoundReal (roughPart b n) (supportedPart b n) <
        roughCeilingReal (roughPart b n) := by
  let t := roughPart b n
  let m := supportedPart b n
  let L := canonicalAlignmentPeriod b n hn
  have htPos : 0 < t := roughPart_pos hn
  have hmPos : 0 < m := supportedPart_pos hn
  have hLPos : 0 < L := canonicalAlignmentPeriod_pos hn
  have hcop : Nat.Coprime t b := roughPart_coprime_base hn
  have hu : Nat.Coprime t (clearingCofactor b m D) :=
    canonicalClearingCofactor_coprime hn hD
  have hbridge := canonicalSynchronizedAlignmentReal_eq_roughAlignment hn hD
  constructor
  · rw [hbridge, canonicalRoughAlignmentReal, if_neg ht]
    exact synchronizedCompositeAlignmentReal_le_finite_bound hb (by omega)
      (by omega) hLPos hcop hu hbeven
  · exact finiteComplementBoundReal_lt_roughCeiling (by omega) (by omega)

/-- The three arithmetic cases and their asserted alignment ranges for every
positive denominator on its canonical synchronized clock. -/
theorem canonicalThreeTierCases {b n D : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    (roughPart b n = 1 ∧
        canonicalSynchronizedAlignmentReal b n D (by omega) = 1) ∨
      (roughPart b n = 3 ∧ 4 ≤ supportedPart b n ∧
        (7 : ℝ) / 11 ≤ canonicalSynchronizedAlignmentReal b n D (by omega) ∧
        canonicalSynchronizedAlignmentReal b n D (by omega) < (2 : ℝ) / 3) ∨
      (roughPart b n ≠ 1 ∧
        ¬(roughPart b n = 3 ∧ 4 ≤ supportedPart b n) ∧
        canonicalSynchronizedAlignmentReal b n D (by omega) ≤ (3 : ℝ) / 5) := by
  have hnPos : 0 < n := by omega
  let t := roughPart b n
  let m := supportedPart b n
  let L := canonicalAlignmentPeriod b n hnPos
  let u := clearingCofactor b m D
  have htPos : 0 < t := roughPart_pos hnPos
  have hmPos : 0 < m := supportedPart_pos hnPos
  have hLPos : 0 < L := canonicalAlignmentPeriod_pos hnPos
  have hmSupported : Supported b m := supportedPart_supported hnPos
  have hcop : Nat.Coprime t b := roughPart_coprime_base hnPos
  have hu : Nat.Coprime t u := canonicalClearingCofactor_coprime hnPos hD
  have hbridge := canonicalSynchronizedAlignmentReal_eq_roughAlignment hnPos hD
  rw [hbridge]
  change
    (t = 1 ∧ canonicalRoughAlignmentReal b t m u L = 1) ∨
      (t = 3 ∧ 4 ≤ m ∧ (7 : ℝ) / 11 ≤ canonicalRoughAlignmentReal b t m u L ∧
        canonicalRoughAlignmentReal b t m u L < (2 : ℝ) / 3) ∨
      (t ≠ 1 ∧ ¬(t = 3 ∧ 4 ≤ m) ∧
        canonicalRoughAlignmentReal b t m u L ≤ (3 : ℝ) / 5)
  by_cases ht1 : t = 1
  · left
    refine ⟨ht1, ?_⟩
    rw [ht1]
    exact canonicalRoughAlignmentReal_eq_one_of_rough_one
  by_cases htierTwo : t = 3 ∧ 4 ≤ m
  · right; left
    rcases htierTwo with ⟨ht3, hm4⟩
    refine ⟨ht3, hm4, ?_⟩
    rw [ht3] at hu
    rw [ht3]
    exact canonicalRoughAlignmentReal_threeCore_range hb h3b hu hmPos hLPos hm4
  · right; right
    refine ⟨ht1, htierTwo, ?_⟩
    by_cases ht3 : t = 3
    · have hmnot4 : ¬4 ≤ m := fun hm4 => htierTwo ⟨ht3, hm4⟩
      have hmne3 : m ≠ 3 := by
        intro hm3
        apply three_not_dvd_supported h3b hmSupported
        simp [hm3]
      have hmCases : m = 1 ∨ m = 2 := by omega
      rw [ht3] at hu
      rw [ht3]
      rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b hu hmPos hLPos]
      rcases hmCases with hm1 | hm2
      · rw [hm1, threeCore_one]
        norm_num
      · rw [hm2, threeCore_two]
    · exact le_of_lt (canonicalRoughAlignmentReal_lt_three_fifths_of_other_rough
        hb hbeven htPos ht1 ht3 hmPos hLPos hcop hu)

/-- The exact forbidden interval, reciprocal-golden test, and both endpoint
conditions on the canonical factors. -/
theorem canonicalThreeTierGapCertificate {b n D : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    ¬((3 : ℝ) / 5 < canonicalSynchronizedAlignmentReal b n D (by omega) ∧
        canonicalSynchronizedAlignmentReal b n D (by omega) < (7 : ℝ) / 11) ∧
      (goldenReciprocal ≤ canonicalSynchronizedAlignmentReal b n D (by omega) ↔
        roughPart b n = 1 ∨
          (roughPart b n = 3 ∧ 4 ≤ supportedPart b n)) ∧
      (canonicalSynchronizedAlignmentReal b n D (by omega) = (3 : ℝ) / 5 ↔
        roughPart b n = 3 ∧ supportedPart b n = 2) ∧
      (canonicalSynchronizedAlignmentReal b n D (by omega) = (7 : ℝ) / 11 ↔
        roughPart b n = 3 ∧ supportedPart b n = 4) := by
  have hnPos : 0 < n := by omega
  let t := roughPart b n
  let m := supportedPart b n
  let L := canonicalAlignmentPeriod b n hnPos
  let u := clearingCofactor b m D
  have htPos : 0 < t := roughPart_pos hnPos
  have hmPos : 0 < m := supportedPart_pos hnPos
  have hLPos : 0 < L := canonicalAlignmentPeriod_pos hnPos
  have hmSupported : Supported b m := supportedPart_supported hnPos
  have hcop : Nat.Coprime t b := roughPart_coprime_base hnPos
  have hu : Nat.Coprime t u := canonicalClearingCofactor_coprime hnPos hD
  have hbridge := canonicalSynchronizedAlignmentReal_eq_roughAlignment hnPos hD
  rw [hbridge]
  exact ⟨canonicalRoughAlignmentReal_gap hb hbeven h3b htPos hmPos hLPos
      hmSupported hcop hu,
    canonicalRoughAlignmentReal_golden_iff hb hbeven h3b htPos hmPos hLPos
      hmSupported hcop hu,
    canonicalRoughAlignmentReal_eq_three_fifths_iff hb hbeven h3b htPos hmPos
      hLPos hcop hu,
    canonicalRoughAlignmentReal_eq_seven_elevenths_iff hb hbeven h3b htPos
      hmPos hLPos hcop hu⟩

/-- The theorem's final threshold statement, expressed without hidden
canonical factors. -/
theorem canonicalAlignment_ge_golden_iff_supported_or_three_supported
    {b n D : ℕ} (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    goldenReciprocal ≤ canonicalSynchronizedAlignmentReal b n D (by omega) ↔
      Supported b n ∨
        ∃ m : ℕ, n = 3 * m ∧ Supported b m ∧ 4 ≤ m := by
  have hnPos : 0 < n := by omega
  have hcanonical := (canonicalThreeTierGapCertificate hb hbeven h3b hn hD).2.1
  rw [hcanonical]
  constructor
  · rintro (ht1 | ⟨ht3, hm4⟩)
    · exact Or.inl ((roughPart_eq_one_iff_supported hnPos).mp ht1)
    · right
      refine ⟨supportedPart b n, ?_, supportedPart_supported hnPos, hm4⟩
      have hdecomp := roughPart_mul_supportedPart (b := b) hnPos
      rw [ht3] at hdecomp
      exact hdecomp.symm
  · rintro (hnSupported | ⟨m, hn3m, hmSupported, hm4⟩)
    · exact Or.inl ((roughPart_eq_one_iff_supported hnPos).mpr hnSupported)
    · have hmPos : 0 < m := by omega
      have hcop : Nat.Coprime 3 b :=
        Nat.prime_three.coprime_iff_not_dvd.mpr h3b
      have hparts := supported_coprime_decomposition_unique hn3m
        (by norm_num) hmPos hmSupported hcop
      exact Or.inr ⟨hparts.2, by simpa [hparts.1] using hm4⟩

/-- The lower endpoint is attained exactly at denominator six. -/
theorem canonicalAlignment_eq_three_fifths_iff_denominator_six
    {b n D : ℕ} (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    canonicalSynchronizedAlignmentReal b n D (by omega) = (3 : ℝ) / 5 ↔
      n = 6 := by
  have hnPos : 0 < n := by omega
  have hparts := (canonicalThreeTierGapCertificate hb hbeven h3b hn hD).2.2.1
  rw [hparts]
  constructor
  · rintro ⟨ht, hm⟩
    have hdecomp := roughPart_mul_supportedPart (b := b) hnPos
    rw [ht, hm] at hdecomp
    norm_num at hdecomp ⊢
    exact hdecomp.symm
  · rintro rfl
    have htwoSupported : Supported b 2 :=
      supported_of_dvd_base (even_iff_two_dvd.mp hbeven)
    have hcop : Nat.Coprime 3 b :=
      Nat.prime_three.coprime_iff_not_dvd.mpr h3b
    exact supported_coprime_decomposition_unique (n := 6) (t := 3) (m := 2)
      (by norm_num) (by norm_num) (by norm_num) htwoSupported hcop |>.symm

/-- The upper endpoint is attained exactly at denominator twelve. -/
theorem canonicalAlignment_eq_seven_elevenths_iff_denominator_twelve
    {b n D : ℕ} (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (hn : 2 ≤ n) (hD : supportedPart b n ∣ b ^ D) :
    canonicalSynchronizedAlignmentReal b n D (by omega) = (7 : ℝ) / 11 ↔
      n = 12 := by
  have hnPos : 0 < n := by omega
  have hparts := (canonicalThreeTierGapCertificate hb hbeven h3b hn hD).2.2.2
  rw [hparts]
  constructor
  · rintro ⟨ht, hm⟩
    have hdecomp := roughPart_mul_supportedPart (b := b) hnPos
    rw [ht, hm] at hdecomp
    norm_num at hdecomp ⊢
    exact hdecomp.symm
  · rintro rfl
    have htwoSupported : Supported b 2 :=
      supported_of_dvd_base (even_iff_two_dvd.mp hbeven)
    have hfourSupported : Supported b 4 := by
      simpa using supported_mul htwoSupported htwoSupported
    have hcop : Nat.Coprime 3 b :=
      Nat.prime_three.coprime_iff_not_dvd.mpr h3b
    exact supported_coprime_decomposition_unique (n := 12) (t := 3) (m := 4)
      (by norm_num) (by norm_num) (by norm_num) hfourSupported hcop |>.symm

/-- The reciprocal golden ratio lies strictly in the forbidden interval. -/
theorem reciprocalGolden_separating_interval :
    (3 : ℝ) / 5 < goldenReciprocal ∧ goldenReciprocal < (7 : ℝ) / 11 :=
  ⟨three_fifths_lt_goldenReciprocal, goldenReciprocal_lt_seven_elevenths⟩

/-- On the continuous three-core profile, the golden crossing occurs exactly
at `goldenRatio^2`. -/
theorem threeCoreProfile_eq_golden_iff {x : ℝ} (hx : 1 ≤ x) :
    (2 * x - 1) / (3 * x - 1) = goldenReciprocal ↔
      x = goldenRatio ^ 2 := by
  have hden : 3 * x - 1 ≠ 0 := by nlinarith
  constructor
  · intro h
    rw [div_eq_iff hden] at h
    dsimp [goldenReciprocal, goldenRatio] at h ⊢
    nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]
  · rintro rfl
    dsimp [goldenReciprocal, goldenRatio]
    have hden' : 3 * ((1 + Real.sqrt 5) / 2) ^ 2 - 1 ≠ 0 := by
      nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]
    apply (div_eq_iff hden').2
    nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- The concrete canonical decompositions used as examples in the manuscript. -/
theorem decimal_supported_rough_examples :
    supportedPart 10 60 = 20 ∧ roughPart 10 60 = 3 ∧
      supportedPart 10 28 = 4 ∧ roughPart 10 28 = 7 := by
  have h20 : Supported 10 20 := ⟨2, by norm_num⟩
  have h4 : Supported 10 4 := ⟨2, by norm_num⟩
  have h3 : Nat.Coprime 3 10 := by norm_num
  have h7 : Nat.Coprime 7 10 := by norm_num
  have h60 := supported_coprime_decomposition_unique
    (b := 10) (n := 60) (t := 3) (m := 20)
    (by norm_num) (by norm_num) (by norm_num) h20 h3
  have h28 := supported_coprime_decomposition_unique
    (b := 10) (n := 28) (t := 7) (m := 4)
    (by norm_num) (by norm_num) (by norm_num) h4 h7
  exact ⟨h60.1, h60.2, h28.1, h28.2⟩

/-- Outside rough parts one and three, a decimal rough part is at least seven. -/
theorem decimalRoughPart_ge_seven {n : ℕ} (hn : 0 < n)
    (ht1 : roughPart 10 n ≠ 1) (ht3 : roughPart 10 n ≠ 3) :
    7 ≤ roughPart 10 n := by
  have htPos := roughPart_pos (b := 10) hn
  have hcop := roughPart_coprime_base (b := 10) hn
  have ht5 := roughPart_ge_five htPos hcop (by norm_num) ht1 ht3
  have htOdd := roughPart_odd_of_even_base hcop (by norm_num : Even 10)
  by_contra hnot
  rcases htOdd with ⟨q, hq⟩
  have heq : roughPart 10 n = 5 := by omega
  rw [heq] at hcop
  norm_num at hcop

/-- The sharper decimal ceiling outside the supported and three-core cases. -/
theorem decimalAlignment_le_four_sevenths {n D : ℕ} (hn : 2 ≤ n)
    (hD : supportedPart 10 n ∣ 10 ^ D)
    (ht1 : roughPart 10 n ≠ 1) (ht3 : roughPart 10 n ≠ 3) :
    canonicalSynchronizedAlignmentReal 10 n D (by omega) < (4 : ℝ) / 7 := by
  have hnPos : 0 < n := by omega
  have hbound := canonicalSynchronizedAlignmentReal_upper_bound
    (b := 10) (n := n) (D := D) (by norm_num) (by norm_num) hnPos hD ht1
  have htSeven : 7 ≤ roughPart 10 n := decimalRoughPart_ge_seven hnPos ht1 ht3
  have hceil : roughCeilingReal (roughPart 10 n) ≤ (4 : ℝ) / 7 := by
    rw [roughCeilingReal]
    have htPos : (0 : ℝ) < roughPart 10 n := by positivity
    have htSevenR : (7 : ℝ) ≤ roughPart 10 n := by exact_mod_cast htSeven
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * roughPart 10 n)]
    nlinarith
  exact lt_of_le_of_lt hbound.1 (lt_of_lt_of_le hbound.2 hceil)

/-- The only decimal three-core denominators below the second-tier threshold
are three and six. -/
theorem decimalThreeCore_below_four {n : ℕ} (hn : 0 < n)
    (ht : roughPart 10 n = 3) (hm4 : supportedPart 10 n < 4) :
    n = 3 ∨ n = 6 := by
  have hmPos := supportedPart_pos (b := 10) hn
  have hmSupported := supportedPart_supported (b := 10) hn
  have hmNeThree : supportedPart 10 n ≠ 3 := by
    intro hm3
    apply three_not_dvd_supported (b := 10) (m := supportedPart 10 n)
      (by norm_num) hmSupported
    simp [hm3]
  have hmCases : supportedPart 10 n = 1 ∨ supportedPart 10 n = 2 := by omega
  have hdecomp := roughPart_mul_supportedPart (b := 10) hn
  rcases hmCases with hm1 | hm2
  · left
    rw [ht, hm1] at hdecomp
    simpa using hdecomp.symm
  · right
    rw [ht, hm2] at hdecomp
    norm_num at hdecomp ⊢
    exact hdecomp.symm

/-- The exact decimal seven-core family on any valid common clearing depth. -/
theorem decimalSevenCoreAlignmentFormula {m D : ℕ} (hm : 1 ≤ m)
    (hD : m ∣ 10 ^ D) :
    clearedAlignmentReal 10 7 m D (coprimeBasePeriod 10 7 (by norm_num)) =
      alignmentFormulaReal 7 m := by
  rw [clearedAlignmentReal_eq_canonicalRoughAlignmentReal (by norm_num) hm hD,
    canonicalRoughAlignmentReal, if_neg (by norm_num)]
  exact synchronizedCompositeAlignmentReal_eq_digitPartitioningFormula
    (by norm_num) (by norm_num)
      (digitPartitioning_of_le (by norm_num) (by norm_num) (by norm_num))
      ((by norm_num : Nat.Coprime 7 10).pow_right D |>.of_dvd_right
        (Nat.div_dvd_of_dvd hD)) hm (coprimeBasePeriod_pos (by norm_num))

/-- The exact seven-core formula tends to `2/7`. -/
theorem decimalSevenCoreFormula_tendsto :
    Tendsto (alignmentFormulaReal 7) atTop (nhds ((2 : ℝ) / 7)) := by
  convert digitPartitioningAlignmentFormulaReal_tendsto (p := 7) (by norm_num) using 1
  · funext m
    unfold alignmentFormulaReal digitPartitioningAlignmentFormulaReal
    ring
  · norm_num

/-- The universal complement expression approaches its rough ceiling. -/
theorem finiteComplementBoundReal_tendsto {t : ℕ} (ht : 0 < t) :
    Tendsto (finiteComplementBoundReal t) atTop
      (nhds (roughCeilingReal t)) := by
  convert (tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) (-1) (-1) (((t : ℝ) + 1) / 2)
      (d := (t : ℝ)) (by exact_mod_cast ht.ne')) using 1
  · funext m
    unfold finiteComplementBoundReal
    ring
  · unfold roughCeilingReal
    field_simp

/-- In an odd base the middle digit is its own radix complement. -/
theorem oddBase_middleDigit_self_complement {b : ℕ} (hodd : Odd b) :
    b - 1 - ((b - 1) / 2) = (b - 1) / 2 := by
  rcases hodd with ⟨q, rfl⟩
  simp
  omega

/-- Base three and denominator two exhibit an even rough part and a
nonterminating fixed complementary numerator. -/
theorem oddBase_nonterminating_fixed_point_example :
    roughPart 3 2 = 2 ∧
      ¬TerminatesInBase 3 1 2 ∧ 2 - 1 = 1 := by
  have hparts := supported_coprime_decomposition_unique
    (b := 3) (n := 2) (t := 2) (m := 1)
    (by norm_num) (by norm_num) (by norm_num) (supported_one 3) (by norm_num)
  refine ⟨hparts.2, ?_, by norm_num⟩
  rw [canonicalNumerator_terminates_iff (b := 3) (n := 2) (k := 1) (by norm_num),
    hparts.2]
  norm_num

/-- Every odd-base two-core family has synchronized alignment one. -/
theorem oddBase_twoCore_alignment_one {b m D : ℕ}
    (hb : 2 ≤ b) (hodd : Odd b) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedAlignmentReal b 2 m D
        (coprimeBasePeriod b 2
          (Nat.prime_two.coprime_iff_not_dvd.mpr
            ((prime_two_odd_base_degenerate hb hodd).1))) = 1 := by
  have hdeg := prime_two_odd_base_degenerate hb hodd
  have hcop : Nat.Coprime 2 b :=
    Nat.prime_two.coprime_iff_not_dvd.mpr hdeg.1
  change clearedAlignmentReal b 2 m D (coprimeBasePeriod b 2 hcop) = 1
  rw [clearedAlignmentReal_eq_canonicalRoughAlignmentReal (by norm_num) hm hD,
    canonicalRoughAlignmentReal, if_neg (by norm_num)]
  have hformula := synchronizedCompositeAlignmentReal_eq_digitPartitioningFormula
    Nat.prime_two hdeg.1 hdeg.2.1
      ((hcop.pow_right D).of_dvd_right (Nat.div_dvd_of_dvd hD)) hm
      (coprimeBasePeriod_pos hcop)
  change synchronizedCompositeAlignmentReal b 2 m (b ^ D / m)
    (coprimeBasePeriod b 2 hcop) = 1
  rw [hformula]
  simpa [alignmentFormulaReal, digitPartitioningAlignmentFormulaReal] using
    hdeg.2.2 m hm

end NField.Alignment
