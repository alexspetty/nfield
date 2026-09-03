/-
Author: Alexander S. Petty
-/

import NField.Alignment.CarrierStateSwitching

/-!
# Square-lock carrier mass

The square-lock selection and collar mass are fixed on the manuscript's
actual prime-square residues and Dedekind prefixes.  Voronoi's divisor count
and the already reduced prefix-height estimate are exposed as named
certificates on these objects; their count-times-height assembly is proved
here.
-/

namespace NField.Alignment.SquareLockCarrierMass

open scoped BigOperators
open NField.Alignment.CarrierStateSwitching
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindFourierMoment
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.RademacherThreeTerm

/-- Least centered residue, using the manuscript's right-closed convention. -/
def centeredNaturalResidue (n k : ℕ) : ℤ :=
  let r := n % k
  if 2 * r ≤ k then (r : ℤ) else (r : ℤ) - (k : ℤ)

theorem centeredPrimeSquareResidue_natAbs_pos
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    0 < (centeredNaturalResidue (p ^ 2) k).natAbs := by
  rw [Int.natAbs_pos]
  have hPk : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp (by omega : 0 < k) hkp).symm
  have hmodNe : p ^ 2 % k ≠ 0 := by
    intro hmod
    have hdvd : k ∣ p ^ 2 := Nat.dvd_of_mod_eq_zero hmod
    have hgcdK : (p ^ 2).gcd k = k :=
      Nat.gcd_eq_right_iff_dvd.mpr hdvd
    have hgcdOne : (p ^ 2).gcd k = 1 := hPk.gcd_eq_one
    omega
  unfold centeredNaturalResidue
  dsimp only
  split_ifs with hhalf
  · exact_mod_cast hmodNe
  · have hmodLt : p ^ 2 % k < k := Nat.mod_lt _ (by omega)
    intro hzero
    have heq : (p ^ 2 % k : ℤ) = (k : ℤ) := sub_eq_zero.mp hzero
    have heqNat : p ^ 2 % k = k := by exact_mod_cast heq
    omega

/-- Carriers whose prime-square displacement lies in the cutoff collar. -/
def smallDisplacementCarriers (p C : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p - 1)).filter fun k =>
    0 < (centeredNaturalResidue (p ^ 2) k).natAbs ∧
      (centeredNaturalResidue (p ^ 2) k).natAbs ≤ C

/-- Absolute collar burden of one actual carrier. -/
noncomputable def carrierAbsoluteCollar (p k : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((p - 1) / (k + 1)),
    |(carrierPrefix p k ((p - 1) / h) : ℝ)|

/-- The manuscript's normalized small-displacement collar mass. -/
noncomputable def squareLockCollarMass (p C : ℕ) : ℝ :=
  8 / (p : ℝ) ^ 2 *
    ∑ k ∈ smallDisplacementCarriers p C, carrierAbsoluteCollar p k

/-- Finite layer-cake identity for a decreasing floor weight.  The vanished
initial prefix is what lets each layer begin at `k + 1`. -/
theorem floorWeighted_eq_prefixLayers
    {N k : ℕ} (hkN : k < N) (f : ℕ → ℚ)
    (hprefix : (∑ a ∈ Finset.Icc 1 k, f a) = 0) :
    (∑ a ∈ Finset.Ico (k + 1) (N + 1),
        (((N / a : ℕ) : ℚ)) * f a) =
      ∑ h ∈ Finset.Icc 1 (N / (k + 1)),
        ∑ a ∈ Finset.Icc 1 (N / h), f a := by
  have hk1 : 0 < k + 1 := by omega
  have hHpos : 0 < N / (k + 1) :=
    Nat.div_pos (by omega : k + 1 ≤ N) hk1
  have hlayer : ∀ h ∈ Finset.Icc 1 (N / (k + 1)),
      (∑ a ∈ Finset.Icc 1 (N / h), f a) =
        ∑ a ∈ Finset.Ico (k + 1) (N + 1),
          if a ≤ N / h then f a else 0 := by
    intro h hh
    have hhdata := Finset.mem_Icc.mp hh
    have hhpos : 0 < h := by omega
    have hkUpper : k ≤ N / h := by
      apply (Nat.le_div_iff_mul_le hhpos).2
      have hmul : h * (k + 1) ≤ N :=
        (Nat.le_div_iff_mul_le hk1).1 hhdata.2
      calc
        k * h ≤ (k + 1) * h := Nat.mul_le_mul_right h (Nat.le_succ k)
        _ = h * (k + 1) := by ring
        _ ≤ N := hmul
    have hUpperN : N / h ≤ N := Nat.div_le_self N h
    have hsplit : Finset.Icc 1 (N / h) =
        Finset.Icc 1 k ∪ Finset.Icc (k + 1) (N / h) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    rw [hsplit, Finset.sum_union]
    · rw [hprefix, zero_add]
      calc
        (∑ a ∈ Finset.Icc (k + 1) (N / h), f a) =
            ∑ a ∈ Finset.Icc (k + 1) (N / h),
              if a ≤ N / h then f a else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [(Finset.mem_Icc.mp ha).2]
        _ = ∑ a ∈ Finset.Ico (k + 1) (N + 1),
              if a ≤ N / h then f a else 0 := by
          apply Finset.sum_subset
          · intro a ha
            have haI := Finset.mem_Icc.mp ha
            simp only [Finset.mem_Ico]
            omega
          · intro a haWide haNarrow
            have haNot : N / h < a := by
              by_contra hnot
              exact haNarrow (Finset.mem_Icc.mpr ⟨by
                exact (Finset.mem_Ico.mp haWide).1, by omega⟩)
            simp [show ¬a ≤ N / h by omega]
    · rw [Finset.disjoint_left]
      intro a haLeft haRight
      have hleft := Finset.mem_Icc.mp haLeft
      have hright := Finset.mem_Icc.mp haRight
      omega
  rw [show
      (∑ h ∈ Finset.Icc 1 (N / (k + 1)),
        ∑ a ∈ Finset.Icc 1 (N / h), f a) =
      ∑ h ∈ Finset.Icc 1 (N / (k + 1)),
        ∑ a ∈ Finset.Ico (k + 1) (N + 1),
          if a ≤ N / h then f a else 0 by
    apply Finset.sum_congr rfl
    intro h hh
    exact hlayer h hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have haI := Finset.mem_Ico.mp ha
  have hapos : 0 < a := by omega
  have hdivLe : N / a ≤ N / (k + 1) :=
    Nat.div_le_div_left haI.1 hk1
  have hinner :
      (∑ h ∈ Finset.Icc 1 (N / (k + 1)),
          if a ≤ N / h then f a else 0) =
        (((N / a : ℕ) : ℚ)) * f a := by
    rw [show
        (∑ h ∈ Finset.Icc 1 (N / (k + 1)),
          if a ≤ N / h then f a else 0) =
        ∑ h ∈ Finset.Icc 1 (N / a), f a by
      calc
        _ = ∑ h ∈ Finset.Icc 1 (N / (k + 1)),
            if h ≤ N / a then f a else 0 := by
          apply Finset.sum_congr rfl
          intro h hh
          have hhpos : 0 < h := by
            have := (Finset.mem_Icc.mp hh).1
            omega
          have hequiv : a ≤ N / h ↔ h ≤ N / a := by
            rw [Nat.le_div_iff_mul_le hhpos,
              Nat.le_div_iff_mul_le hapos, Nat.mul_comm]
          by_cases hcond : a ≤ N / h
          · simp [hcond, hequiv.mp hcond]
          · have hcond' : ¬h ≤ N / a := fun hle => hcond (hequiv.mpr hle)
            simp [hcond, hcond']
        _ = ∑ h ∈ Finset.Icc 1 (N / a),
            if h ≤ N / a then f a else 0 := by
          symm
          apply Finset.sum_subset
          · intro h hh
            have hhI := Finset.mem_Icc.mp hh
            exact Finset.mem_Icc.mpr ⟨hhI.1, hhI.2.trans hdivLe⟩
          · intro h hhWide hhNarrow
            have hhI := Finset.mem_Icc.mp hhWide
            have hnot : N / a < h := by
              by_contra hle
              exact hhNarrow (Finset.mem_Icc.mpr ⟨hhI.1, by omega⟩)
            simp [show ¬h ≤ N / a by omega]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro h hh
          simp [(Finset.mem_Icc.mp hh).2]]
    simp
  rw [hinner]

/-- The Voronoi divisor estimate in the exact carrier-count form consumed by
the localization proof. -/
def SquareLockCountEstimate : Prop :=
  ∃ countConstant : ℝ, 0 ≤ countConstant ∧
    ∀ p C, p.Prime → 1 ≤ C → 2 * C ≤ p →
      ((smallDisplacementCarriers p C).card : ℝ) ≤
        countConstant *
          ((C : ℝ) * Real.log (2 * p) +
            Real.rpow p (2 / 3 : ℝ) * Real.log (2 * p))

/-- The first-moment/Abel prefix estimate in the exact collar form used by
the count-times-height argument. -/
def SquareLockCollarHeightEstimate : Prop :=
  ∃ heightConstant : ℝ, 0 ≤ heightConstant ∧
    ∀ p k, p.Prime → k ∈ Finset.Icc 2 (p - 1) →
      carrierAbsoluteCollar p k ≤
        heightConstant * (p : ℝ) * (Real.log (2 * p)) ^ 2

/-- Every actual collar prefix is bounded by the absolute mass of one
complete Dedekind period. -/
theorem abs_carrierPrefix_le_firstMoment
    {p k X : ℕ} [NeZero k] (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    |(carrierPrefix p k X : ℝ)| ≤ dedekindFirstMoment k := by
  have hpk : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp (by omega : 0 < k) hkp).symm
  let β : (ZMod k)ˣ := ZMod.unitOfCoprime (p ^ 2) hpk
  have hterm (a : ℕ) :
      (((if a.Coprime k then
          arithmeticCoefficientDedekindTerm (p ^ 2) a k else 0 : ℚ) : ℂ)) =
        residueDedekindSequence β a := by
    have ht := coefficientDedekindTerm_filter_eq_residueSequence
      (m := k) (c := p ^ 2) (x := a) hk hpk
    by_cases ha : a.Coprime k
    · rw [if_pos ha]
      rw [dif_pos ha] at ht
      simpa [β] using ht
    · rw [if_neg ha]
      rw [dif_neg ha] at ht
      simpa [β] using ht
  have hprefix :
      (((carrierPrefix p k X : ℚ) : ℂ)) =
        ∑ a ∈ Finset.range (X + 1), residueDedekindSequence β a := by
    unfold carrierPrefix
    push_cast
    calc
      (∑ a ∈ Finset.Icc 1 X,
          (((if a.Coprime k then
              arithmeticCoefficientDedekindTerm (p ^ 2) a k else 0 : ℚ) : ℂ))) =
        ∑ a ∈ Finset.Icc 1 X, residueDedekindSequence β a := by
          apply Finset.sum_congr rfl
          intro a _
          exact hterm a
      _ = ∑ a ∈ Finset.range (X + 1), residueDedekindSequence β a := by
        rw [show Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) by
          ext a
          simp
          omega]
        rw [Finset.sum_insert (by simp)]
        have hzero : residueDedekindSequence β 0 = 0 := by
          unfold residueDedekindSequence
          rw [dif_neg]
          intro hunit
          have hcop : Nat.Coprime 0 k :=
            (ZMod.isUnit_iff_coprime 0 k).mp hunit
          have : k = 1 := by simpa using hcop
          omega
        rw [hzero, zero_add]
  have hnorm := norm_periodic_zeroMean_prefix_le (by omega : 0 < k)
    (residueDedekindSequence β)
    (residueDedekindSequence_periodic β)
    (residueDedekindSequence_sum_period_of_two hk β) (X + 1)
  rw [residueDedekindSequence_norm_period β] at hnorm
  rw [← hprefix] at hnorm
  simpa using hnorm

/-- One concrete floor-weighted Rademacher slice is exactly the sum of its
collar prefixes over all dwell layers. -/
theorem modulusKSlice_re_eq_prefixLayers
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p - 1) :
    (modulusKSlice p k).re =
      ∑ h ∈ Finset.Icc 1 ((p - 1) / (k + 1)),
        (carrierPrefix p k ((p - 1) / h) : ℝ) := by
  have hkp' : k < p := hkp.trans (Nat.sub_lt hp.pos (by omega))
  have hPk : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp (by omega : 0 < k) hkp').symm
  letI : NeZero k := ⟨by omega⟩
  let f : ℕ → ℚ := fun a =>
    if a.Coprime k then
      arithmeticCoefficientDedekindTerm (p ^ 2) a k
    else 0
  have hprefix : (∑ a ∈ Finset.Icc 1 k, f a) = 0 := by
    have hzero := carrierPrefix_self_eq_zero hk hPk
    simpa [carrierPrefix, f] using hzero
  have hlayer := floorWeighted_eq_prefixLayers
    (N := p - 1) (k := k) hkp f hprefix
  have hmodComplex : modulusKSlice p k =
      (((∑ a ∈ Finset.Ico (k + 1) p,
        ((((p - 1) / a : ℕ) : ℚ)) * f a : ℚ)) : ℂ) := by
    rw [modulusKSlice, dif_neg (by omega : k ≠ 0), dif_pos ⟨hk, hPk⟩]
    push_cast
    apply Finset.sum_congr rfl
    intro a _ha
    have hseq := coefficientDedekindTerm_filter_eq_residueSequence
      (m := k) (c := p ^ 2) (x := a) hk hPk
    rw [← hseq]
    unfold f
    split <;> simp_all
  have hlayer' :
      (∑ a ∈ Finset.Ico (k + 1) p,
          (((p - 1) / a : ℕ) : ℚ) * f a) =
        ∑ h ∈ Finset.Icc 1 ((p - 1) / (k + 1)),
          ∑ a ∈ Finset.Icc 1 ((p - 1) / h), f a := by
    simpa [show p - 1 + 1 = p by omega] using hlayer
  have hlayerReal := congrArg (fun q : ℚ => (q : ℝ)) hlayer'
  push_cast at hlayerReal
  rw [hmodComplex]
  norm_num
  rw [hlayerReal]
  apply Finset.sum_congr rfl
  intro h _hh
  unfold carrierPrefix f
  push_cast
  rfl

/-- Hence the absolute value of one floor-weighted carrier slice is bounded
by its absolute collar burden. -/
theorem abs_modulusKSlice_re_le_carrierAbsoluteCollar
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p - 1) :
    |(modulusKSlice p k).re| ≤ carrierAbsoluteCollar p k := by
  rw [modulusKSlice_re_eq_prefixLayers hp hk hkp]
  unfold carrierAbsoluteCollar
  exact Finset.abs_sum_le_sum_abs _ _

/-- The first-moment argument proves the collar-height input used by
square-lock localization, with explicit constant one. -/
theorem squareLockCollarHeightEstimate : SquareLockCollarHeightEstimate := by
  refine ⟨1, by norm_num, ?_⟩
  intro p k hp hk
  have hk2 := (Finset.mem_Icc.mp hk).1
  have hkupper := (Finset.mem_Icc.mp hk).2
  have hkp : k < p := by omega
  letI : NeZero k := ⟨by omega⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcountNat : ((p - 1) / (k + 1)) * k ≤ p := by
    calc
      ((p - 1) / (k + 1)) * k ≤ ((p - 1) / (k + 1)) * (k + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ k)
      _ ≤ p - 1 := Nat.div_mul_le_self _ _
      _ ≤ p := Nat.sub_le _ _
  have hcount :
      ((((p - 1) / (k + 1) : ℕ) : ℝ) * (k : ℝ)) ≤ (p : ℝ) := by
    exact_mod_cast hcountNat
  have hmoment := dedekindFirstMoment_le (by omega : 0 < k)
  have hHkp := harmonic_cast_mono (Nat.le_of_lt hkp)
  have hHk0 : (0 : ℝ) ≤ (harmonic k : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic k by
      unfold harmonic
      positivity)
  have hHp0 : (0 : ℝ) ≤ (harmonic p : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic p by
      unfold harmonic
      positivity)
  have hcollar : carrierAbsoluteCollar p k ≤
      (((p - 1) / (k + 1) : ℕ) : ℝ) * dedekindFirstMoment k := by
    unfold carrierAbsoluteCollar
    calc
      (∑ h ∈ Finset.Icc 1 ((p - 1) / (k + 1)),
          |(carrierPrefix p k ((p - 1) / h) : ℝ)|) ≤
        ∑ _h ∈ Finset.Icc 1 ((p - 1) / (k + 1)),
          dedekindFirstMoment k := by
            apply Finset.sum_le_sum
            intro h _
            exact abs_carrierPrefix_le_firstMoment hp hk2 hkp
      _ = (((p - 1) / (k + 1) : ℕ) : ℝ) * dedekindFirstMoment k := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp
  have hlogMul : Real.log (2 * (p : ℝ)) = Real.log 2 + Real.log p := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (p : ℝ) ≠ 0)]
  have hlogBound : 1 + Real.log (p : ℝ) ≤
      2 * Real.log (2 * (p : ℝ)) := by
    rw [hlogMul]
    have hpLog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
    have htwo : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hHp := harmonic_le_one_add_log p
  have hlog0 : 0 ≤ Real.log (2 * (p : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * p by omega))
  calc
    carrierAbsoluteCollar p k ≤
        (((p - 1) / (k + 1) : ℕ) : ℝ) * dedekindFirstMoment k := hcollar
    _ ≤ (((p - 1) / (k + 1) : ℕ) : ℝ) *
        ((k : ℝ) * (harmonic k : ℝ) ^ 2 / 4) := by gcongr
    _ ≤ (p : ℝ) * (harmonic p : ℝ) ^ 2 / 4 := by
      calc
        _ = (((p - 1) / (k + 1) : ℕ) : ℝ) * (k : ℝ) *
            (harmonic k : ℝ) ^ 2 / 4 := by ring
        _ ≤ (p : ℝ) * (harmonic p : ℝ) ^ 2 / 4 := by gcongr
    _ ≤ (p : ℝ) * (1 + Real.log (p : ℝ)) ^ 2 / 4 := by gcongr
    _ ≤ (p : ℝ) * (Real.log (2 * (p : ℝ))) ^ 2 := by
      nlinarith [sq_nonneg (1 + Real.log (p : ℝ)),
        sq_nonneg (Real.log (2 * (p : ℝ))),
        mul_self_le_mul_self (by linarith : 0 ≤ 1 + Real.log (p : ℝ)) hlogBound]
    _ = 1 * (p : ℝ) * (Real.log (2 * p)) ^ 2 := by ring

/-- Actual square-lock localization, assembled from the cited divisor-count
input and the concrete carrier-height estimate. -/
theorem square_lock_localization
    (hcount : SquareLockCountEstimate) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ p C, p.Prime → 1 ≤ C → 2 * C ≤ p →
        squareLockCollarMass p C ≤
          constant *
            (((C : ℝ) / (p : ℝ)) * (Real.log (2 * p)) ^ 3 +
              Real.rpow p (-1 / 3 : ℝ) *
                (Real.log (2 * p)) ^ 3) := by
  rcases hcount with ⟨C₀, hC₀, hcount⟩
  rcases squareLockCollarHeightEstimate with ⟨C₁, hC₁, hheight⟩
  refine ⟨8 * C₀ * C₁, by positivity, ?_⟩
  intro p C hp hC hpC
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hselected : ∀ k ∈ smallDisplacementCarriers p C,
      k ∈ Finset.Icc 2 (p - 1) := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hsum :
      (∑ k ∈ smallDisplacementCarriers p C,
        carrierAbsoluteCollar p k) ≤
      (smallDisplacementCarriers p C).card *
        (C₁ * (p : ℝ) * (Real.log (2 * p)) ^ 2) := by
    calc
      _ ≤ ∑ _k ∈ smallDisplacementCarriers p C,
          C₁ * (p : ℝ) * (Real.log (2 * p)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact hheight p k hp (hselected k hk)
      _ = _ := by simp
  have hcard := hcount p C hp hC hpC
  have hlog : 0 ≤ Real.log (2 * (p : ℝ)) := by
    have : (1 : ℝ) ≤ 2 * p := by exact_mod_cast (show 1 ≤ 2 * p by omega)
    exact Real.log_nonneg this
  have hpow : 0 ≤ Real.rpow (p : ℝ) (2 / 3 : ℝ) :=
    Real.rpow_nonneg hpR.le _
  unfold squareLockCollarMass
  calc
    8 / (p : ℝ) ^ 2 *
        (∑ k ∈ smallDisplacementCarriers p C,
          carrierAbsoluteCollar p k) ≤
      8 / (p : ℝ) ^ 2 *
        ((smallDisplacementCarriers p C).card *
          (C₁ * (p : ℝ) * (Real.log (2 * p)) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 8 / (p : ℝ) ^ 2 *
        (C₀ * ((C : ℝ) * Real.log (2 * p) +
          Real.rpow p (2 / 3 : ℝ) * Real.log (2 * p)) *
          (C₁ * (p : ℝ) * (Real.log (2 * p)) ^ 2)) := by
        gcongr
    _ = 8 * C₀ * C₁ *
          (((C : ℝ) / (p : ℝ)) * (Real.log (2 * p)) ^ 3 +
            Real.rpow p (-1 / 3 : ℝ) *
              (Real.log (2 * p)) ^ 3) := by
      have hrpow : Real.rpow (p : ℝ) (2 / 3 : ℝ) / (p : ℝ) =
          Real.rpow (p : ℝ) (-1 / 3 : ℝ) := by
        calc
          Real.rpow (p : ℝ) (2 / 3 : ℝ) / (p : ℝ) =
              Real.rpow (p : ℝ) (2 / 3 : ℝ) /
                Real.rpow (p : ℝ) 1 := by
            rw [show Real.rpow (p : ℝ) 1 = (p : ℝ) from
              Real.rpow_one (p : ℝ)]
          _ = Real.rpow (p : ℝ) ((2 / 3 : ℝ) - 1) :=
            (Real.rpow_sub hpR _ _).symm
          _ = Real.rpow (p : ℝ) (-1 / 3 : ℝ) := by
            congr 1
            ring
      rw [← hrpow]
      field_simp [hpR.ne']

/-- The two manuscript cutoffs. -/
noncomputable def fineSquareLockCutoff (p : ℕ) : ℕ :=
  Nat.floor ((p : ℝ) / (Real.log p) ^ 4)

noncomputable def coefficientSquareLockCutoff (p : ℕ) : ℕ :=
  Nat.floor ((p : ℝ) / (Real.log p) ^ 2)

/-- The coefficient cutoff lies in the range required by square-lock
localization for every sufficiently large natural index.  This discharges
the two cutoff side conditions in the manuscript's asymptotic corollary. -/
theorem coefficientSquareLockCutoff_valid_eventually :
    ∀ᶠ p : ℕ in Filter.atTop,
      1 ≤ coefficientSquareLockCutoff p ∧
        2 * coefficientSquareLockCutoff p ≤ p := by
  have hsmall :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).natCast_atTop.bound
      (by norm_num : (0 : ℝ) < 1)
  have hlog :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 : ℝ)
  filter_upwards [hsmall, hlog] with p hsmall hlog
  change (2 : ℝ) ≤ Real.log (p : ℝ) at hlog
  have hp0 : 0 < p := by
    by_contra hp
    have : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    norm_num at hlog
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hlog0 : 0 ≤ Real.log (p : ℝ) := hlog.trans' (by norm_num)
  have hlogSqPos : 0 < Real.log (p : ℝ) ^ 2 := sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hlog)
  have hsmall' : Real.log (p : ℝ) ^ 2 ≤ (p : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_pos hpR,
      Function.comp_apply] using hsmall
  have honeReal : (1 : ℝ) ≤ (p : ℝ) / Real.log (p : ℝ) ^ 2 := by
    apply (le_div_iff₀ hlogSqPos).2
    simpa using hsmall'
  have hone : 1 ≤ coefficientSquareLockCutoff p := by
    unfold coefficientSquareLockCutoff
    apply Nat.le_floor
    norm_num
    exact honeReal
  have hfloor :
      ((coefficientSquareLockCutoff p : ℕ) : ℝ) ≤
        (p : ℝ) / Real.log (p : ℝ) ^ 2 := by
    unfold coefficientSquareLockCutoff
    exact Nat.floor_le (div_nonneg hpR.le (sq_nonneg _))
  have hlogSq : (2 : ℝ) ≤ Real.log (p : ℝ) ^ 2 := by nlinarith
  have hratio :
      2 * ((coefficientSquareLockCutoff p : ℕ) : ℝ) ≤ (p : ℝ) := by
    calc
      2 * ((coefficientSquareLockCutoff p : ℕ) : ℝ) ≤
          2 * ((p : ℝ) / Real.log (p : ℝ) ^ 2) := by gcongr
      _ ≤ (p : ℝ) := by
        rw [show 2 * ((p : ℝ) / Real.log (p : ℝ) ^ 2) =
          (2 * (p : ℝ)) / Real.log (p : ℝ) ^ 2 by ring]
        apply (div_le_iff₀ hlogSqPos).2
        nlinarith
  have hhalf : 2 * coefficientSquareLockCutoff p ≤ p := by
    exact_mod_cast hratio
  exact ⟨hone, hhalf⟩

/-- Direct specialization of the actual localization theorem at the two
named cutoffs. -/
theorem two_localization_scales
    (hcount : SquareLockCountEstimate)
    {p : ℕ} (hp : p.Prime)
    (hfineOne : 1 ≤ fineSquareLockCutoff p)
    (hfineHalf : 2 * fineSquareLockCutoff p ≤ p)
    (hcoefficientOne : 1 ≤ coefficientSquareLockCutoff p)
    (hcoefficientHalf : 2 * coefficientSquareLockCutoff p ≤ p) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      squareLockCollarMass p (fineSquareLockCutoff p) ≤
        constant *
          (((fineSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ) *
              (Real.log (2 * p)) ^ 3 +
            Real.rpow p (-1 / 3 : ℝ) * (Real.log (2 * p)) ^ 3) ∧
      squareLockCollarMass p (coefficientSquareLockCutoff p) ≤
        constant *
          (((coefficientSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ) *
              (Real.log (2 * p)) ^ 3 +
            Real.rpow p (-1 / 3 : ℝ) * (Real.log (2 * p)) ^ 3) := by
  rcases square_lock_localization hcount with ⟨C, hC, hbound⟩
  exact ⟨C, hC,
    hbound p (fineSquareLockCutoff p) hp hfineOne hfineHalf,
    hbound p (coefficientSquareLockCutoff p) hp
      hcoefficientOne hcoefficientHalf⟩

end NField.Alignment.SquareLockCarrierMass
