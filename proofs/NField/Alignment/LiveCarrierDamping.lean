/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CarrierStateSwitching
import NField.Alignment.DedekindAbelRemainder
import NField.Alignment.PrimeCarrierDamping
import NField.Alignment.PrimeSecondaryCoefficient
import NField.Alignment.SquareLockCarrierMass

/-!
# Live carrier sector

The small-displacement and live carrier families are actual finite sets.  The
full weighted fresh sum splits exactly into those two sectors, and the live
bound follows by the triangle inequality from bounds on the actual full and
removed sums.
-/

namespace NField.Alignment.LiveCarrierDamping

open scoped BigOperators
open NField.Alignment.CarrierStateSwitching
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.ExactSamplingReservoirBridge
open NField.Alignment.PrimeCarrierDamping
open NField.Alignment.PrimeSecondaryCoefficient
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.RademacherThreeTerm
open NField.Alignment.SquareLockCarrierMass

def fullCarrierSet (p : ℕ) : Finset ℕ := Finset.Icc 2 (p - 2)

noncomputable def liveCarrierSet (p : ℕ) : Finset ℕ :=
  (fullCarrierSet p).filter fun k =>
    coefficientSquareLockCutoff p <
      (centeredNaturalResidue (p ^ 2) k).natAbs

noncomputable def removedCarrierSet (p : ℕ) : Finset ℕ :=
  (fullCarrierSet p).filter fun k =>
    (centeredNaturalResidue (p ^ 2) k).natAbs ≤
      coefficientSquareLockCutoff p

/-- Lifetime-weighted fresh collisions in one actual carrier family. -/
noncomputable def carrierFamilyFreshMass
    (p : ℕ) (carriers : Finset ℕ) : ℝ :=
  ∑ X ∈ Finset.Icc 3 (p - 1),
    carrierDwell (p - 1) X *
      (selectedCarrierFresh p carriers X : ℝ)

/-- Common rational coordinate for an arbitrary selected carrier family. -/
noncomputable def carrierFamilyWeightedPairSum
    (p : ℕ) (carriers : Finset ℕ) : ℚ :=
  ∑ X ∈ Finset.Icc 3 (p - 1),
    (((p - 1) / X : ℕ) : ℚ) *
      ∑ k ∈ carriers,
        if 2 ≤ k ∧ k < X ∧ k.Coprime X then
          arithmeticCoefficientDedekindTerm (p ^ 2) X k
        else 0

theorem carrierFamilyFreshMass_eq_weightedPairSum
    (p : ℕ) (carriers : Finset ℕ) :
    carrierFamilyFreshMass p carriers =
      (carrierFamilyWeightedPairSum p carriers : ℝ) := by
  unfold carrierFamilyFreshMass carrierFamilyWeightedPairSum carrierDwell
  push_cast
  apply Finset.sum_congr rfl
  intro X _hX
  congr 1
  unfold selectedCarrierFresh
  rw [Finset.sum_filter, Rat.cast_sum]

/-- Every selected subfamily of the full carrier set has the same exact
Rademacher-slice coordinate as its lifetime-weighted fresh sum. -/
theorem sum_modulusKSlice_eq_carrierFamilyWeightedPairSum
    {p : ℕ} (hp : p.Prime) (carriers : Finset ℕ)
    (hcarriers : carriers ⊆ fullCarrierSet p) :
    (∑ k ∈ carriers, modulusKSlice p k) =
      ((carrierFamilyWeightedPairSum p carriers : ℚ) : ℂ) := by
  classical
  unfold carrierFamilyWeightedPairSum
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hkfull := hcarriers hk
  have hkdata := Finset.mem_Icc.mp hkfull
  have hkp : k < p := by omega
  have hPk : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp (by omega : 0 < k) hkp).symm
  letI : NeZero k := ⟨by omega⟩
  rw [modulusKSlice, dif_neg (by omega : k ≠ 0),
    dif_pos ⟨hkdata.1, hPk⟩]
  rw [show
      (∑ X ∈ Finset.Icc 3 (p - 1),
        ((((p - 1) / X : ℕ) : ℂ) *
          ↑(if 2 ≤ k ∧ k < X ∧ k.Coprime X then
            arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0))) =
      ∑ X ∈ Finset.Ico (k + 1) p,
        ((((p - 1) / X : ℕ) : ℂ) *
          ↑(if X.Coprime k then
            arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0)) by
    calc
      _ = ∑ X ∈ Finset.Icc 3 (p - 1),
          ((((p - 1) / X : ℕ) : ℂ) *
            ↑(if k < X ∧ X.Coprime k then
              arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0)) := by
            apply Finset.sum_congr rfl
            intro X _hX
            simp only [hkdata.1, true_and]
            by_cases hcop : k.Coprime X <;>
              simp [hcop, Nat.coprime_comm]
      _ = ∑ X ∈ Finset.Ico (k + 1) p,
          ((((p - 1) / X : ℕ) : ℂ) *
            ↑(if k < X ∧ X.Coprime k then
              arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0)) := by
            symm
            apply Finset.sum_subset
            · intro X hX
              have hXI := Finset.mem_Ico.mp hX
              simp only [Finset.mem_Icc]
              omega
            · intro X hXwide hXnarrow
              have hXdata := Finset.mem_Icc.mp hXwide
              have hXp : X < p := by omega
              have hnotLower : ¬k + 1 ≤ X := by
                intro hkX
                exact hXnarrow (Finset.mem_Ico.mpr ⟨hkX, hXp⟩)
              simp [show ¬k < X by omega]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro X hX
            have hXI := Finset.mem_Ico.mp hX
            simp [show k < X by omega]]
  apply Finset.sum_congr rfl
  intro X _hX
  have hseq := coefficientDedekindTerm_filter_eq_residueSequence
    (m := k) (c := p ^ 2) (x := X) hkdata.1 hPk
  rw [← hseq]
  split <;> simp_all

theorem carrierFamilyFreshMass_eq_modulusKSlices
    {p : ℕ} (hp : p.Prime) (carriers : Finset ℕ)
    (hcarriers : carriers ⊆ fullCarrierSet p) :
    carrierFamilyFreshMass p carriers =
      (∑ k ∈ carriers, modulusKSlice p k).re := by
  rw [carrierFamilyFreshMass_eq_weightedPairSum,
    sum_modulusKSlice_eq_carrierFamilyWeightedPairSum hp carriers hcarriers]
  norm_num

/-- A rational common coordinate for the full switching ledger and the
smaller-modulus Rademacher slices. -/
noncomputable def fullCarrierWeightedPairSum (p : ℕ) : ℚ :=
  ∑ X ∈ Finset.Icc 3 (p - 1),
    (((p - 1) / X : ℕ) : ℚ) *
      ∑ k ∈ fullCarrierSet p,
        if 2 ≤ k ∧ k < X ∧ k.Coprime X then
          arithmeticCoefficientDedekindTerm (p ^ 2) X k
        else 0

/-- The lifetime-weighted fresh mass of the full carrier family is exactly
the rational pair sum. -/
theorem fullCarrierFreshMass_eq_weightedPairSum (p : ℕ) :
    carrierFamilyFreshMass p (fullCarrierSet p) =
      (fullCarrierWeightedPairSum p : ℝ) := by
  unfold carrierFamilyFreshMass fullCarrierWeightedPairSum carrierDwell
  push_cast
  apply Finset.sum_congr rfl
  intro X _hX
  congr 1
  unfold selectedCarrierFresh
  rw [Finset.sum_filter]
  rw [Rat.cast_sum]

/-- The same rational pair sum is the sum of the concrete complex
smaller-modulus slices.  This is the exact finite reindexing behind the first
equality of the switching ledger. -/
theorem sum_modulusKSlice_eq_weightedPairSum
    {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range p, modulusKSlice p k) =
      ((fullCarrierWeightedPairSum p : ℚ) : ℂ) := by
  classical
  have hrestrict :
      (∑ k ∈ Finset.range p, modulusKSlice p k) =
        ∑ k ∈ fullCarrierSet p, modulusKSlice p k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      simp only [Finset.mem_range]
      omega
    · intro k hkrange hkfull
      have hkp : k < p := Finset.mem_range.mp hkrange
      have hkout : k < 2 ∨ p - 2 < k := by
        simp [fullCarrierSet] at hkfull
        omega
      rcases hkout with hklt | hkgt
      · have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl <;> simp [modulusKSlice]
      · have hkpm : k = p - 1 := by omega
        subst k
        by_cases hp2 : p = 2
        · subst p
          simp [modulusKSlice]
        · have hk0 : p - 1 ≠ 0 := by omega
          have hPk : (p ^ 2).Coprime (p - 1) := by
            exact (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
              hp (by omega : 0 < p - 1) (by omega : p - 1 < p)).symm
          rw [modulusKSlice, dif_neg hk0, dif_pos ⟨by omega, hPk⟩]
          rw [show p - 1 + 1 = p by omega]
          simp
  rw [hrestrict]
  unfold fullCarrierWeightedPairSum
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hkfull
  have hkdata := Finset.mem_Icc.mp hkfull
  have hkp : k < p := by omega
  have hPk : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp (by omega : 0 < k) hkp).symm
  letI : NeZero k := ⟨by omega⟩
  rw [modulusKSlice, dif_neg (by omega : k ≠ 0),
    dif_pos ⟨hkdata.1, hPk⟩]
  rw [show
      (∑ X ∈ Finset.Icc 3 (p - 1),
        ((((p - 1) / X : ℕ) : ℂ) *
          ↑(if 2 ≤ k ∧ k < X ∧ k.Coprime X then
            arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0))) =
      ∑ X ∈ Finset.Ico (k + 1) p,
        ((((p - 1) / X : ℕ) : ℂ) *
          ↑(if X.Coprime k then
            arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0)) by
    calc
      _ = ∑ X ∈ Finset.Icc 3 (p - 1),
          ((((p - 1) / X : ℕ) : ℂ) *
            ↑(if k < X ∧ X.Coprime k then
              arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0)) := by
            apply Finset.sum_congr rfl
            intro X _hX
            simp only [hkdata.1, true_and]
            by_cases hcop : k.Coprime X <;>
              simp [hcop, Nat.coprime_comm]
      _ = ∑ X ∈ Finset.Ico (k + 1) p,
          ((((p - 1) / X : ℕ) : ℂ) *
            ↑(if k < X ∧ X.Coprime k then
              arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0)) := by
            symm
            apply Finset.sum_subset
            · intro X hX
              have hXI := Finset.mem_Ico.mp hX
              simp only [Finset.mem_Icc]
              omega
            · intro X hXwide hXnarrow
              have hXdata := Finset.mem_Icc.mp hXwide
              have hXp : X < p := by omega
              have hnotLower : ¬k + 1 ≤ X := by
                intro hkX
                exact hXnarrow (Finset.mem_Ico.mpr ⟨hkX, hXp⟩)
              have hnot : X ≤ k := by omega
              simp [show ¬k < X by omega]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro X hX
            have hXI := Finset.mem_Ico.mp hX
            simp [show k < X by omega]]
  apply Finset.sum_congr rfl
  intro X hX
  have hseq := coefficientDedekindTerm_filter_eq_residueSequence
    (m := k) (c := p ^ 2) (x := X) hkdata.1 hPk
  rw [← hseq]
  split <;> simp_all

/-- The full switching fresh mass is exactly the real part of the sum of the
Rademacher carrier slices. -/
theorem fullCarrierFreshMass_eq_modulusKSlices
    {p : ℕ} (hp : p.Prime) :
    carrierFamilyFreshMass p (fullCarrierSet p) =
      (∑ k ∈ Finset.range p, modulusKSlice p k).re := by
  rw [fullCarrierFreshMass_eq_weightedPairSum,
    sum_modulusKSlice_eq_weightedPairSum hp]
  norm_num

/-- The manuscript's full lifetime-weighted fresh sum is precisely the
surviving lower-modulus Rademacher reservoir, with its displayed factor
`-8`. -/
theorem lowerModulusReservoir_eq_fullCarrierFreshMass
    {p : ℕ} (hp : p.Prime) :
    lowerModulusReservoir p =
      -8 * carrierFamilyFreshMass p (fullCarrierSet p) := by
  unfold lowerModulusReservoir
  rw [offDiagonalModulusK_eq_slices hp]
  rw [fullCarrierFreshMass_eq_modulusKSlices hp]
  simp

theorem live_union_removed (p : ℕ) :
    liveCarrierSet p ∪ removedCarrierSet p = fullCarrierSet p := by
  ext k
  simp only [liveCarrierSet, removedCarrierSet, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hk
    by_cases hcut : coefficientSquareLockCutoff p <
        (centeredNaturalResidue (p ^ 2) k).natAbs
    · exact Or.inl ⟨hk, hcut⟩
    · exact Or.inr ⟨hk, Nat.le_of_not_gt hcut⟩

theorem live_disjoint_removed (p : ℕ) :
    Disjoint (liveCarrierSet p) (removedCarrierSet p) := by
  rw [Finset.disjoint_left]
  intro k hlive hremoved
  have hl := (Finset.mem_filter.mp hlive).2
  have hr := (Finset.mem_filter.mp hremoved).2
  omega

theorem selectedCarrierFresh_union
    (p X : ℕ) {A B : Finset ℕ} (hAB : Disjoint A B) :
    selectedCarrierFresh p (A ∪ B) X =
      selectedCarrierFresh p A X + selectedCarrierFresh p B X := by
  unfold selectedCarrierFresh
  rw [Finset.filter_union]
  rw [Finset.sum_union]
  exact Finset.disjoint_filter_filter hAB

theorem carrierFamilyFreshMass_union
    (p : ℕ) {A B : Finset ℕ} (hAB : Disjoint A B) :
    carrierFamilyFreshMass p (A ∪ B) =
      carrierFamilyFreshMass p A + carrierFamilyFreshMass p B := by
  unfold carrierFamilyFreshMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro X _hX
  rw [selectedCarrierFresh_union p X hAB]
  push_cast
  ring

/-- Exact full/live/removed sector decomposition. -/
theorem full_live_removed_split (p : ℕ) :
    carrierFamilyFreshMass p (fullCarrierSet p) =
      carrierFamilyFreshMass p (liveCarrierSet p) +
        carrierFamilyFreshMass p (removedCarrierSet p) := by
  rw [← live_union_removed p]
  exact carrierFamilyFreshMass_union p (live_disjoint_removed p)

/-- Uniform prime bound for one actual carrier family. -/
def CarrierFamilyPrimeBound
    (family : ℕ → Finset ℕ) (scale : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime →
    |carrierFamilyFreshMass p (family p)| ≤ C * scale p

/-- The asymptotic form used by the manuscript's live-sector proposition. -/
def CarrierFamilyPrimeEventualBound
    (family : ℕ → Finset ℕ) (scale : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ p,
    threshold ≤ p → p.Prime →
      |carrierFamilyFreshMass p (family p)| ≤ C * scale p

theorem CarrierFamilyPrimeBound.eventual
    {family : ℕ → Finset ℕ} {scale : ℕ → ℝ}
    (h : CarrierFamilyPrimeBound family scale) :
    CarrierFamilyPrimeEventualBound family scale := by
  rcases h with ⟨C, hC, hbound⟩
  exact ⟨C, hC, 0, fun p _hp0 hp => hbound p hp⟩

/-- The all-prime carrier theorem therefore bounds the actual full switching
family, not merely a parallel reservoir coordinate. -/
theorem fullCarrierFamilyBound_from_analytic_inputs
    (hKorolev :
      NField.Alignment.DedekindInverseResidueTransform.KorolevAmbientInverseResidueEstimate) :
    CarrierFamilyPrimeBound fullCarrierSet logarithmicCarrierReservoirScale := by
  rcases (all_prime_carrier_damping_from_analytic_inputs hKorolev).1 with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hrelation := lowerModulusReservoir_eq_fullCarrierFreshMass hp
  have hreservoir := hbound p hp
  have hscale0 : 0 ≤ logarithmicCarrierReservoirScale p := by
    unfold logarithmicCarrierReservoirScale
    exact mul_nonneg (sq_nonneg _) (logarithmicCarrierSamplingScale_nonneg p)
  rw [hrelation, abs_mul] at hreservoir
  norm_num at hreservoir
  nlinarith

theorem removedCarrierSet_subset_smallDisplacement
    {p : ℕ} (hp : p.Prime) :
    removedCarrierSet p ⊆
      smallDisplacementCarriers p (coefficientSquareLockCutoff p) := by
  intro k hk
  have hkdata := Finset.mem_filter.mp hk
  have hkfull := Finset.mem_Icc.mp hkdata.1
  have hkp : k < p := by omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hkfull.1, by omega⟩, ?_, hkdata.2⟩
  exact centeredPrimeSquareResidue_natAbs_pos hp hkfull.1 hkp

/-- Square-lock localization controls the actual removed switching family,
not only the separately defined sum of absolute collar prefixes. -/
theorem abs_removedCarrierFreshMass_le_absoluteCollars
    {p : ℕ} (hp : p.Prime) :
    |carrierFamilyFreshMass p (removedCarrierSet p)| ≤
      ∑ k ∈ smallDisplacementCarriers p (coefficientSquareLockCutoff p),
        carrierAbsoluteCollar p k := by
  have hsubset : removedCarrierSet p ⊆ fullCarrierSet p :=
    Finset.filter_subset _ _
  rw [carrierFamilyFreshMass_eq_modulusKSlices hp _ hsubset]
  calc
    |(∑ k ∈ removedCarrierSet p, modulusKSlice p k).re| =
        |∑ k ∈ removedCarrierSet p, (modulusKSlice p k).re| := by
      rw [Complex.re_sum]
    _ ≤ ∑ k ∈ removedCarrierSet p, |(modulusKSlice p k).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ removedCarrierSet p, carrierAbsoluteCollar p k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkfull := Finset.mem_Icc.mp
        (Finset.mem_filter.mp hk).1
      exact abs_modulusKSlice_re_le_carrierAbsoluteCollar hp hkfull.1
        (by omega)
    _ ≤ ∑ k ∈ smallDisplacementCarriers p
        (coefficientSquareLockCutoff p), carrierAbsoluteCollar p k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (removedCarrierSet_subset_smallDisplacement hp)
      intro k _hkBig _hkSmall
      unfold carrierAbsoluteCollar
      positivity

theorem abs_removedCarrierFreshMass_le_squareLockMass
    {p : ℕ} (hp : p.Prime) :
    |carrierFamilyFreshMass p (removedCarrierSet p)| ≤
      (p : ℝ) ^ 2 / 8 *
        squareLockCollarMass p (coefficientSquareLockCutoff p) := by
  have hraw := abs_removedCarrierFreshMass_le_absoluteCollars hp
  calc
    |carrierFamilyFreshMass p (removedCarrierSet p)| ≤
        ∑ k ∈ smallDisplacementCarriers p
          (coefficientSquareLockCutoff p), carrierAbsoluteCollar p k := hraw
    _ = (p : ℝ) ^ 2 / 8 *
        squareLockCollarMass p (coefficientSquareLockCutoff p) := by
      unfold squareLockCollarMass
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp [hpR]

/-- The exact scale delivered by square-lock localization at the manuscript's
coefficient cutoff, before its elementary logarithmic simplification. -/
noncomputable def coefficientSquareLockRemovedScale (p : ℕ) : ℝ :=
  (p : ℝ) ^ 2 / 8 *
    ((((coefficientSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ) *
        (Real.log (2 * p)) ^ 3) +
      Real.rpow p (-1 / 3 : ℝ) * (Real.log (2 * p)) ^ 3)

theorem coefficientSquareLockRemovedScale_nonneg (p : ℕ) :
    0 ≤ coefficientSquareLockRemovedScale p := by
  by_cases hp : p = 0
  · subst p
    simp [coefficientSquareLockRemovedScale]
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 hp
  have hlog : 0 ≤ Real.log (2 * (p : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * p by omega))
  unfold coefficientSquareLockRemovedScale
  exact mul_nonneg (by positivity)
    (add_nonneg
      (mul_nonneg (by positivity) (pow_nonneg hlog 3))
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (pow_nonneg hlog 3)))

/-- Voronoi square-lock localization bounds the actual removed switching
family at its literal coefficient-cutoff scale. -/
theorem removedCarrierFamilyBound_from_squareLock
    (hcount : SquareLockCountEstimate) :
    CarrierFamilyPrimeEventualBound removedCarrierSet
      coefficientSquareLockRemovedScale := by
  rcases square_lock_localization hcount with ⟨C, hC, hbound⟩
  have hcutEvent := coefficientSquareLockCutoff_valid_eventually
  rw [Filter.eventually_atTop] at hcutEvent
  rcases hcutEvent with ⟨threshold, hcut⟩
  refine ⟨C, hC, threshold, ?_⟩
  intro p hpThreshold hp
  have hcutp := hcut p hpThreshold
  have hremoved := abs_removedCarrierFreshMass_le_squareLockMass hp
  have hlocal := hbound p (coefficientSquareLockCutoff p) hp
    hcutp.1 hcutp.2
  calc
    |carrierFamilyFreshMass p (removedCarrierSet p)| ≤
        (p : ℝ) ^ 2 / 8 *
          squareLockCollarMass p (coefficientSquareLockCutoff p) := hremoved
    _ ≤ (p : ℝ) ^ 2 / 8 *
        (C *
          ((((coefficientSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ) *
              (Real.log (2 * p)) ^ 3) +
            Real.rpow p (-1 / 3 : ℝ) *
              (Real.log (2 * p)) ^ 3)) := by
      gcongr
    _ = C * coefficientSquareLockRemovedScale p := by
      unfold coefficientSquareLockRemovedScale
      ring

/-- The literal coefficient-cutoff localization scale is eventually smaller
than the logarithmic full-carrier scale.  This is the elementary asymptotic
comparison used in the proof of live-sector damping. -/
theorem coefficientSquareLockRemovedScale_le_logarithmic_eventually :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ p,
      threshold ≤ p →
        coefficientSquareLockRemovedScale p ≤
          C * logarithmicCarrierReservoirScale p := by
  have hlogEvent :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 : ℝ)
  have hpowerEvent :=
    (isLittleO_log_rpow_rpow_atTop (r := 2) (s := 1 / 3)
      (by norm_num)).natCast_atTop.bound (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at hlogEvent hpowerEvent
  rcases hlogEvent with ⟨Nlog, hlogEvent⟩
  rcases hpowerEvent with ⟨Npower, hpowerEvent⟩
  refine ⟨4, by norm_num, max (max Nlog Npower) 3, ?_⟩
  intro p hpThreshold
  have hpLog : Nlog ≤ p :=
    (le_max_left Nlog Npower).trans
      ((le_max_left (max Nlog Npower) 3).trans hpThreshold)
  have hpPower : Npower ≤ p :=
    (le_max_right Nlog Npower).trans
      ((le_max_left (max Nlog Npower) 3).trans hpThreshold)
  have hp3 : 3 ≤ p :=
    (le_max_right (max Nlog Npower) 3).trans hpThreshold
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hlog : (2 : ℝ) ≤ Real.log (p : ℝ) := by
    simpa [Function.comp_apply] using hlogEvent p hpLog
  have hlog0 : 0 ≤ Real.log (p : ℝ) := hlog.trans' (by norm_num)
  have hlogPos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le (by norm_num) hlog
  have hlog2 : 0 ≤ Real.log (2 * (p : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * p by omega))
  have hlog2le : Real.log (2 * (p : ℝ)) ≤ 2 * Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpR.ne']
    have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast (show 2 ≤ p by omega) : (2 : ℝ) ≤ p)
    linarith
  have hlogCube : Real.log (2 * (p : ℝ)) ^ 3 ≤
      8 * Real.log (p : ℝ) ^ 3 := by
    calc
      Real.log (2 * (p : ℝ)) ^ 3 ≤
          (2 * Real.log (p : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hlog2 hlog2le 3
      _ = 8 * Real.log (p : ℝ) ^ 3 := by ring
  have hpower : Real.log (p : ℝ) ^ 2 ≤
      Real.rpow (p : ℝ) (1 / 3 : ℝ) := by
    have hraw := hpowerEvent p hpPower
    change ‖Real.rpow (Real.log (p : ℝ)) 2‖ ≤
      1 * ‖Real.rpow (p : ℝ) (1 / 3 : ℝ)‖ at hraw
    have hleft :
        ‖Real.rpow (Real.log (p : ℝ)) (2 : ℝ)‖ =
          Real.log (p : ℝ) ^ 2 := by
      calc
        _ = Real.rpow (Real.log (p : ℝ)) 2 :=
          Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _)
        _ = _ := Real.rpow_two _
    have hright : ‖Real.rpow (p : ℝ) (1 / 3 : ℝ)‖ =
        Real.rpow (p : ℝ) (1 / 3 : ℝ) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hpR.le _)
    rw [hleft, hright] at hraw
    simpa only [one_mul] using hraw
  have hfloor : ((coefficientSquareLockCutoff p : ℕ) : ℝ) ≤
      (p : ℝ) / Real.log (p : ℝ) ^ 2 := by
    unfold coefficientSquareLockCutoff
    exact Nat.floor_le (div_nonneg hpR.le (sq_nonneg _))
  let A : ℝ := ((coefficientSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAlog : A * Real.log (p : ℝ) ^ 2 ≤ 1 := by
    dsimp [A]
    rw [show ((coefficientSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ) *
        Real.log (p : ℝ) ^ 2 =
      (((coefficientSquareLockCutoff p : ℕ) : ℝ) *
        Real.log (p : ℝ) ^ 2) / (p : ℝ) by ring]
    apply (div_le_iff₀ hpR).2
    have := mul_le_mul_of_nonneg_right hfloor (sq_nonneg (Real.log (p : ℝ)))
    calc
      ((coefficientSquareLockCutoff p : ℕ) : ℝ) *
          Real.log (p : ℝ) ^ 2 ≤
        ((p : ℝ) / Real.log (p : ℝ) ^ 2) *
          Real.log (p : ℝ) ^ 2 := this
      _ = (p : ℝ) := by field_simp [hlogPos.ne']
      _ = 1 * (p : ℝ) := by ring
  have htermOne : A * Real.log (2 * (p : ℝ)) ^ 3 ≤
      8 * Real.log (p : ℝ) := by
    calc
      A * Real.log (2 * (p : ℝ)) ^ 3 ≤
          A * (8 * Real.log (p : ℝ) ^ 3) := by gcongr
      _ = 8 * Real.log (p : ℝ) *
          (A * Real.log (p : ℝ) ^ 2) := by ring
      _ ≤ 8 * Real.log (p : ℝ) * 1 := by gcongr
      _ = 8 * Real.log (p : ℝ) := by ring
  have hrpowPos : 0 < Real.rpow (p : ℝ) (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hpR _
  have hrpowProduct : Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
      Real.log (p : ℝ) ^ 2 ≤ 1 := by
    calc
      Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
          Real.log (p : ℝ) ^ 2 ≤
        Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
          Real.rpow (p : ℝ) (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hpower
          (Real.rpow_nonneg hpR.le _)
      _ = Real.rpow (p : ℝ) ((-1 / 3 : ℝ) + 1 / 3) := by
        change (p : ℝ) ^ (-1 / 3 : ℝ) *
          (p : ℝ) ^ (1 / 3 : ℝ) =
            (p : ℝ) ^ ((-1 / 3 : ℝ) + 1 / 3)
        rw [Real.rpow_add hpR]
      _ = 1 := by norm_num
  have htermTwo : Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
      Real.log (2 * (p : ℝ)) ^ 3 ≤ 8 * Real.log (p : ℝ) := by
    have hrpow0 : 0 ≤ Real.rpow (p : ℝ) (-1 / 3 : ℝ) :=
      Real.rpow_nonneg hpR.le _
    calc
      Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
          Real.log (2 * (p : ℝ)) ^ 3 ≤
        Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
          (8 * Real.log (p : ℝ) ^ 3) := by gcongr
      _ = 8 * Real.log (p : ℝ) *
          (Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
            Real.log (p : ℝ) ^ 2) := by ring
      _ ≤ 8 * Real.log (p : ℝ) * 1 := by gcongr
      _ = 8 * Real.log (p : ℝ) := by ring
  have hbracket :
      A * Real.log (2 * (p : ℝ)) ^ 3 +
          Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
            Real.log (2 * (p : ℝ)) ^ 3 ≤
        16 * Real.log (p : ℝ) := by linarith
  have hden : 0 < Real.log (Real.log (3 * (p : ℝ))) := by
    have harg : Real.exp 1 < 3 * (p : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * (p : ℝ) := by exact_mod_cast (show 3 ≤ 3 * p by omega)
    exact Real.log_pos ((Real.lt_log_iff_exp_lt (by positivity)).2 harg)
  have hlog3pos : 0 < Real.log (3 * (p : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 3 * p by omega))
  have hlog3le : Real.log (3 * (p : ℝ)) ≤
      2 * Real.log (p : ℝ) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hpR.ne']
    have hthree := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by exact_mod_cast hp3 : (3 : ℝ) ≤ p)
    linarith
  have hdenLe : Real.log (Real.log (3 * (p : ℝ))) ≤
      2 * Real.log (2 * (p : ℝ)) := by
    have hbasic := Real.log_le_sub_one_of_pos hlog3pos
    have hlogMono : Real.log (p : ℝ) ≤ Real.log (2 * (p : ℝ)) :=
      Real.log_le_log hpR (by nlinarith)
    linarith
  have hlogToScale : Real.log (p : ℝ) ≤
      2 * logarithmicCarrierSamplingScale p := by
    rw [logarithmicCarrierSamplingScale, if_pos (by omega : 2 ≤ p)]
    rw [show 2 * (Real.log (2 * (p : ℝ)) ^ 2 /
        Real.log (Real.log (3 * (p : ℝ)))) =
      (2 * Real.log (2 * (p : ℝ)) ^ 2) /
        Real.log (Real.log (3 * (p : ℝ))) by ring]
    apply (le_div_iff₀ hden).2
    have hlogMono : Real.log (p : ℝ) ≤ Real.log (2 * (p : ℝ)) :=
      Real.log_le_log hpR (by nlinarith)
    calc
      Real.log (p : ℝ) * Real.log (Real.log (3 * (p : ℝ))) ≤
          Real.log (2 * (p : ℝ)) *
            (2 * Real.log (2 * (p : ℝ))) :=
        mul_le_mul hlogMono hdenLe hden.le hlog2
      _ = 2 * Real.log (2 * (p : ℝ)) ^ 2 := by ring
  unfold coefficientSquareLockRemovedScale
  change (p : ℝ) ^ 2 / 8 *
      (A * Real.log (2 * (p : ℝ)) ^ 3 +
        Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
          Real.log (2 * (p : ℝ)) ^ 3) ≤
    4 * logarithmicCarrierReservoirScale p
  unfold logarithmicCarrierReservoirScale
  have hpSq0 : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
  calc
    (p : ℝ) ^ 2 / 8 *
        (A * Real.log (2 * (p : ℝ)) ^ 3 +
          Real.rpow (p : ℝ) (-1 / 3 : ℝ) *
            Real.log (2 * (p : ℝ)) ^ 3) ≤
      (p : ℝ) ^ 2 / 8 * (16 * Real.log (p : ℝ)) := by gcongr
    _ = 2 * ((p : ℝ) ^ 2 * Real.log (p : ℝ)) := by ring
    _ ≤ 4 * ((p : ℝ) ^ 2 * logarithmicCarrierSamplingScale p) := by
      calc
        2 * ((p : ℝ) ^ 2 * Real.log (p : ℝ)) ≤
            2 * ((p : ℝ) ^ 2 *
              (2 * logarithmicCarrierSamplingScale p)) := by gcongr
        _ = 4 * ((p : ℝ) ^ 2 * logarithmicCarrierSamplingScale p) := by ring

/-- The actual removed family is coefficient-negligible at the full-carrier
logarithmic scale. -/
theorem removedCarrierFamilyBound_logarithmic
    (hcount : SquareLockCountEstimate) :
    CarrierFamilyPrimeEventualBound removedCarrierSet
      logarithmicCarrierReservoirScale := by
  rcases removedCarrierFamilyBound_from_squareLock hcount with
    ⟨C₁, hC₁, N₁, hremoved⟩
  rcases coefficientSquareLockRemovedScale_le_logarithmic_eventually with
    ⟨C₂, hC₂, N₂, hscale⟩
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, max N₁ N₂, ?_⟩
  intro p hpN hp
  calc
    |carrierFamilyFreshMass p (removedCarrierSet p)| ≤
        C₁ * coefficientSquareLockRemovedScale p :=
      hremoved p ((le_max_left _ _).trans hpN) hp
    _ ≤ C₁ * (C₂ * logarithmicCarrierReservoirScale p) := by
      exact mul_le_mul_of_nonneg_left
        (hscale p ((le_max_right _ _).trans hpN)) hC₁
    _ = (C₁ * C₂) * logarithmicCarrierReservoirScale p := by ring

/-- Actual live-sector damping. -/
theorem live_sector_damping
    (scale : ℕ → ℝ)
    (hfull : CarrierFamilyPrimeBound fullCarrierSet scale)
    (hremoved : CarrierFamilyPrimeBound removedCarrierSet scale) :
    CarrierFamilyPrimeBound liveCarrierSet scale := by
  rcases hfull with ⟨C₁, hC₁, hfull⟩
  rcases hremoved with ⟨C₂, hC₂, hremoved⟩
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro p hp
  have hsplit := full_live_removed_split p
  have hlive : carrierFamilyFreshMass p (liveCarrierSet p) =
      carrierFamilyFreshMass p (fullCarrierSet p) -
        carrierFamilyFreshMass p (removedCarrierSet p) := by
    linarith
  rw [hlive]
  calc
    |_ - _| ≤ |_| + |_| := abs_sub _ _
    _ ≤ C₁ * scale p + C₂ * scale p :=
      add_le_add (hfull p hp) (hremoved p hp)
    _ = (C₁ + C₂) * scale p := by ring

/-- Eventual version of the exact live/full/removed triangle transfer. -/
theorem live_sector_damping_eventual
    (scale : ℕ → ℝ)
    (hfull : CarrierFamilyPrimeEventualBound fullCarrierSet scale)
    (hremoved : CarrierFamilyPrimeEventualBound removedCarrierSet scale) :
    CarrierFamilyPrimeEventualBound liveCarrierSet scale := by
  rcases hfull with ⟨C₁, hC₁, N₁, hfull⟩
  rcases hremoved with ⟨C₂, hC₂, N₂, hremoved⟩
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, max N₁ N₂, ?_⟩
  intro p hpN hp
  have hsplit := full_live_removed_split p
  have hlive : carrierFamilyFreshMass p (liveCarrierSet p) =
      carrierFamilyFreshMass p (fullCarrierSet p) -
        carrierFamilyFreshMass p (removedCarrierSet p) := by
    linarith
  rw [hlive]
  calc
    |_ - _| ≤ |_| + |_| := abs_sub _ _
    _ ≤ C₁ * scale p + C₂ * scale p :=
      add_le_add (hfull p ((le_max_left _ _).trans hpN) hp)
        (hremoved p ((le_max_right _ _).trans hpN) hp)
    _ = (C₁ + C₂) * scale p := by ring

/-- Complete proved live-sector estimate from the two source-level analytic
inputs used by the manuscript. -/
theorem live_sector_damping_from_analytic_inputs
    (hKorolev :
      NField.Alignment.DedekindInverseResidueTransform.KorolevAmbientInverseResidueEstimate)
    (hcount : SquareLockCountEstimate) :
    CarrierFamilyPrimeEventualBound liveCarrierSet
      logarithmicCarrierReservoirScale :=
  live_sector_damping_eventual logarithmicCarrierReservoirScale
    (fullCarrierFamilyBound_from_analytic_inputs hKorolev).eventual
    (removedCarrierFamilyBound_logarithmic hcount)

/-- Actual interval sum in the open signed-damping problem. -/
noncomputable def signedDedekindIntervalSum
    (k : ℕ) [NeZero k] (β : (ZMod k)ˣ) (start length : ℕ) : ℂ :=
  ∑ a ∈ Finset.Ico start (start + length),
    residueDedekindSequence β a

/-- The manuscript's open signed carrier-damping statement. -/
def SignedDedekindCarrierDamping : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∀ _hk : NeZero k, ∀ β : (ZMod k)ˣ,
    ∀ start length,
      ‖signedDedekindIntervalSum k β start length‖ ≤
        C * (k : ℝ) * Real.log (2 * k)

/-- A signed interval bound gives the manuscript's one-logarithm estimate
for one actual floor-weighted carrier slice. -/
theorem norm_modulusKSlice_le_of_signedDamping
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    {C : ℝ} (hC : 0 ≤ C)
    (hsigned : ∀ k, ∀ _hk : NeZero k, ∀ β : (ZMod k)ˣ,
      ∀ start length,
        ‖signedDedekindIntervalSum k β start length‖ ≤
          C * (k : ℝ) * Real.log (2 * k)) :
    ‖modulusKSlice p k‖ ≤
      2 * C * (p : ℝ) * Real.log (2 * p) := by
  letI : NeZero k := ⟨by omega⟩
  have hPk : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp (by omega : 0 < k) hkp).symm
  let β : (ZMod k)ˣ := ZMod.unitOfCoprime (p ^ 2) hPk
  have hklog : 0 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * k by omega))
  have hprefix : ∀ start length,
      ‖∑ a ∈ Finset.Ico start (start + length),
          residueDedekindSequence β a‖ ≤
        C * (k : ℝ) * Real.log (2 * k) := by
    intro start length
    simpa [signedDedekindIntervalSum] using
      hsigned k (inferInstance : NeZero k) β start length
  have habel := norm_floorWeighted_residueDedekindSequence_le_of_prefix
    hkp β (C * (k : ℝ) * Real.log (2 * k)) (by positivity) hprefix
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
  have hlog : Real.log (2 * (k : ℝ)) ≤ Real.log (2 * (p : ℝ)) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < 2 * k by omega)
    · exact_mod_cast (Nat.mul_le_mul_left 2 (Nat.le_of_lt hkp))
  rw [modulusKSlice, dif_neg (by omega : k ≠ 0), dif_pos ⟨hk, hPk⟩]
  calc
    ‖∑ a ∈ Finset.Ico (k + 1) p,
        (((p - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      2 * (((p - 1) / (k + 1) : ℕ) : ℝ) *
        (C * (k : ℝ) * Real.log (2 * k)) := habel
    _ = 2 * C *
        ((((p - 1) / (k + 1) : ℕ) : ℝ) * (k : ℝ)) *
          Real.log (2 * k) := by ring
    _ ≤ 2 * C * (p : ℝ) * Real.log (2 * p) := by
      have hpLog : 0 ≤ Real.log (2 * (p : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * p by omega))
      gcongr

/-- Signed carrier damping implies the required bound for the actual
surviving lower-modulus reservoir. -/
theorem lowerModulusReservoir_bound_of_signedDamping
    (hsigned : SignedDedekindCarrierDamping) :
    PrimeUniformBound lowerModulusReservoir
      (fun p => (p : ℝ) ^ 2 * Real.log p) := by
  rcases hsigned with ⟨C, hC, hsigned⟩
  refine ⟨32 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro p hp
  have hpLog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hlogSplit : Real.log (2 * (p : ℝ)) =
      Real.log 2 + Real.log p := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by exact_mod_cast hp.ne_zero : (p : ℝ) ≠ 0)]
  have hlog : Real.log (2 * (p : ℝ)) ≤ 2 * Real.log p := by
    rw [hlogSplit]
    linarith
  have hslices := offDiagonalModulusK_eq_slices hp
  have hpoint : ∀ k ∈ Finset.range p,
      ‖modulusKSlice p k‖ ≤
        2 * C * (p : ℝ) * Real.log (2 * p) := by
    intro k hkp
    have hRhs0 : 0 ≤ 2 * C * (p : ℝ) * Real.log (2 * p) := by
      have hp0 : (0 : ℝ) ≤ p := by positivity
      have hlog0 : 0 ≤ Real.log (2 * (p : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * p by
          have := hp.pos
          omega))
      positivity
    by_cases hk : 2 ≤ k
    · exact norm_modulusKSlice_le_of_signedDamping hp hk
        (Finset.mem_range.mp hkp) hC hsigned
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp [modulusKSlice]
        exact hRhs0
      · simp [modulusKSlice]
        exact hRhs0
  have hoff : ‖offDiagonalModulusK p‖ ≤
      16 * C * (p : ℝ) ^ 2 * Real.log (2 * p) := by
    rw [hslices, norm_mul]
    norm_num
    calc
      8 * ‖∑ k ∈ Finset.range p, modulusKSlice p k‖ ≤
        8 * ∑ k ∈ Finset.range p, ‖modulusKSlice p k‖ := by
          gcongr
          exact norm_sum_le _ _
      _ ≤ 8 * ∑ _k ∈ Finset.range p,
          2 * C * (p : ℝ) * Real.log (2 * p) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Finset.sum_le_sum
            intro k hk
            exact hpoint k hk
      _ = 16 * C * (p : ℝ) ^ 2 * Real.log (2 * p) := by
        simp
        ring
  unfold lowerModulusReservoir
  calc
    |(offDiagonalModulusK p).re| ≤ ‖offDiagonalModulusK p‖ :=
      Complex.abs_re_le_norm _
    _ ≤ 16 * C * (p : ℝ) ^ 2 * Real.log (2 * p) := hoff
    _ ≤ 32 * C * ((p : ℝ) ^ 2 * Real.log p) := by
      calc
        16 * C * (p : ℝ) ^ 2 * Real.log (2 * p) ≤
            16 * C * (p : ℝ) ^ 2 * (2 * Real.log p) := by
          gcongr
        _ = 32 * C * ((p : ℝ) ^ 2 * Real.log p) := by ring

/-- The analytic transfer in the conditional theorem is proved from the
exact reservoir decomposition and finite Abel summation. -/
theorem signedDampingSamplingTransfer :
    SignedDedekindCarrierDamping →
      PrimeUniformBound primeSamplingDefect (fun p => Real.log p) := by
  intro hsigned
  rcases lowerModulusReservoir_bound_of_signedDamping hsigned with
    ⟨C, hC, hreservoir⟩
  let C₂ : ℝ := |primeSamplingDefect 2| / Real.log 2
  refine ⟨max (5 + C) C₂, ?_, ?_⟩
  · exact le_max_of_le_left (by positivity)
  · intro p hp
    have hlogTwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpLog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    by_cases hp2 : p = 2
    · subst p
      have hC₂ : C₂ ≤ max (5 + C) C₂ := le_max_right _ _
      dsimp [C₂] at hC₂ ⊢
      calc
        |primeSamplingDefect 2| =
            (|primeSamplingDefect 2| / Real.log 2) * Real.log 2 := by
              field_simp [hlogTwo.ne']
        _ ≤ max (5 + C) (|primeSamplingDefect 2| / Real.log 2) *
            Real.log 2 := mul_le_mul_of_nonneg_right hC₂ hlogTwo.le
    · rw [primeSamplingDefect, dif_pos hp]
      have hbridge := samplingDefect_le_lowerReservoir hp hp2
      have hpReal : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hpR : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hpReal
      have hR := hreservoir p hp
      have hnormalized :
          |lowerModulusReservoir p| / (p : ℝ) ^ 2 ≤ C * Real.log p := by
        apply (div_le_iff₀ hpR).2
        calc
          |lowerModulusReservoir p| ≤
              C * ((p : ℝ) ^ 2 * Real.log p) := hR
          _ = C * Real.log p * (p : ℝ) ^ 2 := by ring
      have hfive : (3 : ℝ) ≤ 5 * Real.log p := by
        nlinarith [Real.log_two_gt_d9]
      calc
        |samplingDefect hp| ≤
            3 + |lowerModulusReservoir p| / (p : ℝ) ^ 2 := hbridge
        _ ≤ 3 + C * Real.log p := by linarith
        _ ≤ (5 + C) * Real.log p := by nlinarith
        _ ≤ max (5 + C) C₂ * Real.log p := by
          gcongr
          exact le_max_left _ _

theorem sampling_conditional_on_signed_damping
    (hsigned : SignedDedekindCarrierDamping) :
    PrimeUniformBound primeSamplingDefect (fun p => Real.log p) :=
  signedDampingSamplingTransfer hsigned

end NField.Alignment.LiveCarrierDamping
