/-
Author: Alexander S. Petty
-/

import NField.Alignment.CoprimeEulerMass
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The secondary capacity ledger

Finite reduced-ratio coordinates for the continuous Bernoulli capacity.  The
module isolates the exact floor defect from the analytic estimates used to
evaluate it.
-/

namespace NField.Alignment.SecondaryCapacityLedger

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open NField.Alignment.CoprimeEulerMass

/-- The reciprocal sum over reduced numerators below `k`. -/
noncomputable def reducedHarmonicStar (k : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Ico 1 k).filter fun a => a.Coprime k, (a : ℝ)⁻¹

/-- The finite reduced Euler mass through denominator `N`. -/
noncomputable def reducedEulerPartialMass (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, reducedHarmonicStar k / (k : ℝ) ^ 2

/-- The complementary Euler mass after denominator `N`. -/
noncomputable def reducedEulerTailMass (N : ℕ) : ℝ :=
  1 - reducedEulerPartialMass N

/-- The denominator-first reduced Euler mass is exactly the pair mass used by
the Calkin--Wilf telescoping proof. -/
theorem reducedEulerPartialMass_eq_pairWeight_sum (N : ℕ) :
    reducedEulerPartialMass N =
      ∑ ka ∈ reducedEulerPairs N, pairWeight ka := by
  classical
  unfold reducedEulerPartialMass reducedHarmonicStar reducedEulerPairs
    pairWeight eulerPairWeight
  simp_rw [Finset.sum_filter]
  change
    (∑ k ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Ico 1 k, if a.Coprime k then (a : ℝ)⁻¹ else 0) /
        (k : ℝ) ^ 2) =
      ∑ ka ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        if 0 < ka.1 ∧ ka.1 < ka.2 ∧ ka.1.Coprime ka.2 then
          1 / ((ka.1 : ℝ) * (ka.2 : ℝ) ^ 2) else 0
  rw [Finset.sum_product, Finset.sum_comm]
  have hIcc : Finset.Icc 2 N =
      (Finset.range (N + 1)).filter fun k => 2 ≤ k := by
    ext k
    simp
    omega
  rw [hIcc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk2 : 2 ≤ k
  · have hkN : k ≤ N := by
      simp only [Finset.mem_range] at hk
      omega
    simp only [hk2, if_true]
    have hIco : Finset.Ico 1 k =
        (Finset.range (N + 1)).filter fun a => 0 < a ∧ a < k := by
      ext a
      simp
      omega
    rw [hIco]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases hpos : 0 < a ∧ a < k
    · by_cases hcop : a.Coprime k
      · simp [hpos.1, hpos.2]
        rw [if_pos hcop, if_pos hcop]
        simp [div_eq_mul_inv, mul_comm]
      · simp [hpos, hcop]
    · have hcond : ¬(0 < a ∧ a < k ∧ a.Coprime k) := by
        intro h
        exact hpos ⟨h.1, h.2.1⟩
      simp [hpos, hcond]
  · simp only [hk2, if_false]
    symm
    apply Finset.sum_eq_zero
    intro a _ha
    have hcond : ¬(0 < a ∧ a < k ∧ a.Coprime k) := by omega
    simp [hcond]

/-- The finite Euler tail is the positive Calkin--Wilf frontier potential. -/
theorem reducedEulerTailMass_eq_frontier
    {N : ℕ} (hN : 2 ≤ N) :
    reducedEulerTailMass N = eulerFrontierPotential N := by
  unfold reducedEulerTailMass
  rw [reducedEulerPartialMass_eq_pairWeight_sum,
    reducedEulerPairs_weight_sum_eq_one_sub_frontier hN]
  ring

/-- The exact reduced-ratio normal form of three times the continuous
capacity. -/
noncomputable def continuousCapacity (N : ℕ) : ℝ :=
  ((N : ℝ) + 2 * ∑ k ∈ Finset.Icc 2 N,
    (((N / k : ℕ) : ℝ) / (k : ℝ)) * reducedHarmonicStar k) / 3

/-- The fractional-floor term retained by the secondary calculation. -/
noncomputable def fractionalFloorTerm (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N,
    (((N % k : ℕ) : ℝ) / (k : ℝ) ^ 2) * reducedHarmonicStar k

/-- Manuscript Lemma `Reduced-ratio capacity`, in the exact reduced-pair
normal form. -/
theorem reduced_ratio_capacity (N : ℕ) :
    3 * continuousCapacity N =
      (N : ℝ) + 2 * ∑ k ∈ Finset.Icc 2 N,
        (((N / k : ℕ) : ℝ) / (k : ℝ)) * reducedHarmonicStar k := by
  unfold continuousCapacity
  ring

/-- One floor weight splits exactly into its continuous mass and remainder
fraction. -/
theorem floor_weight_split
    {N k : ℕ} (hk : 0 < k) :
    (((N / k : ℕ) : ℝ) / (k : ℝ)) =
      (N : ℝ) / (k : ℝ) ^ 2 -
        ((N % k : ℕ) : ℝ) / (k : ℝ) ^ 2 := by
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdivision := Nat.mod_add_div N k
  have hdivisionℝ := congrArg (fun n : ℕ => (n : ℝ)) hdivision
  simp only [Nat.cast_add, Nat.cast_mul] at hdivisionℝ
  field_simp [hkℝ]
  linear_combination hdivisionℝ

/-- Manuscript Proposition `Exact continuous-defect ledger`. -/
theorem exact_continuous_defect_ledger (N : ℕ) :
    (N : ℝ) - continuousCapacity N =
      (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N +
        (2 / 3 : ℝ) * fractionalFloorTerm N := by
  classical
  have hsplit :
      (∑ k ∈ Finset.Icc 2 N,
          (((N / k : ℕ) : ℝ) / (k : ℝ)) * reducedHarmonicStar k) =
        (N : ℝ) * reducedEulerPartialMass N - fractionalFloorTerm N := by
    unfold reducedEulerPartialMass fractionalFloorTerm
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [floor_weight_split (by omega : 0 < k)]
    ring
  unfold continuousCapacity reducedEulerTailMass
  rw [hsplit]
  ring

/-- The Calkin--Wilf theorem already proved in the library is the manuscript's
coprime Euler sum: every reduced pair `a < k` contributes `1/(a k^2)`, and
the increasing finite masses converge to one. -/
theorem coprime_euler_sum :
    Filter.Tendsto
      (fun N => ∑ ak ∈ reducedEulerPairs N, pairWeight ak)
      Filter.atTop (nhds 1) :=
  tendsto_reducedEulerPairs_weight_sum_one

/-- An explicit eventual error bound, used instead of informal big-O prose in
the companion. -/
def EventualErrorBound
    (value main scale : ℕ → ℝ) : Prop :=
  ∃ constant : ℝ, 0 ≤ constant ∧ ∃ threshold : ℕ,
    ∀ N, threshold ≤ N →
      |value N - main N| ≤ constant * scale N

/-- Scaling an explicit error bound scales both its main term and error
envelope. -/
theorem EventualErrorBound.const_mul
    {value main scale : ℕ → ℝ}
    (h : EventualErrorBound value main scale) (c : ℝ) :
    EventualErrorBound
      (fun N => c * value N) (fun N => c * main N)
      (fun N => |c| * scale N) := by
  rcases h with ⟨C, hC, N₀, hbound⟩
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN
  rw [← mul_sub, abs_mul]
  calc
    |c| * |value N - main N| ≤ |c| * (C * scale N) := by
      gcongr
      exact hbound N hN
    _ = C * (|c| * scale N) := by ring

/-- The main term of the reduced fractional-floor contribution before the
factor `2/3` in the continuous defect ledger. -/
noncomputable def fractionalFloorMain (N : ℕ) : ℝ :=
  (1 / (4 * Real.pi ^ 2 / 6) : ℝ) * Real.log N ^ 2

/-- The continuous capacity main term after the exact defect ledger is
assembled. -/
noncomputable def continuousCapacityMain (N : ℕ) : ℝ :=
  (N : ℝ) - (Real.pi ^ 2)⁻¹ * Real.log N ^ 2

/-- The evaluated fractional-floor term and the elementary Euler tail imply
the continuous secondary coefficient.  These are the two analytic inputs
used by the manuscript; the combination itself is proved here from the exact
finite ledger. -/
theorem continuous_secondary_coefficient_of_fractional_and_tail
    (scale : ℕ → ℝ) (hscale : ∀ N, 0 ≤ scale N)
    (hfractional : EventualErrorBound fractionalFloorTerm
      fractionalFloorMain scale)
    (htail : EventualErrorBound
      (fun N => (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N)
      (fun _ => 0) scale) :
    EventualErrorBound continuousCapacity continuousCapacityMain scale := by
  rcases hfractional with ⟨C₁, hC₁, N₁, hfrac⟩
  rcases htail with ⟨C₂, hC₂, N₂, htail⟩
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, max N₁ N₂, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  have hF := hfrac N hN₁
  have hT := htail N hN₂
  simp only [sub_zero] at hT
  have hledger := exact_continuous_defect_ledger N
  rw [show continuousCapacity N =
      (N : ℝ) -
        (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N -
        (2 / 3 : ℝ) * fractionalFloorTerm N by
    linear_combination -hledger]
  unfold continuousCapacityMain
  unfold fractionalFloorMain at hF
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcoefficient :
      (2 / 3 : ℝ) * (1 / (4 * Real.pi ^ 2 / 6) : ℝ) =
        (Real.pi ^ 2)⁻¹ := by
    field_simp [hpi]
    ring
  rw [show
    (N : ℝ) -
          (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N -
            (2 / 3 : ℝ) * fractionalFloorTerm N -
        ((N : ℝ) - (Real.pi ^ 2)⁻¹ * Real.log N ^ 2) =
      -((2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N) -
        (2 / 3 : ℝ) *
          (fractionalFloorTerm N -
            (1 / (4 * Real.pi ^ 2 / 6) : ℝ) * Real.log N ^ 2) by
    field_simp [hpi]
    ring]
  calc
    |-((2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N) -
        (2 / 3 : ℝ) *
          (fractionalFloorTerm N -
            (1 / (4 * Real.pi ^ 2 / 6) : ℝ) * Real.log N ^ 2)| ≤
      |(2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N| +
        (2 / 3 : ℝ) *
          |fractionalFloorTerm N -
            (1 / (4 * Real.pi ^ 2 / 6) : ℝ) * Real.log N ^ 2| := by
        calc
          _ ≤ |-((2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N)| +
              |(2 / 3 : ℝ) *
                (fractionalFloorTerm N -
                  (1 / (4 * Real.pi ^ 2 / 6) : ℝ) *
                    Real.log N ^ 2)| := abs_sub _ _
          _ = _ := by norm_num [abs_mul]
    _ ≤ C₂ * scale N + (2 / 3 : ℝ) * (C₁ * scale N) := by
          gcongr
    _ ≤ (C₁ + C₂) * scale N := by
          have hs := hscale N
          nlinarith

/-- Multiplying the continuous capacity by three gives the square-box GCD and
LCM secondary term with the same explicit remainder scale. -/
theorem gcd_lcm_secondary_term
    (J : ℕ → ℝ)
    (h : EventualErrorBound J
      (fun N => (N : ℝ) - (Real.pi ^ 2)⁻¹ * Real.log N ^ 2)
      (fun N => Real.rpow (Real.log N) (5 / 3 : ℝ))) :
    EventualErrorBound (fun N => 3 * J N)
      (fun N => 3 * (N : ℝ) - 3 * (Real.pi ^ 2)⁻¹ * Real.log N ^ 2)
      (fun N => 3 * Real.rpow (Real.log N) (5 / 3 : ℝ)) := by
  simpa [mul_sub, mul_assoc] using h.const_mul 3

end NField.Alignment.SecondaryCapacityLedger
