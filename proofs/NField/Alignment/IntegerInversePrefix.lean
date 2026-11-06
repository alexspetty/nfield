/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerInverseResidue
import NField.Alignment.RealBernoulliBoundaryLimits
import NField.Alignment.KloostermanGlobalBound
import NField.Alignment.CompletedPrefixDivisorGrowth

/-! # Completed inverse prefixes with signed numerators and real cutoffs -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerInversePrefix
open scoped BigOperators Topology Classical
open CollisionDedekindPairing RealBernoulliBoundaryLimits IntegerInverseResidue
  DedekindInverseResidueTransform InverseResiduePrefixCompletion

theorem real_sawtooth_neg (x : ℝ) : periodicSawtooth (-x)= -periodicSawtooth x := by
  by_cases hx : Int.fract x=0
  · simp [periodicSawtooth,hx,Int.fract_neg_eq_zero.mpr hx]
  · have hn : Int.fract (-x)≠0 := fun h => hx (Int.fract_neg_eq_zero.mp h)
    rw [periodicSawtooth,if_neg hn,periodicSawtooth,if_neg hx,Int.fract_neg hx]
    ring

def integerRealPrefix (q : ℕ) (r : ℤ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, if n.Coprime q then
    periodicSawtooth ((r:ℝ)*(inverseResidue n q:ℝ)/(q:ℝ)) else 0

theorem integer_real_prefix_nat {q : ℕ} (hq : 0<q) (r : ℕ) (X : ℝ) :
    integerRealPrefix q (r:ℤ) X=inverseResiduePrefix q r ⌊X⌋₊ := by
  unfold integerRealPrefix inverseResiduePrefix
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hcop
  · simpa only [Int.cast_natCast,Nat.cast_mul] using sawtooth_rational (r*inverseResidue n q) q hq
  · rfl

theorem integer_real_prefix_neg (q : ℕ) (r : ℤ) (X : ℝ) :
    integerRealPrefix q (-r) X= -integerRealPrefix q r X := by
  unfold integerRealPrefix
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp only [Int.cast_neg,neg_mul,neg_div,real_sawtooth_neg,neg_zero]

theorem floor_cutoff_bounds {q : ℕ} {X : ℝ} (hX : 1≤X) (hXq : X≤q) :
    1≤⌊X⌋₊ ∧ ⌊X⌋₊≤q := by
  exact ⟨Nat.le_floor (by exact_mod_cast hX),Nat.floor_le_of_le hXq⟩

/-- Title: `Completed inverse prefixes for signed numerators and real cutoffs`. -/
theorem completed_integer_real_prefixes :
    ∃ C : ℝ, 0≤C ∧ ∀ (q : ℕ) (r : ℤ) (X : ℝ),
      2≤q → Int.gcd r (q:ℤ)=1 → 1≤X → X≤q →
      |integerRealPrefix q r X|≤C*(q:ℝ).sqrt*q.divisors.card*
        reciprocalSqrtDivisorSum q*(Real.log (2*q))^2 := by
  obtain ⟨C,hC,hbound⟩ := completed_inverse_prefixes
    KloostermanGlobalBound.weil_estermann_inverse_prefix_estimate
  refine ⟨C,hC,?_⟩
  intro q r X hq hcop hX hXq
  obtain ⟨hfloor,hfloorq⟩ := floor_cutoff_bounds hX hXq
  cases r with
  | ofNat r =>
      change |integerRealPrefix q (r:ℤ) X|≤_
      rw [integer_real_prefix_nat (by omega)]
      exact hbound q r ⌊X⌋₊ hq hcop hfloor hfloorq
  | negSucc r =>
      change |integerRealPrefix q (-((r+1:ℕ):ℤ)) X|≤_
      rw [integer_real_prefix_neg,abs_neg,integer_real_prefix_nat (by omega)]
      exact hbound q (r+1) ⌊X⌋₊ hq hcop hfloor hfloorq

/-- Title: `Square-root prefix exponent for signed numerators and real cutoffs`. -/
theorem completed_integer_real_prefixes_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∃ threshold : ℕ, ∀ (q : ℕ) (r : ℤ) (X : ℝ),
      threshold≤q → 2≤q → Int.gcd r (q:ℤ)=1 → 1≤X → X≤q →
      |integerRealPrefix q r X|≤C*Real.rpow q (1/2+ε) := by
  obtain ⟨C,hC,T,hbound⟩ := CompletedPrefixDivisorGrowth.completed_inverse_prefix_small_power
    (completed_inverse_prefixes KloostermanGlobalBound.weil_estermann_inverse_prefix_estimate) ε hε
  refine ⟨C,hC,T,?_⟩
  intro q r X hT hq hcop hX hXq
  obtain ⟨hfloor,hfloorq⟩ := floor_cutoff_bounds hX hXq
  cases r with
  | ofNat r =>
      change |integerRealPrefix q (r:ℤ) X|≤_
      rw [integer_real_prefix_nat (by omega)]
      exact hbound q r ⌊X⌋₊ hT hq hcop hfloor hfloorq
  | negSucc r =>
      change |integerRealPrefix q (-((r+1:ℕ):ℤ)) X|≤_
      rw [integer_real_prefix_neg,abs_neg,integer_real_prefix_nat (by omega)]
      exact hbound q (r+1) ⌊X⌋₊ hT hq hcop hfloor hfloorq

end NField.Alignment.IntegerInversePrefix
