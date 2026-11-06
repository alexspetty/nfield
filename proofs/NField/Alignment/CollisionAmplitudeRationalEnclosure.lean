/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMultipleTailDisplay
import NField.Alignment.CollisionRationalZetaTail
import NField.Alignment.CollisionFourierEnclosure
import NField.Alignment.CollisionAmplitudeRefinement
import NField.Alignment.CollisionAmplitudeMobiusSeries
import NField.Alignment.CollisionInverseRationalBound

/-! Rational full-amplitude and harmonic-seed enclosures. Initial amplitude
bounds come from the independently proved positive period-mass tail. The
Jordan budget then evaluates the actual harmonic seed with explicit bounds. -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionAmplitudeRationalEnclosure
open scoped BigOperators
open CollisionHarmonicSeed CollisionAmplitudeArithmetic CollisionAmplitudeRefinement
open CollisionJordanVariance CollisionRemainderDynamics CollisionMassReadout
open CollisionInverseRationalBound CollisionFourierEnclosure CollisionRationalZetaTail
open CollisionAmplitudeEnclosure CollisionMultipleTailDisplay

def seedPrefix (q M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (M+1), if q ∣ n then harmonicKernel n else 0

theorem harmonicSeed_nonneg (q : ℕ) : 0 ≤ harmonicSeed q :=
  tsum_nonneg (fun n => harmonicKernel_nonneg (q*n))

theorem harmonicSeed_subseries {q : ℕ} (hq : 0 < q) :
    harmonicSeed q = ∑' n, if q ∣ n then harmonicKernel n else 0 := by
  rw [harmonicSeed,tsum_multiples hq]

theorem harmonicSeed_subseries_summable (q : ℕ) :
    Summable (fun n => if q ∣ n then harmonicKernel n else 0) := by
  apply Summable.of_nonneg_of_le _ _ harmonicKernel_hasSum.summable
  · intro n; split_ifs <;> simp [harmonicKernel_nonneg]
  · intro n; split_ifs <;> simp [harmonicKernel_nonneg]

theorem harmonicSeed_le_zetaThree {q : ℕ} (hq : 0 < q) :
    harmonicSeed q ≤ zetaThree := by
  rw [harmonicSeed_subseries hq]
  have hs := harmonicSeed_subseries_summable q
  have h := hs.tsum_le_tsum (fun n => show (if q ∣ n then harmonicKernel n else 0) ≤ harmonicKernel n by
    split_ifs <;> simp [harmonicKernel_nonneg]) harmonicKernel_hasSum.summable
  exact h.trans_eq harmonicKernel_hasSum.tsum_eq

theorem seedPrefix_le {q : ℕ} (hq : 0 < q) (M : ℕ) :
    seedPrefix q M ≤ harmonicSeed q := by
  rw [harmonicSeed_subseries hq]
  exact (harmonicSeed_subseries_summable q).sum_le_tsum _
    (fun n _ => by change 0 ≤ if q ∣ n then harmonicKernel n else 0; split_ifs <;> simp [harmonicKernel_nonneg])

theorem amplitude_binary_majorant {q b : ℕ} (hq : 2 ≤ q) (hb : 2*q ≤ 2^b) :
    amplitude q ≤ 4*(1+(b : ℝ))/(q : ℝ)^2 := by
  have ha := amplitude_four_log_bound hq
  have hl := log_le_binary_bound (by omega : 1 ≤ q) hb
  unfold CollisionPositiveLogTail.positiveLogKernel at ha
  apply ha.trans
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg (q : ℝ))

def jordanBudget (q : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ d ∈ q.divisors, jordanThree d*v d

theorem jordanBudget_interval {q : ℕ} (L U : ℕ → ℝ)
    (hL : ∀ d ∈ q.divisors, 0 ≤ L d)
    (hv : ∀ d ∈ q.divisors, L d ≤ amplitude d ∧ amplitude d ≤ U d) :
    0 ≤ jordanBudget q L ∧ jordanBudget q L ≤ jordanBudget q amplitude ∧
    jordanBudget q amplitude ≤ jordanBudget q U := by
  refine ⟨Finset.sum_nonneg (fun d hd => ?_),?_,?_⟩
  · exact mul_nonneg (jordanThree_pos (Nat.pos_of_mem_divisors hd)).le (hL d hd)
  · exact Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hv d hd).1
      (jordanThree_pos (Nat.pos_of_mem_divisors hd)).le)
  · exact Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hv d hd).2
      (jordanThree_pos (Nat.pos_of_mem_divisors hd)).le)

theorem seed_budget_identity {q : ℕ} (hq : 0 < q) :
    harmonicSeed q = zetaThree*jordanBudget q amplitude/(q : ℝ)^3 := by
  rw [jordanBudget,amplitude_jordan_budget hq]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp [hqR,zetaThree_pos.ne']

theorem seed_budget_enclosure {q : ℕ} (hq : 0 < q) {zl zh : ℝ}
    (hz : zl ≤ zetaThree ∧ zetaThree ≤ zh) (L U : ℕ → ℝ)
    (hL : ∀ d ∈ q.divisors, 0 ≤ L d)
    (hv : ∀ d ∈ q.divisors, L d ≤ amplitude d ∧ amplitude d ≤ U d) :
    zl*jordanBudget q L/(q : ℝ)^3 ≤ harmonicSeed q ∧
    harmonicSeed q ≤ zh*jordanBudget q U/(q : ℝ)^3 := by
  have hb := jordanBudget_interval L U hL hv
  have hza : 0 ≤ zh := zetaThree_pos.le.trans hz.2
  have hba : 0 ≤ jordanBudget q amplitude := hb.1.trans hb.2.1
  rw [seed_budget_identity hq]
  constructor
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact (mul_le_mul_of_nonneg_right hz.1 hb.1).trans
      (mul_le_mul_of_nonneg_left hb.2.1 zetaThree_pos.le)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact (mul_le_mul_of_nonneg_right hz.2 hba).trans
      (mul_le_mul_of_nonneg_left hb.2.2 hza)

theorem seed_prefix_tail_enclosure {q : ℕ} (hq : 0 < q) (M : ℕ) {l u : ℝ}
    (hf : l ≤ harmonicSeed q ∧ harmonicSeed q ≤ u) :
    max (seedPrefix q M) l ≤ harmonicSeed q ∧ harmonicSeed q ≤ u ∧
    0 ≤ harmonicSeed q-seedPrefix q M ∧
    harmonicSeed q-seedPrefix q M ≤ u-seedPrefix q M := by
  have hp := seedPrefix_le hq M
  exact ⟨max_le hp hf.1,hf.2,sub_nonneg.mpr hp,sub_le_sub_right hf.2 _⟩

def signedLower (c l u : ℝ) : ℝ := min (c*l) (c*u)
def signedUpper (c l u : ℝ) : ℝ := max (c*l) (c*u)

theorem signed_interval {x l u : ℝ} (c : ℝ) (hx : l ≤ x ∧ x ≤ u) :
    signedLower c l u ≤ c*x ∧ c*x ≤ signedUpper c l u :=
  scale_between hx (min_le_left _ _) (min_le_right _ _) (le_max_left _ _) (le_max_right _ _)

def refinementLower (q : ℕ) (L U : ℕ → ℝ) : ℝ :=
  ∑ d ∈ q.divisors, signedLower ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3) (L (q/d)) (U (q/d))
def refinementUpper (q : ℕ) (L U : ℕ → ℝ) : ℝ :=
  ∑ d ∈ q.divisors, signedUpper ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3) (L (q/d)) (U (q/d))

theorem refinement_numerator_interval {q : ℕ} (hq : 0 < q) (L U : ℕ → ℝ)
    (hf : ∀ d ∈ q.divisors, L d ≤ harmonicSeed d ∧ harmonicSeed d ≤ U d) :
    refinementLower q L U ≤
      (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d)) ∧
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/d)) ≤
      refinementUpper q L U := by
  have h (d : ℕ) (hd : d ∈ q.divisors) :=
    signed_interval ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3)
      (hf (q/d) (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd),hq.ne'⟩))
  exact ⟨Finset.sum_le_sum (fun d hd => (h d hd).1),
    Finset.sum_le_sum (fun d hd => (h d hd).2)⟩

theorem amplitude_refinement_enclosure {q : ℕ} (hq : 0 < q) {zl zh : ℝ}
    (hz0 : 0 < zl) (hz : zl ≤ zetaThree ∧ zetaThree ≤ zh) (L U : ℕ → ℝ)
    (hf : ∀ d ∈ q.divisors, L d ≤ harmonicSeed d ∧ harmonicSeed d ≤ U d) :
    productLower (refinementLower q L U) (refinementUpper q L U)
      (1/(zh*deltaThree q)) (1/(zl*deltaThree q)) ≤ amplitude q ∧
    amplitude q ≤ productUpper (refinementLower q L U) (refinementUpper q L U)
      (1/(zh*deltaThree q)) (1/(zl*deltaThree q)) := by
  have hd := deltaThree_pos q
  have hi := reciprocal_interval (mul_pos hz0 hd)
    ⟨mul_le_mul_of_nonneg_right hz.1 hd.le,mul_le_mul_of_nonneg_right hz.2 hd.le⟩
  have h := product_interval (refinement_numerator_interval hq L U hf) hi
  rw [amplitude_exact_transform hq]
  simpa only [mul_comm] using h

def moebiusSeedTerm (q d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3*harmonicSeed (q/(q.gcd d))
def moebiusPrefix (q D : ℕ) : ℝ := ∑ d ∈ Finset.range (D+1), moebiusSeedTerm q d
def moebiusLower (q D : ℕ) (L U : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.range (D+1), signedLower ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3)
    (L (q/(q.gcd d))) (U (q/(q.gcd d)))
def moebiusUpper (q D : ℕ) (L U : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.range (D+1), signedUpper ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3)
    (L (q/(q.gcd d))) (U (q/(q.gcd d)))

theorem moebiusSeedTerm_norm {q : ℕ} (hq : 0 < q) (d : ℕ) :
    ‖moebiusSeedTerm q d‖ ≤ zetaThree*cubeKernel d := by
  have hr : 0 < q/(q.gcd d) := Nat.div_pos (Nat.gcd_le_left d hq) (Nat.gcd_pos_of_pos_left d hq)
  rw [moebiusSeedTerm,norm_mul,norm_div,norm_pow,Real.norm_natCast,
    Real.norm_of_nonneg (harmonicSeed_nonneg _)]
  have hm := div_le_div_of_nonneg_right (CollisionMassInverse.moebius_real_norm_le d)
    (show (0 : ℝ) ≤ (d : ℝ)^3 by positivity)
  have h := mul_le_mul hm (harmonicSeed_le_zetaThree hr) (harmonicSeed_nonneg _)
    (show (0 : ℝ) ≤ 1/(d : ℝ)^3 by positivity)
  simpa only [cubeKernel,mul_comm] using h

theorem moebius_tail_rational {q D : ℕ} (hq : 0 < q) (hD : 1 ≤ D) :
    |amplitude q-moebiusPrefix q D| ≤ zetaThree/(2*(D : ℝ)^2) := by
  have hs : Summable (moebiusSeedTerm q) := CollisionAmplitudeMobiusSeries.amplitude_infinite_moebius_summable hq
  have he := hs.sum_add_tsum_nat_add (D+1)
  have ht : (∑' d, moebiusSeedTerm q d)=amplitude q :=
    (CollisionAmplitudeMobiusSeries.amplitude_infinite_moebius hq).symm
  rw [ht] at he
  have hd : amplitude q-moebiusPrefix q D=(∑' n,moebiusSeedTerm q (n+(D+1))) := by
    unfold moebiusPrefix
    linarith
  rw [hd,← Real.norm_eq_abs]
  have hst : Summable (fun n : ℕ => moebiusSeedTerm q (n+(D+1))) :=
    hs.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hsc : Summable (fun n : ℕ => cubeKernel (n+(D+1))) :=
    cubeKernel_summable.comp_injective (fun a b h => Nat.add_right_cancel h)
  apply (norm_tsum_le_tsum_norm hst.norm).trans
  apply (hst.norm.tsum_le_tsum (fun n => moebiusSeedTerm_norm hq (n+(D+1)))
    (hsc.mul_left zetaThree)).trans
  rw [tsum_mul_left]
  have hb : (∑' n : ℕ, cubeKernel (n+(D+1))) ≤ 1/(2*(D : ℝ)^2) := by
    simpa only [cubeKernel,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using cube_tail_bound hD
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hb zetaThree_pos.le

theorem moebius_prefix_interval {q : ℕ} (hq : 0 < q) (D : ℕ) (L U : ℕ → ℝ)
    (hf : ∀ d ∈ q.divisors, L d ≤ harmonicSeed d ∧ harmonicSeed d ≤ U d) :
    moebiusLower q D L U ≤ moebiusPrefix q D ∧ moebiusPrefix q D ≤ moebiusUpper q D L U := by
  have h (d : ℕ) := signed_interval ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^3)
    (hf (q/(q.gcd d)) (Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q d),hq.ne'⟩))
  exact ⟨Finset.sum_le_sum (fun d _ => (h d).1),Finset.sum_le_sum (fun d _ => (h d).2)⟩

theorem amplitude_moebius_enclosure {q D : ℕ} (hq : 0 < q) (hD : 1 ≤ D)
    {zh : ℝ} (hz : zetaThree ≤ zh) (L U : ℕ → ℝ)
    (hf : ∀ d ∈ q.divisors, L d ≤ harmonicSeed d ∧ harmonicSeed d ≤ U d) :
    moebiusLower q D L U-zh/(2*(D : ℝ)^2) ≤ amplitude q ∧
    amplitude q ≤ moebiusUpper q D L U+zh/(2*(D : ℝ)^2) := by
  have hp := moebius_prefix_interval hq D L U hf
  have he := abs_le.mp (moebius_tail_rational hq hD)
  have hz' := div_le_div_of_nonneg_right hz (show (0 : ℝ) ≤ 2*(D : ℝ)^2 by positivity)
  constructor <;> linarith

theorem omittedAmplitude_eq_omittedMass (q M : ℕ) :
    omittedAmplitude q M = omittedMass q M := by
  have h := (omittedMass_summable q M).sum_add_tsum_nat_add (M+1)
  have hz : (∑ k ∈ Finset.range (M+1), if M<k ∧ q∣k then collisionWeight k else 0)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkM : k ≤ M := by have := Finset.mem_range.mp hk; omega
    simp [show ¬M<k by omega]
  rw [hz,zero_add] at h
  have ht (n : ℕ) : M<n+(M+1) := by omega
  simpa only [omittedAmplitude,omittedMass,ht,true_and] using h

theorem omittedMass_binary_bound {q M b : ℕ} (hq : 0<q) (hM : 1≤M)
    (hb : 2*M ≤ 2^b) :
    omittedMass q M ≤ (2*(b : ℝ)+3)/((q : ℝ)*(M : ℝ)) := by
  apply (omittedMass_counting_bound hq hM).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := log_le_binary_bound hM hb
  linarith

theorem amplitude_period_tail_enclosure {q M b : ℕ} (hq : 0<q) (hM : 1≤M)
    (hb : 2*M ≤ 2^b) :
    amplitude q ≤ finiteAmplitude collisionWeight q M+
      (2*(b : ℝ)+3)/((q : ℝ)*(M : ℝ)) := by
  rw [amplitude_cutoff_split q M,omittedAmplitude_eq_omittedMass]
  have h := omittedMass_binary_bound hq hM hb
  linarith

end NField.Alignment.CollisionAmplitudeRationalEnclosure
