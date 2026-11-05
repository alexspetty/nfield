/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionElementaryDisplays

/-!
# The period-specific omitted-mass estimate

The positive-multiple counting function is bounded by N/q. Applying the
proved positive Abel tail estimate gives the small-period bound directly;
above the cutoff the omitted mass is the entire amplitude.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMultipleTailDisplay

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionMassReadout CollisionJordanVariance
open CollisionPositiveLogTail CollisionAmplitudeTail CollisionElementaryDisplays

def multipleIndicator (q n : ℕ) : ℝ := if 0<n ∧ q∣n then 1 else 0
def omittedMass (q M : ℕ) : ℝ := ∑' k : ℕ, if M<k ∧ q∣k then collisionWeight k else 0

theorem multipleIndicator_zero (q : ℕ) : multipleIndicator q 0=0 := by simp [multipleIndicator]

theorem multipleIndicator_nonneg (q n : ℕ) : 0 ≤ multipleIndicator q n := by
  unfold multipleIndicator
  split_ifs <;> norm_num

theorem positive_multiples_image {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (Finset.Ioc 0 N).filter (fun k => q∣k)=(Finset.Ioc 0 (N/q)).image (fun j => q*j) := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_image]
  constructor
  · rintro ⟨⟨hk,hkN⟩,hqd⟩
    refine ⟨k/q,⟨Nat.div_pos (Nat.le_of_dvd hk hqd) hq,Nat.div_le_div_right hkN⟩,
      Nat.mul_div_cancel' hqd⟩
  · rintro ⟨j,⟨hj,hjN⟩,rfl⟩
    refine ⟨⟨Nat.mul_pos hq hj,?_⟩,dvd_mul_right q j⟩
    have h := (Nat.le_div_iff_mul_le hq).mp hjN
    simpa only [Nat.mul_comm] using h

theorem multipleIndicator_partial_sum {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, multipleIndicator q n)=((N/q : ℕ) : ℝ) := by
  have he : (∑ n ∈ Finset.Ioc 0 N, multipleIndicator q n)=
      ∑ n ∈ (Finset.Ioc 0 N).filter (fun k => q∣k), (1 : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [multipleIndicator,(Finset.mem_Ioc.mp hn).1,true_and]
  rw [he,positive_multiples_image hq]
  rw [Finset.sum_image]
  · simp
  · intro x _ y _ hxy
    exact Nat.mul_left_cancel hq hxy

theorem multipleIndicator_partial_bound {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, multipleIndicator q n) ≤ (1/(q : ℝ))*(N : ℝ) := by
  rw [multipleIndicator_partial_sum hq]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [one_div,inv_mul_eq_div]
  apply (le_div_iff₀ hqR).mpr
  exact_mod_cast Nat.div_mul_le_self N q

theorem omittedMass_summable (q M : ℕ) :
    Summable (fun k : ℕ => if M<k ∧ q∣k then collisionWeight k else 0) := by
  apply Summable.of_nonneg_of_le _ _ collisionWeight_summable
  · intro k
    split_ifs <;> simp [collisionWeight_nonneg]
  · intro k
    split_ifs <;> simp [collisionWeight_nonneg]

theorem omittedMass_nonneg (q M : ℕ) : 0 ≤ omittedMass q M := by
  apply tsum_nonneg
  intro k
  split_ifs <;> simp [collisionWeight_nonneg]

theorem omittedMass_le_counting_tail {q M : ℕ} (hq : 0 < q) (hM : 1 ≤ M) :
    omittedMass q M ≤ positiveLogTail (multipleIndicator q) (M : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs := positiveLog_tail_summable_of_nat (multipleIndicator_zero q)
    (multipleIndicator_nonneg q) (by positivity : 0 ≤ 1/(q : ℝ))
    (by exact_mod_cast hM : (1 : ℝ) ≤ M) (multipleIndicator_partial_bound hq)
  apply (omittedMass_summable q M).tsum_le_tsum _ hs
  intro k
  by_cases hk : M<k
  · have hkR : (M : ℝ) < k := by exact_mod_cast hk
    rw [if_pos hkR]
    by_cases hd : q∣k
    · have hk0 : 0<k := by omega
      simpa [hk,hd,hk0,positiveLogTerm,multipleIndicator,positiveLogKernel] using
        (collisionWeight_log_bound (k := k) (by omega))
    · simp [hk,hd,positiveLogTerm,multipleIndicator]
  · have hkR : ¬(M : ℝ)<k := by exact_mod_cast hk
    simp [hk,hkR]

theorem omittedMass_counting_bound {q M : ℕ} (hq : 0 < q) (hM : 1 ≤ M) :
    omittedMass q M ≤ (2*Real.log M+3)/((q : ℝ)*(M : ℝ)) := by
  have hb := positiveLog_tail_bound_of_nat (multipleIndicator_zero q)
    (multipleIndicator_nonneg q) (by positivity : 0 ≤ 1/(q : ℝ))
    (by exact_mod_cast hM : (1 : ℝ) ≤ M) (multipleIndicator_partial_bound hq)
  exact (omittedMass_le_counting_tail hq hM).trans (by convert! hb using 1; ring)

theorem omittedMass_log_bound {q M : ℕ} (hq : 0 < q) (hM : 1 ≤ M) :
    omittedMass q M ≤ 6*Real.log (2*(M : ℝ))/((q : ℝ)*(M : ℝ)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hl := Real.log_natCast_nonneg M
  have htwo := Real.log_two_gt_d9
  have he : 2*Real.log (M : ℝ)+3 ≤ 6*Real.log (2*(M : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hM0.ne']
    linarith
  exact (omittedMass_counting_bound hq hM).trans
    (div_le_div_of_nonneg_right he (mul_nonneg (Nat.cast_nonneg _) hM0.le))

theorem omittedMass_above_cutoff {q M : ℕ} (hq : M<q) : omittedMass q M=amplitude q := by
  apply tsum_congr
  intro k
  by_cases hk : k=0
  · simp [hk]
  by_cases hd : q∣k
  · have hm : M<k := hq.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hd)
    simp [hm,hd]
  · simp [hd]

theorem literal_period_specific_tail : ∃ C : ℝ, 0<C ∧
    ∀ q M : ℕ, 2 ≤ q → 1 ≤ M → omittedMass q M ≤
      C*(if q≤M then Real.log (2*(M : ℝ))/((q : ℝ)*(M : ℝ))
        else Real.log (2*(q : ℝ))/(q : ℝ)^2) := by
  refine ⟨6+2*amplitudeLogConstant,by linarith [amplitudeLogConstant_pos],?_⟩
  intro q M hq hM
  by_cases hqm : q≤M
  · rw [if_pos hqm]
    have hl : 0 ≤ Real.log (2*(M : ℝ))/((q : ℝ)*(M : ℝ)) := by
      apply div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤2*M by omega)))
      positivity
    have hb := omittedMass_log_bound (by omega : 0<q) hM
    rw [mul_div_assoc] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith [amplitudeLogConstant_pos]) hl)
  · rw [if_neg hqm,omittedMass_above_cutoff (by omega)]
    have hl : 0 ≤ Real.log (2*(q : ℝ))/(q : ℝ)^2 := by
      apply div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤2*q by omega)))
      positivity
    have hb := amplitude_log_two_bound hq
    rw [mul_div_assoc] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hl)

end NField.Alignment.CollisionMultipleTailDisplay
