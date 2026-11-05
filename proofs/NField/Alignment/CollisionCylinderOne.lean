/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeTail
import NField.Alignment.CollisionPositionStability
import NField.Alignment.CollisionOdometerRecurrence

/-!
# The address-one gap on complete period cylinders

Periods missed by the least common multiple lie beyond the cutoff. Their
actual mass is controlled by the proved full-amplitude tail.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCylinderOne

open scoped BigOperators Classical
open Filter
open CollisionRemainderDynamics CollisionMassReadout CollisionPotentialConvergence
open CollisionJordanVariance CollisionCylinderMeans CollisionOdometerRecurrence
open CollisionAmplitudeTail CollisionPositionStability

def coprimeMass (L : ℕ) : ℝ := ∑' k : ℕ, if k.gcd L=1 then collisionWeight k else 0
def nontrivialMass (L : ℕ) : ℝ := ∑' k : ℕ, if 1 < k.gcd L then collisionWeight k else 0
def cylinderOneError (M : ℕ) : ℝ :=
  cylinderMean (cutoffPeriod M) 1+alignmentConstant (cutoffPeriod M)-(2/3 : ℝ)

theorem coprimeMass_summable (L : ℕ) :
    Summable (fun k : ℕ => if k.gcd L=1 then collisionWeight k else 0) := by
  apply (collisionWeight_summable.indicator {k : ℕ | k.gcd L=1}).congr
  intro k
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

theorem nontrivialMass_summable (L : ℕ) :
    Summable (fun k : ℕ => if 1 < k.gcd L then collisionWeight k else 0) := by
  apply (collisionWeight_summable.indicator {k : ℕ | 1 < k.gcd L}).congr
  intro k
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

theorem coprimeMass_nonneg (L : ℕ) : 0 ≤ coprimeMass L := by
  apply tsum_nonneg
  intro k
  split_ifs
  · exact collisionWeight_nonneg k
  · rfl

theorem cylinder_mass_partition {L : ℕ} (hL : 0 < L) : nontrivialMass L+coprimeMass L=1 := by
  rw [nontrivialMass,coprimeMass,← (nontrivialMass_summable L).tsum_add (coprimeMass_summable L)]
  convert! collisionWeight_tsum using 1
  apply tsum_congr
  intro k
  by_cases hd : 1 < k.gcd L
  · have hd1 : k.gcd L≠1 := by omega
    simp only [if_pos hd,if_neg hd1,add_zero]
  · have hd1 : k.gcd L=1 := by have := Nat.gcd_pos_of_pos_right k hL; omega
    simp only [if_neg hd,if_pos hd1,zero_add]

theorem cylinder_one_gap {L : ℕ} (hL : 0 < L) :
    cylinderMean L 1+alignmentConstant L=(2/3 : ℝ)*nontrivialMass L := by
  rw [cylinderMean_gap hL]
  congr 1
  apply tsum_congr
  intro k
  by_cases hd : 1 < k.gcd L
  · simp only [ageTerm,Nat.mod_eq_of_lt hd,Nat.cast_one,mul_one,if_pos hd]
  · have hd1 : k.gcd L=1 := by have := Nat.gcd_pos_of_pos_right k hL; omega
    rw [if_neg hd]
    simp only [ageTerm,hd1,Nat.mod_one,Nat.cast_zero,mul_zero]

theorem cutoffPeriod_pos (M : ℕ) : 0 < cutoffPeriod M := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro k hk
  have h := (Finset.mem_Icc.mp hk).1
  change k≠0
  omega

theorem weight_le_amplitude (q : ℕ) : collisionWeight q ≤ amplitude q := by
  have h := (amplitude_summable q).le_tsum q
    (fun k _ => by split_ifs <;> simp [collisionWeight_nonneg])
  simp only [dvd_refl,if_true] at h
  convert! h using 1

theorem coprime_cutoff_term_bound (M k : ℕ) :
    (if k.gcd (cutoffPeriod M)=1 then collisionWeight k else 0) ≤
      if (M : ℝ) < (k : ℝ) then amplitude k else 0 := by
  by_cases hk : M < k
  · have hkR : (M : ℝ) < k := by exact_mod_cast hk
    rw [if_pos hkR]
    split_ifs
    · exact weight_le_amplitude k
    · exact amplitude_nonneg k
  · have hkR : ¬(M : ℝ) < k := by exact_mod_cast hk
    rw [if_neg hkR]
    by_cases hk2 : 2 ≤ k
    · have hd := dvd_cutoffPeriod (by omega : 1 ≤ k) (by omega : k ≤ M)
      have hg : k.gcd (cutoffPeriod M)=k := Nat.gcd_eq_left_iff_dvd.mpr hd
      have hn : k.gcd (cutoffPeriod M)≠1 := by rw [hg]; omega
      simp only [if_neg hn,le_refl]
    · have hsmall : k < 2 := by omega
      interval_cases k <;> simp [collisionWeight_zero,collisionWeight_one]

theorem coprimeMass_cutoff_bound {M : ℕ} (hM : 2 ≤ M) :
    coprimeMass (cutoffPeriod M) ≤ amplitudeTail M :=
  (coprimeMass_summable _).tsum_le_tsum (coprime_cutoff_term_bound M)
    (amplitude_tail_summable (by exact_mod_cast (show 1 ≤ M by omega)))

theorem cylinderOneError_exact (M : ℕ) :
    cylinderOneError M=-(2/3 : ℝ)*coprimeMass (cutoffPeriod M) := by
  have hg := cylinder_one_gap (cutoffPeriod_pos M)
  have hp := cylinder_mass_partition (cutoffPeriod_pos M)
  unfold cylinderOneError
  nlinarith

theorem cylinderOneError_bound {M : ℕ} (hM : 2 ≤ M) :
    ‖cylinderOneError M‖ ≤ (2/3 : ℝ)*amplitudeTail M := by
  rw [cylinderOneError_exact,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (coprimeMass_nonneg _)]
  have hc : |-(2/3 : ℝ)|=(2/3 : ℝ) := by norm_num
  rw [hc]
  exact mul_le_mul_of_nonneg_left (coprimeMass_cutoff_bound hM) (by norm_num)

theorem cylinderOneError_isBigO_log :
    Asymptotics.IsBigO atTop cylinderOneError (fun M : ℕ => Real.log M/(M : ℝ)) := by
  have hc : Asymptotics.IsBigO atTop cylinderOneError (fun M : ℕ => amplitudeTail M) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨2/3,?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with M hM
    rw [Real.norm_of_nonneg (amplitude_tail_nonneg M)]
    exact cylinderOneError_bound hM
  exact hc.trans (amplitude_tail_isBigO.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem log_over_nat_isBigO_log_double :
    Asymptotics.IsBigO atTop (fun M : ℕ => Real.log M/(M : ℝ))
      (fun M : ℕ => Real.log (2*(M : ℝ))/(M : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.norm_of_nonneg (div_nonneg (Real.log_natCast_nonneg M) hM0.le),
    Real.norm_of_nonneg (div_nonneg (Real.log_nonneg (by linarith)) hM0.le),one_mul]
  exact div_le_div_of_nonneg_right (Real.log_le_log hM0 (by linarith)) hM0.le

theorem cylinder_address_one_asymptotic :
    Asymptotics.IsBigO atTop
      (fun M : ℕ => cylinderMean (cutoffPeriod M) 1+alignmentConstant (cutoffPeriod M)-(2/3 : ℝ))
      (fun M : ℕ => Real.log (2*(M : ℝ))/(M : ℝ)) :=
  cylinderOneError_isBigO_log.trans log_over_nat_isBigO_log_double

end NField.Alignment.CollisionCylinderOne
