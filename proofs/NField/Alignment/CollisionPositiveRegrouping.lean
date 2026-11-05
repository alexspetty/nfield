/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPositiveConstants
import NField.Alignment.CollisionWeightMultiples

/-!
# Positive Mobius regrouping for every finite conductor cutoff

The exact finite transform uses full infinite amplitudes. Its negative
period contribution is controlled by the actual convergent divisor-deficit
series, with the manuscript's strict rational margin.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPositiveRegrouping

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionMassReadout CollisionConductorOne
open CollisionFiniteRegrouping CollisionWeightMultiples CollisionMobiusDeficit
open CollisionDivisorSeries CollisionPositiveConstants

theorem harmonic_predecessor_log {m : ℕ} (hm : 2 ≤ m) :
    (harmonic (m-1) : ℝ) ≤ 1+Real.log (m : ℝ) := by
  have h := harmonic_le_one_add_log (m-1)
  have hp : (0 : ℝ) < ((m-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m-1)
  have hl := Real.log_le_log hp (show ((m-1 : ℕ) : ℝ) ≤ (m : ℝ) by exact_mod_cast Nat.sub_le m 1)
  linarith

theorem sqrt_zetaKernel_two {m : ℕ} (hm : 0 < m) :
    Real.sqrt (m : ℝ)*zetaKernel 2 m=zetaKernel (3/2) m := by
  rw [zetaKernel_rpow (by norm_num : (2 : ℝ)≠0),
    zetaKernel_rpow (by norm_num : (3/2 : ℝ)≠0),Real.sqrt_eq_rpow,
    ← Real.rpow_add (by exact_mod_cast hm : (0 : ℝ) < m)]
  congr 1
  norm_num

theorem collisionWeight_multiple_series_bound {d m : ℕ} (hd : 2 ≤ d) (hm : 2 ≤ m) :
    collisionWeight (d*m) ≤ collisionWeight d*
      ((3/2 : ℝ)*zetaKernel 2 m+(37/100 : ℝ)*zetaKernel (3/2) m) := by
  have hl := logarithm_half_rational (show (0 : ℝ) < m by exact_mod_cast (by omega : 0 < m))
  have hh := harmonic_predecessor_log hm
  have hc : 1+(harmonic (m-1) : ℝ)/2 ≤ (3/2 : ℝ)+(37/100 : ℝ)*Real.sqrt (m : ℝ) := by
    linarith
  calc
    collisionWeight (d*m) ≤ collisionWeight d/(m : ℝ)^2*(1+(harmonic (m-1) : ℝ)/2) :=
      collisionWeight_multiple_bound hd (by omega)
    _ ≤ collisionWeight d/(m : ℝ)^2*((3/2 : ℝ)+(37/100 : ℝ)*Real.sqrt (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (div_nonneg (collisionWeight_nonneg d) (sq_nonneg _))
    _ = _ := by
      have hk : zetaKernel 2 m=1/(m : ℝ)^2 := zetaKernel_nat (by norm_num) m
      rw [← sqrt_zetaKernel_two (by omega : 0 < m),hk]
      ring

def deficitMajorant (m : ℕ) : ℝ :=
  (3/2 : ℝ)*(divisorDeficit m*zetaKernel 2 m)+
    (37/100 : ℝ)*(divisorDeficit m*zetaKernel (3/2) m)
def deficitWeight (d m : ℕ) : ℝ := collisionWeight (d*m)*divisorDeficit m

theorem deficitMajorant_nonneg (m : ℕ) : 0 ≤ deficitMajorant m := by
  unfold deficitMajorant
  exact add_nonneg
    (mul_nonneg (by norm_num) (mul_nonneg (divisorDeficit_nonneg m) (zetaKernel_nonneg 2 m)))
    (mul_nonneg (by norm_num) (mul_nonneg (divisorDeficit_nonneg m) (zetaKernel_nonneg (3/2) m)))

theorem deficitMajorant_summable : Summable deficitMajorant :=
  ((deficitSeries_summable (by norm_num : (1 : ℝ) < 2)).mul_left (3/2)).add
    ((deficitSeries_summable (by norm_num : (1 : ℝ) < 3/2)).mul_left (37/100))

theorem deficitMajorant_tsum : (∑' m, deficitMajorant m)=
    (3/2 : ℝ)*deficitSeries 2+(37/100 : ℝ)*deficitSeries (3/2) := by
  unfold deficitMajorant
  rw [Summable.tsum_add
    ((deficitSeries_summable (by norm_num : (1 : ℝ) < 2)).mul_left (3/2))
    ((deficitSeries_summable (by norm_num : (1 : ℝ) < 3/2)).mul_left (37/100)),
    tsum_mul_left,tsum_mul_left]
  rfl

theorem deficitWeight_bounds {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    0 ≤ deficitWeight d m ∧ deficitWeight d m ≤ collisionWeight d*deficitMajorant m := by
  refine ⟨mul_nonneg (collisionWeight_nonneg (d*m)) (divisorDeficit_nonneg m),?_⟩
  by_cases hm : 2 ≤ m
  · have h := mul_le_mul_of_nonneg_right (collisionWeight_multiple_series_bound hd hm)
      (divisorDeficit_nonneg m)
    convert! h using 1
    unfold deficitMajorant
    ring
  · have hz : divisorDeficit m=0 := by simp [divisorDeficit,hm]
    simp [deficitWeight,deficitMajorant,hz]

theorem deficitWeight_summable {d : ℕ} (hd : 2 ≤ d) : Summable (deficitWeight d) :=
  Summable.of_nonneg_of_le (fun m => (deficitWeight_bounds hd m).1)
    (fun m => (deficitWeight_bounds hd m).2) (deficitMajorant_summable.mul_left (collisionWeight d))

theorem deficitWeight_tsum_bound {d : ℕ} (hd : 2 ≤ d) :
    (∑' m, deficitWeight d m) ≤ collisionWeight d*
      ((3/2 : ℝ)*deficitSeries 2+(37/100 : ℝ)*deficitSeries (3/2)) := by
  have h := (deficitWeight_summable hd).tsum_le_tsum (fun m => (deficitWeight_bounds hd m).2)
    (deficitMajorant_summable.mul_left (collisionWeight d))
  rwa [tsum_mul_left,deficitMajorant_tsum] at h

theorem beta_term_lower {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) (m : ℕ) :
    (if m=1 then collisionWeight d else 0)-deficitWeight d m ≤
      collisionWeight (d*m)*partialMobius (Q/d) m := by
  have hJ : 1 ≤ Q/d := Nat.div_pos hdQ (by omega)
  by_cases hm0 : m=0
  · simp [hm0,deficitWeight]
  by_cases hm1 : m=1
  · simp [hm1,partialMobius_one hJ,deficitWeight,divisorDeficit]
  have h := mul_le_mul_of_nonneg_left (partialMobius_lower (by omega : 2 ≤ m) hJ)
    (collisionWeight_nonneg (d*m))
  simpa only [if_neg hm1,zero_sub,deficitWeight,mul_neg] using h

theorem beta_deficit_lower {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    collisionWeight d-(∑' m, deficitWeight d m) ≤ beta d Q := by
  have hs := (hasSum_ite_eq (1 : ℕ) (collisionWeight d)).summable
  have ht := (hs.sub (deficitWeight_summable hd)).tsum_le_tsum (beta_term_lower hd hdQ)
    (beta_period_series_summable (by omega : 0 < d) (Q/d))
  rw [Summable.tsum_sub hs (deficitWeight_summable hd),tsum_ite_eq,
    ← beta_period_series (by omega : 0 < d) Q] at ht
  exact ht

theorem beta_series_lower {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    collisionWeight d*(1-(3/2 : ℝ)*deficitSeries 2-(37/100 : ℝ)*deficitSeries (3/2)) ≤ beta d Q := by
  have h := beta_deficit_lower hd hdQ
  have ht := deficitWeight_tsum_bound hd
  nlinarith

theorem beta_strict_half {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    collisionWeight d/2 < beta d Q := by
  have h := beta_series_lower hd hdQ
  have hp := collisionWeight_pos hd
  have hc := deficitSeries_combined_upper
  nlinarith [mul_pos hp (show 0 < (1/2 : ℝ)-
    ((3/2 : ℝ)*deficitSeries 2+(37/100 : ℝ)*deficitSeries (3/2)) by linarith)]

theorem beta_ratio_lower {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    1-(3/2 : ℝ)*deficitSeries 2-(37/100 : ℝ)*deficitSeries (3/2) ≤
      beta d Q/collisionWeight d := by
  apply (le_div_iff₀ (collisionWeight_pos hd)).mpr
  simpa only [mul_comm] using beta_series_lower hd hdQ

theorem positive_regrouping_margin {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    1-(3/2 : ℝ)*deficitSeries 2-(37/100 : ℝ)*deficitSeries (3/2) ≤
        beta d Q/collisionWeight d ∧
      (1-3979/8000 : ℝ) < 1-(3/2 : ℝ)*deficitSeries 2-(37/100 : ℝ)*deficitSeries (3/2) ∧
      (1/2 : ℝ) < 1-3979/8000 := by
  refine ⟨beta_ratio_lower hd hdQ,?_,by norm_num⟩
  linarith [deficitSeries_combined_upper]

theorem positive_mobius_regrouping (Q a : ℕ) :
    fixedConductorValue Q a=(2/3 : ℝ)*
      ∑ d ∈ Finset.Icc 2 Q, beta d Q*centeredRemainder d a ∧
      ∀ d : ℕ, 2 ≤ d → d ≤ Q → collisionWeight d/2 < beta d Q :=
  ⟨fixedConductor_regrouping Q a,fun _ hd hdQ => beta_strict_half hd hdQ⟩

end NField.Alignment.CollisionPositiveRegrouping
