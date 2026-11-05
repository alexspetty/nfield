/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorExtrema

/-!
# Uniform remainder in the full Mobius inverse

The error in the finite beta transform is the tail of the absolutely
convergent full amplitude inverse. The logarithms of the conductor and its
quotient are kept additive, preserving the manuscript's single logarithm.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionInverseRemainder

open scoped BigOperators Classical
open Filter MeasureTheory Set
open CollisionRemainderDynamics CollisionMassReadout CollisionJordanVariance
open CollisionGeneralWeightCriterion CollisionMassInverse CollisionFiniteRegrouping
open CollisionAmplitudeTail CollisionPositiveLogTail CollisionDivisorSeries CollisionPositiveConstants

theorem tail_indicator_shift (f : ℕ → ℝ) (J : ℕ)
    (hs : Summable (fun n => if J < n then f n else 0)) :
    (∑' n, if J < n then f n else 0)=∑' n, f (n+J+1) := by
  have h := hs.sum_add_tsum_nat_add (J+1)
  have hz : (∑ n ∈ Finset.range (J+1), if J < n then f n else 0)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact if_neg (by have := Finset.mem_range.mp hn; omega)
  rw [hz,zero_add] at h
  have he : (fun n => if J < n+(J+1) then f (n+(J+1)) else 0)=fun n => f (n+J+1) := by
    funext n
    rw [if_pos (by omega)]
    congr 1
  rw [he] at h
  exact h.symm

theorem inverseSquare_shift_summable (J : ℕ) : Summable (fun n => zetaKernel 2 (n+J+1)) := by
  exact (zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).comp_injective (fun a b h => by omega)

theorem inverseSquare_shift_bound {J : ℕ} (hJ : 1 ≤ J) :
    (∑' n, zetaKernel 2 (n+J+1)) ≤ 1/(J : ℝ) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have ha : AntitoneOn (fun x : ℝ => x^(-(2 : ℝ))) (Ici (J : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hJR.trans_le hx) hxy (by norm_num)
  have ht := ha.tsum_comp_add_le_integral J
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) hJR)
    (fun x hx => Real.rpow_nonneg (hJR.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) hJR] at ht
  norm_num only [show -(2 : ℝ)+1 = -1 by norm_num,Real.rpow_neg_one,neg_div_neg_eq,
    div_one] at ht
  simpa only [zetaKernel_rpow (by norm_num : (2 : ℝ)≠0),one_div] using ht

theorem positiveLog_shift_summable {J : ℕ} (hJ : 1 ≤ J) :
    Summable (fun n => positiveLogKernel (n+J+1 : ℕ)) := by
  have hs := (positiveUnit_tail_summable (by exact_mod_cast hJ : (1 : ℝ) ≤ J)).comp_injective
    (fun a b : ℕ => show a+J+1=b+J+1 → a=b from by omega)
  apply hs.congr
  intro n
  simp only [Function.comp_def,Nat.cast_lt,if_pos (by omega : J < n+J+1),
    positiveLogTerm,positiveUnit,if_neg (by omega : n+J+1≠0),mul_one]

theorem positiveLog_shift_bound {J : ℕ} (hJ : 1 ≤ J) :
    (∑' n, positiveLogKernel (n+J+1 : ℕ)) ≤ (2*Real.log (J : ℝ)+3)/(J : ℝ) := by
  have hs := positiveUnit_tail_summable (by exact_mod_cast hJ : (1 : ℝ) ≤ J)
  have he (n : ℕ) : (if (J : ℝ) < (n : ℝ) then positiveLogTerm positiveUnit n else 0)=
      if J < n then positiveLogKernel n else 0 := by
    simp only [Nat.cast_lt]
    by_cases hn : J < n
    · simp [hn,positiveLogTerm,positiveUnit,show n≠0 by omega]
    · simp [hn]
  have hs' : Summable (fun n => if J < n then positiveLogKernel n else 0) := hs.congr he
  have h := positiveUnit_tail_bound (by exact_mod_cast hJ : (1 : ℝ) ≤ J)
  unfold positiveLogTail at h
  simp_rw [he] at h
  rwa [tail_indicator_shift _ J hs'] at h

theorem amplitude_scaled_log_bound {d j : ℕ} (hd : 2 ≤ d) (hj : 1 ≤ j) :
    amplitude (d*j) ≤ amplitudeLogConstant/(d : ℝ)^2*
      (Real.log (d : ℝ)*zetaKernel 2 j+positiveLogKernel j) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have h := amplitude_log_bound (show 2 ≤ d*j by nlinarith)
  convert! h using 1
  unfold positiveLogKernel
  have hk : zetaKernel 2 j=1/(j : ℝ)^2 := zetaKernel_nat (by norm_num) j
  rw [Nat.cast_mul,Real.log_mul hdR.ne' hjR.ne',hk]
  field_simp
  ring

theorem amplitude_multiple_shift_summable {d : ℕ} (hd : 0 < d) (J : ℕ) :
    Summable (fun n => amplitude (d*(n+J+1))) := by
  have hs := all_amplitudes_summable collisionWeight collisionWeight_nonneg
    (show Summable (generalEnergy collisionWeight) from conductorEnergy_summable)
  exact hs.comp_injective (fun a b h => by have := Nat.mul_left_cancel hd h; omega)

theorem amplitude_multiple_shift_bound {d J : ℕ} (hd : 2 ≤ d) (hJ : 1 ≤ J) :
    (∑' n, amplitude (d*(n+J+1))) ≤
      amplitudeLogConstant*(Real.log (d : ℝ)+2*Real.log (J : ℝ)+3)/((d : ℝ)^2*(J : ℝ)) := by
  have hm := ((inverseSquare_shift_summable J).mul_left (Real.log (d : ℝ))).add
    (positiveLog_shift_summable hJ)
  have ht := (amplitude_multiple_shift_summable (by omega : 0 < d) J).tsum_le_tsum
    (fun n => amplitude_scaled_log_bound hd (by omega : 1 ≤ n+J+1))
    (hm.mul_left (amplitudeLogConstant/(d : ℝ)^2))
  rw [tsum_mul_left,Summable.tsum_add
    ((inverseSquare_shift_summable J).mul_left (Real.log (d : ℝ)))
    (positiveLog_shift_summable hJ),tsum_mul_left] at ht
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left (inverseSquare_shift_bound hJ) (Real.log_natCast_nonneg d))
    (positiveLog_shift_bound hJ)
  have hu := mul_le_mul_of_nonneg_left hb
    (div_nonneg amplitudeLogConstant_pos.le (sq_nonneg (d : ℝ)))
  apply ht.trans
  convert! hu using 1
  ring

def inverseTerm (d j : ℕ) : ℝ := (ArithmeticFunction.moebius j : ℝ)*amplitude (d*j)

theorem inverseTerm_summable {d : ℕ} (hd : 0 < d) : Summable (inverseTerm d) := by
  exact (inverse_norm_summable collisionWeight collisionWeight_nonneg
    (show Summable (generalEnergy collisionWeight) from conductorEnergy_summable) hd).of_norm

theorem inverseTerm_tsum {d : ℕ} (hd : 0 < d) :
    (∑' j, inverseTerm d j)=collisionWeight d := by
  exact (mass_moebius_inverse collisionWeight collisionWeight_nonneg collisionWeight_zero
    collisionWeight_summable
    (show Summable (generalEnergy collisionWeight) from conductorEnergy_summable) hd).symm

theorem inverseTerm_norm_le (d j : ℕ) : ‖inverseTerm d j‖ ≤ amplitude (d*j) := by
  rw [inverseTerm,norm_mul,Real.norm_of_nonneg (amplitude_nonneg (d*j))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (moebius_real_norm_le j)
    (amplitude_nonneg (d*j))

theorem inverseTerm_prefix (d Q : ℕ) :
    (∑ j ∈ Finset.range (Q/d+1), inverseTerm d j)=beta d Q := by
  rw [Nat.range_succ_eq_Icc_zero,Finset.Icc_eq_cons_Ioc (Nat.zero_le (Q/d)),Finset.sum_cons]
  have hz : inverseTerm d 0=0 := by simp [inverseTerm]
  rw [hz,zero_add]
  have he : Finset.Ioc 0 (Q/d)=Finset.Icc 1 (Q/d) := by
    ext j
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  rw [he]
  rfl

theorem beta_inverse_remainder {d : ℕ} (hd : 0 < d) (Q : ℕ) :
    beta d Q-collisionWeight d=-(∑' j, inverseTerm d (j+Q/d+1)) := by
  have h := (inverseTerm_summable hd).sum_add_tsum_nat_add (Q/d+1)
  rw [inverseTerm_prefix,inverseTerm_tsum hd] at h
  have he : (∑' j, inverseTerm d (j+(Q/d+1)))=∑' j, inverseTerm d (j+Q/d+1) := by
    apply tsum_congr
    intro j
    rw [Nat.add_assoc]
  rw [he] at h
  linarith

theorem beta_inverse_remainder_norm {d : ℕ} (hd : 0 < d) (Q : ℕ) :
    |beta d Q-collisionWeight d| ≤ ∑' j, amplitude (d*(j+Q/d+1)) := by
  rw [beta_inverse_remainder hd,abs_neg,← Real.norm_eq_abs]
  have hs : Summable (fun j => inverseTerm d (j+Q/d+1)) :=
    (inverseTerm_summable hd).comp_injective (fun a b h => by omega)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (fun j => inverseTerm_norm_le d (j+Q/d+1))
      (amplitude_multiple_shift_summable hd (Q/d)))

theorem beta_inverse_quotient_bound {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    |beta d Q-collisionWeight d| ≤
      amplitudeLogConstant*(Real.log (d : ℝ)+2*Real.log ((Q/d : ℕ) : ℝ)+3)/
        ((d : ℝ)^2*((Q/d : ℕ) : ℝ)) :=
  (beta_inverse_remainder_norm (by omega : 0 < d) Q).trans
    (amplitude_multiple_shift_bound hd (Nat.div_pos hdQ (by omega)))

theorem beta_inverse_uniform_bound {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) :
    |beta d Q-collisionWeight d| ≤
      (16*amplitudeLogConstant)*Real.log (2*(Q : ℝ))/((d : ℝ)*(Q : ℝ)) := by
  have hd0 : 0 < d := by omega
  have hQ0 : 0 < Q := by omega
  have hJ : 1 ≤ Q/d := Nat.div_pos hdQ hd0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hJR : (0 : ℝ) < ((Q/d : ℕ) : ℝ) := by exact_mod_cast hJ
  have hdJ : (d : ℝ)*((Q/d : ℕ) : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast Nat.mul_div_le Q d
  have h2N : Q ≤ 2*d*(Q/d) := by
    have hr := Nat.mod_lt Q hd0
    have he := Nat.mod_add_div Q d
    nlinarith
  have h2R : (Q : ℝ) ≤ 2*(d : ℝ)*((Q/d : ℕ) : ℝ) := by exact_mod_cast h2N
  have hlog := Real.log_le_log (mul_pos hdR hJR) hdJ
  rw [Real.log_mul hdR.ne' hJR.ne'] at hlog
  have hdlog := Real.log_natCast_nonneg d
  have hQlog := Real.log_natCast_nonneg Q
  have hnum : Real.log (d : ℝ)+2*Real.log ((Q/d : ℕ) : ℝ)+3 ≤ 2*Real.log (Q : ℝ)+3 := by
    linarith
  have ht : |beta d Q-collisionWeight d| ≤
      2*amplitudeLogConstant*(2*Real.log (Q : ℝ)+3)/((d : ℝ)*(Q : ℝ)) := by
    calc
      _ ≤ amplitudeLogConstant*(Real.log (d : ℝ)+2*Real.log ((Q/d : ℕ) : ℝ)+3)/
          ((d : ℝ)^2*((Q/d : ℕ) : ℝ)) := beta_inverse_quotient_bound hd hdQ
      _ ≤ amplitudeLogConstant*(2*Real.log (Q : ℝ)+3)/((d : ℝ)^2*((Q/d : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum amplitudeLogConstant_pos.le)
          (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ)^2*((Q/d : ℕ) : ℝ))
          (mul_pos hdR hQR)).mpr
        have hh := mul_le_mul_of_nonneg_left h2R
          (show 0 ≤ amplitudeLogConstant*(2*Real.log (Q : ℝ)+3)*(d : ℝ) by positivity [amplitudeLogConstant_pos])
        convert! hh using 1 <;> ring
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ Q by omega))
  have hlogdouble : Real.log (Q : ℝ) ≤ Real.log (2*(Q : ℝ)) :=
    Real.log_le_log hQR (by linarith)
  have hnum2 : 2*Real.log (Q : ℝ)+3 ≤ 8*Real.log (2*(Q : ℝ)) := by
    linarith [Real.log_two_gt_d9]
  apply ht.trans
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnum2 (by positivity [amplitudeLogConstant_pos] : 0 ≤ 2*amplitudeLogConstant))
    (mul_nonneg hdR.le hQR.le)
  convert! hh using 1
  ring

end NField.Alignment.CollisionInverseRemainder
