/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralTailMean

/-!
# Logarithmic tails from linear positive partial-sum bounds

The hypothesis concerns actual finite sums of an arbitrary nonnegative
sequence. Summability of the weighted tail is proved, not assumed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPositiveLogTail

open scoped BigOperators Classical
open Filter MeasureTheory
open CollisionLogTailKernel

def positiveLogKernel (x : ℝ) : ℝ := (1+Real.log x)/x^2
def positiveLogDerivative (x : ℝ) : ℝ := -(1+2*Real.log x)/x^3
def positiveLogPrimitive (x : ℝ) : ℝ := (2*Real.log x+3)/x
def countingSum (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, c n
def positiveLogTerm (c : ℕ → ℝ) (n : ℕ) : ℝ := positiveLogKernel n*c n
def positiveLogTail (c : ℕ → ℝ) (Q : ℝ) : ℝ :=
  ∑' n : ℕ, if Q < (n : ℝ) then positiveLogTerm c n else 0

theorem positiveLogKernel_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ positiveLogKernel x := by
  unfold positiveLogKernel
  positivity [Real.log_nonneg hx]

theorem positiveLogKernel_nat_nonneg (n : ℕ) : 0 ≤ positiveLogKernel n := by
  unfold positiveLogKernel
  positivity [Real.log_natCast_nonneg n]

theorem positiveLogDerivative_nonpos {x : ℝ} (hx : 1 ≤ x) :
    positiveLogDerivative x ≤ 0 := by
  unfold positiveLogDerivative
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith [Real.log_nonneg hx]
  · positivity

theorem positiveLogKernel_hasDerivAt {x : ℝ} (hx : x≠0) :
    HasDerivAt positiveLogKernel (positiveLogDerivative x) x := by
  have h := ((Real.hasDerivAt_log hx).const_add 1).div ((hasDerivAt_id x).pow 2)
    (pow_ne_zero 2 hx)
  convert! h using 1
  dsimp [positiveLogDerivative]
  field_simp
  ring

theorem positiveLogPrimitive_hasDerivAt {x : ℝ} (hx : x≠0) :
    HasDerivAt positiveLogPrimitive (x*positiveLogDerivative x) x := by
  have h := (((Real.hasDerivAt_log hx).const_mul 2).add_const 3).div (hasDerivAt_id x) hx
  convert! h using 1
  dsimp [positiveLogDerivative]
  field_simp
  ring

theorem positiveLogPrimitive_tendsto_zero :
    Tendsto positiveLogPrimitive atTop (nhds 0) := by
  have h := ((logPower_div_linear_tendsto 1).const_mul 2).add
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun x : ℝ => 3/x) atTop (nhds 0))
  simp only [mul_zero,zero_add,pow_one] at h
  convert! h using 1
  funext x
  unfold positiveLogPrimitive
  ring

theorem positiveLogDerivative_linear_integrableOn {Q : ℝ} (hQ : 1 ≤ Q) :
    IntegrableOn (fun x => x*positiveLogDerivative x) (Set.Ioi Q) :=
  integrableOn_Ioi_deriv_of_nonpos'
    (fun x hx => positiveLogPrimitive_hasDerivAt
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hQ.trans hx))))
    (fun _ hx => mul_nonpos_of_nonneg_of_nonpos
      ((by norm_num : (0 : ℝ) ≤ 1).trans (hQ.trans hx.le))
      (positiveLogDerivative_nonpos (hQ.trans hx.le)))
    positiveLogPrimitive_tendsto_zero

theorem positiveLogDerivative_linear_integral {Q : ℝ} (hQ : 1 ≤ Q) :
    (∫ x in Set.Ioi Q, x*positiveLogDerivative x) = -positiveLogPrimitive Q := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun x hx => positiveLogPrimitive_hasDerivAt
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hQ.trans hx))))
    (fun _ hx => mul_nonpos_of_nonneg_of_nonpos
      ((by norm_num : (0 : ℝ) ≤ 1).trans (hQ.trans hx.le))
      (positiveLogDerivative_nonpos (hQ.trans hx.le)))
    positiveLogPrimitive_tendsto_zero
  simpa only [zero_sub] using h

theorem countingSum_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (x : ℝ) :
    0 ≤ countingSum c x := Finset.sum_nonneg (fun n _ => hc n)

theorem countingSum_monotone {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) :
    Monotone (countingSum c) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
  · exact fun n _ _ => hc n

theorem countingSum_Icc {c : ℕ → ℝ} (hc0 : c 0=0) (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n)=countingSum c x := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _),Finset.sum_cons,hc0,zero_add]
  rfl

theorem countingSum_real_bound {c : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ N : ℕ, (∑ n ∈ Finset.Ioc 0 N, c n) ≤ M*N)
    {x : ℝ} (hx : 0 ≤ x) : countingSum c x ≤ M*x :=
  (hA ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hM)

theorem positiveLogDerivative_count_norm_bound {c : ℕ → ℝ} {M x : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hx : 1 ≤ x) (hA : countingSum c x ≤ M*x) :
    ‖positiveLogDerivative x*countingSum c x‖ ≤ -M*(x*positiveLogDerivative x) := by
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonpos (positiveLogDerivative_nonpos hx),
    abs_of_nonneg (countingSum_nonneg hc x)]
  calc
    _ ≤ -positiveLogDerivative x*(M*x) :=
      mul_le_mul_of_nonneg_left hA (neg_nonneg.mpr (positiveLogDerivative_nonpos hx))
    _ = _ := by ring

theorem positiveLogDerivative_count_integrableOn {c : ℕ → ℝ} {M Q : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hQ : 1 ≤ Q)
    (hA : ∀ x ≥ Q, countingSum c x ≤ M*x) :
    IntegrableOn (fun x => positiveLogDerivative x*countingSum c x) (Set.Ioi Q) := by
  have hD : Measurable positiveLogDerivative := by unfold positiveLogDerivative; fun_prop
  have hC : Measurable (countingSum c) := (countingSum_monotone hc).measurable
  apply ((positiveLogDerivative_linear_integrableOn hQ).const_mul (-M)).mono'
    (hD.mul hC).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact positiveLogDerivative_count_norm_bound hc (hQ.trans hx.le) (hA x hx.le)

theorem positiveLogDerivative_count_integral_bound {c : ℕ → ℝ} {M Q : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hQ : 1 ≤ Q)
    (hA : ∀ x ≥ Q, countingSum c x ≤ M*x) :
    |∫ x in Set.Ioi Q, positiveLogDerivative x*countingSum c x| ≤
      M*positiveLogPrimitive Q := by
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Ioi Q),
      ‖positiveLogDerivative x*countingSum c x‖ ≤ -M*(x*positiveLogDerivative x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact positiveLogDerivative_count_norm_bound hc (hQ.trans hx.le) (hA x hx.le)
  have h := norm_integral_le_of_norm_le
    ((positiveLogDerivative_linear_integrableOn hQ).const_mul (-M)) hbound
  simpa only [Real.norm_eq_abs,integral_const_mul,positiveLogDerivative_linear_integral hQ,
    neg_mul_neg] using h

theorem positiveLogKernel_linear_tendsto :
    Tendsto (fun x : ℝ => positiveLogKernel x*x) atTop (nhds 0) := by
  have h := (tendsto_const_nhds.div_atTop tendsto_id :
    Tendsto (fun x : ℝ => 1/x) atTop (nhds 0)).add (logPower_div_linear_tendsto 1)
  simp only [zero_add,pow_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold positiveLogKernel
  field_simp

theorem positiveLogKernel_count_tendsto {c : ℕ → ℝ} {M : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hA : ∀ x ≥ 1, countingSum c x ≤ M*x) :
    Tendsto (fun x => positiveLogKernel x*countingSum c x) atTop (nhds 0) := by
  have h := positiveLogKernel_linear_tendsto.const_mul M
  simp only [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (positiveLogKernel_nonneg hx) (countingSum_nonneg hc x)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    calc
      _ ≤ positiveLogKernel x*(M*x) :=
        mul_le_mul_of_nonneg_left (hA x hx) (positiveLogKernel_nonneg hx)
      _ = _ := by ring

theorem positiveLogDerivative_continuousOn {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    ContinuousOn positiveLogDerivative (Set.Icc Q R) := by
  intro x hx
  have hx0 : x≠0 := ne_of_gt (hQ.trans_le hx.1)
  have hl := Real.continuousAt_log hx0
  exact (((hl.const_mul 2).const_add 1).neg.div
    (continuousAt_id.pow 3) (pow_ne_zero 3 hx0)).continuousWithinAt

theorem positiveLogKernel_derivative_integrable {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    IntegrableOn (deriv positiveLogKernel) (Set.Icc Q R) := by
  have h : ContinuousOn (deriv positiveLogKernel) (Set.Icc Q R) :=
    (positiveLogDerivative_continuousOn hQ R).congr (fun x hx =>
      (positiveLogKernel_hasDerivAt (ne_of_gt (hQ.trans_le hx.1))).deriv)
  exact h.integrableOn_Icc

theorem finite_positiveLog_abel {c : ℕ → ℝ} (hc0 : c 0=0)
    {Q R : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) :
    (∑ n ∈ Finset.Ioc ⌊Q⌋₊ ⌊R⌋₊, positiveLogTerm c n)=
      positiveLogKernel R*countingSum c R-positiveLogKernel Q*countingSum c Q-
        ∫ x in Set.Ioc Q R, positiveLogDerivative x*countingSum c x := by
  have h := sum_mul_eq_sub_sub_integral_mul c hQ.le hQR
    (fun x hx => (positiveLogKernel_hasDerivAt (ne_of_gt (hQ.trans_le hx.1))).differentiableAt)
    (positiveLogKernel_derivative_integrable hQ R)
  simp only [countingSum_Icc hc0] at h
  have he : (∫ x in Set.Ioc Q R, positiveLogDerivative x*countingSum c x)=
      ∫ x in Set.Ioc Q R, deriv positiveLogKernel x*countingSum c x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [(positiveLogKernel_hasDerivAt (ne_of_gt (hQ.trans hx.1))).deriv]
  rw [he]
  exact h

theorem positiveLog_finite_tail_eq_range (c : ℕ → ℝ) {Q : ℝ} (hQ : 0 ≤ Q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊Q⌋₊ N, positiveLogTerm c n)=
      ∑ n ∈ Finset.range (N+1), if Q < (n : ℝ) then positiveLogTerm c n else 0 := by
  have he : Finset.Ioc ⌊Q⌋₊ N=
      (Finset.range (N+1)).filter (fun n : ℕ => Q < (n : ℝ)) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_filter,Finset.mem_range,← Nat.floor_lt hQ]
    omega
  rw [he,Finset.sum_filter]

theorem positiveLog_count_integral_tendsto {c : ℕ → ℝ} {M Q : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hQ : 1 ≤ Q)
    (hA : ∀ x ≥ 1, countingSum c x ≤ M*x) :
    Tendsto (fun N : ℕ => ∫ x in Set.Ioc Q (N : ℝ), positiveLogDerivative x*countingSum c x)
      atTop (nhds (∫ x in Set.Ioi Q, positiveLogDerivative x*countingSum c x)) := by
  have hi := positiveLogDerivative_count_integrableOn hc hQ
    (fun x hx => hA x (hQ.trans hx))
  have h := intervalIntegral_tendsto_integral_Ioi Q hi (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop Q] with N hN
  exact intervalIntegral.integral_of_le hN

theorem positiveLog_finite_tail_tendsto {c : ℕ → ℝ} {M Q : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hQ : 1 ≤ Q)
    (hA : ∀ x ≥ 1, countingSum c x ≤ M*x) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ioc ⌊Q⌋₊ N, positiveLogTerm c n) atTop
      (nhds (-positiveLogKernel Q*countingSum c Q-
        ∫ x in Set.Ioi Q, positiveLogDerivative x*countingSum c x)) := by
  have h := (((positiveLogKernel_count_tendsto hc hA).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).sub_const
      (positiveLogKernel Q*countingSum c Q)).sub (positiveLog_count_integral_tendsto hc hQ hA)
  simp only [zero_sub,neg_mul] at h ⊢
  apply h.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop Q] with N hN
  simpa only [Nat.floor_natCast,Function.comp_def] using
    (finite_positiveLog_abel hc0 (by linarith : 0 < Q) hN).symm

theorem positiveLog_tail_hasSum {c : ℕ → ℝ} {M Q : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hQ : 1 ≤ Q)
    (hA : ∀ x ≥ 1, countingSum c x ≤ M*x) :
    HasSum (fun n : ℕ => if Q < (n : ℝ) then positiveLogTerm c n else 0)
      (-positiveLogKernel Q*countingSum c Q-
        ∫ x in Set.Ioi Q, positiveLogDerivative x*countingSum c x) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg _ _).mpr
  · apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [positiveLog_finite_tail_eq_range c (show 0 ≤ Q by linarith)] using
      positiveLog_finite_tail_tendsto hc0 hc hQ hA
  · intro n
    split_ifs
    · exact mul_nonneg (positiveLogKernel_nat_nonneg n) (hc n)
    · rfl

theorem positiveLog_infinite_abel {c : ℕ → ℝ} {M Q : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hQ : 1 ≤ Q)
    (hA : ∀ x ≥ 1, countingSum c x ≤ M*x) :
    positiveLogTail c Q = -positiveLogKernel Q*countingSum c Q-
      ∫ x in Set.Ioi Q, positiveLogDerivative x*countingSum c x :=
  (positiveLog_tail_hasSum hc0 hc hQ hA).tsum_eq

theorem positiveLog_tail_bound {c : ℕ → ℝ} {M Q : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hQ : 1 ≤ Q)
    (hA : ∀ x ≥ 1, countingSum c x ≤ M*x) :
    positiveLogTail c Q ≤ M*(2*Real.log Q+3)/Q := by
  have hb := mul_nonneg (positiveLogKernel_nonneg hQ) (countingSum_nonneg hc Q)
  have hI := positiveLogDerivative_count_integral_bound hc hQ
    (fun x hx => hA x (hQ.trans hx))
  rw [positiveLog_infinite_abel hc0 hc hQ hA]
  calc
    _ ≤ -(∫ x in Set.Ioi Q, positiveLogDerivative x*countingSum c x) := by linarith
    _ ≤ |∫ x in Set.Ioi Q, positiveLogDerivative x*countingSum c x| := neg_le_abs _
    _ ≤ M*positiveLogPrimitive Q := hI
    _ = _ := by unfold positiveLogPrimitive; ring

theorem positiveLog_tail_bound_of_nat {c : ℕ → ℝ} {M Q : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hM : 0 ≤ M) (hQ : 1 ≤ Q)
    (hA : ∀ N : ℕ, (∑ n ∈ Finset.Ioc 0 N, c n) ≤ M*N) :
    positiveLogTail c Q ≤ M*(2*Real.log Q+3)/Q :=
  positiveLog_tail_bound hc0 hc hQ
    (fun _ hx => countingSum_real_bound hM hA (by linarith))

theorem positiveLog_tail_summable_of_nat {c : ℕ → ℝ} {M Q : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hM : 0 ≤ M) (hQ : 1 ≤ Q)
    (hA : ∀ N : ℕ, (∑ n ∈ Finset.Ioc 0 N, c n) ≤ M*N) :
    Summable (fun n : ℕ => if Q < (n : ℝ) then positiveLogTerm c n else 0) :=
  (positiveLog_tail_hasSum hc0 hc hQ
    (fun _ hx => countingSum_real_bound hM hA (by linarith))).summable

theorem positiveLog_tail_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (Q : ℝ) :
    0 ≤ positiveLogTail c Q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact mul_nonneg (positiveLogKernel_nat_nonneg n) (hc n)
  · rfl

theorem positiveLog_tail_isBigO {c : ℕ → ℝ} {M : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hM : 0 ≤ M)
    (hA : ∀ N : ℕ, (∑ n ∈ Finset.Ioc 0 N, c n) ≤ M*N) :
    Asymptotics.IsBigO atTop (positiveLogTail c) (fun Q : ℝ => Real.log Q/Q) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨5*M,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with Q hQ hl
  have hQ0 : 0 < Q := by linarith
  rw [Real.norm_of_nonneg (positiveLog_tail_nonneg hc Q),
    Real.norm_of_nonneg (div_nonneg (by linarith) hQ0.le)]
  calc
    _ ≤ M*(2*Real.log Q+3)/Q := positiveLog_tail_bound_of_nat hc0 hc hM hQ hA
    _ ≤ M*(5*Real.log Q)/Q := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hM) hQ0.le
    _ = _ := by ring

theorem log_linear_isLittleO_square :
    Asymptotics.IsLittleO atTop (fun Q : ℝ => Real.log Q/Q)
      (fun Q : ℝ => (Real.log Q)^2/Q) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with Q hQ
    have hg : (Real.log Q)^2/Q≠0 := div_ne_zero (pow_ne_zero 2 (Real.log_pos hQ).ne')
      (by linarith)
    exact fun h => (hg h).elim
  · have h : Tendsto (fun Q : ℝ => 1/Real.log Q) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Q hQ
    have hQ0 : Q≠0 := by linarith
    have hl0 : Real.log Q≠0 := (Real.log_pos hQ).ne'
    field_simp

theorem positiveLog_tail_isLittleO {c : ℕ → ℝ} {M : ℝ}
    (hc0 : c 0=0) (hc : ∀ n, 0 ≤ c n) (hM : 0 ≤ M)
    (hA : ∀ N : ℕ, (∑ n ∈ Finset.Ioc 0 N, c n) ≤ M*N) :
    Asymptotics.IsLittleO atTop (positiveLogTail c) (fun Q : ℝ => (Real.log Q)^2/Q) :=
  (positiveLog_tail_isBigO hc0 hc hM hA).trans_isLittleO log_linear_isLittleO_square

end NField.Alignment.CollisionPositiveLogTail
