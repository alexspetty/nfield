/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralAbel

/-!
# The weighted square-log tail from the actual spectral mean

The infinite Abel identity is obtained from finite sums and integrable tails.
The mean input is the proved mean of the actual multiplicative spectral weight.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralTailMean

open scoped BigOperators Classical
open Filter MeasureTheory
open CollisionSpectralArithmetic CollisionSpectralEuler CollisionSpectralMean
open CollisionLogTailKernel CollisionSpectralAbel

theorem finite_tail_eq_range {Q : ℝ} (hQ : 0 ≤ Q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊Q⌋₊ N, weightedTerm n)=
      ∑ n ∈ Finset.range (N+1), if Q < (n : ℝ) then weightedTerm n else 0 := by
  have he : Finset.Ioc ⌊Q⌋₊ N=
      (Finset.range (N+1)).filter (fun n : ℕ => Q < (n : ℝ)) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_filter,Finset.mem_range,← Nat.floor_lt hQ]
    omega
  rw [he,Finset.sum_filter]

theorem finite_tail_tendsto {Q : ℝ} (hQ : 0 ≤ Q) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ioc ⌊Q⌋₊ N, weightedTerm n)
      atTop (nhds (weightedTail Q)) := by
  have h := (weightedTerm_summable.indicator {n : ℕ | Q < (n : ℝ)}).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,Set.indicator_apply,Set.mem_setOf_eq,
    ← finite_tail_eq_range hQ,weightedTail] using h

theorem weighted_boundary_tendsto :
    Tendsto (fun x : ℝ => logPowerKernel 2 x*partialWeight x) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun x =>
    mul_nonneg (squareLogKernel_nonneg x) (partialWeight_nonneg x))) _
    (logPower_div_linear_tendsto 2)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  calc
    _ ≤ logPowerKernel 2 x*x :=
      mul_le_mul_of_nonneg_left (partialWeight_le hx.le) (squareLogKernel_nonneg x)
    _ = (Real.log x)^2/x := by unfold logPowerKernel; field_simp

theorem derivative_partial_integral_tendsto {Q : ℝ} (hQ : 0 < Q)
    (hlog : 1 ≤ Real.log Q) :
    Tendsto (fun N : ℕ => ∫ x in Set.Ioc Q (N : ℝ), kernelDerivative x*partialWeight x)
      atTop (nhds (∫ x in Set.Ioi Q, kernelDerivative x*partialWeight x)) := by
  have h := intervalIntegral_tendsto_integral_Ioi Q (derivative_partial_integrableOn hQ hlog)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop Q] with N hN
  exact intervalIntegral.integral_of_le hN

theorem infinite_spectral_abel {Q : ℝ} (hQ : 0 < Q) (hlog : 1 ≤ Real.log Q) :
    weightedTail Q = -logPowerKernel 2 Q*partialWeight Q-
      ∫ x in Set.Ioi Q, kernelDerivative x*partialWeight x := by
  have h := ((weighted_boundary_tendsto.comp (tendsto_natCast_atTop_atTop (R := ℝ))).sub_const
    (logPowerKernel 2 Q*partialWeight Q)).sub (derivative_partial_integral_tendsto hQ hlog)
  simp only [zero_sub,neg_mul] at h ⊢
  apply tendsto_nhds_unique (finite_tail_tendsto hQ.le)
  apply h.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop Q] with N hN
  simpa only [Nat.floor_natCast,weightedTerm,Function.comp_def] using
    (finite_spectral_abel hQ hN).symm

def linearKernelPrimitive (x : ℝ) : ℝ := x*logPowerKernel 2 x+kernelTail x

theorem linearKernelPrimitive_hasDerivAt {x : ℝ} (hx : x≠0) :
    HasDerivAt linearKernelPrimitive (x*kernelDerivative x) x := by
  have h := ((hasDerivAt_id x).mul (squareLogKernel_hasDerivAt hx)).add
    (kernelTail_hasDerivAt hx)
  convert! h using 1
  dsimp [kernelDerivative]
  ring

theorem linearKernelPrimitive_tendsto_zero :
    Tendsto linearKernelPrimitive atTop (nhds 0) := by
  have h := (logPower_div_linear_tendsto 2).add kernelTail_tendsto_zero
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold linearKernelPrimitive logPowerKernel
  congr 1
  field_simp

theorem derivative_linear_integrableOn {Q : ℝ} (hQ : 0 < Q)
    (hlog : 1 ≤ Real.log Q) :
    IntegrableOn (fun x => x*kernelDerivative x) (Set.Ioi Q) :=
  integrableOn_Ioi_deriv_of_nonpos'
    (fun _ hx => linearKernelPrimitive_hasDerivAt (ne_of_gt (hQ.trans_le hx)))
    (fun _ hx => mul_nonpos_of_nonneg_of_nonpos (hQ.trans hx).le
      (kernelDerivative_nonpos (hQ.trans hx) (hlog.trans (Real.log_le_log hQ hx.le))))
    linearKernelPrimitive_tendsto_zero

theorem derivative_linear_integral {Q : ℝ} (hQ : 0 < Q)
    (hlog : 1 ≤ Real.log Q) :
    (∫ x in Set.Ioi Q, x*kernelDerivative x) = -linearKernelPrimitive Q := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun _ hx => linearKernelPrimitive_hasDerivAt (ne_of_gt (hQ.trans_le hx)))
    (fun _ hx => mul_nonpos_of_nonneg_of_nonpos (hQ.trans hx).le
      (kernelDerivative_nonpos (hQ.trans hx) (hlog.trans (Real.log_le_log hQ hx.le))))
    linearKernelPrimitive_tendsto_zero
  simpa only [zero_sub] using h

theorem kernelTail_pos {Q : ℝ} (hQ : 0 < Q) : 0 < kernelTail Q := by
  unfold kernelTail
  apply div_pos _ hQ
  nlinarith [sq_nonneg (Real.log Q+1)]

theorem kernel_boundary_le_tail {Q : ℝ} (hQ : 0 < Q) (hlog : 0 ≤ Real.log Q) :
    logPowerKernel 2 Q*Q ≤ kernelTail Q := by
  have he : logPowerKernel 2 Q*Q=(Real.log Q)^2/Q := by
    unfold logPowerKernel
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith) hQ.le

theorem derivative_mean_error_integral {Q : ℝ} (hQ : 0 < Q)
    (hlog : 1 ≤ Real.log Q) (C : ℝ) :
    (∫ x in Set.Ioi Q, kernelDerivative x*(partialWeight x-C*x))=
      (∫ x in Set.Ioi Q, kernelDerivative x*partialWeight x)+C*linearKernelPrimitive Q := by
  have he : (fun x => kernelDerivative x*(partialWeight x-C*x))=
      (fun x => kernelDerivative x*partialWeight x-C*(x*kernelDerivative x)) := by
    funext x
    ring
  rw [he,integral_sub (derivative_partial_integrableOn hQ hlog)
    ((derivative_linear_integrableOn hQ hlog).const_mul C),integral_const_mul,
    derivative_linear_integral hQ hlog]
  ring

theorem weighted_tail_error_identity {Q : ℝ} (hQ : 0 < Q)
    (hlog : 1 ≤ Real.log Q) (C : ℝ) :
    weightedTail Q-C*kernelTail Q =
      -(logPowerKernel 2 Q*(partialWeight Q-C*Q))-
        ∫ x in Set.Ioi Q, kernelDerivative x*(partialWeight x-C*x) := by
  rw [infinite_spectral_abel hQ hlog,derivative_mean_error_integral hQ hlog]
  unfold linearKernelPrimitive
  ring

theorem weighted_tail_error_bound {Q ε C : ℝ} (hQ : 0 < Q)
    (hlog : 1 ≤ Real.log Q) (hε : 0 ≤ ε)
    (hA : ∀ x ≥ Q, |partialWeight x-C*x| ≤ ε*x) :
    |weightedTail Q-C*kernelTail Q| ≤ 3*ε*kernelTail Q := by
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Ioi Q),
      ‖kernelDerivative x*(partialWeight x-C*x)‖ ≤ (2*ε)*logPowerKernel 2 x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ |kernelDerivative x| *(ε*x) :=
        mul_le_mul_of_nonneg_left (hA x hx.le) (abs_nonneg _)
      _ = ε*(|kernelDerivative x| *x) := by ring
      _ ≤ ε*(2*logPowerKernel 2 x) := mul_le_mul_of_nonneg_left
        (kernelDerivative_abs_bound (hQ.trans hx) (hlog.trans (Real.log_le_log hQ hx.le))) hε
      _ = _ := by ring
  have hI : |∫ x in Set.Ioi Q, kernelDerivative x*(partialWeight x-C*x)| ≤
      2*ε*kernelTail Q := by
    have h := norm_integral_le_of_norm_le ((squareLogKernel_integrableOn hQ).const_mul (2*ε))
      hbound
    simpa only [Real.norm_eq_abs,integral_const_mul,squareLogKernel_integral hQ] using h
  have hB : |logPowerKernel 2 Q*(partialWeight Q-C*Q)| ≤ ε*kernelTail Q := by
    rw [abs_mul,abs_of_nonneg (squareLogKernel_nonneg Q)]
    calc
      _ ≤ logPowerKernel 2 Q*(ε*Q) :=
        mul_le_mul_of_nonneg_left (hA Q le_rfl) (squareLogKernel_nonneg Q)
      _ = ε*(logPowerKernel 2 Q*Q) := by ring
      _ ≤ ε*kernelTail Q := mul_le_mul_of_nonneg_left
        (kernel_boundary_le_tail hQ (by linarith)) hε
  rw [weighted_tail_error_identity hQ hlog]
  calc
    _ ≤ |-(logPowerKernel 2 Q*(partialWeight Q-C*Q))|+
        |∫ x in Set.Ioi Q, kernelDerivative x*(partialWeight x-C*x)| := abs_sub _ _
    _ ≤ ε*kernelTail Q+2*ε*kernelTail Q := by rw [abs_neg]; exact add_le_add hB hI
    _ = _ := by ring

theorem weighted_tail_normalized_mean :
    Tendsto (fun Q : ℝ => weightedTail Q/kernelTail Q) atTop (nhds spectralConstant) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T,hT⟩ := Metric.tendsto_atTop.mp spectralWeight_real_mean (ε/6) (by positivity)
  refine ⟨max T (Real.exp 1),fun Q hQ => ?_⟩
  have hQT : T ≤ Q := (le_max_left _ _).trans hQ
  have hQE : Real.exp 1 ≤ Q := (le_max_right _ _).trans hQ
  have hQ0 : 0 < Q := (Real.exp_pos _).trans_le hQE
  have hlQ : 1 ≤ Real.log Q := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hQE
  have hA : ∀ x ≥ Q, |partialWeight x-spectralConstant*x| ≤ (ε/6)*x := by
    intro x hx
    have hx0 : 0 < x := hQ0.trans_le hx
    have ht := (hT x (hQT.trans hx)).le
    rw [Real.dist_eq] at ht
    change |partialWeight x/x-spectralConstant| ≤ ε/6 at ht
    have he : partialWeight x-spectralConstant*x=(partialWeight x/x-spectralConstant)*x := by
      field_simp
    rw [he,abs_mul,abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_right ht hx0.le
  have hb := weighted_tail_error_bound hQ0 hlQ (by positivity : 0 ≤ ε/6) hA
  rw [Real.dist_eq]
  have he : weightedTail Q/kernelTail Q-spectralConstant=
      (weightedTail Q-spectralConstant*kernelTail Q)/kernelTail Q := by
    field_simp [ne_of_gt (kernelTail_pos hQ0)]
  rw [he,abs_div,abs_of_pos (kernelTail_pos hQ0)]
  apply (div_le_iff₀ (kernelTail_pos hQ0)).mpr at hb
  exact hb.trans_lt (by linarith)

theorem weighted_tail_leading_mean :
    Tendsto (fun Q : ℝ => weightedTail Q/((Real.log Q)^2/Q))
      atTop (nhds spectralConstant) := by
  have h := weighted_tail_normalized_mean.mul kernelTail_leading_ratio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  exact div_mul_div_cancel₀ (ne_of_gt (kernelTail_pos hQ))

theorem weighted_tail_asymptotic :
    Asymptotics.IsEquivalent atTop weightedTail
      (fun Q : ℝ => spectralConstant*(Real.log Q)^2/Q) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have h := weighted_tail_leading_mean.div_const spectralConstant
  rw [div_self (ne_of_gt spectralConstant_pos)] at h
  convert! h using 1
  funext Q
  simp only [Pi.div_apply,div_div]
  congr 1
  ring

theorem spectral_weighted_tail_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun Q : ℝ => ∑' n : ℕ,
        if Q < (n : ℝ) then spectralWeight n*(Real.log n)^2/(n : ℝ)^2 else 0)
      (fun Q : ℝ => spectralConstant*(Real.log Q)^2/Q) := by
  have he : (fun Q : ℝ => ∑' n : ℕ,
      if Q < (n : ℝ) then spectralWeight n*(Real.log n)^2/(n : ℝ)^2 else 0)=weightedTail := by
    funext Q
    apply tsum_congr
    intro n
    dsimp only [weightedTail,weightedTerm,logPowerKernel]
    split_ifs <;> ring
  rw [he]
  exact weighted_tail_asymptotic

end NField.Alignment.CollisionSpectralTailMean
