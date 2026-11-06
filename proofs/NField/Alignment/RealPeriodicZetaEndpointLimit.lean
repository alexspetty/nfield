/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealPeriodicZetaEndpoint

/-! # The full real cotangent endpoint of the periodic zeta kernel -/

noncomputable section
namespace NField.Alignment.RealPeriodicZetaEndpoint

open scoped BigOperators Topology
open Filter Set

theorem paired_tail_summable {x σ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hσ : σ ∈ Icc (1 : ℝ) 2) : Summable (fun n : ℕ => pairedTerm x σ (n+1)) := by
  have hmajorant : Summable (fun n : ℕ => 4*(n+1 : ℝ)^(-2 : ℝ)) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-2 : ℝ)) 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  exact hmajorant.of_norm_bounded (paired_tail_bound hx hσ)

def pairedValue (x σ : ℝ) : ℝ :=
  x^(-σ) + pairedTerm x σ 0 + ∑' n : ℕ, pairedTerm x σ (n+1)

theorem paired_value_eq {x σ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hσ : σ ∈ Icc (1 : ℝ) 2) :
    pairedValue x σ = x^(-σ) + ∑' n : ℕ, pairedTerm x σ n := by
  have hs : Summable (pairedTerm x σ) :=
    (summable_nat_add_iff 1).mp (paired_tail_summable hx hσ)
  have h := hs.sum_add_tsum_nat_add 1
  simpa [pairedValue, add_assoc] using congrArg (fun y : ℝ => x^(-σ)+y) h

theorem paired_value_continuous {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (pairedValue x) (Icc 1 2) := by
  unfold pairedValue
  apply ContinuousOn.add _ (paired_tail_continuous hx)
  apply ContinuousOn.add
  · exact (continuous_const.rpow continuous_neg (fun _ => Or.inl hx.1.ne')).continuousOn
  · unfold pairedTerm
    apply Continuous.continuousOn
    apply Continuous.sub
    · exact continuous_const.rpow continuous_neg (fun _ => Or.inl (by linarith [hx.1]))
    · exact continuous_const.rpow continuous_neg (fun _ => Or.inl (by linarith [hx.2]))

theorem real_interior_not_integer {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n,hn⟩
  have he : (n : ℝ) = x := by exact_mod_cast hn
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith [hx.1])
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith [hx.2])
  omega

theorem paired_value_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ((pairedValue x 1 : ℝ) : ℂ) =
      (Real.pi : ℂ)*Complex.cot ((Real.pi : ℂ)*(x : ℂ)) := by
  rw [paired_value_eq hx (by norm_num), Complex.ofReal_add, Complex.ofReal_tsum]
  have hterms (n : ℕ) : ((pairedTerm x 1 n : ℝ) : ℂ) =
      1/((x : ℂ)-(n+1)) + 1/((x : ℂ)+(n+1)) := by
    simp only [pairedTerm, Real.rpow_neg_one, Complex.ofReal_sub, Complex.ofReal_inv,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
    rw [show (n : ℂ)+1-(x : ℂ) = -((x : ℂ)-(n+1)) by ring, inv_neg]
    simp only [one_div]
    ring
  simp_rw [hterms]
  rw [← cot_series_rep' (real_interior_not_integer hx), Real.rpow_neg_one, Complex.ofReal_inv]
  ring

/-- The odd Hurwitz function has its cotangent value at every real
interior argument, including irrational arguments. -/
theorem hurwitz_odd_one_cotangent {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) 1 =
      (Real.pi : ℂ)/2*Complex.cot ((Real.pi : ℂ)*(x : ℂ)) := by
  have hlim : Tendsto (pairedValue x) (𝓝[>] (1 : ℝ)) (𝓝 (pairedValue x 1)) := by
    have h := (paired_value_continuous hx) 1 (by norm_num)
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE (by norm_num : (1 : ℝ) < 2)] at h
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hlimC : Tendsto (fun σ : ℝ => ((pairedValue x σ : ℝ) : ℂ)/2)
      (𝓝[>] (1 : ℝ)) (𝓝 (((pairedValue x 1 : ℝ) : ℂ)/2)) :=
    (Complex.continuous_ofReal.tendsto _ |>.comp hlim).div_const 2
  have heq : (fun σ : ℝ => ((pairedValue x σ : ℝ) : ℂ)/2) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun σ : ℝ => HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) (σ : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), σ < 2 from
        (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds)]
      with σ hσ hσ2
    rw [paired_value_eq hx ⟨hσ.le,hσ2.le⟩]
    exact paired_series_eq hx hσ
  have hcont : Tendsto (fun σ : ℝ =>
      HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) (σ : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) 1)) := by
    have h : Continuous (fun σ : ℝ =>
        HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) (σ : ℂ)) :=
      (HurwitzZeta.differentiable_hurwitzZetaOdd (x : UnitAddCircle)).continuous.comp
        Complex.continuous_ofReal
    exact (h.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have h := tendsto_nhds_unique hcont (hlimC.congr' heq)
  rw [paired_value_one hx] at h
  exact h.trans (by ring)

/-- Title: `Cotangent endpoint of the real kernel`.

The exact printed right endpoint, with the paper's complete real
quantifier and Mathlib's continued exponential zeta function. -/
theorem real_kernel_right_cotangent (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HurwitzZeta.expZeta (x : UnitAddCircle) (1-(1 : ℂ)) =
      -(1/2 : ℂ) + Complex.I/2*Complex.cot ((Real.pi : ℂ)*(x : ℂ)) := by
  have hs := HurwitzZeta.sinZeta_one_sub (x : UnitAddCircle) (s := 1) (by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  norm_num only [sub_self, Complex.cpow_neg_one, Complex.Gamma_one,
    Complex.sin_pi_div_two, mul_one] at hs
  rw [hurwitz_odd_one_cotangent hx] at hs
  rw [sub_self, HurwitzZeta.expZeta, HurwitzZeta.cosZeta_apply_zero, hs]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end NField.Alignment.RealPeriodicZetaEndpoint
