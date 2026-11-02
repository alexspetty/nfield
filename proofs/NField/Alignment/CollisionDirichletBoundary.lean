/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SawtoothLValue
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform Dirichlet bounds for the actual boundary derivatives

All limits here are limits of ordered finite sums. The quantitative
summation-by-parts estimate works for any nonnegative decreasing real
coefficient sequence, including the harmonic coefficients after their
initial terms have been removed.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionDirichletBoundary

open scoped BigOperators Topology
open Filter Finset

theorem norm_sum_range_smul_le
    {f : ℕ → ℝ} {z : ℕ → ℂ} {C : ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hfanti : Antitone f)
    (hC : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ C) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, f i • z i‖ ≤ C * f 0 := by
  rw [Finset.sum_range_by_parts]
  calc
    ‖f (n - 1) • ∑ i ∈ Finset.range n, z i -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖
        ≤ ‖f (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
            ‖∑ i ∈ Finset.range (n - 1),
              (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖ :=
          norm_sub_le _ _
    _ ≤ f (n - 1) * C +
          ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * C := by
      gcongr
      · rw [norm_smul, Real.norm_of_nonneg (hf0 _)]
        exact mul_le_mul_of_nonneg_left (hC n) (hf0 _)
      · calc
          ‖∑ i ∈ Finset.range (n - 1),
              (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖
              ≤ ∑ i ∈ Finset.range (n - 1),
                  ‖(f (i + 1) - f i) •
                    ∑ j ∈ Finset.range (i + 1), z j‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * C := by
            gcongr with i hi
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr (hfanti (Nat.le_succ i))),
              neg_sub]
            exact mul_le_mul_of_nonneg_left (hC (i + 1))
              (sub_nonneg.mpr (hfanti (Nat.le_succ i)))
    _ = C * f 0 := by
      rw [← Finset.sum_mul]
      rw [show (∑ i ∈ Finset.range (n - 1), (f i - f (i + 1))) =
          -(∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i)) by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring]
      rw [Finset.sum_range_sub, mul_comm (f (n - 1)) C]
      ring


theorem norm_geometric_partial_le {z : ℂ} (hzNorm : ‖z‖=1)
    (hz : z≠1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z^k‖ ≤ 2/‖z-1‖ := by
  rw [geom_sum_eq hz,norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z^n-1‖ ≤ ‖z^n‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow,hzNorm,one_pow,norm_one]; norm_num

theorem norm_geometric_tail_le {z : ℂ} (hzNorm : ‖z‖=1)
    (hz : z≠1) (m n : ℕ) :
    ‖∑ k ∈ Finset.range n, z^(m+k+1)‖ ≤ 2/‖z-1‖ := by
  have heq : (∑ k ∈ Finset.range n, z^(m+k+1)) =
      z^(m+1)*∑ k ∈ Finset.range n, z^k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← pow_add]
    congr 1
    omega
  rw [heq,norm_mul,norm_pow,hzNorm,one_pow,one_mul]
  exact norm_geometric_partial_le hzNorm hz n

def dirichletPartial (f : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, (f k : ℂ)*z^(k+1)

theorem norm_weighted_geometric_tail_le {f : ℕ → ℝ}
    (hf0 : ∀ n, 0≤f n) (hfanti : Antitone f)
    {z : ℂ} (hzNorm : ‖z‖=1) (hz : z≠1) (m n : ℕ) :
    ‖∑ k ∈ Finset.range n, (f (m+k) : ℂ)*z^(m+k+1)‖ ≤
      (2/‖z-1‖)*f m := by
  have hb := norm_sum_range_smul_le
    (f := fun k => f (m+k)) (z := fun k => z^(m+k+1))
    (fun k => hf0 _) (fun i j hij => hfanti (Nat.add_le_add_left hij m))
    (norm_geometric_tail_le hzNorm hz m) n
  simpa only [add_zero,Complex.real_smul] using hb

theorem dirichletPartial_add (f : ℕ → ℝ) (m n : ℕ) (z : ℂ) :
    dirichletPartial f (m+n) z-dirichletPartial f m z =
      ∑ k ∈ Finset.range n, (f (m+k) : ℂ)*z^(m+k+1) := by
  simp only [dirichletPartial,Finset.sum_range_add,add_sub_cancel_left]

theorem dirichletPartial_cauchy {f : ℕ → ℝ}
    (hfanti : Antitone f) (hf : Tendsto f atTop (𝓝 0))
    {z : ℂ} (hzNorm : ‖z‖=1) (hz : z≠1) :
    CauchySeq (fun n => dirichletPartial f n z) := by
  have h := hfanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf
    (norm_geometric_tail_le hzNorm hz 0)
  simpa only [zero_add,Complex.real_smul,dirichletPartial] using h

theorem dirichlet_limit_tail_bound {f : ℕ → ℝ}
    (hf0 : ∀ n, 0≤f n) (hfanti : Antitone f)
    {z L : ℂ} (hzNorm : ‖z‖=1) (hz : z≠1)
    (hL : Tendsto (fun n => dirichletPartial f n z) atTop (𝓝 L)) (m : ℕ) :
    ‖L-dirichletPartial f m z‖ ≤ (2/‖z-1‖)*f m := by
  have ht := ((hL.comp (tendsto_add_atTop_nat m)).sub_const
    (dirichletPartial f m z)).norm
  apply le_of_tendsto ht
  exact Eventually.of_forall fun n => by
    change ‖dirichletPartial f (n+m) z-dirichletPartial f m z‖ ≤ _
    rw [Nat.add_comm n m]
    rw [dirichletPartial_add]
    exact norm_weighted_geometric_tail_le hf0 hfanti hzNorm hz m n

/-- Pointwise ordered convergence upgrades to uniform convergence on any
set of unit roots separated from one. No absolute summability is assumed. -/
theorem dirichlet_tendstoUniformlyOn {α : Type*} {s : Set α}
    {f : ℕ → ℝ} (hf0 : ∀ n, 0≤f n) (hfanti : Antitone f)
    (hf : Tendsto f atTop (𝓝 0)) {root L : α → ℂ} {δ : ℝ}
    (hδ : 0<δ) (hnorm : ∀ x∈s, ‖root x‖=1)
    (hsep : ∀ x∈s, δ≤‖root x-1‖)
    (hL : ∀ x∈s, Tendsto (fun n => dirichletPartial f n (root x)) atTop (𝓝 (L x))) :
    TendstoUniformlyOn (fun n x => dirichletPartial f n (root x)) L atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, (2/δ)*f n<ε := by
    have hlim := hf.const_mul (2/δ)
    have hlim' : Tendsto (fun n => (2/δ)*f n) atTop (𝓝 0) := by simpa using hlim
    exact (tendsto_order.1 hlim').2 ε hε
  filter_upwards [hsmall] with n hn x hx
  have hne : root x≠1 := by
    intro heq
    have hb := hsep x hx
    rw [heq,sub_self,norm_zero] at hb
    linarith
  rw [dist_eq_norm]
  calc
    ‖L x-dirichletPartial f n (root x)‖ ≤ (2/‖root x-1‖)*f n :=
      dirichlet_limit_tail_bound hf0 hfanti (hnorm x hx) hne (hL x hx) n
    _ ≤ (2/δ)*f n := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) hδ (hsep x hx)) (hf0 n)
    _ < ε := hn

end NField.Alignment.CollisionDirichletBoundary
