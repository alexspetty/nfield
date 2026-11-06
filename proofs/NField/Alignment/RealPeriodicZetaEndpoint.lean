/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.Tannery

/-! # The cotangent endpoint at every real interior argument

The paired Hurwitz series is uniformly dominated at the boundary parameter.
This identifies Mathlib's continued value, and then uses Mathlib's cotangent
partial-fraction expansion. No rationality hypothesis is imposed.
-/

noncomputable section
namespace NField.Alignment.RealPeriodicZetaEndpoint

open scoped BigOperators Topology
open Filter Set

theorem paired_rpow_bound {r a b σ : ℝ} (hr : 1 ≤ r)
    (ha : r ≤ a) (hb : r ≤ b) (hab : |a-b| ≤ 2)
    (hσ : σ ∈ Icc (1 : ℝ) 2) :
    |a ^ (-σ) - b ^ (-σ)| ≤ 4 * r ^ (-2 : ℝ) := by
  rcases hσ with ⟨hσ1,hσ2⟩
  have hd (t : ℝ) (ht : t ∈ Ici r) :
      HasDerivWithinAt (fun t : ℝ => t ^ (-σ))
        ((-σ)*t^(-σ-1)) (Ici r) t := by
    change r ≤ t at ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith : t ≠ 0))).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Ici r) :
      ‖(-σ)*t^(-σ-1)‖ ≤ 2*r^(-2 : ℝ) := by
    have ht1 : 1 ≤ t := hr.trans ht
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ σ),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have hp : t^(-σ-1) ≤ r^(-2 : ℝ) := by
      calc
        _ ≤ t^(-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) ht (by norm_num)
    exact mul_le_mul hσ2 hp (Real.rpow_nonneg (by linarith) _) (by norm_num)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound
    (convex_Ici r) hb ha
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
  calc
    _ ≤ 2*r^(-2 : ℝ)*|a-b| := hm
    _ ≤ 2*r^(-2 : ℝ)*2 := mul_le_mul_of_nonneg_left hab (by positivity)
    _ = _ := by ring

def pairedTerm (x σ : ℝ) (n : ℕ) : ℝ :=
  (n+1+x)^(-σ) - (n+1-x)^(-σ)

theorem paired_tail_bound {x σ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hσ : σ ∈ Icc (1 : ℝ) 2) (n : ℕ) :
    ‖pairedTerm x σ (n+1)‖ ≤ 4*(n+1 : ℝ)^(-2 : ℝ) := by
  unfold pairedTerm
  rw [Real.norm_eq_abs]
  push_cast
  apply paired_rpow_bound (r := (n : ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  · linarith [hx.1]
  · linarith [hx.2]
  · rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  · exact hσ

theorem paired_tail_continuous {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun σ : ℝ => ∑' n : ℕ, pairedTerm x σ (n+1)) (Icc 1 2) := by
  apply continuousOn_tsum (u := fun n : ℕ => 4*(n+1 : ℝ)^(-2 : ℝ))
  · intro n
    apply Continuous.continuousOn
    unfold pairedTerm
    apply Continuous.sub
    · exact continuous_const.rpow continuous_neg (fun _ => Or.inl (by
        have hn := Nat.cast_nonneg (α := ℝ) (n+1)
        linarith [hx.1]))
    · exact continuous_const.rpow continuous_neg (fun _ => Or.inl (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        push_cast
        linarith [hx.2]))
  · apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-2 : ℝ)) 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  · intro n σ hσ
    exact paired_tail_bound hx hσ n

theorem ofReal_rpow_neg {t : ℝ} (ht : 0 ≤ t) (σ : ℝ) :
    ((t^(-σ) : ℝ) : ℂ) = 1/(t : ℂ)^(σ : ℂ) := by
  rw [Real.rpow_neg ht, Complex.ofReal_inv, Complex.ofReal_cpow ht]
  simp only [one_div]

/-- The paired real series agrees with the continued odd Hurwitz function
where the original Dirichlet series converges absolutely. -/
theorem paired_series_eq {x σ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hσ : 1 < σ) :
    (((x^(-σ) + ∑' n : ℕ, pairedTerm x σ n : ℝ) : ℂ) / 2) =
      HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) (σ : ℂ) := by
  have hfirst := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨hx.1.le,hx.2.le⟩
    (s := (σ : ℂ)) (by simpa using hσ)
  have hsecond := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (show (1-x : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hx.1,hx.2])
    (s := (σ : ℂ)) (by simpa using hσ)
  have htail : HasSum (fun n : ℕ => 1/(((n+1 : ℕ) : ℂ)+(x : ℂ))^(σ : ℂ))
      (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (σ : ℂ) -
        1/(x : ℂ)^(σ : ℂ)) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ =>
      1/((n : ℂ)+(x : ℂ))^(σ : ℂ)) 1).mpr
    simpa using hfirst
  have hpaired : HasSum (fun n : ℕ => ((pairedTerm x σ n : ℝ) : ℂ))
      (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (σ : ℂ) -
        ((x^(-σ) : ℝ) : ℂ) -
        HurwitzZeta.hurwitzZeta ((1-x : ℝ) : UnitAddCircle) (σ : ℂ)) := by
    rw [ofReal_rpow_neg hx.1.le]
    refine (htail.sub hsecond).congr_fun fun n => ?_
    unfold pairedTerm
    rw [Complex.ofReal_sub, ofReal_rpow_neg (by
      have hn := Nat.cast_nonneg (α := ℝ) n; linarith [hx.1]),
      ofReal_rpow_neg (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith [hx.2])]
    push_cast
    ring
  have hreflect : ((1-x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  rw [Complex.ofReal_add, Complex.ofReal_tsum, hpaired.tsum_eq, hreflect,
    HurwitzZeta.hurwitzZetaOdd_eq]
  ring

end NField.Alignment.RealPeriodicZetaEndpoint
