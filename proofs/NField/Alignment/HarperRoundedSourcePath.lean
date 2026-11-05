/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperCriticalGoodEvent

/-!
# The recursive approximations satisfy the actual source frequency bounds

The frequency is the approximation at each selected block minus the
original frequency. Reversed-block growth proves the needed two-thirds
power condition; it is not assumed as an approximation hypothesis.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperRoundedSourcePath
open MeasureTheory HarperPrimeBlocks HarperPrimeBlockGrowth HarperPrimeBlockPath
  HarperFrequencyMesh HarperSourceBarrierBound HarperTiltedMeasure HarperEulerIntegral

theorem two_thirds_power_bound {s : ℝ} (hs : 0 ≤ s) :
    2*(s+1)^(2/3 : ℝ) ≤ s+4 := by
  have hp : 0 < s+1 := by linarith
  have hc : ((s+1)^(2/3 : ℝ))^3 = (s+1)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp.le]
    norm_num
  apply (pow_le_pow_iff_left₀ (by positivity) (by linarith : 0 ≤ s+4) (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow,hc]
  nlinarith [pow_nonneg hs 3,sq_nonneg s]

theorem reversed_logScale_frequency {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l)
    (hfirst : Real.exp 4 ≤ logScale x (l 0)) (i : Fin (n+1)) :
    2*((i.val : ℝ)+1)^(2/3 : ℝ) ≤ Real.log (logScale x (l i)) := by
  have hp : 0 < logScale x (l 0) := (Real.exp_pos 4).trans_le hfirst
  have hg := reversed_block_log_growth hx hl i
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos (i.val : ℝ)) hp) hg
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) hp.ne',Real.log_exp] at hlog
  change (i.val : ℝ)+Real.log (logScale x (l 0)) ≤ Real.log (logScale x (l i)) at hlog
  have hb : 4 ≤ Real.log (logScale x (l 0)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 4) hfirst
  exact (two_thirds_power_bound (Nat.cast_nonneg (α := ℝ) i.val)).trans (by linarith)

theorem approximation_frequency_bound {x : ℝ} (hx : 1 < x) {n : ℕ}
    {l : Fin (n+1) → ℕ} (hl : StrictAnti l)
    (hfirst : Real.exp 4 ≤ logScale x (l 0)) (t : ℝ) (i : Fin (n+1)) :
    |approximation x t (l i)-t| ≤
      1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i))) := by
  have he : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hLi : Real.exp 4 ≤ logScale x (l i) :=
    hfirst.trans (reversed_block_log_ge hx hl i)
  have hL : 1 < logScale x (l i) := by linarith
  have hpow := reversed_logScale_frequency hx hl hfirst i
  have hp : 0 < ((i.val : ℝ)+1)^(2/3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hlog := Real.log_pos hL
  calc
    _ ≤ 2*mesh x (l i) := by simpa only [abs_sub_comm] using approximation_error hx (l i) hL t
    _ ≤ _ := by
      unfold mesh
      rw [mul_one_div]
      apply (div_le_div_iff₀ (mul_pos (by linarith) hlog) (mul_pos hp (by linarith : 0 < logScale x (l i)))).mpr
      change 2*(_*logScale x (l i)) ≤ 1*(logScale x (l i)*Real.log (logScale x (l i)))
      have hm := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ logScale x (l i))
      nlinarith

theorem actual_rounded_source_barrier {b : ℝ} (hb : 0 ≤ b) :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ (t : ℝ) (u v : Fin (n+1) → ℝ),
        ∀ a : ℝ, 1 ≤ a →
        (∀ j, -a-b*((j.val : ℝ)+1) ≤ u j) →
        (∀ j, v j ≤ a+((j.val : ℝ)+1)+10*Real.log ((j.val : ℝ)+1)) →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real
          (blockPathEvent x l (fun i => approximation x t (l i)-t) u v) ≤
          sourceBarrierConstant b*min 1 (a/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨A,hA⟩ := actual_source_barrier_array hb
  refine ⟨max A (Real.exp (Real.exp 4)),fun x hx n l hl hfirst t u v a ha hu hv => ?_⟩
  have hlog : Real.exp 4 ≤ logScale x (l 0) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 4)) ((le_max_right _ _).trans hfirst)
    simpa only [Real.log_exp,logScale] using h
  exact hA x hx n l hl ((le_max_left _ _).trans hfirst) _ u v
    (approximation_frequency_bound hx hl hlog t) a ha hu hv

end NField.Alignment.HarperRoundedSourcePath
