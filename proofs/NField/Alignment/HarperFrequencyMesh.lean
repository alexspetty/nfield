/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperFrequencyRounding

/-!
# The literal multiscale frequency mesh

The mesh at block j is 1/(log(X_j)*log(log(X_j))), exactly the source
denominator. Its widths at least double while log(X_j)>1. This turns
the recursive rounding error into twice the current mesh width.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperFrequencyMesh
open HarperPrimeBlocks HarperFrequencyRounding

def logScale (x : ℝ) (j : ℕ) : ℝ := Real.log (blockUpper x j)
def mesh (x : ℝ) (j : ℕ) : ℝ := 1/(logScale x j*Real.log (logScale x j))
def approximation (x t : ℝ) (j : ℕ) : ℝ := rounded (mesh x) t (j+1)

theorem logScale_eq {x : ℝ} (hx : 0 < x) (j : ℕ) :
    logScale x j = Real.exp (-((j : ℝ)+1))*Real.log x := by
  exact Real.log_rpow hx _

theorem logScale_succ {x : ℝ} (hx : 0 < x) (j : ℕ) :
    logScale x j = Real.exp 1*logScale x (j+1) := by
  rw [logScale_eq hx,logScale_eq hx,← mul_assoc,← Real.exp_add]
  congr 2
  push_cast
  ring

theorem logScale_antitone {x : ℝ} (hx : 1 < x) : Antitone (logScale x) := by
  intro i j hij
  exact Real.log_le_log (by linarith [blockUpper_gt_one hx j]) (blockUpper_antitone hx.le hij)

theorem mesh_pos {x : ℝ} {j : ℕ} (hj : 1 < logScale x j) : 0 < mesh x j := by
  exact one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos hj))

theorem mesh_doubling {x : ℝ} (hx : 1 < x) (j : ℕ) (hj : 1 < logScale x (j+1)) :
    2*mesh x j ≤ mesh x (j+1) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : 0 < logScale x (j+1) := by linarith
  have hlog := Real.log_pos hj
  have hprev : 1 < logScale x j := hj.trans_le (logScale_antitone hx (Nat.le_succ j))
  have hden : 2*(logScale x (j+1)*Real.log (logScale x (j+1))) ≤
      logScale x j*Real.log (logScale x j) := by
    rw [logScale_succ (by linarith : 0 < x) j,Real.log_mul (ne_of_gt (Real.exp_pos 1)) hp.ne',Real.log_exp]
    have hmul := mul_le_mul_of_nonneg_right he (mul_nonneg hp.le hlog.le)
    have heL : 0 ≤ Real.exp 1*logScale x (j+1) := mul_nonneg (Real.exp_nonneg _) hp.le
    nlinarith
  unfold mesh
  rw [mul_one_div]
  exact (div_le_div_iff₀ (mul_pos (by linarith) (Real.log_pos hprev)) (mul_pos hp hlog)).mpr
    (by simpa only [one_mul] using hden)

theorem approximation_error {x : ℝ} (hx : 1 < x) (j : ℕ) (hj : 1 < logScale x j) (t : ℝ) :
    |t-approximation x t j| ≤ 2*mesh x j := by
  apply rounded_error_le_two
  · intro i hi
    exact mesh_pos (hj.trans_le (logScale_antitone hx hi))
  · intro i hi
    exact mesh_doubling hx i (hj.trans_le (logScale_antitone hx (by omega)))

theorem approximation_le {x : ℝ} (hx : 1 < x) (j : ℕ) (hj : 1 < logScale x j) (t : ℝ) :
    approximation x t j ≤ t := by
  have h := rounded_error (d := mesh x) (j+1) (fun i hi => mesh_pos (hj.trans_le (logScale_antitone hx (by omega)))) t
  exact sub_nonneg.mp h.1

theorem mesh_le_quarter {x : ℝ} {j : ℕ} (hj : Real.exp 2 ≤ logScale x j) :
    mesh x j ≤ 1/4 := by
  have he : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hp : 0 < logScale x j := by linarith
  have hl : 2 ≤ Real.log (logScale x j) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hj
  unfold mesh
  apply (div_le_div_iff₀ (mul_pos hp (by linarith)) (by norm_num : (0 : ℝ) < 4)).mpr
  nlinarith

theorem approximation_abs_le_one {x t : ℝ} (hx : 1 < x) (j : ℕ)
    (hj : Real.exp 2 ≤ logScale x j) (ht : |t| ≤ 1/2) : |approximation x t j| ≤ 1 := by
  have he : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h := approximation_error hx j (by linarith : 1 < logScale x j) t
  have hm := mesh_le_quarter hj
  have ht' := abs_le.mp ht
  have hd := abs_le.mp h
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end NField.Alignment.HarperFrequencyMesh
