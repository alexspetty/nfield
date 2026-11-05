/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLogarithmicSourcePath

/-!
# Removing a prefix from an actual block path

The suffix bounds subtract the opposite prefix endpoint bound. These are
deterministic inclusions under the original weighted measure; no change
of law or independence assertion is needed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPathSuffix
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperKilledPath
  HarperGaussianPathSplit HarperPathMaximum HarperPrimeBlockPath HarperPrimeBlocks
  HarperTiltedMeasure HarperEulerIntegral

theorem partialSum_suffix {m n : ℕ} (z : Fin (m+n) → ℝ) (j : Fin n) :
    partialSum z (Fin.natAdd m j) =
      (∑ i : Fin m, z (Fin.castAdd n i))+partialSum (fun i => z (Fin.natAdd m i)) j := by
  have he : Fin.append (fun i => z (Fin.castAdd n i)) (fun i => z (Fin.natAdd m i)) = z := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [← partialSum_append_right,he]

theorem prefix_endpoint {m n : ℕ} (z : Fin ((m+1)+n) → ℝ) :
    partialSum z (Fin.castAdd n (Fin.last m)) = ∑ i : Fin (m+1), z (Fin.castAdd n i) := by
  have he : Fin.append (fun i => z (Fin.castAdd n i)) (fun i => z (Fin.natAdd (m+1) i)) = z := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [← he,partialSum_append_left,partialSum_last]
  simp

theorem pathEvent_suffix {m n : ℕ} (u v : Fin ((m+1)+n) → ℝ) :
    pathEvent u v ⊆ (fun z i => z (Fin.natAdd (m+1) i)) ⁻¹'
      pathEvent (fun j => u (Fin.natAdd (m+1) j)-v (Fin.castAdd n (Fin.last m)))
        (fun j => v (Fin.natAdd (m+1) j)-u (Fin.castAdd n (Fin.last m))) := by
  intro z hz j
  have hp := hz (Fin.castAdd n (Fin.last m))
  have hs := hz (Fin.natAdd (m+1) j)
  rw [prefix_endpoint] at hp
  rw [partialSum_suffix] at hs
  exact ⟨by linarith [hp.2,hs.1],by linarith [hp.1,hs.2]⟩

theorem blockPathEvent_suffix {m n : ℕ} (x : ℝ) (l : Fin ((m+1)+n) → ℕ)
    (t u v : Fin ((m+1)+n) → ℝ) :
    blockPathEvent x l t u v ⊆
      blockPathEvent x (fun i => l (Fin.natAdd (m+1) i)) (fun i => t (Fin.natAdd (m+1) i))
        (fun j => u (Fin.natAdd (m+1) j)-v (Fin.castAdd n (Fin.last m)))
        (fun j => v (Fin.natAdd (m+1) j)-u (Fin.castAdd n (Fin.last m))) := by
  intro ω hω
  exact pathEvent_suffix u v hω

theorem suffix_strictAnti {m n : ℕ} {l : Fin (m+n) → ℕ} (hl : StrictAnti l) :
    StrictAnti (fun i : Fin n => l (Fin.natAdd m i)) := by
  intro i j hij
  apply hl
  simpa only [Fin.lt_def,Fin.val_natAdd,Nat.add_lt_add_iff_left] using hij

theorem suffix_frequency_bound {m n : ℕ} {x : ℝ} (hx : 1 < x)
    (l : Fin (m+n) → ℕ) (t : Fin (m+n) → ℝ)
    (ht : ∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i))))
    (i : Fin n) :
    |t (Fin.natAdd m i)| ≤
      1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l (Fin.natAdd m i)))) := by
  apply (ht _).trans
  apply one_div_le_one_div_of_le
  · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.log_pos (blockUpper_gt_one hx _))
  · apply mul_le_mul_of_nonneg_right _ (Real.log_pos (blockUpper_gt_one hx _)).le
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    simp only [Fin.val_natAdd,Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) m]

end NField.Alignment.HarperPathSuffix
