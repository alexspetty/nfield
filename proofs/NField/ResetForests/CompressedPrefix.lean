/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PrefixReadout
/-! # Exact correspondence with the smaller physical prefix records -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PrefixGeometry

open scoped BigOperators Matrix
open RecordGeometry

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def compressedRecord (A : Matrix ι (Fin N) ℝ) (s : Finset ι) : Matrix ↥s (Fin N) ℝ :=
  fun i j => A i.val j

omit [Fintype ι] [DecidableEq ι] in
theorem compressed_reading (A : Matrix ι (Fin N) ℝ) (s : Finset ι)
    (c : Fin N → ℝ) (i : ↥s) : (compressedRecord A s *ᵥ c) i = (A *ᵥ c) i.val := rfl

omit [Fintype ι] in
theorem compressed_reading_eq_iff (A : Matrix ι (Fin N) ℝ) (s : Finset ι)
    (x y : Fin N → ℝ) :
    compressedRecord A s *ᵥ x = compressedRecord A s *ᵥ y ↔
      restrictedRecord A s *ᵥ x = restrictedRecord A s *ᵥ y := by
  constructor
  · intro h
    ext i
    by_cases hi : i ∈ s
    · simpa only [restricted_reading, if_pos hi, compressed_reading] using congrFun h ⟨i, hi⟩
    · simp only [restricted_reading, if_neg hi]
  · intro h
    ext i
    simpa only [restricted_reading, if_pos i.property, compressed_reading] using congrFun h i.val

theorem compressed_projection_eq_restricted (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (s : Finset ι) (c : Fin N → ℝ) :
    oldSource G hG (compressedRecord A s) c = oldSource G hG (restrictedRecord A s) c := by
  let u := oldSource G hG (compressedRecord A s) c
  let w := oldSource G hG (restrictedRecord A s) c
  let d := u - w
  have hu : compressedRecord A s *ᵥ u = compressedRecord A s *ᵥ c := old_source_reading G hG _ c
  have hw : restrictedRecord A s *ᵥ w = restrictedRecord A s *ᵥ c := old_source_reading G hG _ c
  have hwc := (compressed_reading_eq_iff A s w c).mpr hw
  have hum := (compressed_reading_eq_iff A s u c).mp hu
  have hdc : compressedRecord A s *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hu, hwc, sub_self]
  have hdm : restrictedRecord A s *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hum, hw, sub_self]
  have h1 : sourceWork G u d = 0 := lifted_kernel_work_zero G hG (compressedRecord A s) _ _ hdc
  have h2 : sourceWork G w d = 0 := lifted_kernel_work_zero G hG (restrictedRecord A s) _ _ hdm
  have he : sourceWork G d d = 0 := by
    change sourceWork G (u - w) d = 0
    rw [work_sub_left, h1, h2, sub_self]
  exact sub_eq_zero.mp ((source_work_zero_iff G hG d).mp he)

theorem prefix_source_compressed (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    prefixSource G hG A J c r = oldSource G hG (compressedRecord A (J r)) c :=
  (compressed_projection_eq_restricted G hG A (J r) c).symm

def compressedEnergy (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) : ℝ :=
  let A_J := compressedRecord A (J r)
  (A_J *ᵥ c) ⬝ᵥ (recordInverse G hG A_J *ᵥ (A_J *ᵥ c))

def compressedPrediction (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) : ℝ :=
  let A_J := compressedRecord A (J r)
  b ⬝ᵥ ((A * G⁻¹ * A_Jᵀ) *ᵥ (recordInverse G hG A_J *ᵥ (A_J *ᵥ c)))

theorem compressed_work_formula (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    sourceWork G (prefixSource G hG A J c r) (prefixSource G hG A J c r) =
      compressedEnergy G hG A J c r := by
  rw [prefix_source_compressed]
  exact lifted_record_work G hG (compressedRecord A (J r)) c

theorem compressed_full_future_readings (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    A *ᵥ prefixSource G hG A J c r =
      (A * G⁻¹ * (compressedRecord A (J r))ᵀ) *ᵥ
        (recordInverse G hG (compressedRecord A (J r)) *ᵥ (compressedRecord A (J r) *ᵥ c)) := by
  rw [prefix_source_compressed]
  simp only [oldSource, liftMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem compressed_detector_formula (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (c : Fin N → ℝ) (r : ℕ) :
    finalReadout A b (prefixSource G hG A J c r) = compressedPrediction G hG A b J c r :=
  congrArg (fun y => b ⬝ᵥ y) (compressed_full_future_readings G hG A J c r)

theorem compressed_increment_cost_formula (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ) (J : ℕ → Finset ι) (hJ : Monotone J)
    (c : Fin N → ℝ) (L : ℕ) :
    prefixCost G hG A b J c L =
      ∑ r ∈ Finset.range L,
        (compressedPrediction G hG A b J c (r + 1) - compressedPrediction G hG A b J c r) ^ 2 /
          (compressedEnergy G hG A J c (r + 1) - compressedEnergy G hG A J c r) := by
  rw [prefix_increment_cost_formula G hG A b J hJ c L]
  simp only [compressed_work_formula, compressed_detector_formula]

end NField.ResetForests.PrefixGeometry
