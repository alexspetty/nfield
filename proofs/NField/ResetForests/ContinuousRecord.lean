/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.MinimumWork
/-! # The actual continuous work retains every mixed source term -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.RecordGeometry

open scoped BigOperators Matrix
open MeasureTheory NField.Alignment CollisionRampEnergy CommonResetGram SourceMetrics

theorem cutoff_field_add (N : ℕ) (c e : Fin N → ℝ) (x : ℝ) :
    weightedProfile N (cutoffCoefficients N (c + e)) x =
      weightedProfile N (cutoffCoefficients N c) x + weightedProfile N (cutoffCoefficients N e) x := by
  simp only [weighted_profile_fin, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem continuous_gram_mixed (N : ℕ) (c e : Fin N → ℝ) :
    sourceWork (continuousGram N) c e =
      FibreReconstruction.continuousWork N (cutoffCoefficients N c) (cutoffCoefficients N e) := by
  let f := weightedProfile N (cutoffCoefficients N c)
  let g := weightedProfile N (cutoffCoefficients N e)
  have hc := weighted_square_interval_integrable N (cutoffCoefficients N c) 0 1
  have he := weighted_square_interval_integrable N (cutoffCoefficients N e) 0 1
  have hce := FibreReconstruction.weighted_product_interval_integrable N
    (cutoffCoefficients N c) (cutoffCoefficients N e) 0 1
  have hi : (∫ x in (0 : ℝ)..1, weightedProfile N (cutoffCoefficients N (c + e)) x ^ 2) =
      (∫ x in (0 : ℝ)..1, f x ^ 2) + (∫ x in (0 : ℝ)..1, g x ^ 2) +
        2 * (∫ x in (0 : ℝ)..1, f x * g x) := by
    have hp (x : ℝ) : weightedProfile N (cutoffCoefficients N (c + e)) x ^ 2 =
        (f x ^ 2 + g x ^ 2) + 2 * (f x * g x) := by
      rw [cutoff_field_add]
      change (f x + g x) ^ 2 = _
      ring
    simp_rw [hp]
    rw [intervalIntegral.integral_add (hc.add he) (hce.const_mul 2),
      intervalIntegral.integral_add hc he, intervalIntegral.integral_const_mul]
  have hplus := continuous_gram_quadratic N (c + e)
  have hleft := continuous_gram_quadratic N c
  have hright := continuous_gram_quadratic N e
  simp only [star_trivial] at hplus hleft hright
  have hm := PacketQueries.symmetric_query_add (continuousGram N)
    (hermitian_transpose _ (continuous_gram_hermitian N)) c e
  change sourceWork (continuousGram N) c e = ∫ x in (0 : ℝ)..1, f x * g x
  change sourceWork (continuousGram N) (c + e) (c + e) =
    sourceWork (continuousGram N) c c + sourceWork (continuousGram N) e e +
    2 * sourceWork (continuousGram N) c e at hm
  change sourceWork (continuousGram N) (c + e) (c + e) = _ at hplus
  change sourceWork (continuousGram N) c c = ∫ x in (0 : ℝ)..1, f x ^ 2 at hleft
  change sourceWork (continuousGram N) e e = ∫ x in (0 : ℝ)..1, g x ^ 2 at hright
  linarith

theorem complete_continuous_record_work {N : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (A : Matrix ι (Fin N) ℝ) (B : Matrix κ (Fin N) ℝ) (c : Fin N → ℝ) :
    let u := oldSource G hG A c
    let v := enteringSource G hG A B c
    let z := residualSource G hG A B c
    FibreReconstruction.continuousWork N (cutoffCoefficients N c) (cutoffCoefficients N c) =
      FibreReconstruction.continuousWork N (cutoffCoefficients N u) (cutoffCoefficients N u) +
      FibreReconstruction.continuousWork N (cutoffCoefficients N v) (cutoffCoefficients N v) +
      FibreReconstruction.continuousWork N (cutoffCoefficients N z) (cutoffCoefficients N z) +
      2 * FibreReconstruction.continuousWork N (cutoffCoefficients N u) (cutoffCoefficients N v) +
      2 * FibreReconstruction.continuousWork N (cutoffCoefficients N u) (cutoffCoefficients N z) +
      2 * FibreReconstruction.continuousWork N (cutoffCoefficients N v) (cutoffCoefficients N z) := by
  dsimp only
  have hc := complete_source_decomposition G hG A B c
  have he := congrArg (fun x => sourceWork (continuousGram N) x x) hc
  rw [three_source_work _ (continuous_gram_hermitian N)] at he
  simpa only [continuous_gram_mixed] using he

end NField.ResetForests.RecordGeometry
