/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothRough
import NField.Alignment.SteinhausCoordinates

/-!
# Weighted orthogonality of the actual rough factors

Weights depending only on primes at most `P` preserve orthogonality between
distinct rough factors. Apply this to the constructed Harper partition,
retaining the smooth factors inside the weighted expectation.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRoughOrthogonality

open scoped BigOperators
open MeasureTheory SteinhausMoment SteinhausCoordinates HarperSmoothRough
  HarperSmoothDivisor CollisionMertensInput HarperActualConditioning
  HarperRoundedCutoff HarperProductApproximation HarperParameterBounds

theorem rough_coordinates_disjoint {P : ℝ} {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    Disjoint (primesUpTo P)
      ((roughPart (primeBase P) u).primeFactors ∪
        (roughPart (primeBase P) v).primeFactors) := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  have hp := (primesUpTo_mem.mp hr).1
  have hle := (primesUpTo_mem.mp hr).2
  rcases Finset.mem_union.mp hs with hs | hs
  · exact (not_lt_of_ge hle) (canonical_rough_primes hu hp (Nat.mem_primeFactors.mp hs).2.1)
  · exact (not_lt_of_ge hle) (canonical_rough_primes hv hp (Nat.mem_primeFactors.mp hs).2.1)

theorem weighted_rough_pair_integral {P : ℝ} {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    {W : PhaseSpace → ℂ} (hW : Measurable W) (hdep : DependsOn (primesUpTo P) W) :
    (∫ ω, W ω * (steinhaus (roughPart (primeBase P) u) ω *
      star (steinhaus (roughPart (primeBase P) v) ω)) ∂phaseMeasure) =
      (∫ ω, W ω ∂phaseMeasure) *
        (if roughPart (primeBase P) u = roughPart (primeBase P) v then 1 else 0) := by
  have h := integral_mul_of_disjoint_coordinates
    (g := fun ω => steinhaus (roughPart (primeBase P) u) ω *
      star (steinhaus (roughPart (primeBase P) v) ω))
    (rough_coordinates_disjoint hu hv) hW
    ((steinhaus_measurable _).mul
      (Complex.continuous_conj.measurable.comp (steinhaus_measurable _)))
    hdep (steinhaus_pair_dependsOn _ _)
  rwa [steinhaus_orthogonality (roughPart_pos hu).ne' (roughPart_pos hv).ne'] at h

/-- Only equal rough parts survive. The smooth factors remain in the integral. -/
theorem weighted_pair_integral {P : ℝ} {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    {W : PhaseSpace → ℂ} (hW : Measurable W) (hdep : DependsOn (primesUpTo P) W) :
    (∫ ω, W ω * (steinhaus u ω * star (steinhaus v ω)) ∂phaseMeasure) =
      if roughPart (primeBase P) u = roughPart (primeBase P) v then
        ∫ ω, W ω * (steinhaus (supportedPart (primeBase P) u) ω *
          star (steinhaus (supportedPart (primeBase P) v) ω)) ∂phaseMeasure
      else 0 := by
  let V : PhaseSpace → ℂ := fun ω => W ω *
    (steinhaus (supportedPart (primeBase P) u) ω *
      star (steinhaus (supportedPart (primeBase P) v) ω))
  have hV : Measurable V := hW.mul ((steinhaus_measurable _).mul
    (Complex.continuous_conj.measurable.comp (steinhaus_measurable _)))
  have hVdep : DependsOn (primesUpTo P) V := by
    intro ω ω' h
    dsimp only [V]
    rw [hdep h, steinhaus_smooth_congr (canonical_smooth_part hu) h,
      steinhaus_smooth_congr (canonical_smooth_part hv) h]
  have he (n : ℕ) (hn : 0 < n) (ω : PhaseSpace) :
      steinhaus n ω = steinhaus (roughPart (primeBase P) n) ω *
        steinhaus (supportedPart (primeBase P) n) ω := by
    rw [← steinhaus_mul, roughPart_mul_supportedPart hn]
  calc
    _ = ∫ ω, V ω * (steinhaus (roughPart (primeBase P) u) ω *
        star (steinhaus (roughPart (primeBase P) v) ω)) ∂phaseMeasure := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [he u hu ω, he v hv ω, star_mul]
      dsimp only [V]
      ring
    _ = (∫ ω, V ω ∂phaseMeasure) *
        (if roughPart (primeBase P) u = roughPart (primeBase P) v then 1 else 0) :=
      weighted_rough_pair_integral hu hv hV hVdep
    _ = _ := by split_ifs <;> simp only [mul_one, mul_zero, V]

theorem smoothBox_measurable {p : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) :
    Measurable (fun ω => smoothBox p c1 c2 i (fun n => steinhaus n ω)) :=
  random_smooth_measurable (precision_pos hell) _ _ _ _ c1 c2

theorem smoothBox_pair_integral {p u v : ℕ} (hell : 0 < cutoffLog ((p : ℝ)-1))
    (c1 c2 : Coefficients p) (i : Boxes p) (hu : 0 < u) (hv : 0 < v) :
    (∫ ω, (smoothBox p c1 c2 i (fun n => steinhaus n ω) : ℂ) *
      (steinhaus u ω * star (steinhaus v ω)) ∂phaseMeasure) =
      if roughPart (primeBase (primeCutoff ((p : ℝ)-1))) u =
          roughPart (primeBase (primeCutoff ((p : ℝ)-1))) v then
        ∫ ω, (smoothBox p c1 c2 i (fun n => steinhaus n ω) : ℂ) *
          (steinhaus (supportedPart (primeBase (primeCutoff ((p : ℝ)-1))) u) ω *
            star (steinhaus (supportedPart (primeBase (primeCutoff ((p : ℝ)-1))) v) ω))
          ∂phaseMeasure
      else 0 := by
  apply weighted_pair_integral hu hv
  · exact Complex.continuous_ofReal.measurable.comp (smoothBox_measurable hell c1 c2 i)
  · intro ω ω' h
    exact congrArg (fun x : ℝ => (x : ℂ)) (smoothBox_small_coordinates p c1 c2 i h)

end NField.Alignment.HarperRoughOrthogonality
