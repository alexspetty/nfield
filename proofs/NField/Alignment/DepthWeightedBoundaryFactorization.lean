/-
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthDilation

/-!
# Depth-weighted boundary factorization

This module isolates the finite summation-by-parts argument. Any exact
sawtooth response immediately yields both the cell-difference and signed-chain
factorizations, so the conductor-depth arithmetic can remain separate from the
boundary algebra.
-/

namespace NField.Alignment.DepthWeightedBoundaryFactorization

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra

/-- Carry transform against a character supplied directly, without inversion convention. -/
noncomputable def characterCarryTransform
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (ψ : Character m) : ℂ :=
  ∑ a : ZMod m, carryObservable w a * ψ a

/-- Cell-difference pairing with an arbitrary exact response function. -/
noncomputable def depthDifferencePairing
    {m : ℕ} [NeZero m] (w η : ZMod m → ℂ) : ℂ :=
  ∑ n : ZMod m, w n * (η (n + 1) - η n)

/-- Signed-boundary-chain pairing with an arbitrary exact response function. -/
noncomputable def depthBoundaryPairing
    {m : ℕ} [NeZero m] (w η : ZMod m → ℂ) : ℂ :=
  ∑ x : ZMod m, signedBoundary w x * η x

/-- Cyclic summation by parts identifies cell differences with the signed boundary chain. -/
theorem depthDifferencePairing_eq_boundary
    {m : ℕ} [NeZero m] (w η : ZMod m → ℂ) :
    depthDifferencePairing w η = depthBoundaryPairing w η := by
  classical
  unfold depthDifferencePairing depthBoundaryPairing signedBoundary
  have hshift :
      (∑ n : ZMod m, w n * η (n + 1)) =
        ∑ x : ZMod m, w (x - 1) * η x := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : ZMod m))
      (fun x : ZMod m => w (x - 1) * η x))
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hshift]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Every exact sawtooth response factors the carry transform through its cell differences. -/
theorem carryTransform_of_exact_response
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (ψ : Character m)
    (B : ℂ) (η : ZMod m → ℂ)
    (hresponse : ∀ k : ZMod m,
      twistedTransform centeredSawtooth ψ k = B * η k) :
    characterCarryTransform w ψ =
      -(B * depthDifferencePairing w η) := by
  classical
  unfold characterCarryTransform carryObservable depthDifferencePairing
  calc
    (∑ a : ZMod m,
        (-∑ n : ZMod m, w n *
          (centeredSawtooth ((n + 1) * a) - centeredSawtooth (n * a))) * ψ a) =
      ∑ a : ZMod m, ∑ n : ZMod m,
        -(w n * (centeredSawtooth ((n + 1) * a) -
          centeredSawtooth (n * a))) * ψ a := by
            apply Finset.sum_congr rfl
            intro a _
            rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro n _
            ring
    _ = ∑ n : ZMod m, ∑ a : ZMod m,
        -(w n * (centeredSawtooth ((n + 1) * a) -
          centeredSawtooth (n * a))) * ψ a := by
            rw [Finset.sum_comm]
    _ = ∑ n : ZMod m, -w n *
        (twistedTransform centeredSawtooth ψ (n + 1) -
          twistedTransform centeredSawtooth ψ n) := by
            apply Finset.sum_congr rfl
            intro n _
            unfold twistedTransform
            calc
              (∑ a : ZMod m,
                  -(w n * (centeredSawtooth ((n + 1) * a) -
                    centeredSawtooth (n * a))) * ψ a) =
                ∑ a : ZMod m, -w n *
                  (centeredSawtooth ((n + 1) * a) * ψ a -
                    centeredSawtooth (n * a) * ψ a) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      ring
              _ = -w n * ∑ a : ZMod m,
                  (centeredSawtooth ((n + 1) * a) * ψ a -
                    centeredSawtooth (n * a) * ψ a) := by
                      rw [Finset.mul_sum]
              _ = -w n *
                  ((∑ a : ZMod m, centeredSawtooth ((n + 1) * a) * ψ a) -
                    ∑ a : ZMod m, centeredSawtooth (n * a) * ψ a) := by
                      rw [Finset.sum_sub_distrib]
    _ = ∑ n : ZMod m, -w n *
        (B * η (n + 1) - B * η n) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [hresponse, hresponse]
    _ = -(B * ∑ n : ZMod m, w n * (η (n + 1) - η n)) := by
          calc
            (∑ n : ZMod m, -w n * (B * η (n + 1) - B * η n)) =
              ∑ n : ZMod m, -(B * (w n * (η (n + 1) - η n))) := by
                apply Finset.sum_congr rfl
                intro n _
                ring
            _ = -(∑ n : ZMod m, B * (w n * (η (n + 1) - η n))) := by
              rw [Finset.sum_neg_distrib]
            _ = _ := by rw [Finset.mul_sum]

/-- Boundary-chain form of exact response factorization. -/
theorem carryTransform_of_exact_boundary_response
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (ψ : Character m)
    (B : ℂ) (η : ZMod m → ℂ)
    (hresponse : ∀ k : ZMod m,
      twistedTransform centeredSawtooth ψ k = B * η k) :
    characterCarryTransform w ψ =
      -(B * depthBoundaryPairing w η) := by
  rw [carryTransform_of_exact_response w ψ B η hresponse]
  rw [depthDifferencePairing_eq_boundary]

/-- Compatibility with the manuscript's inverse-character transform convention. -/
theorem characterCarryTransform_eq_carryTransform_inverse
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (χ : Character m) :
    characterCarryTransform w χ⁻¹ = carryTransform w χ := by
  rfl

end NField.Alignment.DepthWeightedBoundaryFactorization
