/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianKilledPath

/-!
# Killed-potential control for the actual source comparison normals

One first-endpoint threshold supplies comparable positive variances for
all blocks of a reversed source family, independently of its length.
The finite-path potential and surviving-deficit tail bounds then apply
without a remaining variance or path-recurrence hypothesis.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSourceKilledPath
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter HarperPrimeBlocks HarperPrimeBlockVariance
  HarperPrimeBlockGaussian HarperCenteredPath HarperKilledPath HarperGaussianKilledPath

theorem source_comparable_variances :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) →
        ∀ i, (1/4 : ℝ) ≤ blockNormalVariance x (l i) ∧
          (blockNormalVariance x (l i) : ℝ) ≤ 3/4 := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp eventual_blockVariance_bounds
  refine ⟨X₀,fun x hx n l hl hfirst i => ?_⟩
  have h := hX₀ _ (hfirst.trans
    (blockUpper_antitone hx.le (hl.antitone (Fin.zero_le i))))
  change (1/4 : ℝ) ≤ HarperPrimeRangeCharacteristic.rangeVariance (primeBlock x (l i)) ∧
    HarperPrimeRangeCharacteristic.rangeVariance (primeBlock x (l i)) ≤ 3/4
  rwa [source_blockVariance (by linarith : 0 ≤ x)]

theorem source_pathPotential_bound :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ c : ℝ, 0 ≤ c →
        (∫ z, pathPotential c z ∂centeredNormalProductLaw x l) ≤ c+2 := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst c hc => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  apply gaussian_pathPotential_bound hc (fun i => blockNormalVariance x (l i))
  · intro i
    change (0 : ℝ) < blockNormalVariance x (l i)
    linarith [(hi i).1]
  · intro i
    linarith [(hi i).2]

theorem source_survival_deficit_tail :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (n : ℕ) (l : Fin (n+1) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ c R : ℝ, 0 ≤ c → 0 ≤ R →
        (centeredNormalProductLaw x l).real
          (survivalEvent c ∩ {z | R ≤ c-∑ i, z i}) ≤ (c+2)/(R+2) := by
  obtain ⟨X₀,hX₀⟩ := source_comparable_variances
  refine ⟨X₀,fun x hx n l hl hfirst c R hc hR => ?_⟩
  have hi := hX₀ x hx n l hl hfirst
  apply gaussian_survival_deficit_tail hc hR (fun i => blockNormalVariance x (l i))
  · intro i
    change (0 : ℝ) < blockNormalVariance x (l i)
    linarith [(hi i).1]
  · intro i
    linarith [(hi i).2]

end NField.Alignment.HarperSourceKilledPath
