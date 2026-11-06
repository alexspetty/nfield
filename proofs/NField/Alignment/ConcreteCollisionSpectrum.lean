/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MatrixHeatTrace

/-! Exact bulk multiplicity and heat trace for the literal collision-label matrix. -/

namespace NField.Alignment.ConcreteCollisionSpectrum

open scoped BigOperators
open Matrix ConcreteCollisionBlocks ExponentialSpectralQuotient BlockSpectralMultiplicity MatrixHeatTrace

theorem particleNormalized_isHermitian {ι κ : Type*} [Fintype ι]
    (label : ι → κ) (x : κ → ℝ) (τ : ℝ) : (particleNormalized label x τ).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, particleNormalized, ExponentialDistanceKernel.kernel_symm, mul_comm]

theorem quotient_no_bulk_root {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) :
    (1 : ℝ) ∉ (hamiltonian (quotient x pop τ)).charpoly.roots := by
  rw [hamiltonian_roots (quotient_posDef x pop hx hp hτ).isHermitian]
  intro h
  obtain ⟨i, hi, hmode⟩ := Multiset.mem_map.mp h
  exact (ne_of_lt (quotient_modes_bounds x pop hx hp hτ i).2) hmode

/-- Title: `The bulk multiplicity is exactly the number of repeated labels`.

Eigenvalue one has exactly the manuscript's bulk multiplicity, with no quotient contribution. -/
theorem particle_bulk_multiplicity {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (label : ι → Fin (n + 1)) (hsurj : Function.Surjective label)
    (x : Fin (n + 1) → ℝ) {τ : ℝ} (hx : StrictMono x) (hτ : 0 < τ) :
    ((hamiltonian (particleNormalized label x τ)).charpoly.roots).count 1 =
      Fintype.card ι - (n + 1) := by
  rw [particle_spectral_multiset label hsurj x τ, Multiset.count_add]
  have h := quotient_no_bulk_root x (population label) hx (population_pos label hsurj) hτ
  simp [Multiset.count_eq_zero.mpr h]

/-- Title: `The literal heat trace splits into bulk and quotient terms`.

The literal matrix-exponential heat trace splits into the bulk and all quotient modes. -/
theorem particle_heat_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (label : ι → Fin (n + 1)) (hsurj : Function.Surjective label)
    (x : Fin (n + 1) → ℝ) {τ : ℝ} (hx : StrictMono x) (hτ : 0 < τ) (t : ℝ) :
    (NormedSpace.exp (-t • hamiltonian (particleNormalized label x τ))).trace =
      (Fintype.card ι - (n + 1) : ℕ) * Real.exp (-t) +
        ∑ i, Real.exp (-t * (1 - (quotient_posDef x (population label) hx
          (population_pos label hsurj) hτ).isHermitian.eigenvalues i) ^ 2) := by
  rw [trace_exp_eq_sum_roots (hamiltonian_isHermitian (particleNormalized_isHermitian label x τ)),
    particle_spectral_multiset label hsurj x τ,
    hamiltonian_roots (quotient_posDef x (population label) hx (population_pos label hsurj) hτ).isHermitian]
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
    Multiset.map_singleton, mul_one, Multiset.nsmul_singleton, Multiset.map_replicate, Multiset.sum_replicate,
    nsmul_eq_mul, Multiset.map_map, Function.comp_def, Finset.sum]

theorem sum_heat_modes_bounds {κ : Type*} [Fintype κ] [DecidableEq κ]
    (mode : κ → ℝ) (zeroMode : κ) (hz : mode zeroMode = 0)
    (hmode : ∀ i, 0 ≤ mode i ∧ mode i ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    1 + (Fintype.card κ - 1 : ℕ) * Real.exp (-t) ≤ ∑ i, Real.exp (-t * mode i) ∧
      (∑ i, Real.exp (-t * mode i)) ≤ 1 + (Fintype.card κ - 1 : ℕ) := by
  have hzterm : Real.exp (-t * mode zeroMode) = 1 := by simp [hz]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ zeroMode), hzterm]
  have hc : (Finset.univ.erase zeroMode).card = Fintype.card κ - 1 := by simp
  have hlo : ∑ i ∈ Finset.univ.erase zeroMode, Real.exp (-t) ≤
      ∑ i ∈ Finset.univ.erase zeroMode, Real.exp (-t * mode i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Real.exp_le_exp.mpr
    nlinarith [(hmode i).2]
  have hhi : ∑ i ∈ Finset.univ.erase zeroMode, Real.exp (-t * mode i) ≤
      ∑ i ∈ Finset.univ.erase zeroMode, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [(hmode i).1]
  simp only [Finset.sum_const, nsmul_eq_mul, hc, mul_one] at hlo hhi
  constructor <;> linarith

/-- Title: `The heat trace obeys the sharp comparison bounds`.

The complete sharp heat-trace comparison from the manuscript. -/
theorem particle_heat_trace_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (label : ι → Fin (n + 1)) (hsurj : Function.Surjective label)
    (x : Fin (n + 1) → ℝ) {τ : ℝ} (hx : StrictMono x) (hτ : 0 < τ)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (NormedSpace.exp (-t • hamiltonian (particleNormalized label x τ))).trace -
      (1 + (Fintype.card ι - 1 : ℕ) * Real.exp (-t)) ∧
    (NormedSpace.exp (-t • hamiltonian (particleNormalized label x τ))).trace -
      (1 + (Fintype.card ι - 1 : ℕ) * Real.exp (-t)) ≤ n * (1 - Real.exp (-t)) := by
  rw [particle_heat_trace label hsurj x hx hτ t]
  obtain ⟨i, hi⟩ := quotient_exists_eigenvalue_one x (population label) hx (population_pos label hsurj) hτ
  have hb := sum_heat_modes_bounds
    (fun i => (1 - (quotient_posDef x (population label) hx
      (population_pos label hsurj) hτ).isHermitian.eigenvalues i) ^ 2) i
    (by rw [hi]; norm_num)
    (fun j => ⟨(quotient_modes_bounds x (population label) hx (population_pos label hsurj) hτ j).1,
      (quotient_modes_bounds x (population label) hx (population_pos label hsurj) hτ j).2.le⟩) t ht
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at hb
  have hcard : n + 1 ≤ Fintype.card ι := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective label hsurj
  have hnat : Fintype.card ι - 1 = (Fintype.card ι - (n + 1)) + n := by omega
  rw [hnat, Nat.cast_add]
  constructor <;> nlinarith [hb.1, hb.2]

end NField.Alignment.ConcreteCollisionSpectrum
