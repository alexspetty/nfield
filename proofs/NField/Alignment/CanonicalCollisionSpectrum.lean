/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConcreteCollisionSpectrum
import NField.Alignment.EventualCollisionLabels

/-! Sorting the actual labels supplies every hypothesis of the finite spectral theorem. -/

namespace NField.Alignment.CanonicalCollisionSpectrum

open scoped BigOperators
open Matrix ConcreteCollisionBlocks ConcreteCollisionSpectrum BlockSpectralMultiplicity
open EventualCollisionLabels TheStructureThatSurvives
open NField.CollisionDefinition
open NField.Alignment.CenteredCollisionSum

noncomputable def integerAffinity {ι : Type*} [Fintype ι] (s : ι → ℤ) (τ : ℝ) : Matrix ι ι ℝ :=
  particleNormalized id (fun i => (s i : ℝ)) τ

/-- Title: `Sorting actual labels supplies the ordered quotient`. -/
theorem sorted_label_representation {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℤ) :
    ∃ (n : ℕ) (label : ι → Fin (n + 1)) (x : Fin (n + 1) → ℝ),
      (Finset.univ.image s).card = n + 1 ∧ Function.Surjective label ∧ StrictMono x ∧
      ∀ i, x (label i) = (s i : ℝ) := by
  classical
  let S := Finset.univ.image s
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.univ_nonempty.image s)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e := S.orderIsoOfFin hn
  let label (i : ι) : Fin (n + 1) := e.symm ⟨s i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let x (j : Fin (n + 1)) : ℝ := ((e j).val : ℤ)
  refine ⟨n, label, x, hn, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (e j).property
    refine ⟨i, ?_⟩
    apply e.injective
    change e (e.symm _) = e j
    rw [e.apply_symm_apply]
    exact Subtype.ext heq
  · intro i j hij
    have h : (e i).val < (e j).val := e.strictMono hij
    dsimp [x]
    exact_mod_cast h
  · intro i
    simp only [x, label, e.apply_symm_apply]

theorem integerAffinity_eq_sorted {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → ℤ) (label : ι → Fin (n + 1)) (x : Fin (n + 1) → ℝ)
    (hvalues : ∀ i, x (label i) = (s i : ℝ)) (τ : ℝ) :
    integerAffinity s τ = particleNormalized label x τ := by
  ext i j
  simp only [integerAffinity, particleNormalized, particleDegree, ExponentialDistanceKernel.kernel,
    Function.comp_apply, id_eq, hvalues]

/-- Title: `Actual integer labels determine the exact bulk multiplicity`.

No label enumeration or spectral hypothesis is supplied: sorting the actual input proves them. -/
theorem integer_bulk_multiplicity {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (s : ι → ℤ) {τ : ℝ} (hτ : 0 < τ) :
    ((hamiltonian (integerAffinity s τ)).charpoly.roots).count 1 =
      Fintype.card ι - (Finset.univ.image s).card := by
  obtain ⟨n, label, x, hc, hsurj, hx, hvalues⟩ := sorted_label_representation s
  rw [integerAffinity_eq_sorted s label x hvalues τ, hc]
  exact particle_bulk_multiplicity label hsurj x hx hτ

noncomputable def firstPrimeAffinity (b ell N : ℕ) (τ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  integerAffinity (fun i => directAllLagDeviation b ell (Nat.nth Nat.Prime i.val)) τ

theorem fin_prime_labels_eq (b ell N : ℕ) :
    (Finset.univ.image (fun i : Fin N => directAllLagDeviation b ell (Nat.nth Nat.Prime i.val))) =
      firstPrimeLabelSet b ell N := by
  ext z
  simp only [firstPrimeLabelSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi⟩
  · rintro ⟨i, hi, hz⟩
    exact ⟨⟨i, hi⟩, hz⟩

/-- Title: `The first prime list has the exact bulk multiplicity`.

The first `N` actual primes have exactly `N` minus their actual label count bulk modes. -/
theorem first_prime_bulk_multiplicity (b ell N : ℕ) (hN : 0 < N) {τ : ℝ} (hτ : 0 < τ) :
    ((hamiltonian (firstPrimeAffinity b ell N τ)).charpoly.roots).count 1 =
      N - (firstPrimeLabelSet b ell N).card := by
  letI : NeZero N := ⟨ne_of_gt hN⟩
  have h := integer_bulk_multiplicity
    (fun i : Fin N => directAllLagDeviation b ell (Nat.nth Nat.Prime i.val)) hτ
  simpa only [firstPrimeAffinity, Fintype.card_fin, fin_prime_labels_eq] using h

/-- Title: `The eventual prime bulk has the fixed table multiplicity`.

Once every table label appears, the exact bulk multiplicity is `N-q_(b,ell)`. -/
theorem eventually_first_prime_bulk {b ell : ℕ} (hb : 2 ≤ b) (hell : 1 ≤ ell)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N in Filter.atTop,
      ((hamiltonian (firstPrimeAffinity b ell N τ)).charpoly.roots).count 1 =
        N - (allPrimeLabelSet b ell).card := by
  filter_upwards [eventually_firstPrimeLabelSet_eq hb hell, Filter.eventually_gt_atTop 0] with N hlabel hN
  rw [first_prime_bulk_multiplicity b ell N hN hτ, hlabel]

end NField.Alignment.CanonicalCollisionSpectrum
