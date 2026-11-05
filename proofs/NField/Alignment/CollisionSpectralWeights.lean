/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCosecantIdentity
import NField.Alignment.CollisionWeightMultiples
import NField.Alignment.CollisionSpectralMomentRecurrence

/-!
# Positive, summable masses at every primitive rational frequency

The index records an actual reduced address in the open unit interval.
The potential weights use the inverse squared chord; the finite cosecant
identity and the proved Jordan variance give their exact infinite mass.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralWeights

open scoped BigOperators
open CollisionWeightMultiples CollisionJordanVariance CollisionCosecantIdentity
open CollisionPotentialConvergence CollisionPrimitiveFourier DedekindFourierMoment
open CollisionRamanujan

abbrev SpectralAddress := Σ q : ℕ, {a : ℕ // a ∈ primitiveNumerators q}

def frequency (i : SpectralAddress) : ℝ := (i.2.1 : ℝ)/(i.1 : ℝ)

theorem address_bounds (i : SpectralAddress) : 1 ≤ i.2.1 ∧ i.2.1 < i.1 :=
  Finset.mem_Ico.mp (Finset.mem_filter.mp i.2.2).1

theorem address_period (i : SpectralAddress) : 2 ≤ i.1 := by
  have := address_bounds i
  omega

theorem address_coprime (i : SpectralAddress) : i.2.1.Coprime i.1 :=
  (Finset.mem_filter.mp i.2.2).2

theorem frequency_mem (i : SpectralAddress) : frequency i ∈ Set.Ioo (0 : ℝ) 1 := by
  have ha := address_bounds i
  have hq : (0 : ℝ) < i.1 := by exact_mod_cast (show 0 < i.1 by omega)
  constructor
  · exact div_pos (by exact_mod_cast (show 0 < i.2.1 by omega)) hq
  · exact (div_lt_one hq).mpr (by exact_mod_cast ha.2)

def incrementMass (i : SpectralAddress) : ℝ := (4/9 : ℝ)*(amplitude i.1)^2

def potentialMass (i : SpectralAddress) : ℝ :=
  incrementMass i * chordEnergy i.1 i.2.1

theorem incrementMass_nonneg (i : SpectralAddress) : 0 ≤ incrementMass i := by
  unfold incrementMass
  positivity

theorem potentialMass_nonneg (i : SpectralAddress) : 0 ≤ potentialMass i := by
  apply mul_nonneg (incrementMass_nonneg i)
  unfold chordEnergy
  positivity

theorem potentialMass_literal (i : SpectralAddress) :
    potentialMass i = (1/9 : ℝ)*(amplitude i.1)^2 *
      (Real.sin (Real.pi*(i.2.1 : ℝ)/(i.1 : ℝ))^2)⁻¹ := by
  rw [potentialMass, chordEnergy_eq_cosecant (by have := address_period i; omega)]
  unfold incrementMass
  ring

theorem potentialMass_fiber (q : ℕ) :
    (∑ a : {a : ℕ // a ∈ primitiveNumerators q}, potentialMass ⟨q,a⟩) =
      conductorEnergy q/27 := by
  classical
  by_cases hq : 2 ≤ q
  · simp only [potentialMass, incrementMass]
    rw [← Finset.mul_sum, Finset.sum_coe_sort]
    change (4/9 : ℝ)*amplitude q^2*primitiveChordEnergy q = conductorEnergy q/27
    rw [primitive_chord_sum hq, conductorEnergy, if_pos hq]
    ring
  · haveI : IsEmpty {a : ℕ // a ∈ primitiveNumerators q} := ⟨by
      intro a
      have h := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
      omega⟩
    simp [conductorEnergy, hq]

theorem incrementMass_fiber_bound (q : ℕ) :
    (∑ a : {a : ℕ // a ∈ primitiveNumerators q}, incrementMass ⟨q,a⟩) ≤
      (4/9 : ℝ)*conductorEnergy q := by
  classical
  by_cases hq : 2 ≤ q
  · simp only [incrementMass, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    rw [primitiveNumerators_card hq, conductorEnergy, if_pos hq]
    have htq : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have ht : (Nat.totient q : ℝ) ≤ jordanTwo q :=
      htq.trans (jordanTwo_linear_lower hq)
    nlinarith [mul_le_mul_of_nonneg_right ht (sq_nonneg (amplitude q))]
  · haveI : IsEmpty {a : ℕ // a ∈ primitiveNumerators q} := ⟨by
      intro a
      have h := Finset.mem_Ico.mp (Finset.mem_filter.mp a.2).1
      omega⟩
    simp [conductorEnergy, hq]

theorem potentialMass_summable : Summable potentialMass := by
  classical
  rw [summable_sigma_of_nonneg potentialMass_nonneg]
  refine ⟨fun q => (hasSum_fintype _).summable, ?_⟩
  simp_rw [tsum_fintype, potentialMass_fiber]
  exact conductorEnergy_summable.div_const 27

theorem incrementMass_summable : Summable incrementMass := by
  classical
  rw [summable_sigma_of_nonneg incrementMass_nonneg]
  refine ⟨fun q => (hasSum_fintype _).summable, ?_⟩
  simp_rw [tsum_fintype]
  exact Summable.of_nonneg_of_le
    (fun q => Finset.sum_nonneg (fun a _ => incrementMass_nonneg ⟨q,a⟩))
    incrementMass_fiber_bound (conductorEnergy_summable.mul_left (4/9 : ℝ))

theorem potentialMass_total : (∑' i, potentialMass i) = ‖collisionPotential‖^2 := by
  classical
  rw [potentialMass_summable.tsum_sigma]
  simp_rw [tsum_fintype, potentialMass_fiber]
  rw [tsum_div_const, conductorEnergy_hasSum.tsum_eq]
  ring

end NField.Alignment.CollisionSpectralWeights
