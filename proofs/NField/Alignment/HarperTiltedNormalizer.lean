/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTiltedCoordinates

/-!
# Exact normalization of each weighted prime coordinate

Comparing the already proved product masses at the adjacent cutoffs q and
q-1 evaluates each prime's Haar integral. The resulting explicit density
is proved for every positive real part, not assumed as a Poisson law.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperTiltedNormalizer
open scoped BigOperators Topology
open MeasureTheory HarperTiltedFactors HarperTiltedMeasure HarperEulerSecondMoment
  HarperSmoothCount CollisionMertensInput

theorem prime_not_mem_previous (q : ℕ) :
    q ∉ primesUpTo ((q : ℝ)-1) := by
  intro h
  have hle := (primesUpTo_mem.mp h).2
  linarith

theorem primesUpTo_prime_insert {q : ℕ} (hq : q.Prime) :
    primesUpTo (q : ℝ) = insert q (primesUpTo ((q : ℝ)-1)) := by
  ext p
  simp only [primesUpTo_mem, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hpq⟩
    by_cases he : p = q
    · exact Or.inl he
    · right
      refine ⟨hp, ?_⟩
      have hn : p < q := lt_of_le_of_ne (by exact_mod_cast hpq) he
      have hn' : (p : ℝ)+1 ≤ q := by exact_mod_cast hn
      linarith
  · rintro (rfl | ⟨hp, hpq⟩)
    · exact ⟨hq, le_rfl⟩
    · exact ⟨hp, by linarith⟩

theorem localMass_eq {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re) :
    localMass q s = (1-(q : ℝ)^(-(2*s.re)))⁻¹ := by
  have h := localMass_product (q : ℝ) hs
  rw [primesUpTo_prime_insert hq, Finset.prod_insert (prime_not_mem_previous q),
    localMass_product ((q : ℝ)-1) hs] at h
  unfold shiftedProduct at h
  rw [primesUpTo_prime_insert hq, Finset.prod_insert (prime_not_mem_previous q)] at h
  exact mul_right_cancel₀ (ne_of_gt (shiftedProduct_pos ((q : ℝ)-1) (by linarith))) h

theorem localDensity_eq {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re)
    (z : UnitAddCircle) :
    localDensity q s z = (1-(q : ℝ)^(-(2*s.re)))*
      ‖(1-fourier 1 z/(q : ℂ)^s)⁻¹‖^2 := by
  rw [localDensity, localMass_eq hq hs, div_inv_eq_mul, localEnergy, mul_comm]

theorem localDensity_norm_form {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re)
    (z : UnitAddCircle) :
    localDensity q s z = (1-‖fourier 1 z/(q : ℂ)^s‖^2)/
      ‖1-fourier 1 z/(q : ℂ)^s‖^2 := by
  rw [localDensity_eq hq hs, norm_inv, inv_pow, ← div_eq_mul_inv,
    localTerm_norm hq.ne_zero, ← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
  congr 3
  push_cast
  ring

end NField.Alignment.HarperTiltedNormalizer
