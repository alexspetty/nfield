/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMassInverse
import NField.Alignment.ProfiniteOdometerErgodic

/-!
# Recovery from the actual Haar potential

Pairing the limiting potential with finite remainder rows recovers every
conductor amplitude by finite Mobius inversion. The absolutely convergent
inverse over multiples then recovers every period mass.
-/

noncomputable section

namespace NField.Alignment.CollisionPotentialRecovery

open scoped BigOperators
open Filter MeasureTheory
open CollisionGeneralWeightCriterion CollisionRamanujan CollisionJordanVariance
open CollisionMassInverse CollisionPotentialHilbert CollisionPotentialConvergence
open ProfiniteRemainderMeasure CollisionPotentialCoboundary ProfiniteOdometerErgodic

theorem gcd_jordan_divisors {k l : ℕ} (hk : 0 < k) :
    (k.gcd l : ℝ)^2 - 1 = ∑ q ∈ k.divisors,
      if 2 ≤ q ∧ q ∣ l then jordanTwo q else 0 := by
  have hgpos := Nat.gcd_pos_of_pos_left l hk
  have he : k.divisors.filter (fun q => 2 ≤ q ∧ q ∣ l) =
      (k.gcd l).divisors.erase 1 := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hqk, _⟩, hq2, hql⟩
      exact ⟨by omega, Nat.dvd_gcd hqk hql, hgpos.ne'⟩
    · rintro ⟨hq1, hqg, _⟩
      have hqpos := Nat.pos_of_dvd_of_pos hqg hgpos
      obtain ⟨hqk, hql⟩ := Nat.dvd_gcd_iff.mp hqg
      exact ⟨⟨hqk, hk.ne'⟩, by omega, hql⟩
  rw [← Finset.sum_filter, he]
  have hs := Finset.sum_erase_add (k.gcd l).divisors jordanTwo
    (Nat.one_mem_divisors.mpr hgpos.ne')
  rw [sum_jordanTwo_divisors, jordanTwo_one] at hs
  linarith

theorem finite_potential_remainder_inner (v : ℕ → ℝ) (M : ℕ) {k : ℕ} (hk : 0 < k) :
    inner ℝ (finitePotential v M) (remainderVector k) =
      (1/18 : ℝ) * ∑ q ∈ k.divisors,
        if 2 ≤ q then jordanTwo q * finiteAmplitude v q M else 0 := by
  unfold finitePotential
  simp only [inner_smul_left, conj_trivial, sum_inner]
  calc
    _ = (1/18 : ℝ) * ∑ l ∈ Finset.Icc 2 M, v l * ((k.gcd l : ℝ)^2-1) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [remainder_inner
        (by have := (Finset.mem_Icc.mp hl).1; omega) hk, Nat.gcd_comm l k]
      ring
    _ = (1/18 : ℝ) * ∑ l ∈ Finset.Icc 2 M, ∑ q ∈ k.divisors,
        v l * (if 2 ≤ q ∧ q ∣ l then jordanTwo q else 0) := by
      simp_rw [gcd_jordan_divisors hk, Finset.mul_sum]
    _ = (1/18 : ℝ) * ∑ q ∈ k.divisors, ∑ l ∈ Finset.Icc 2 M,
        v l * (if 2 ≤ q ∧ q ∣ l then jordanTwo q else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : 2 ≤ q
      · rw [if_pos hq, finiteAmplitude, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hd : q ∣ l <;> simp [hq, hd, mul_comm]
      · simp [hq]

def weightedAmplitude (v : ℕ → ℝ) (q : ℕ) : ℝ :=
  if 2 ≤ q then jordanTwo q * generalAmplitude v q else 0

theorem potential_remainder_inner (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : Summable v) (Y : HaarL2)
    (hY : Tendsto (finitePotential v) atTop (nhds Y)) {k : ℕ} (hk : 0 < k) :
    inner ℝ Y (remainderVector k) = (1/18 : ℝ) * ∑ q ∈ k.divisors, weightedAmplitude v q := by
  have hl := Filter.Tendsto.inner (𝕜 := ℝ) hY (tendsto_const_nhds (x := remainderVector k))
  have hr : Tendsto (fun M => (1/18 : ℝ) * ∑ q ∈ k.divisors,
      if 2 ≤ q then jordanTwo q * finiteAmplitude v q M else 0) atTop
      (nhds ((1/18 : ℝ)* ∑ q ∈ k.divisors, weightedAmplitude v q)) := by
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum
    intro q _
    unfold weightedAmplitude
    split_ifs
    · exact (generalAmplitude_tendsto v hv h0 h1 hs q).const_mul (jordanTwo q)
    · exact tendsto_const_nhds
  simp_rw [finite_potential_remainder_inner v _ hk] at hl
  exact tendsto_nhds_unique hl hr

theorem amplitude_from_potential (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (hs : Summable v) (Y : HaarL2)
    (hY : Tendsto (finitePotential v) atTop (nhds Y)) {q : ℕ} (hq : 2 ≤ q) :
    jordanTwo q * generalAmplitude v q =
      ∑ p ∈ q.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℝ) *
        (18 * inner ℝ Y (remainderVector p.2)) := by
  have hp (k : ℕ) (hk : 0 < k) :
      (∑ d ∈ k.divisors, weightedAmplitude v d) = 18 * inner ℝ Y (remainderVector k) := by
    rw [potential_remainder_inner v hv h0 h1 hs Y hY hk]
    ring
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := weightedAmplitude v) (g := fun k => 18 * inner ℝ Y (remainderVector k))).mp hp
      q (by omega)
  simpa only [weightedAmplitude, if_pos hq] using hi.symm

theorem potential_determines_mass (v u : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n) (hu : ∀ n, 0 ≤ u n)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hu0 : u 0 = 0) (hu1 : u 1 = 0)
    (hvs : Summable v) (hus : Summable u) (Y : HaarL2)
    (hYv : Tendsto (finitePotential v) atTop (nhds Y))
    (hYu : Tendsto (finitePotential u) atTop (nhds Y)) : v = u := by
  have ham (q : ℕ) (hq : 2 ≤ q) : generalAmplitude v q = generalAmplitude u q := by
    have hvq := amplitude_from_potential v hv hv0 hv1 hvs Y hYv hq
    have huq := amplitude_from_potential u hu hu0 hu1 hus Y hYu hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hj : jordanTwo q ≠ 0 := by
      have hlow := jordanTwo_quadratic_lower (by omega : 1 ≤ q)
      nlinarith [sq_pos_of_pos hqR]
    exact mul_left_cancel₀ hj (hvq.trans huq.symm)
  have hev := (generalEnergy_hasSum_of_limit v hv hv0 hv1 hvs Y hYv).summable
  have heu := (generalEnergy_hasSum_of_limit u hu hu0 hu1 hus Y hYu).summable
  funext k
  by_cases hk : 2 ≤ k
  · rw [mass_moebius_inverse v hv hv0 hvs hev (by omega : 0 < k),
      mass_moebius_inverse u hu hu0 hus heu (by omega : 0 < k)]
    apply tsum_congr
    intro j
    by_cases hj : j = 0
    · simp [hj]
    · have hkj : 2 ≤ k*j := hk.trans (Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hj))
      rw [ham (k*j) hkj]
  · have hk2 : k < 2 := by omega
    interval_cases k <;> simp [hv0, hv1, hu0, hu1]

theorem limiting_potential_mean_zero (v : ℕ → ℝ) (Y : HaarL2)
    (hY : Tendsto (finitePotential v) atTop (nhds Y)) :
    (∫ x, Y x ∂phaseHaar) = 0 := by
  rw [← mean_inner_eq_integral]
  have hm := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := oneVector)) hY
  simp only [finitePotential_mean_inner] at hm
  exact tendsto_nhds_unique hm tendsto_const_nhds

theorem coboundary_determines_mass (v u : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n) (hu : ∀ n, 0 ≤ u n)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hu0 : u 0 = 0) (hu1 : u 1 = 0)
    (hvs : Summable v) (hus : Summable u) (Y Z : HaarL2)
    (hY : Tendsto (finitePotential v) atTop (nhds Y))
    (hZ : Tendsto (finitePotential u) atTop (nhds Z))
    (hg : Y - shift (-1) Y = Z - shift (-1) Z) : v = u := by
  have he := mean_zero_coboundary_unique Y Z (limiting_potential_mean_zero v Y hY)
    (limiting_potential_mean_zero u Z hZ) hg
  subst Z
  exact potential_determines_mass v u hv hu hv0 hv1 hu0 hu1 hvs hus Y hY hZ

theorem admissible_mass_recovery (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hvs : Summable v)
    (hev : Summable (generalEnergy v)) :
    (∀ k : ℕ, 2 ≤ k → v k = ∑' j,
      (ArithmeticFunction.moebius j : ℝ)*generalAmplitude v (k*j)) ∧
    (∀ k : ℕ, 2 ≤ k → Summable (fun j =>
      ‖(ArithmeticFunction.moebius j : ℝ)*generalAmplitude v (k*j)‖)) ∧
    (∃ Y : HaarL2, Tendsto (finitePotential v) atTop (nhds Y) ∧
      ∀ (u : ℕ → ℝ), (∀ n, 0 ≤ u n) → u 0 = 0 → u 1 = 0 → Summable u →
        ∀ Z : HaarL2, Tendsto (finitePotential u) atTop (nhds Z) →
          Y - shift (-1) Y = Z - shift (-1) Z → v = u) := by
  obtain ⟨Y, hY⟩ := (general_weights_converge_iff v hv hv0 hv1 hvs).mpr hev
  refine ⟨fun k hk => mass_moebius_inverse v hv hv0 hvs hev (by omega),
    fun k hk => inverse_norm_summable v hv hev (by omega), Y, hY, ?_⟩
  intro u hu hu0 hu1 hus Z hZ hg
  exact coboundary_determines_mass v u hv hu hv0 hv1 hu0 hu1 hvs hus Y Z hY hZ hg

end NField.Alignment.CollisionPotentialRecovery
