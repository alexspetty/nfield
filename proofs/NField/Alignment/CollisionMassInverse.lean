/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionGeneralWeightCriterion
import NField.Alignment.CollisionRamanujan
import Mathlib.Analysis.PSeries

/-!
# Absolutely convergent inversion of the period masses

The Jordan energy forces summability of all conductor amplitudes. This
summability justifies exchanging the two sums in inversion over multiples.
The zero index is included with zero mass and zero Mobius coefficient.
-/

noncomputable section

namespace NField.Alignment.CollisionMassInverse

open scoped BigOperators
open CollisionGeneralWeightCriterion CollisionRamanujan CollisionJordanVariance

theorem generalAmplitude_nonneg (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) (q : ℕ) :
    0 ≤ generalAmplitude v q := by
  apply tsum_nonneg
  intro k
  split_ifs <;> simp [hv]

theorem generalAmplitude_le_energy {v : ℕ → ℝ} {q : ℕ} (hq : 2 ≤ q) :
    generalAmplitude v q ≤ generalEnergy v q + 1 / (q : ℝ)^2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h := two_mul_le_add_sq ((q : ℝ) * generalAmplitude v q) ((q : ℝ)⁻¹)
  have hc : 2 * ((q : ℝ) * generalAmplitude v q) * (q : ℝ)⁻¹ =
      2 * generalAmplitude v q := by field_simp
  rw [hc, mul_pow] at h
  have he := mul_le_mul_of_nonneg_right (jordanTwo_quadratic_lower (by omega : 1 ≤ q))
    (sq_nonneg (generalAmplitude v q))
  rw [generalEnergy, if_pos hq]
  have hinv : ((q : ℝ)⁻¹)^2 = 1 / (q : ℝ)^2 := by simp [inv_pow, one_div]
  rw [hinv] at h
  have hp : 0 ≤ 1 / (q : ℝ)^2 := by positivity
  nlinarith

theorem all_amplitudes_summable (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (he : Summable (generalEnergy v)) : Summable (generalAmplitude v) := by
  have hp : Summable (fun q : ℕ => 1 / (q : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (summable_nat_add_iff 2).mp
  apply Summable.of_nonneg_of_le (fun q => generalAmplitude_nonneg v hv (q+2))
    (fun q => generalAmplitude_le_energy (by omega : 2 ≤ q+2))
  exact (he.add hp).comp_injective (fun a b hab => by omega)

theorem moebius_real_norm_le (j : ℕ) : ‖(ArithmeticFunction.moebius j : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, ← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := j)

theorem inverse_norm_summable (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (he : Summable (generalEnergy v)) {k : ℕ} (hk : 0 < k) :
    Summable (fun j => ‖(ArithmeticFunction.moebius j : ℝ) * generalAmplitude v (k*j)‖) := by
  have hs := (all_amplitudes_summable v hv he).comp_injective
    (fun a b h => Nat.mul_left_cancel hk h)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro j
  rw [norm_mul, Real.norm_of_nonneg (generalAmplitude_nonneg v hv (k*j))]
  simpa only [one_mul, Function.comp_def] using mul_le_mul_of_nonneg_right (moebius_real_norm_le j)
    (generalAmplitude_nonneg v hv (k*j))

def inverseDoubleTerm (v : ℕ → ℝ) (k : ℕ) (jn : ℕ × ℕ) : ℝ :=
  (ArithmeticFunction.moebius jn.1 : ℝ) * (if k*jn.1 ∣ jn.2 then v jn.2 else 0)

theorem inverseDoubleTerm_summable (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (hs : Summable v) (he : Summable (generalEnergy v)) {k : ℕ} (hk : 0 < k) :
    Summable (inverseDoubleTerm v k) := by
  have hpos : ∀ jn : ℕ × ℕ, 0 ≤ (if k*jn.1 ∣ jn.2 then v jn.2 else 0) := by
    intro jn
    split_ifs <;> simp [hv]
  have hsum : Summable (fun jn : ℕ × ℕ => if k*jn.1 ∣ jn.2 then v jn.2 else 0) := by
    apply (summable_prod_of_nonneg hpos).mpr
    refine ⟨fun j => generalAmplitude_summable v hv hs (k*j), ?_⟩
    exact (all_amplitudes_summable v hv he).comp_injective
      (fun a b h => Nat.mul_left_cancel hk h)
  apply Summable.of_norm_bounded hsum
  intro jn
  rw [inverseDoubleTerm, norm_mul, Real.norm_of_nonneg (hpos jn)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (moebius_real_norm_le jn.1) (hpos jn)

theorem moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using he

theorem moebius_multiple_sum {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (∑' j, if k*j ∣ n then (ArithmeticFunction.moebius j : ℝ) else 0) =
      if n = k then 1 else 0 := by
  classical
  by_cases hkn : k ∣ n
  · have ht : 0 < n/k := Nat.div_pos (Nat.le_of_dvd hn hkn) hk
    have hd (j : ℕ) : k*j ∣ n ↔ j ∣ n/k := by
      conv_lhs => rw [← Nat.mul_div_cancel' hkn]
      exact Nat.mul_dvd_mul_iff_left hk
    simp_rw [hd]
    have hs : HasSum (fun j => if j ∣ n/k then (ArithmeticFunction.moebius j : ℝ) else 0)
        (∑ j ∈ (n/k).divisors, if j ∣ n/k then (ArithmeticFunction.moebius j : ℝ) else 0) := by
      apply hasSum_sum_of_ne_finset_zero
      intro j hj
      have hnd : ¬ j ∣ n/k := by
        intro hd
        exact hj (Nat.mem_divisors.mpr ⟨hd, ht.ne'⟩)
      exact if_neg hnd
    rw [hs.tsum_eq]
    have hf : (∑ j ∈ (n/k).divisors, if j ∣ n/k then (ArithmeticFunction.moebius j : ℝ) else 0) =
        ∑ j ∈ (n/k).divisors, (ArithmeticFunction.moebius j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact if_pos (Nat.mem_divisors.mp hj).1
    rw [hf, moebius_divisor_sum]
    have hunit : n/k = 1 ↔ n = k := by
      constructor
      · intro h
        have he := Nat.mul_div_cancel' hkn
        rw [h, mul_one] at he
        exact he.symm
      · intro h
        subst n
        exact Nat.div_self hk
    simp only [hunit]
  · have hz (j : ℕ) : ¬ k*j ∣ n := by
      intro h
      exact hkn ((Nat.dvd_mul_right k j).trans h)
    have hnk : n ≠ k := by intro h; subst n; exact hkn (dvd_refl k)
    simp [hz, hnk]

theorem inverseDoubleTerm_column (v : ℕ → ℝ) (h0 : v 0 = 0) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (∑' j, inverseDoubleTerm v k (j,n)) = if n = k then v k else 0 := by
  by_cases hn : n = 0
  · subst n
    have hk0 : ¬ (0 = k) := by omega
    simp [inverseDoubleTerm, h0, hk0]
  have hp (j : ℕ) : inverseDoubleTerm v k (j,n) =
      (if k*j ∣ n then (ArithmeticFunction.moebius j : ℝ) else 0) * v n := by
    unfold inverseDoubleTerm
    split_ifs <;> simp
  simp_rw [hp]
  rw [tsum_mul_right, moebius_multiple_sum hk (Nat.pos_of_ne_zero hn)]
  split_ifs with hnk
  · simp [hnk]
  · simp

theorem mass_moebius_inverse (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n) (h0 : v 0 = 0)
    (hs : Summable v) (he : Summable (generalEnergy v)) {k : ℕ} (hk : 0 < k) :
    v k = ∑' j, (ArithmeticFunction.moebius j : ℝ) * generalAmplitude v (k*j) := by
  have hsum := inverseDoubleTerm_summable v hv hs he hk
  have hrow (j : ℕ) : (∑' n, inverseDoubleTerm v k (j,n)) =
      (ArithmeticFunction.moebius j : ℝ) * generalAmplitude v (k*j) := by
    unfold inverseDoubleTerm generalAmplitude
    exact tsum_mul_left (f := fun n : ℕ => if k*j ∣ n then v n else 0)
      (a := (ArithmeticFunction.moebius j : ℝ))
  have hu : Summable (Function.uncurry (fun j n => inverseDoubleTerm v k (j,n))) := hsum
  calc
    v k = ∑' n, ∑' j, inverseDoubleTerm v k (j,n) := by
      simp_rw [inverseDoubleTerm_column v h0 hk]
      simp
    _ = ∑' j, ∑' n, inverseDoubleTerm v k (j,n) := hu.tsum_comm
    _ = _ := tsum_congr hrow

end NField.Alignment.CollisionMassInverse
