/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialRecovery

/-!
# Finite conductor rows in the actual Haar Hilbert space

Mobius inversion separates the centered remainder rows by denominator.
Their exact inner products are derived from the proved gcd covariance.
-/

noncomputable section

set_option autoImplicit false

namespace NField.Alignment.CollisionConductorRows

open scoped BigOperators
open Filter MeasureTheory
open CollisionPotentialHilbert CollisionPotentialRecovery CollisionJordanVariance
open CollisionMassReadout CollisionRemainderDynamics ProfiniteRemainderMeasure
open CollisionPotentialConvergence

def primitiveRowMap (q : ℕ) : C(Phase, ℝ) :=
  ∑ p ∈ q.divisorsAntidiagonal, ArithmeticFunction.moebius p.1 • remainderMap p.2

def primitiveRow (q : ℕ) : HaarL2 :=
  ∑ p ∈ q.divisorsAntidiagonal, ArithmeticFunction.moebius p.1 • remainderVector p.2

theorem primitiveRow_toLp (q : ℕ) :
    primitiveRow q = ContinuousMap.toLp 2 phaseHaar ℝ (primitiveRowMap q) := by
  simp only [primitiveRow, primitiveRowMap, map_sum, map_zsmul, remainderVector]

theorem primitiveRowMap_formula (q : ℕ) (x : Phase) :
    primitiveRowMap q x = ∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius (q/d) : ℝ) * centered d x := by
  rw [primitiveRowMap, Nat.sum_divisorsAntidiagonal'
    (fun a b => ArithmeticFunction.moebius a • remainderMap b)]
  simp only [← Int.cast_smul_eq_zsmul ℝ, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, remainderMap, ContinuousMap.coe_mk, smul_eq_mul]

theorem remainderVector_one : remainderVector 1 = 0 := by
  have h := remainder_inner (by norm_num : 0 < 1) (by norm_num : 0 < 1)
  simpa using h

@[simp] theorem primitiveRow_zero : primitiveRow 0 = 0 := by simp [primitiveRow]

@[simp] theorem primitiveRow_one : primitiveRow 1 = 0 := by
  simp [primitiveRow, remainderVector_one]

theorem sum_primitiveRow_divisors {k : ℕ} (hk : 0 < k) :
    (∑ q ∈ k.divisors, primitiveRow q) = remainderVector k := by
  exact (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := primitiveRow) (g := remainderVector)).mpr (fun _ _ => rfl) k hk

theorem remainder_primitiveRow_inner {k q : ℕ} (hk : 0 < k) (hq : 0 < q) :
    inner ℝ (remainderVector k) (primitiveRow q) =
      if 2 ≤ q ∧ q ∣ k then jordanTwo q / 12 else 0 := by
  let f : ℕ → ℝ := fun d => if 2 ≤ d ∧ d ∣ k then jordanTwo d / 12 else 0
  have hf : ∀ m > 0, (∑ d ∈ m.divisors, f d) =
      inner ℝ (remainderVector k) (remainderVector m) := by
    intro m hm
    rw [remainder_inner hk hm, Nat.gcd_comm, gcd_jordan_divisors hm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [f]
    split_ifs <;> simp
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := f) (g := fun m => inner ℝ (remainderVector k) (remainderVector m))).mp hf q hq
  unfold primitiveRow
  simpa only [inner_sum, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, f] using hi

theorem primitiveRow_inner {p q : ℕ} (hp : 0 < p) (hq : 2 ≤ q) :
    inner ℝ (primitiveRow p) (primitiveRow q) =
      if p = q then jordanTwo q / 12 else 0 := by
  let f : ℕ → ℝ := fun m => if m = q then jordanTwo q / 12 else 0
  have hf : ∀ m > 0, (∑ d ∈ m.divisors, f d) =
      inner ℝ (remainderVector m) (primitiveRow q) := by
    intro m hm
    rw [remainder_primitiveRow_inner hm (by omega)]
    simp only [f, Finset.sum_ite_eq']
    by_cases hqm : q ∣ m
    · rw [if_pos (Nat.mem_divisors.mpr ⟨hqm, hm.ne'⟩), if_pos ⟨hq, hqm⟩]
    · rw [if_neg (fun h => hqm (Nat.mem_divisors.mp h).1),
        if_neg (fun h => hqm h.2)]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := f) (g := fun m => inner ℝ (remainderVector m) (primitiveRow q))).mp hf p hp
  unfold primitiveRow at ⊢
  change inner ℝ (∑ x ∈ p.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • remainderVector x.2)
    (primitiveRow q) = _
  simpa only [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, conj_trivial, f] using hi

theorem primitiveRow_norm_sq {q : ℕ} (hq : 2 ≤ q) :
    ‖primitiveRow q‖^2 = jordanTwo q / 12 := by
  rw [← real_inner_self_eq_norm_sq, primitiveRow_inner (by omega) hq, if_pos rfl]

theorem primitiveRows_orthogonal {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : p ≠ q) :
    inner ℝ (primitiveRow p) (primitiveRow q) = 0 := by
  rw [primitiveRow_inner (by omega) hq, if_neg hpq]

theorem divisor_row_sum_within {k M : ℕ} (hk : 0 < k) (hkM : k ≤ M) :
    remainderVector k = ∑ q ∈ Finset.Icc 2 M, if q ∣ k then primitiveRow q else 0 := by
  have he : (Finset.Icc 2 M).filter (fun q => q ∣ k) = k.divisors.erase 1 := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq2,hqM⟩,hqk⟩
      exact ⟨by omega, hqk, hk.ne'⟩
    · rintro ⟨hq1,hqk,_⟩
      have hqpos := Nat.pos_of_dvd_of_pos hqk hk
      exact ⟨⟨by omega, (Nat.le_of_dvd hk hqk).trans hkM⟩, hqk⟩
  rw [← Finset.sum_filter, he]
  have hs := Finset.sum_erase_add k.divisors primitiveRow (Nat.one_mem_divisors.mpr hk.ne')
  simpa only [primitiveRow_one, add_zero, sum_primitiveRow_divisors hk] using hs.symm

def weightedRows (c : ℕ → ℝ) (M : ℕ) : HaarL2 :=
  (2/3 : ℝ) • ∑ q ∈ Finset.Icc 2 M, c q • primitiveRow q

theorem finite_potential_rows (v : ℕ → ℝ) (M : ℕ) :
    finitePotential v M = weightedRows (fun q => finiteAmplitude v q M) M := by
  have he : (∑ k ∈ Finset.Icc 2 M, v k • remainderVector k) =
      ∑ k ∈ Finset.Icc 2 M, ∑ q ∈ Finset.Icc 2 M,
        if q ∣ k then v k • primitiveRow q else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [divisor_row_sum_within (by have := (Finset.mem_Icc.mp hk).1; omega)
      (Finset.mem_Icc.mp hk).2, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    split_ifs <;> simp
  rw [finitePotential, he, Finset.sum_comm, weightedRows]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [finiteAmplitude, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp

theorem weightedRows_norm_sq (c : ℕ → ℝ) (M : ℕ) :
    ‖weightedRows c M‖^2 = (1/27 : ℝ) *
      ∑ q ∈ Finset.Icc 2 M, jordanTwo q * (c q)^2 := by
  rw [← real_inner_self_eq_norm_sq, weightedRows]
  simp only [inner_smul_left, inner_smul_right, conj_trivial,
    sum_inner, inner_sum]
  have hrow (q : ℕ) (hq : q ∈ Finset.Icc 2 M) :
      (∑ r ∈ Finset.Icc 2 M, c q * (c r * inner ℝ (primitiveRow q) (primitiveRow r))) =
      jordanTwo q * (c q)^2 / 12 := by
    have he : (∑ r ∈ Finset.Icc 2 M, c q * (c r * inner ℝ (primitiveRow q) (primitiveRow r))) =
        ∑ r ∈ Finset.Icc 2 M, if q = r then jordanTwo q * (c q)^2 / 12 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [primitiveRow_inner (by have := (Finset.mem_Icc.mp hq).1; omega)
        (Finset.mem_Icc.mp hr).1]
      split_ifs with hqr
      · subst r; ring
      · simp
    rw [he]
    simp [hq]
  have hs := Finset.sum_congr rfl hrow
  calc
    _ = (4/9 : ℝ) * ∑ q ∈ Finset.Icc 2 M, ∑ r ∈ Finset.Icc 2 M,
        c q * (c r * inner ℝ (primitiveRow q) (primitiveRow r)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      rw [real_inner_comm (primitiveRow r) (primitiveRow q)]
      ring
    _ = _ := by rw [hs, ← Finset.sum_div]; ring

theorem weightedRows_sub (c d : ℕ → ℝ) (M : ℕ) :
    weightedRows (fun q => c q - d q) M = weightedRows c M - weightedRows d M := by
  simp only [weightedRows, sub_smul, Finset.sum_sub_distrib, smul_sub]

theorem conductorCutoff_norm_le (M : ℕ) :
    ‖weightedRows amplitude M‖^2 ≤ ‖collisionPotential‖^2 := by
  rw [weightedRows_norm_sq, collisionPotential_variance]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have he : (∑ q ∈ Finset.Icc 2 M, jordanTwo q * (amplitude q)^2) =
      ∑ q ∈ Finset.Icc 2 M, conductorEnergy q := by
    apply Finset.sum_congr rfl
    intro q hq
    simp only [conductorEnergy, if_pos (Finset.mem_Icc.mp hq).1]
  rw [he]
  exact conductorEnergy_summable.sum_le_tsum _ (fun q _ => conductorEnergy_nonneg q)

theorem conductorCutoff_difference_bound (M : ℕ) :
    ‖weightedRows amplitude M - finitePotential collisionWeight M‖^2 ≤
      ‖collisionPotential‖^2 - ‖finitePotential collisionWeight M‖^2 := by
  have he : ‖weightedRows amplitude M - finitePotential collisionWeight M‖^2 =
      (1/27 : ℝ) * ∑ q ∈ Finset.Icc 2 M,
        jordanTwo q * (amplitude q - finiteAmplitude collisionWeight q M)^2 := by
    rw [finite_potential_rows, ← weightedRows_sub, weightedRows_norm_sq]
  have hbound : ‖weightedRows amplitude M - finitePotential collisionWeight M‖^2 ≤
      ‖weightedRows amplitude M‖^2 - ‖finitePotential collisionWeight M‖^2 := by
    rw [he, weightedRows_norm_sq, finite_potential_conductor_norm_sq,
      ← mul_sub, ← Finset.sum_sub_distrib]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro q hq
    have h0 := finiteAmplitude_nonneg q M
    have h1 := finiteAmplitude_le_amplitude q M
    have hi : (amplitude q - finiteAmplitude collisionWeight q M)^2 ≤
        (amplitude q)^2 - (finiteAmplitude collisionWeight q M)^2 := by
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
    have hj := mul_le_mul_of_nonneg_left hi (jordanTwo_nonneg q)
    simpa only [mul_sub] using hj
  exact hbound.trans (sub_le_sub_right (conductorCutoff_norm_le M) _)

theorem conductorCutoff_difference_tendsto :
    Tendsto (fun M => weightedRows amplitude M - finitePotential collisionWeight M)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsq : Tendsto
      (fun M => ‖collisionPotential‖^2 - ‖finitePotential collisionWeight M‖^2)
      atTop (nhds 0) := by
    have hn : Tendsto (fun M : ℕ => ‖finitePotential collisionWeight M‖^2)
        atTop (nhds (‖collisionPotential‖^2)) := tendsto_collisionPotential.norm.pow 2
    have ht := (tendsto_const_nhds (x := ‖collisionPotential‖^2)).sub hn
    rw [sub_self] at ht
    exact ht
  apply squeeze_zero (fun M => norm_nonneg _) (fun M =>
    Real.le_sqrt_of_sq_le (conductorCutoff_difference_bound M))
  simpa only [Real.sqrt_zero] using hsq.sqrt

/-- The full conductor amplitudes reconstruct the same Haar potential. -/
theorem conductor_expansion_tendsto :
    Tendsto (weightedRows amplitude) atTop (nhds collisionPotential) := by
  have ht := conductorCutoff_difference_tendsto.add tendsto_collisionPotential
  simpa only [sub_add_cancel, zero_add] using ht

end NField.Alignment.CollisionConductorRows
