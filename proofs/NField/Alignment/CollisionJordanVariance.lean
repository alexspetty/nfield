/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialConvergence
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Jordan conductor variance of the collision potential

The Jordan factor is defined by its Euler product, not by the desired
variance identity. Its divisor identity reorganizes the actual Haar Gram form.
-/

noncomputable section

namespace NField.Alignment.CollisionJordanVariance

open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Filter
open CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialConvergence

def jordanTwo : ArithmeticFunction ℝ :=
  (ArithmeticFunction.pow 2 : ArithmeticFunction ℝ).pmul
    (prodPrimeFactors (fun p => 1 - ((p : ℝ)^2)⁻¹))

theorem jordanTwo_euler_product {n : ℕ} (hn : n ≠ 0) :
    jordanTwo n = (n : ℝ)^2 * ∏ p ∈ n.primeFactors, (1 - ((p : ℝ)^2)⁻¹) := by
  simp [jordanTwo, prodPrimeFactors_apply hn]

theorem jordanTwo_multiplicative : jordanTwo.IsMultiplicative :=
  isMultiplicative_pow.natCast.pmul (IsMultiplicative.prodPrimeFactors _)

@[simp] theorem jordanTwo_zero : jordanTwo 0 = 0 := jordanTwo.map_zero

@[simp] theorem jordanTwo_one : jordanTwo 1 = 1 := jordanTwo_multiplicative.1

theorem jordanTwo_nonneg (n : ℕ) : 0 ≤ jordanTwo n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [jordanTwo_euler_product hn]
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have hp2 : (1 : ℝ) ≤ (p : ℝ)^2 := by nlinarith
  have : ((p : ℝ)^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp2
  linarith

theorem jordanTwo_prime_power_succ {p : ℕ} (hp : p.Prime) (i : ℕ) :
    jordanTwo (p^(i+1)) = ((p : ℝ)^(i+1))^2 - ((p : ℝ)^i)^2 := by
  rw [jordanTwo_euler_product (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow (by omega) hp]
  simp only [Finset.prod_singleton, pow_succ]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast
  field_simp

theorem sum_jordanTwo_prime_power {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (∑ j ∈ Finset.range (i+1), jordanTwo (p^j)) = ((p : ℝ)^i)^2 := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Finset.sum_range_succ, ih, jordanTwo_prime_power_succ hp]
      ring

theorem jordanTwo_mul_zeta : jordanTwo * (ζ : ArithmeticFunction ℝ) =
    (ArithmeticFunction.pow 2 : ArithmeticFunction ℝ) := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (jordanTwo_multiplicative.mul isMultiplicative_zeta.natCast) _
    isMultiplicative_pow.natCast).mpr
  intro p i hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sum_jordanTwo_prime_power hp]
  simp

theorem sum_jordanTwo_divisors (n : ℕ) :
    (∑ q ∈ n.divisors, jordanTwo q) = (n : ℝ)^2 := by
  rw [← coe_mul_zeta_apply, jordanTwo_mul_zeta]
  simp

theorem gcd_jordan_expansion {k l M : ℕ} (hk : k ∈ Finset.Icc 2 M)
    (_hl : l ∈ Finset.Icc 2 M) :
    (k.gcd l : ℝ)^2 - 1 = ∑ q ∈ Finset.Icc 2 M,
      if q ∣ k ∧ q ∣ l then jordanTwo q else 0 := by
  have hkpos : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
  have hgpos := Nat.gcd_pos_of_pos_left l hkpos
  have he : (Finset.Icc 2 M).filter (fun q => q ∣ k ∧ q ∣ l) =
      (k.gcd l).divisors.erase 1 := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq, _⟩, hqk, hql⟩
      exact ⟨by omega, Nat.dvd_gcd hqk hql, hgpos.ne'⟩
    · rintro ⟨hq1, hqd, _⟩
      have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqd hgpos
      have hqM := (Nat.le_of_dvd hgpos hqd).trans
        ((Nat.gcd_le_left l hkpos).trans (Finset.mem_Icc.mp hk).2)
      exact ⟨⟨by omega, hqM⟩, Nat.dvd_gcd_iff.mp hqd⟩
  rw [← Finset.sum_filter, he]
  have h := Finset.sum_erase_add (k.gcd l).divisors jordanTwo
    (Nat.one_mem_divisors.mpr hgpos.ne')
  rw [sum_jordanTwo_divisors, jordanTwo_one] at h
  linarith

def finiteAmplitude (v : ℕ → ℝ) (q M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 M, if q ∣ k then v k else 0

theorem finite_potential_conductor_norm_sq (v : ℕ → ℝ) (M : ℕ) :
    ‖finitePotential v M‖^2 = (1 / 27 : ℝ) * ∑ q ∈ Finset.Icc 2 M,
      jordanTwo q * (finiteAmplitude v q M)^2 := by
  rw [finite_potential_norm_sq]
  congr 1
  calc
    _ = ∑ k ∈ Finset.Icc 2 M, ∑ l ∈ Finset.Icc 2 M,
        ∑ q ∈ Finset.Icc 2 M, v k * v l *
          (if q ∣ k ∧ q ∣ l then jordanTwo q else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [gcd_jordan_expansion hk hl, Finset.mul_sum]
    _ = ∑ k ∈ Finset.Icc 2 M, ∑ q ∈ Finset.Icc 2 M,
        ∑ l ∈ Finset.Icc 2 M, v k * v l *
          (if q ∣ k ∧ q ∣ l then jordanTwo q else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M,
        ∑ l ∈ Finset.Icc 2 M, v k * v l *
          (if q ∣ k ∧ q ∣ l then jordanTwo q else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [finiteAmplitude, pow_two, Finset.sum_mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      by_cases hk : q ∣ k <;> by_cases hl : q ∣ l <;> simp [hk, hl, mul_comm, mul_assoc]

def amplitude (q : ℕ) : ℝ := ∑' k : ℕ, if q ∣ k then collisionWeight k else 0

theorem amplitude_summable (q : ℕ) :
    Summable (fun k : ℕ => if q ∣ k then collisionWeight k else 0) := by
  apply Summable.of_nonneg_of_le
    (fun k => by split_ifs <;> simp [collisionWeight_nonneg])
    (fun k => by split_ifs <;> simp [collisionWeight_nonneg]) collisionWeight_summable

theorem amplitude_nonneg (q : ℕ) : 0 ≤ amplitude q :=
  tsum_nonneg (fun k => by split_ifs <;> simp [collisionWeight_nonneg])

theorem finiteAmplitude_nonneg (q M : ℕ) : 0 ≤ finiteAmplitude collisionWeight q M := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> simp [collisionWeight_nonneg]

theorem finiteAmplitude_le_amplitude (q M : ℕ) :
    finiteAmplitude collisionWeight q M ≤ amplitude q :=
  (amplitude_summable q).sum_le_tsum (Finset.Icc 2 M)
    (fun k _ => by split_ifs <;> simp [collisionWeight_nonneg])

theorem finiteAmplitude_tendsto (q : ℕ) :
    Tendsto (finiteAmplitude collisionWeight q) atTop (nhds (amplitude q)) := by
  have h := (amplitude_summable q).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h0 : (if q ∣ 0 then collisionWeight 0 else 0) = 0 := by simp
  have h1 : (if q ∣ 1 then collisionWeight 1 else 0) = 0 := by simp
  change Tendsto (fun M => ∑ k ∈ Finset.Icc 2 M, if q ∣ k then collisionWeight k else 0)
    atTop (nhds (∑' k, if q ∣ k then collisionWeight k else 0))
  simpa only [Function.comp_def,
    sum_range_zero_one (fun k => if q ∣ k then collisionWeight k else 0) h0 h1] using h

def finiteConductorEnergy (M q : ℕ) : ℝ :=
  if 2 ≤ q then jordanTwo q * (finiteAmplitude collisionWeight q M)^2 else 0

def conductorEnergy (q : ℕ) : ℝ :=
  if 2 ≤ q then jordanTwo q * (amplitude q)^2 else 0

theorem finiteConductorEnergy_nonneg (M q : ℕ) : 0 ≤ finiteConductorEnergy M q := by
  unfold finiteConductorEnergy
  split_ifs
  · exact mul_nonneg (jordanTwo_nonneg q) (sq_nonneg _)
  · rfl

theorem conductorEnergy_nonneg (q : ℕ) : 0 ≤ conductorEnergy q := by
  unfold conductorEnergy
  split_ifs
  · exact mul_nonneg (jordanTwo_nonneg q) (sq_nonneg _)
  · rfl

theorem finiteConductorEnergy_le (M q : ℕ) :
    finiteConductorEnergy M q ≤ conductorEnergy q := by
  unfold finiteConductorEnergy conductorEnergy
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (jordanTwo_nonneg q)
    exact pow_le_pow_left₀ (finiteAmplitude_nonneg q M) (finiteAmplitude_le_amplitude q M) 2
  · rfl

theorem finiteConductorEnergy_tendsto (q : ℕ) :
    Tendsto (fun M => finiteConductorEnergy M q) atTop (nhds (conductorEnergy q)) := by
  unfold finiteConductorEnergy conductorEnergy
  split_ifs
  · exact ((finiteAmplitude_tendsto q).pow 2).const_mul _
  · exact tendsto_const_nhds

theorem finiteConductorEnergy_support (M q : ℕ) (hq : q ∉ Finset.Icc 2 M) :
    finiteConductorEnergy M q = 0 := by
  unfold finiteConductorEnergy
  split_ifs with hq2
  · have hz : finiteAmplitude collisionWeight q M = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkp := Finset.mem_Icc.mp hk
      have hqk : ¬ q ∣ k := by
        intro h
        have hle := (Nat.le_of_dvd (by omega : 0 < k) h).trans hkp.2
        exact hq (Finset.mem_Icc.mpr ⟨hq2, hle⟩)
      simp [hqk]
    rw [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  · rfl

theorem finiteConductorEnergy_hasSum (M : ℕ) :
    HasSum (finiteConductorEnergy M) (27 * ‖finitePotential collisionWeight M‖^2) := by
  have h : HasSum (finiteConductorEnergy M)
      (∑ q ∈ Finset.Icc 2 M, finiteConductorEnergy M q) :=
    hasSum_sum_of_ne_finset_zero (finiteConductorEnergy_support M)
  have he : (∑ q ∈ Finset.Icc 2 M, finiteConductorEnergy M q) =
      27 * ‖finitePotential collisionWeight M‖^2 := by
    rw [finite_potential_conductor_norm_sq]
    have : (∑ q ∈ Finset.Icc 2 M, finiteConductorEnergy M q) =
        ∑ q ∈ Finset.Icc 2 M, jordanTwo q * (finiteAmplitude collisionWeight q M)^2 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [finiteConductorEnergy, (Finset.mem_Icc.mp hq).1]
    rw [this]
    ring
  rwa [he] at h

/-- Nonnegative rows with known sums and an increasing pointwise envelope
retain their full mass at the limit. Both inequalities are proved from
finite subsets; no interchange of an unverified infinite series is assumed. -/
theorem hasSum_of_nonnegative_rows (F : ℕ → ℕ → ℝ) (f S : ℕ → ℝ) (C : ℝ)
    (hF : ∀ n q, 0 ≤ F n q) (hf : ∀ q, 0 ≤ f q)
    (hs : ∀ n, HasSum (F n) (S n))
    (hp : ∀ q, Tendsto (fun n => F n q) atTop (nhds (f q)))
    (hS : Tendsto S atTop (nhds C)) (hle : ∀ n q, F n q ≤ f q) :
    HasSum f C := by
  have hbound (u : Finset ℕ) : ∑ q ∈ u, f q ≤ C := by
    apply le_of_tendsto_of_tendsto (tendsto_finsetSum u (fun q _ => hp q)) hS
    exact Filter.Eventually.of_forall (fun n => by
      have h := (hs n).summable.sum_le_tsum u (fun q _ => hF n q)
      rwa [(hs n).tsum_eq] at h)
  have hsum : Summable f := summable_of_sum_le hf hbound
  have hupper : (∑' q, f q) ≤ C := hsum.tsum_le_of_sum_le hbound
  have hlower : C ≤ ∑' q, f q := by
    apply le_of_tendsto hS
    exact Filter.Eventually.of_forall (fun n => by
      have h := (hs n).summable.tsum_le_tsum (hle n) hsum
      rwa [(hs n).tsum_eq] at h)
  simpa only [le_antisymm hupper hlower] using hsum.hasSum

theorem conductorEnergy_hasSum :
    HasSum conductorEnergy (27 * ‖collisionPotential‖^2) := by
  exact hasSum_of_nonnegative_rows finiteConductorEnergy conductorEnergy
    (fun M => 27 * ‖finitePotential collisionWeight M‖^2)
    (27 * ‖collisionPotential‖^2) finiteConductorEnergy_nonneg conductorEnergy_nonneg
    finiteConductorEnergy_hasSum finiteConductorEnergy_tendsto
    ((tendsto_collisionPotential.norm.pow 2).const_mul 27) finiteConductorEnergy_le

theorem conductorEnergy_summable : Summable conductorEnergy := conductorEnergy_hasSum.summable

/-- The exact infinite variance of the constructed Haar potential. -/
theorem collisionPotential_variance :
    ‖collisionPotential‖^2 = (1 / 27 : ℝ) *
      ∑' q : ℕ, if 2 ≤ q then jordanTwo q * (amplitude q)^2 else 0 := by
  change ‖collisionPotential‖^2 = (1 / 27 : ℝ) * ∑' q, conductorEnergy q
  rw [conductorEnergy_hasSum.tsum_eq]
  ring

theorem collisionPotential_second_moment :
    (∫ x, (collisionPotential x)^2 ∂ProfiniteRemainderMeasure.phaseHaar) =
      (1 / 27 : ℝ) * ∑' q : ℕ,
        if 2 ≤ q then jordanTwo q * (amplitude q)^2 else 0 := by
  rw [← collisionPotential_variance, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end NField.Alignment.CollisionJordanVariance
