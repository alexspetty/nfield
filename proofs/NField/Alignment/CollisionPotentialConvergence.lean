/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialHilbert
import NField.Alignment.CollisionMassReadout
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Convergence of the collision potential

The capacity bound controls complete Gram boxes. Dyadic blocks retain
that arithmetic covariance while making the collision coefficients small.
-/

noncomputable section

namespace NField.Alignment.CollisionPotentialConvergence

open scoped BigOperators
open Filter
open CollisionRemainderDynamics CollisionMassReadout CollisionPotentialHilbert
open SecondaryCapacityLedger GcdLcmCapacity PrimeSquareCollisionWindow

theorem sum_firstWindow_eq_Icc (M : ℕ) (f : ℕ → ℝ) :
    (∑ i : FirstWindowIndex (M + 1), f (firstWindowNat i)) =
      ∑ k ∈ Finset.Icc 1 M, f k := by
  change (∑ i : Fin M, f (i.val + 1)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) M]
  simpa only [Nat.zero_add, Nat.add_zero, Finset.range_eq_Ico,
    Finset.Ico_add_one_right_eq_Icc] using
    (Finset.sum_Ico_add' f 0 M 1)

theorem gcd_box_bound (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
      ((k.gcd l : ℝ)^2 / ((k : ℝ) * (l : ℝ)))) ≤ 3 * (M : ℝ) := by
  have hcap : continuousCapacity M ≤ (M : ℝ) := by
    have := deficit_nonneg M
    rw [deficit_eq_capacity] at this
    linarith
  have he : gcdLcmSquareSum M =
      ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
        ((k.gcd l : ℝ)^2 / ((k : ℝ) * (l : ℝ))) := by
    unfold gcdLcmSquareSum gcdLcmKernel
    calc
      _ = ∑ i : FirstWindowIndex (M + 1), ∑ l ∈ Finset.Icc 1 M,
          ((Nat.gcd (firstWindowNat i) l : ℝ)^2 / ((firstWindowNat i : ℝ) * (l : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_firstWindow_eq_Icc M (fun l =>
          ((Nat.gcd (firstWindowNat i) l : ℝ)^2 / ((firstWindowNat i : ℝ) * (l : ℝ))))
      _ = _ := sum_firstWindow_eq_Icc M (fun k => ∑ l ∈ Finset.Icc 1 M,
        ((k.gcd l : ℝ)^2 / ((k : ℝ) * (l : ℝ))))
  rw [← he, gcdLcmSquareSum_eq_three_continuousCapacity]
  linarith

def potentialOn (s : Finset ℕ) (v : ℕ → ℝ) : HaarL2 :=
  (2 / 3 : ℝ) • ∑ k ∈ s, v k • remainderVector k

theorem potentialOn_norm_sq (s : Finset ℕ) (v : ℕ → ℝ)
    (hs : ∀ k ∈ s, 0 < k) :
    ‖potentialOn s v‖^2 = (1 / 27 : ℝ) * ∑ k ∈ s, ∑ l ∈ s,
      v k * v l * ((k.gcd l : ℝ)^2 - 1) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold potentialOn
  simp only [inner_smul_left, inner_smul_right, conj_trivial]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
  have he : (∑ k ∈ s, ∑ l ∈ s,
      v k * (v l * inner ℝ (remainderVector k) (remainderVector l))) =
      (1 / 12 : ℝ) * ∑ k ∈ s, ∑ l ∈ s,
        v k * v l * ((k.gcd l : ℝ)^2 - 1) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [remainder_inner (hs k hk) (hs l hl)]
    ring
  rw [he]
  ring

theorem potentialOn_norm_sq_bound (s : Finset ℕ) (v : ℕ → ℝ) (M : ℕ) (A : ℝ)
    (hs : s ⊆ Finset.Icc 1 M) (hv : ∀ k ∈ s, 0 ≤ v k)
    (hA : 0 ≤ A) (hbound : ∀ k ∈ s, (k : ℝ) * v k ≤ A) :
    ‖potentialOn s v‖^2 ≤ A^2 * (M : ℝ) / 9 := by
  have hpos (k : ℕ) (hk : k ∈ s) : 0 < k := (Finset.mem_Icc.mp (hs hk)).1
  rw [potentialOn_norm_sq s v hpos]
  have hterm (k : ℕ) (hk : k ∈ s) (l : ℕ) (hl : l ∈ s) :
      v k * v l * ((k.gcd l : ℝ)^2 - 1) ≤
        A^2 * ((k.gcd l : ℝ)^2 / ((k : ℝ) * (l : ℝ))) := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hpos k hk
    have hlR : (0 : ℝ) < l := by exact_mod_cast hpos l hl
    have hvk : v k ≤ A / (k : ℝ) := (le_div_iff₀ hkR).mpr (by nlinarith [hbound k hk])
    have hvl : v l ≤ A / (l : ℝ) := (le_div_iff₀ hlR).mpr (by nlinarith [hbound l hl])
    calc
      _ ≤ v k * v l * (k.gcd l : ℝ)^2 := by
        nlinarith [mul_nonneg (hv k hk) (hv l hl)]
      _ ≤ (A / (k : ℝ)) * (A / (l : ℝ)) * (k.gcd l : ℝ)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hvk hvl (hv l hl) (div_nonneg hA hkR.le))
          (sq_nonneg _)
      _ = _ := by ring
  have hsum : (∑ k ∈ s, ∑ l ∈ s, v k * v l * ((k.gcd l : ℝ)^2 - 1)) ≤
      A^2 * (3 * (M : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ s, ∑ l ∈ s,
          A^2 * ((k.gcd l : ℝ)^2 / ((k : ℝ) * (l : ℝ))) :=
        Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun l hl => hterm k hk l hl))
      _ ≤ ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
          A^2 * ((k.gcd l : ℝ)^2 / ((k : ℝ) * (l : ℝ))) := by
        apply le_trans (Finset.sum_le_sum (fun k _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)))
        exact Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
      _ = A^2 * ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
          ((k.gcd l : ℝ)^2 / ((k : ℝ) * (l : ℝ))) := by simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (gcd_box_bound M) (sq_nonneg _)
  linarith

theorem collision_age_rpow_bound {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * collisionWeight k ≤ 5 * (k : ℝ)^(-(3 / 4 : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hroot : 1 ≤ (k : ℝ)^(1 / 4 : ℝ) := Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg k) (show (0 : ℝ) < 1/4 by norm_num)
  have hH : 1 + Real.log (k : ℝ) ≤ 5 * (k : ℝ)^(1 / 4 : ℝ) := by nlinarith
  calc
    _ ≤ (k : ℝ) * ((1 + Real.log (k : ℝ)) / (k : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (collisionWeight_log_bound hk) hkR.le
    _ = (1 + Real.log (k : ℝ)) / (k : ℝ) := by field_simp
    _ ≤ (5 * (k : ℝ)^(1 / 4 : ℝ)) / (k : ℝ) :=
      div_le_div_of_nonneg_right hH hkR.le
    _ = _ := by
      rw [show (-(3/4 : ℝ)) = 1/4 - 1 by norm_num, Real.rpow_sub hkR, Real.rpow_one]
      ring

theorem block_norm_bound {L : ℕ} (hL : 1 ≤ L) :
    ‖potentialOn (Finset.Ioc L (2 * L)) collisionWeight‖ ≤
      3 * (L : ℝ)^(-(1 / 4 : ℝ)) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have h := potentialOn_norm_sq_bound (Finset.Ioc L (2 * L)) collisionWeight (2 * L)
    (5 * (L : ℝ)^(-(3 / 4 : ℝ)))
    (by intro k hk; have hk' := Finset.mem_Ioc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩)
    (fun k _ => collisionWeight_nonneg k) (by positivity)
    (by
      intro k hk
      have hk' := Finset.mem_Ioc.mp hk
      calc
        _ ≤ 5 * (k : ℝ)^(-(3 / 4 : ℝ)) := collision_age_rpow_bound (by omega)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hLR (by exact_mod_cast hk'.1.le) (by norm_num))
          (by norm_num))
  have he : (5 * (L : ℝ)^(-(3 / 4 : ℝ)))^2 * ((2 * L : ℕ) : ℝ) / 9 =
      (50 / 9 : ℝ) * (L : ℝ)^(-(1 / 2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hLR.le, Nat.cast_mul, Nat.cast_two]
    calc
      _ = (50 / 9 : ℝ) * ((L : ℝ)^((-(3/4 : ℝ)) * 2) * (L : ℝ)^ (1 : ℝ)) := by
        rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hLR]; norm_num
  have he' : (3 * (L : ℝ)^(-(1 / 4 : ℝ)))^2 =
      9 * (L : ℝ)^(-(1 / 2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hLR.le]
    norm_num
  rw [he] at h
  have hp : 0 < (L : ℝ)^(-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hLR _
  have hn : 0 ≤ 3 * (L : ℝ)^(-(1 / 4 : ℝ)) := by positivity
  nlinarith [norm_nonneg (potentialOn (Finset.Ioc L (2 * L)) collisionWeight)]

theorem finitePotential_double {L : ℕ} (hL : 1 ≤ L) :
    finitePotential collisionWeight (2 * L) = finitePotential collisionWeight L +
      potentialOn (Finset.Ioc L (2 * L)) collisionWeight := by
  have hu : Finset.Icc 2 (2 * L) = Finset.Icc 2 L ∪ Finset.Ioc L (2 * L) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 2 L) (Finset.Ioc L (2 * L)) := by
    rw [Finset.disjoint_left]
    intro k hk hl
    have := (Finset.mem_Icc.mp hk).2
    have := (Finset.mem_Ioc.mp hl).1
    omega
  simp only [finitePotential, potentialOn, hu, Finset.sum_union hd, smul_add]

def dyadicRatio : ℝ := (2 : ℝ)^(-(1 / 4 : ℝ))

theorem dyadicRatio_pos : 0 < dyadicRatio := Real.rpow_pos_of_pos (by norm_num) _

theorem dyadicRatio_lt_one : dyadicRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem dyadic_rpow (j : ℕ) : ((2^j : ℕ) : ℝ)^(-(1 / 4 : ℝ)) = dyadicRatio^j := by
  rw [Nat.cast_pow, Nat.cast_two, ← Real.rpow_natCast_mul (by norm_num)]
  unfold dyadicRatio
  rw [← Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem dyadic_potential_norm (j : ℕ) :
    ‖finitePotential collisionWeight (2^j)‖ ≤
      ∑ i ∈ Finset.range j, 3 * dyadicRatio^i := by
  induction j with
  | zero => simp [finitePotential]
  | succ j ih =>
      have hp : 1 ≤ 2^j := Nat.one_le_pow _ _ (by norm_num)
      rw [pow_succ, Nat.mul_comm, finitePotential_double hp, Finset.sum_range_succ]
      have hb := block_norm_bound hp
      rw [dyadic_rpow] at hb
      exact (norm_add_le _ _).trans (add_le_add ih hb)

def collisionVector (k : ℕ) : HaarL2 :=
  (2 / 3 * collisionWeight k : ℝ) • remainderVector k

@[simp] theorem collisionVector_zero : collisionVector 0 = 0 := by
  simp [collisionVector]

@[simp] theorem collisionVector_one : collisionVector 1 = 0 := by
  simp [collisionVector]

theorem collisionVector_gram_nonneg (k l : ℕ) :
    0 ≤ inner ℝ (collisionVector k) (collisionVector l) := by
  by_cases hk : k = 0
  · simp [hk]
  by_cases hl : l = 0
  · simp [hl]
  have hwk := collisionWeight_nonneg k
  have hwl := collisionWeight_nonneg l
  simp only [collisionVector, inner_smul_left, inner_smul_right, conj_trivial]
  exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
    (remainder_inner_nonneg (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl)))

theorem collisionVector_partial_sum (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), collisionVector k) = finitePotential collisionWeight N := by
  have hs : (∑ k ∈ Finset.Icc 2 N, collisionVector k) =
      ∑ k ∈ Finset.range (N + 1), collisionVector k := by
    apply Finset.sum_subset
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro k hk hnot
      have hk' := Finset.mem_range.mp hk
      have hk2 : k < 2 := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
        omega
      interval_cases k <;> simp
  rw [← hs]
  simp [collisionVector, finitePotential, Finset.smul_sum, mul_smul]

theorem finitePotential_norm_sq_monotone :
    Monotone (fun N => ‖finitePotential collisionWeight N‖^2) := by
  intro m n hmn
  dsimp only
  rw [← collisionVector_partial_sum, ← collisionVector_partial_sum]
  exact positive_gram_norm_monotone collisionVector collisionVector_gram_nonneg (by omega)

theorem collisionVector_energy_bounded :
    BddAbove (Set.range (fun n => ‖∑ k ∈ Finset.range n, collisionVector k‖^2)) := by
  let C : ℝ := ∑' i : ℕ, 3 * dyadicRatio^i
  have hsum : Summable (fun i : ℕ => 3 * dyadicRatio^i) :=
    (summable_geometric_of_lt_one dyadicRatio_pos.le dyadicRatio_lt_one).mul_left 3
  have hr := dyadicRatio_pos
  have hC : 0 ≤ C := tsum_nonneg (fun i => by positivity)
  refine ⟨C^2, ?_⟩
  rintro _ ⟨n, rfl⟩
  dsimp only
  cases n with
  | zero => simp [sq_nonneg]
  | succ N =>
      rw [collisionVector_partial_sum]
      have hmono := finitePotential_norm_sq_monotone (show N ≤ 2^N from Nat.lt_two_pow_self.le)
      have hb := (dyadic_potential_norm N).trans (hsum.sum_le_tsum
        (Finset.range N) (fun i _ => by positivity))
      have hnon := norm_nonneg (finitePotential collisionWeight (2^N))
      change ‖finitePotential collisionWeight N‖^2 ≤ C^2
      nlinarith

theorem collision_potential_converges :
    ∃ Y : HaarL2, Tendsto (finitePotential collisionWeight) atTop (nhds Y) := by
  obtain ⟨Y, hY⟩ := (positive_gram_converges_iff_bounded collisionVector
    collisionVector_gram_nonneg).mpr collisionVector_energy_bounded
  refine ⟨Y, ?_⟩
  have hshift := hY.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, collisionVector_partial_sum] using hshift

def collisionPotential : HaarL2 := collision_potential_converges.choose

theorem tendsto_collisionPotential :
    Tendsto (finitePotential collisionWeight) atTop (nhds collisionPotential) :=
  collision_potential_converges.choose_spec

open MeasureTheory ProfiniteRemainderMeasure

def oneVector : HaarL2 := ContinuousMap.toLp 2 phaseHaar ℝ (1 : C(Phase, ℝ))

theorem remainder_mean_inner {k : ℕ} (hk : 0 < k) :
    inner ℝ oneVector (remainderVector k) = 0 := by
  rw [oneVector, remainderVector, ContinuousMap.inner_toLp]
  simpa only [ContinuousMap.one_apply, map_one, mul_one, remainderMap,
    ContinuousMap.coe_mk] using haar_centered_mean hk

theorem finitePotential_mean_inner (v : ℕ → ℝ) (M : ℕ) :
    inner ℝ oneVector (finitePotential v M) = 0 := by
  unfold finitePotential
  simp_rw [inner_smul_right, inner_sum, inner_smul_right]
  have hs : (∑ k ∈ Finset.Icc 2 M, v k * inner ℝ oneVector (remainderVector k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [remainder_mean_inner (by have := (Finset.mem_Icc.mp hk).1; omega), mul_zero]
  rw [hs, mul_zero]

theorem collisionPotential_mean_inner : inner ℝ oneVector collisionPotential = 0 := by
  have h : Tendsto (fun M => inner ℝ oneVector (finitePotential collisionWeight M)) atTop
      (nhds (inner ℝ oneVector collisionPotential)) :=
    (tendsto_const_nhds (x := oneVector)).inner tendsto_collisionPotential
  simp only [finitePotential_mean_inner] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem finitePotential_two_norm_sq :
    ‖finitePotential collisionWeight 2‖^2 = (1 / 144 : ℝ) := by
  rw [finite_potential_norm_sq]
  norm_num [collisionWeight_two]

theorem collisionPotential_variance_lower : (1 / 144 : ℝ) ≤ ‖collisionPotential‖^2 := by
  apply ge_of_tendsto (tendsto_collisionPotential.norm.pow 2)
  filter_upwards [eventually_ge_atTop 2] with M hM
  rw [← finitePotential_two_norm_sq]
  exact finitePotential_norm_sq_monotone hM

theorem collisionPotential_ne_zero : collisionPotential ≠ 0 := by
  intro h
  have hb := collisionPotential_variance_lower
  rw [h, norm_zero] at hb
  norm_num at hb

theorem mean_inner_eq_integral (Y : HaarL2) :
    inner ℝ oneVector Y = ∫ x, Y x ∂phaseHaar := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase, ℝ))
  filter_upwards [h] with x hx
  change inner ℝ (oneVector x) (Y x) = Y x
  change (ContinuousMap.toLp 2 phaseHaar ℝ (1 : C(Phase, ℝ))) x = 1 at hx
  rw [show oneVector x = 1 from hx]
  simp

theorem collisionPotential_mean_zero : (∫ x, collisionPotential x ∂phaseHaar) = 0 := by
  rw [← mean_inner_eq_integral, collisionPotential_mean_inner]

end NField.Alignment.CollisionPotentialConvergence
