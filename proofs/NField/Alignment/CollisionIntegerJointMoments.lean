/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionJointMoments

/-!
# Uniform positive-integer bounds for joint reset products

A joint divisibility event lies inside each single event. The largest
period gives a summable product bound uniform in the averaging length.
Positive-integer series are proved from finite divisor traces, independently
of the Haar almost-everywhere convergence statements.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionIntegerJointMoments

open scoped BigOperators Classical
open Filter MeasureTheory
open ProfiniteRemainderMeasure ProfinitePeriodicTesting CollisionRemainderDynamics
open CollisionBoundaryMeasure CollisionBoundaryTesting CollisionPotentialCoboundary
open CollisionResetIntegrability CollisionJointCRT CollisionJointMoments

def divisorIndicator (k n : ℕ) : ℝ := if k∣n then 1 else 0

theorem positive_divisor_count (k N : ℕ) :
    (∑ n ∈ Finset.range N, divisorIndicator k (n+1))=((N/k : ℕ) : ℝ) := by
  unfold divisorIndicator
  rw [positive_sum_Icc (fun n => if k∣n then (1 : ℝ) else 0) N]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, multiples_Icc_card, mul_one]

theorem shifted_divisor_count_bound (k N h : ℕ) :
    (∑ n ∈ Finset.range N, divisorIndicator k (n+1+h))≤(((N+h)/k : ℕ) : ℝ) := by
  have he := Finset.sum_range_add (fun n => divisorIndicator k (n+1)) h N
  have hz : 0≤∑ n ∈ Finset.range h, divisorIndicator k (n+1) :=
    Finset.sum_nonneg (fun n _ => by unfold divisorIndicator; split_ifs <;> norm_num)
  have hc : (∑ n ∈ Finset.range N, divisorIndicator k (n+1+h)) =
      ∑ n ∈ Finset.range N, divisorIndicator k (h+n+1) := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    omega
  rw [hc]
  rw [positive_divisor_count, Nat.add_comm h N] at he
  linarith

theorem nat_div_average_bound (k N h : ℕ) (hk : 0<k) (hN : 0<N) :
    (((N+h)/k : ℕ) : ℝ)/(N : ℝ)≤(1+(h : ℝ))/(k : ℝ) := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hd : ((((N+h)/k : ℕ) : ℝ))*(k : ℝ)≤(N : ℝ)+(h : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (N+h) k
  apply (div_le_div_iff₀ hNR hkR).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) h]

def jointIndicator (r : ℕ) (k h : Fin r → ℕ) (n : ℕ) : ℝ :=
  if ∀ i, k i+2∣n+h i then 1 else 0

theorem jointIndicator_nonneg (r : ℕ) (k h : Fin r → ℕ) (n : ℕ) :
    0≤jointIndicator r k h n := by unfold jointIndicator; split_ifs <;> norm_num

theorem jointIndicator_le_single (r : ℕ) (k h : Fin r → ℕ) (n : ℕ) (j : Fin r) :
    jointIndicator r k h n≤divisorIndicator (k j+2) (n+h j) := by
  by_cases H : ∀ i, k i+2∣n+h i
  · simp only [jointIndicator, if_pos H, divisorIndicator, if_pos (H j), le_refl]
  · simp only [jointIndicator, if_neg H, divisorIndicator]
    split_ifs <;> norm_num

theorem jointIndicator_average_bound (r N : ℕ) (k h : Fin r → ℕ) (j : Fin r)
    (hN : 0<N) : orbitAverage N (jointIndicator r k h)≤(1+(h j : ℝ))/(k j+2 : ℝ) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  unfold orbitAverage
  calc
    _ ≤ (∑ n ∈ Finset.range N, divisorIndicator (k j+2) (n+1+h j))/(N : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ =>
        jointIndicator_le_single r k h (n+1) j)) hNR.le
    _ ≤ (((N+h j)/(k j+2) : ℕ) : ℝ)/(N : ℝ) :=
      div_le_div_of_nonneg_right (shifted_divisor_count_bound (k j+2) N (h j)) hNR.le
    _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_ofNat] using
      nat_div_average_bound (k j+2) N (h j) (by omega) hN

theorem inverse_max_le_product (r : ℕ) (hr : 0<r) (k : Fin r → ℕ) (j : Fin r)
    (hj : ∀ i, k i≤k j) : (((k j+2 : ℕ) : ℝ))⁻¹ ≤
      ∏ i : Fin r, ((k i+2 : ℕ) : ℝ)^(-(1/(r : ℝ))) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hkR : (0 : ℝ)<((k j+2 : ℕ) : ℝ) := by positivity
  have he : (((k j+2 : ℕ) : ℝ)^(-(1/(r : ℝ))))^r = (((k j+2 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hkR.le]
    rw [show -(1/(r : ℝ))*(r : ℝ)=(-1) by field_simp]
    exact Real.rpow_neg_one _
  calc
    _ = ∏ _i : Fin r, ((k j+2 : ℕ) : ℝ)^(-(1/(r : ℝ))) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, he]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        apply Real.rpow_le_rpow_of_nonpos (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (hj i) 2)
        exact neg_nonpos.mpr (by positivity)

theorem translate_integerPhase (n h : ℕ) :
    CollisionPotentialCoboundary.translate (h : ℤ) (integerPhase (n : ℤ)) =
      integerPhase ((n+h : ℕ) : ℤ) := by
  unfold CollisionPotentialCoboundary.translate
  rw [← integerPhase_add]
  congr 1
  push_cast
  omega

theorem jointResetTerm_integer (r : ℕ) (h k : Fin r → ℕ) (n : ℕ) :
    jointResetTerm r h k (integerPhase (n : ℤ)) =
      (∏ i, ((k i+2 : ℕ) : ℝ)*collisionWeight (k i+2))*jointIndicator r k h n := by
  unfold jointResetTerm
  simp_rw [translate_integerPhase, resetTerm_integer]
  by_cases H : ∀ i, k i+2∣n+h i
  · rw [jointIndicator, if_pos H, mul_one]
    exact Finset.prod_congr rfl (fun i _ => if_pos (H i))
  · have he : ∃ i, ¬k i+2∣n+h i := not_forall.mp H
    obtain ⟨i, hi⟩ := he
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp only [jointIndicator, if_neg H, mul_zero]

def jointTrace (r N : ℕ) (h k : Fin r → ℕ) : ℝ :=
  orbitAverage N (fun n => jointResetTerm r h k (integerPhase (n : ℤ)))

theorem jointTrace_eq_indicator (r N : ℕ) (h k : Fin r → ℕ) :
    jointTrace r N h k =
      (∏ i, ((k i+2 : ℕ) : ℝ)*collisionWeight (k i+2))*
        orbitAverage N (jointIndicator r k h) := by
  unfold jointTrace orbitAverage
  simp_rw [jointResetTerm_integer]
  rw [← Finset.mul_sum, mul_div_assoc]

def jointMajorant (r : ℕ) (h k : Fin r → ℕ) : ℝ :=
  (1+∑ i, (h i : ℝ))*∏ i, (((k i+2 : ℕ) : ℝ)*collisionWeight (k i+2)*
    ((k i+2 : ℕ) : ℝ)^(-(1/(r : ℝ))))

theorem jointMajorant_nonneg (r : ℕ) (h k : Fin r → ℕ) :
    0≤jointMajorant r h k := by
  apply mul_nonneg (by positivity)
  exact Finset.prod_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (by positivity) (collisionWeight_nonneg _)) (by positivity))

theorem jointTrace_norm_bound (r : ℕ) (hr : 0<r) (N : ℕ) (h k : Fin r → ℕ) :
    ‖jointTrace r N h k‖≤jointMajorant r h k := by
  by_cases hN : N=0
  · subst N
    simpa only [jointTrace, orbitAverage, Finset.range_zero, Finset.sum_empty,
      Nat.cast_zero, div_zero, norm_zero] using jointMajorant_nonneg r h k
  have hNp := Nat.pos_of_ne_zero hN
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ k Finset.univ_nonempty
  let A : ℝ := ∏ i, ((k i+2 : ℕ) : ℝ)*collisionWeight (k i+2)
  let C : ℝ := 1+∑ i, (h i : ℝ)
  have hA : 0≤A := Finset.prod_nonneg (fun _ _ =>
    mul_nonneg (by positivity) (collisionWeight_nonneg _))
  have hC : 0≤C := by dsimp [C]; positivity
  have hfreq : 0≤orbitAverage N (jointIndicator r k h) :=
    div_nonneg (Finset.sum_nonneg (fun n _ => jointIndicator_nonneg r k h (n+1)))
      (Nat.cast_nonneg N)
  have hcj : 1+(h j : ℝ)≤C := by
    have hb := Finset.single_le_sum (fun i _ => Nat.cast_nonneg (α := ℝ) (h i))
      (Finset.mem_univ j)
    dsimp [C]
    linarith
  have hi := inverse_max_le_product r hr k j (fun i => hj i (Finset.mem_univ i))
  have hf : orbitAverage N (jointIndicator r k h)≤
      C*∏ i, ((k i+2 : ℕ) : ℝ)^(-(1/(r : ℝ))) := by
    calc
      _ ≤ (1+(h j : ℝ))/(k j+2 : ℝ) := jointIndicator_average_bound r N k h j hNp
      _ ≤ C/((k j+2 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          div_le_div_of_nonneg_right hcj (by positivity : 0≤((k j+2 : ℕ) : ℝ))
      _ ≤ _ := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hi hC
  rw [jointTrace_eq_indicator, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hfreq)]
  calc
    _ ≤ A*(C*∏ i, ((k i+2 : ℕ) : ℝ)^(-(1/(r : ℝ)))) :=
      mul_le_mul_of_nonneg_left hf hA
    _ = jointMajorant r h k := by
      unfold jointMajorant A C
      simp only [Finset.prod_mul_distrib]
      ring

theorem jointMajorant_summable (r : ℕ) (hr : 0<r) (h : Fin r → ℕ) :
    Summable (jointMajorant r h) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  let b : ℕ → ℝ := fun k => ((k+2 : ℕ) : ℝ)*collisionWeight (k+2)*
    ((k+2 : ℕ) : ℝ)^(-(1/(r : ℝ)))
  have hb := (weighted_power_summable (one_div_pos.mpr hrR)).comp_injective
    (fun _ _ he => Nat.add_right_cancel he : Function.Injective (fun k : ℕ => k+2))
  have hbn (k : ℕ) : 0≤b k :=
    mul_nonneg (mul_nonneg (by positivity) (collisionWeight_nonneg _)) (by positivity)
  have hp := hasSum_nonneg_fin_product r (fun _ => b) (fun _ => ∑' k, b k)
    (fun _ k => hbn k) (fun _ => hb.hasSum)
  convert! hp.summable.mul_left (1+∑ i, (h i : ℝ)) using 1

theorem locallyConstant_finsetProd {ι : Type*} (S : Finset ι) (f : ι → Phase → ℝ)
    (hf : ∀ i ∈ S, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x => ∏ i ∈ S, f i x) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    convert! (IsLocallyConstant.const (1 : ℝ)) using 1
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem jointResetTerm_locallyConstant (r : ℕ) (h k : Fin r → ℕ) :
    IsLocallyConstant (jointResetTerm r h k) := by
  apply locallyConstant_finsetProd
  intro i _
  exact (resetTerm_locallyConstant (k i+2)).comp_continuous
    (continuous_const.mul continuous_id)

theorem jointTrace_tendsto (r : ℕ) (h k : Fin r → ℕ) :
    Tendsto (fun N => jointTrace r N h k) atTop
      (nhds (∫ x, jointResetTerm r h k x ∂phaseHaar)) := by
  exact locallyConstant_orbit_tendsto
    ⟨jointResetTerm r h k, jointResetTerm_locallyConstant r h k⟩

theorem resetTerm_from_two_hasSum_integer {n : ℕ} (hn : 0<n) :
    HasSum (fun k : ℕ => resetTerm (k+2) (integerPhase n))
      (resetFunction (integerPhase n)) := by
  have hx := resetTerm_trace_summable hn
  have ht := hx.comp_injective (fun _ _ h => Nat.add_right_cancel h :
    Function.Injective (fun k : ℕ => k+2))
  have he := hx.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, resetTerm_zero,
    resetTerm_one, Pi.zero_apply, zero_add] at he
  rw [show resetFunction (integerPhase n)=∑' k, resetTerm (k+2) (integerPhase n)
    from he.symm]
  exact ht.hasSum

theorem jointResetTerm_hasSum_integer (r : ℕ) (h : Fin r → ℕ) {n : ℕ} (hn : 0<n) :
    HasSum (fun k => jointResetTerm r h k (integerPhase n))
      (∏ i, resetFunction (integerPhase (n+h i : ℕ))) := by
  unfold jointResetTerm
  simp_rw [translate_integerPhase]
  exact hasSum_nonneg_fin_product r
    (fun (i : Fin r) (k : ℕ) => resetTerm (k+2) (integerPhase (n+h i : ℕ)))
    (fun i => resetFunction (integerPhase (n+h i : ℕ)))
    (fun i k => resetTerm_nonneg _ _) (fun i => resetTerm_from_two_hasSum_integer (by omega))

theorem joint_average_split (r N : ℕ) (h : Fin r → ℕ) :
    orbitAverage N (fun n => ∏ i, resetFunction (integerPhase (n+h i : ℕ))) =
      ∑' k, jointTrace r N h k := by
  unfold jointTrace orbitAverage
  rw [tsum_div_const]
  congr 1
  have hs (n : ℕ) (_ : n ∈ Finset.range N) :=
    (jointResetTerm_hasSum_integer r h (Nat.succ_pos n)).summable
  rw [Summable.tsum_finsetSum hs]
  apply Finset.sum_congr rfl
  intro n _
  exact (jointResetTerm_hasSum_integer r h (Nat.succ_pos n)).tsum_eq.symm

theorem reset_joint_moment_tendsto (r : ℕ) (h : Fin r → ℕ) :
    Tendsto (fun N => orbitAverage N
      (fun n => ∏ i, resetFunction (integerPhase (n+h i : ℕ)))) atTop
      (nhds (∫ x, ∏ i, resetFunction
        (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar)) := by
  by_cases hr : r=0
  · subst r
    have ht := locallyConstant_orbit_tendsto (LocallyConstant.const Phase (1 : ℝ))
    convert! ht using 1
  have ht := tendsto_tsum_of_dominated_convergence
    (jointMajorant_summable r (Nat.pos_of_ne_zero hr) h)
    (fun k => jointTrace_tendsto r h k)
    (Eventually.of_forall (fun N k => jointTrace_norm_bound r (Nat.pos_of_ne_zero hr) N h k))
  simp only [joint_average_split]
  rw [← (jointResetTerm_integral_hasSum r h).tsum_eq] 
  exact ht

end NField.Alignment.CollisionIntegerJointMoments
