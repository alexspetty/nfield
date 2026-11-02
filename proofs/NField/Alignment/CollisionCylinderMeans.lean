/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorRows
import NField.Alignment.CollisionDivisibilityCovariance

/-!
# Conditional means on actual residue cylinders

The conditional mean is a normalized Haar integral on a positive-measure
residue event. No values of an L2 representative at integers are used.
-/

noncomputable section

set_option autoImplicit false

namespace NField.Alignment.CollisionCylinderMeans

open scoped BigOperators
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionRemainderCovariance
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionDivisibilityCovariance
open CollisionMassReadout CollisionJordanVariance CollisionConductorRows

theorem centered_congruence_sum {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hdk : d ∣ k) (a : ℕ) :
    (∑ j ∈ Finset.range k, if Nat.ModEq d j a then centeredRemainder k j else 0) =
      ((k/d : ℕ) : ℝ) * centeredRemainder d a := by
  classical
  have hu : 0 < k/d := Nat.div_pos (Nat.le_of_dvd hk hdk) hd
  have hfac := Nat.div_mul_cancel hdk
  have ha (t j : ℕ) (ht : t < d) :
      centeredRemainder k (t+d*j) =
        centeredRemainder d t + (d : ℝ) * centeredRemainder (k/d) j := by
    calc
      _ = centeredRemainder (d*(k/d)) (t+d*j) := by rw [Nat.mul_div_cancel' hdk]
      _ = _ := centered_affine hd hu ht j
  calc
    _ = ∑ j ∈ Finset.range ((k/d)*d),
        if Nat.ModEq d j a then centeredRemainder k j else 0 := by rw [hfac]
    _ = ∑ t ∈ Finset.range d, ∑ j ∈ Finset.range (k/d),
        if Nat.ModEq d (t+d*j) a then centeredRemainder k (t+d*j) else 0 := by
      rw [sum_range_product, Finset.sum_comm]
    _ = ∑ t ∈ Finset.range d,
        if t = a%d then ((k/d : ℕ) : ℝ)*centeredRemainder d t else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_range.mp ht
      have he (j : ℕ) : Nat.ModEq d (t+d*j) a ↔ t = a%d := by
        simp [Nat.ModEq, Nat.add_mod, Nat.mod_eq_of_lt ht']
      simp_rw [he, ha t _ ht']
      split_ifs with hta
      · exact shifted_centered_cycle_sum hu _ _
      · simp
    _ = _ := by simp [Nat.mod_lt a hd, centeredRemainder]

def residueMap (L a : ℕ) : C(Phase, ℝ) := by
  by_cases hL : 0 < L
  · letI : NeZero L := ⟨hL.ne'⟩
    exact ⟨fun x => if (residueHom L x).toAdd = (a : ZMod L) then 1 else 0,
      (continuous_of_discreteTopology (f := fun z : Multiplicative (ZMod L) =>
        if z.toAdd = (a : ZMod L) then (1 : ℝ) else 0)).comp
        (residueHom L).continuous_toFun⟩
  · exact 0

theorem residueMap_indicator (L a : ℕ) (x : Phase) :
    residueMap L a x = (residueEvent L a).indicator (fun _ => (1 : ℝ)) x := by
  classical
  unfold residueMap residueEvent
  split_ifs with hL
  · simp only [ContinuousMap.coe_mk, Set.indicator, Set.mem_setOf_eq]
  · simp

def residueVector (L a : ℕ) : HaarL2 :=
  ContinuousMap.toLp 2 phaseHaar ℝ (residueMap L a)

theorem residueVector_pair_inner {k L : ℕ} (hk : 0 < k) (hL : 0 < L) (j a : ℕ) :
    inner ℝ (residueVector k j) (residueVector L a) =
      if Nat.ModEq (k.gcd L) j a then 1/(k.lcm L : ℝ) else 0 := by
  rw [residueVector, residueVector, ContinuousMap.inner_toLp]
  simpa only [residueMap_indicator, conj_trivial, mul_comm]
    using residueEvent_pair_integral hk hL j a

theorem remainderMap_residue_sum {k : ℕ} (hk : 0 < k) :
    remainderMap k = ∑ j ∈ Finset.range k, centeredRemainder k j • residueMap k j := by
  classical
  letI : NeZero k := ⟨hk.ne'⟩
  ext x
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have he (j : ℕ) (hj : j ∈ Finset.range k) :
      centeredRemainder k j * residueMap k j x =
        if j = (residueHom k x).toAdd.val then centeredRemainder k j else 0 := by
    rw [residueMap_indicator]
    have hm := mem_residueEvent_via (a := j) (dvd_refl k) x
    have hval := ZMod.val_lt (residueHom k x).toAdd
    have heq : Nat.ModEq k (residueHom k x).toAdd.val j ↔
        j = (residueHom k x).toAdd.val := by
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hval,
        Nat.mod_eq_of_lt (Finset.mem_range.mp hj), eq_comm]
    by_cases h : j = (residueHom k x).toAdd.val
    · rw [Set.indicator_of_mem (hm.mpr (heq.mpr h)), if_pos h, mul_one]
    · rw [Set.indicator_of_notMem (fun hx => h (heq.mp (hm.mp hx))), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_ite_eq', Finset.mem_range,
    ZMod.val_lt, if_true]
  exact centered_via_residue (dvd_refl k) x

theorem remainderVector_residue_sum {k : ℕ} (hk : 0 < k) :
    remainderVector k = ∑ j ∈ Finset.range k, centeredRemainder k j • residueVector k j := by
  rw [remainderVector, remainderMap_residue_sum hk]
  simp only [map_sum, map_smul, residueVector]

theorem residue_remainder_inner {k L : ℕ} (hk : 0 < k) (hL : 0 < L) (a : ℕ) :
    inner ℝ (residueVector L a) (remainderVector k) =
      centeredRemainder (k.gcd L) a / (L : ℝ) := by
  classical
  rw [real_inner_comm, remainderVector_residue_sum hk]
  simp only [sum_inner, inner_smul_left, conj_trivial, residueVector_pair_inner hk hL]
  have he : (∑ j ∈ Finset.range k, centeredRemainder k j *
      (if Nat.ModEq (k.gcd L) j a then 1/(k.lcm L : ℝ) else 0)) =
      (∑ j ∈ Finset.range k, if Nat.ModEq (k.gcd L) j a then
        centeredRemainder k j else 0) / (k.lcm L : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp [div_eq_mul_inv]
  rw [he, centered_congruence_sum hk (Nat.gcd_pos_of_pos_left L hk) (Nat.gcd_dvd_left k L)]
  have hratio : (k.lcm L : ℝ) = ((k / k.gcd L : ℕ) : ℝ) * (L : ℝ) := by
    exact_mod_cast (Nat.lcm_eq_mul_div k L).trans (by
      rw [Nat.mul_comm k L, Nat.mul_div_assoc L (Nat.gcd_dvd_left k L), Nat.mul_comm])
  have hu : ((k / k.gcd L : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.div_gcd_pos_of_pos_left L hk).ne'
  rw [hratio]
  field_simp

def cylinderFunctional (L a : ℕ) : HaarL2 →L[ℝ] ℝ :=
  (L : ℝ) • innerSL ℝ (residueVector L a)

theorem cylinderFunctional_apply (L a : ℕ) (Y : HaarL2) :
    cylinderFunctional L a Y = (L : ℝ) * inner ℝ (residueVector L a) Y := rfl

theorem cylinderFunctional_integral (L a : ℕ) (Y : HaarL2) :
    cylinderFunctional L a Y = (L : ℝ) *
      ∫ x in residueEvent L a, Y x ∂phaseHaar := by
  rw [cylinderFunctional_apply, L2.inner_def,
    ← integral_indicator (residueEvent_measurable L a)]
  congr 1
  apply integral_congr_ae
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (residueMap L a)
  filter_upwards [hr] with x hx
  simp only [RCLike.inner_apply, conj_trivial]
  change Y x * residueVector L a x = _
  change residueVector L a x = residueMap L a x at hx
  rw [hx, residueMap_indicator]
  by_cases h : x ∈ residueEvent L a <;> simp [h]

theorem residueEvent_measure {L : ℕ} (hL : 0 < L) (a : ℕ) :
    phaseHaar.real (residueEvent L a) = 1/(L : ℝ) := by
  have h := residueEvent_pair_integral hL hL a a
  have he : (fun x : Phase => (residueEvent L a).indicator (fun _ => (1 : ℝ)) x *
      (residueEvent L a).indicator (fun _ => (1 : ℝ)) x) =
      (residueEvent L a).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ residueEvent L a <;> simp [hx]
  rw [he, integral_indicator (residueEvent_measurable L a), setIntegral_const] at h
  simpa [Nat.ModEq] using h

theorem cylinderFunctional_normalized_integral {L : ℕ} (hL : 0 < L)
    (a : ℕ) (Y : HaarL2) :
    cylinderFunctional L a Y =
      (∫ x in residueEvent L a, Y x ∂phaseHaar) / phaseHaar.real (residueEvent L a) := by
  rw [cylinderFunctional_integral, residueEvent_measure hL]
  simp [div_eq_mul_inv, mul_comm]

theorem cylinderFunctional_remainder {k L : ℕ} (hk : 0 < k) (hL : 0 < L) (a : ℕ) :
    cylinderFunctional L a (remainderVector k) = centeredRemainder (k.gcd L) a := by
  rw [cylinderFunctional_apply, residue_remainder_inner hk hL]
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

theorem cylinderFunctional_finite {L : ℕ} (hL : 0 < L) (a M : ℕ) (v : ℕ → ℝ) :
    cylinderFunctional L a (finitePotential v M) =
      (2/3 : ℝ) * ∑ k ∈ Finset.Icc 2 M, v k * centeredRemainder (k.gcd L) a := by
  simp only [finitePotential, map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [cylinderFunctional_remainder (by have := (Finset.mem_Icc.mp hk).1; omega) hL]

def cylinderMean (L a : ℕ) : ℝ := cylinderFunctional L a collisionPotential

theorem centered_gcd_bound {L : ℕ} (hL : 0 < L) (k a : ℕ) :
    |centeredRemainder (k.gcd L) a| ≤ (L : ℝ) := by
  have hd : 0 < k.gcd L := Nat.gcd_pos_of_pos_right k hL
  have hdL : (k.gcd L : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.gcd_le_right k hL
  have hd1 : (1 : ℝ) ≤ (k.gcd L : ℝ) := by exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ (a % k.gcd L : ℕ) := by positivity
  have hr1 : ((a % k.gcd L : ℕ) : ℝ) < (k.gcd L : ℝ) := by
    exact_mod_cast Nat.mod_lt a hd
  rw [centeredRemainder, abs_le]
  constructor <;> linarith

theorem cylinder_series_summable {L : ℕ} (hL : 0 < L) (a : ℕ) :
    Summable (fun k => collisionWeight k * centeredRemainder (k.gcd L) a) := by
  apply Summable.of_norm_bounded (collisionWeight_summable.mul_right (L : ℝ))
  intro k
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (collisionWeight_nonneg k)]
  exact mul_le_mul_of_nonneg_left (centered_gcd_bound hL k a) (collisionWeight_nonneg k)

theorem cylinderMean_series {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a = (2/3 : ℝ) *
      ∑' k, collisionWeight k * centeredRemainder (k.gcd L) a := by
  have ht := (cylinderFunctional L a).continuous.tendsto collisionPotential |>.comp
    tendsto_collisionPotential
  have hs := ((cylinder_series_summable hL a).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)).const_mul (2/3 : ℝ)
  have h0 : collisionWeight 0 * centeredRemainder (Nat.gcd 0 L) a = 0 := by simp
  have h1 : collisionWeight 1 * centeredRemainder (Nat.gcd 1 L) a = 0 := by simp
  simp only [Function.comp_def, cylinderFunctional_finite hL] at ht
  simp only [Function.comp_def, sum_range_zero_one
    (fun k => collisionWeight k * centeredRemainder (k.gcd L) a) h0 h1] at hs
  exact tendsto_nhds_unique ht hs

def primitiveValue (q a : ℕ) : ℝ := primitiveRowMap q (integerPhase (a : ℤ))

theorem primitiveValue_formula (q a : ℕ) :
    primitiveValue q a = ∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius (q/d) : ℝ) * centeredRemainder d a := by
  rw [primitiveValue, primitiveRowMap_formula]
  apply Finset.sum_congr rfl
  intro d hd
  rw [centered_integer (Nat.pos_of_mem_divisors hd)]

@[simp] theorem primitiveValue_one (a : ℕ) : primitiveValue 1 a = 0 := by
  simp [primitiveValue_formula, centeredRemainder, Nat.mod_one]

theorem primitiveValue_divisor_sum {k : ℕ} (hk : 0 < k) (a : ℕ) :
    (∑ q ∈ k.divisors, primitiveValue q a) = centeredRemainder k a := by
  have he : ∀ q > 0,
      (∑ p ∈ q.divisorsAntidiagonal,
        (ArithmeticFunction.moebius p.1 : ℝ) * centeredRemainder p.2 a) = primitiveValue q a := by
    intro q hq
    rw [Nat.sum_divisorsAntidiagonal' (fun d e =>
      (ArithmeticFunction.moebius d : ℝ) * centeredRemainder e a), primitiveValue_formula]
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun q => primitiveValue q a) (g := fun k => centeredRemainder k a)).mpr he k hk

theorem divisors_gcd_filter {L : ℕ} (hL : 0 < L) (k : ℕ) :
    L.divisors.filter (fun q => q ∣ k) = (k.gcd L).divisors := by
  ext q
  simp only [Finset.mem_filter, Nat.mem_divisors]
  have hg := (Nat.gcd_pos_of_pos_right k hL).ne'
  constructor
  · rintro ⟨⟨hqL,_⟩,hqk⟩
    exact ⟨Nat.dvd_gcd hqk hqL,hg⟩
  · rintro ⟨hqg,_⟩
    exact ⟨⟨hqg.trans (Nat.gcd_dvd_right k L),hL.ne'⟩,
      hqg.trans (Nat.gcd_dvd_left k L)⟩

theorem centered_gcd_primitive_sum {L : ℕ} (hL : 0 < L) (k a : ℕ) :
    centeredRemainder (k.gcd L) a =
      ∑ q ∈ L.divisors, if q ∣ k then primitiveValue q a else 0 := by
  rw [← Finset.sum_filter, divisors_gcd_filter hL,
    primitiveValue_divisor_sum (Nat.gcd_pos_of_pos_right k hL)]

theorem finite_cylinder_regrouping {L : ℕ} (hL : 0 < L)
    (a M : ℕ) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 M, v k * centeredRemainder (k.gcd L) a) =
      ∑ q ∈ L.divisors, finiteAmplitude v q M * primitiveValue q a := by
  simp_rw [centered_gcd_primitive_sum hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [finiteAmplitude, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp

theorem cylinderMean_conductors {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a = (2/3 : ℝ) *
      ∑ q ∈ L.divisors, amplitude q * primitiveValue q a := by
  have ht := (cylinderFunctional L a).continuous.tendsto collisionPotential |>.comp
    tendsto_collisionPotential
  simp only [Function.comp_def, cylinderFunctional_finite hL,
    finite_cylinder_regrouping hL] at ht
  have hs := (tendsto_finsetSum L.divisors (fun q _ =>
    (finiteAmplitude_tendsto q).mul_const (primitiveValue q a))).const_mul (2/3 : ℝ)
  exact tendsto_nhds_unique ht hs

theorem cylinderMean_conductors_ge_two {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a = (2/3 : ℝ) *
      ∑ q ∈ L.divisors, if 2 ≤ q then amplitude q * primitiveValue q a else 0 := by
  rw [cylinderMean_conductors hL]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqp := Nat.pos_of_mem_divisors hq
  by_cases hq2 : 2 ≤ q
  · rw [if_pos hq2]
  · have hq1 : q = 1 := by omega
    simp [hq1]

def alignmentConstant (L : ℕ) : ℝ :=
  (1/3 : ℝ) * ∑' k, collisionWeight k * ((k.gcd L : ℝ)-1)

theorem alignment_series_summable {L : ℕ} (hL : 0 < L) :
    Summable (fun k => collisionWeight k * ((k.gcd L : ℝ)-1)) := by
  apply Summable.of_norm_bounded (collisionWeight_summable.mul_right (L : ℝ))
  intro k
  have hd1 : (1 : ℝ) ≤ (k.gcd L : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_right k hL
  have hdL : (k.gcd L : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.gcd_le_right k hL
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (collisionWeight_nonneg k),
    abs_of_nonneg (sub_nonneg.mpr hd1)]
  exact mul_le_mul_of_nonneg_left (by linarith) (collisionWeight_nonneg k)

theorem alignmentConstant_nonneg {L : ℕ} (hL : 0 < L) : 0 ≤ alignmentConstant L := by
  unfold alignmentConstant
  refine mul_nonneg (by norm_num) ?_
  apply tsum_nonneg
  intro k
  apply mul_nonneg (collisionWeight_nonneg k)
  have hd1 : (1 : ℝ) ≤ (k.gcd L : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_right k hL
  linarith

theorem totient_divisor_sum_ge_two {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ d.divisors, if 2 ≤ q then (Nat.totient q : ℝ) else 0) = (d : ℝ)-1 := by
  classical
  have he : d.divisors.filter (fun q => 2 ≤ q) = d.divisors.erase 1 := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hq,hq2⟩; exact ⟨by omega,hq⟩
    · rintro ⟨hq1,hq⟩
      have hqp := Nat.pos_of_mem_divisors hq
      exact ⟨hq,by omega⟩
  rw [← Finset.sum_filter, he]
  have hs := Finset.sum_erase_add d.divisors (fun q => (Nat.totient q : ℝ))
    (Nat.one_mem_divisors.mpr hd.ne')
  have hc : (∑ q ∈ d.divisors, (Nat.totient q : ℝ)) = (d : ℝ) := by
    exact_mod_cast Nat.sum_totient d
  rw [hc] at hs
  norm_num at hs
  linarith

theorem weighted_gcd_divisor_tsum {L : ℕ} (hL : 0 < L) (f : ℕ → ℝ) :
    (∑' k, collisionWeight k * ∑ q ∈ (k.gcd L).divisors, f q) =
      ∑ q ∈ L.divisors, amplitude q * f q := by
  classical
  have he (k : ℕ) : collisionWeight k * ∑ q ∈ (k.gcd L).divisors, f q =
      ∑ q ∈ L.divisors, (if q ∣ k then collisionWeight k else 0) * f q := by
    rw [← divisors_gcd_filter hL k, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    split_ifs <;> simp
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun q _ => (amplitude_summable q).mul_right (f q))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [tsum_mul_right]
  rfl

theorem alignmentConstant_conductors {L : ℕ} (hL : 0 < L) :
    alignmentConstant L = (1/3 : ℝ) *
      ∑ q ∈ L.divisors, if 2 ≤ q then (Nat.totient q : ℝ) * amplitude q else 0 := by
  unfold alignmentConstant
  simp_rw [← totient_divisor_sum_ge_two (Nat.gcd_pos_of_pos_right _ hL)]
  rw [weighted_gcd_divisor_tsum hL]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> simp [mul_comm]

def ageTerm (L a k : ℕ) : ℝ := collisionWeight k * ((a % k.gcd L : ℕ) : ℝ)

theorem ageTerm_nonneg (L a k : ℕ) : 0 ≤ ageTerm L a k :=
  mul_nonneg (collisionWeight_nonneg k) (Nat.cast_nonneg _)

theorem ageTerm_summable {L : ℕ} (hL : 0 < L) (a : ℕ) : Summable (ageTerm L a) := by
  apply Summable.of_nonneg_of_le (ageTerm_nonneg L a) _
    (collisionWeight_summable.mul_right (L : ℝ))
  intro k
  apply mul_le_mul_of_nonneg_left _ (collisionWeight_nonneg k)
  exact_mod_cast (Nat.mod_lt a (Nat.gcd_pos_of_pos_right k hL)).le.trans
    (Nat.gcd_le_right k hL)

theorem cylinderMean_gap {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a + alignmentConstant L = (2/3 : ℝ) * ∑' k, ageTerm L a k := by
  rw [cylinderMean_series hL, alignmentConstant]
  have he (k : ℕ) : collisionWeight k * centeredRemainder (k.gcd L) a =
      ageTerm L a k - collisionWeight k * ((k.gcd L : ℝ)-1) / 2 := by
    unfold ageTerm centeredRemainder
    ring
  simp_rw [he]
  rw [(ageTerm_summable hL a).tsum_sub ((alignment_series_summable hL).div_const 2),
    tsum_div_const]
  ring

theorem cylinderMean_lower {L : ℕ} (hL : 0 < L) (a : ℕ) :
    -alignmentConstant L ≤ cylinderMean L a := by
  have h := cylinderMean_gap hL a
  have hn : 0 ≤ ∑' k, ageTerm L a k := tsum_nonneg (ageTerm_nonneg L a)
  linarith

theorem cylinderMean_near_zero {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a ≤ -alignmentConstant L + (2/3 : ℝ)*(a : ℝ) := by
  have hs : (∑' k, ageTerm L a k) ≤ (a : ℝ) := by
    have hb : ∀ k, ageTerm L a k ≤ collisionWeight k * (a : ℝ) := fun k =>
      mul_le_mul_of_nonneg_left
        (show ((a % k.gcd L : ℕ) : ℝ) ≤ (a : ℝ) by exact_mod_cast Nat.mod_le a (k.gcd L))
        (collisionWeight_nonneg k)
    have h := Summable.tsum_le_tsum hb (ageTerm_summable hL a)
      (collisionWeight_summable.mul_right (a : ℝ))
    simpa only [tsum_mul_right, collisionWeight_tsum, one_mul] using h
  have h := cylinderMean_gap hL a
  linarith

theorem cylinderMean_min_iff {L : ℕ} (hL : 2 ≤ L) (a : ℕ) :
    cylinderMean L a = -alignmentConstant L ↔ L ∣ a := by
  have hLp : 0 < L := by omega
  constructor
  · intro h
    have hs := cylinderMean_gap hLp a
    have hzero : (∑' k, ageTerm L a k) = 0 := by linarith
    have hterm := (ageTerm_summable hLp a).le_tsum L (fun k _ => ageTerm_nonneg L a k)
    rw [hzero] at hterm
    have he : ageTerm L a L = 0 := le_antisymm hterm (ageTerm_nonneg L a L)
    simp only [ageTerm, Nat.gcd_self] at he
    have hr := (mul_eq_zero.mp he).resolve_left (collisionWeight_pos hL).ne'
    exact Nat.dvd_of_mod_eq_zero (by exact_mod_cast hr)
  · intro ha
    have hz : (∑' k, ageTerm L a k) = 0 := by
      have hp (k : ℕ) : ageTerm L a k = 0 := by
        simp [ageTerm, Nat.mod_eq_zero_of_dvd ((Nat.gcd_dvd_right k L).trans ha)]
      simp only [hp, tsum_zero]
    have h := cylinderMean_gap hLp a
    rw [hz] at h
    linarith

def complementTerm (L a k : ℕ) : ℝ :=
  collisionWeight k * ((k.gcd L : ℝ)-1-((a % k.gcd L : ℕ) : ℝ))

theorem complementTerm_nonneg {L : ℕ} (hL : 0 < L) (a k : ℕ) :
    0 ≤ complementTerm L a k := by
  apply mul_nonneg (collisionWeight_nonneg k)
  have hr : ((a % k.gcd L : ℕ) : ℝ)+1 ≤ (k.gcd L : ℝ) := by
    exact_mod_cast Nat.mod_lt a (Nat.gcd_pos_of_pos_right k hL)
  linarith

theorem complementTerm_summable {L : ℕ} (hL : 0 < L) (a : ℕ) :
    Summable (complementTerm L a) := by
  have h := (alignment_series_summable hL).sub (ageTerm_summable hL a)
  change Summable (fun k => collisionWeight k *
    ((k.gcd L : ℝ)-1-((a % k.gcd L : ℕ) : ℝ)))
  simpa only [complementTerm, ageTerm, mul_sub] using h

theorem cylinderMean_upper_gap {L : ℕ} (hL : 0 < L) (a : ℕ) :
    alignmentConstant L - cylinderMean L a = (2/3 : ℝ) * ∑' k, complementTerm L a k := by
  have he : (∑' k, complementTerm L a k) =
      (∑' k, collisionWeight k * ((k.gcd L : ℝ)-1)) - ∑' k, ageTerm L a k := by
    have hp (k : ℕ) : complementTerm L a k =
        collisionWeight k * ((k.gcd L : ℝ)-1) - ageTerm L a k := by
      unfold complementTerm ageTerm
      ring
    simp only [hp]
    exact (alignment_series_summable hL).tsum_sub (ageTerm_summable hL a)
  rw [he]
  have h := cylinderMean_gap hL a
  unfold alignmentConstant at h ⊢
  linarith

theorem cylinderMean_upper {L : ℕ} (hL : 0 < L) (a : ℕ) :
    cylinderMean L a ≤ alignmentConstant L := by
  have h := cylinderMean_upper_gap hL a
  have hn : 0 ≤ ∑' k, complementTerm L a k := tsum_nonneg (complementTerm_nonneg hL a)
  linarith

theorem mod_predecessor_of_dvd {d a : ℕ} (hd : 0 < d) (ha : d ∣ a+1) :
    a%d+1=d := by
  have hz := Nat.mod_eq_zero_of_dvd ha
  have hr := Nat.mod_lt a hd
  rw [Nat.add_mod] at hz
  by_cases hd1 : d=1
  · simp [hd1, Nat.mod_one]
  · have hone : 1%d=1 := Nat.mod_eq_of_lt (by omega)
    rw [hone] at hz
    have hle : a%d+1 ≤ d := by omega
    by_cases he : a%d+1=d
    · exact he
    · rw [Nat.mod_eq_of_lt (by omega : a%d+1<d)] at hz
      omega

theorem cylinderMean_max_iff {L : ℕ} (hL : 2 ≤ L) (a : ℕ) :
    cylinderMean L a = alignmentConstant L ↔ L ∣ a+1 := by
  have hLp : 0 < L := by omega
  constructor
  · intro h
    have hs := cylinderMean_upper_gap hLp a
    have hzero : (∑' k, complementTerm L a k) = 0 := by linarith
    have hterm := (complementTerm_summable hLp a).le_tsum L
      (fun k _ => complementTerm_nonneg hLp a k)
    rw [hzero] at hterm
    have he : complementTerm L a L = 0 :=
      le_antisymm hterm (complementTerm_nonneg hLp a L)
    simp only [complementTerm, Nat.gcd_self] at he
    have hr := (mul_eq_zero.mp he).resolve_left (collisionWeight_pos hL).ne'
    have hmod : a%L+1=L := by
      have hc : ((a%L : ℕ) : ℝ)+1=(L : ℝ) := by linarith
      exact_mod_cast hc
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, Nat.mod_eq_of_lt hL, hmod, Nat.mod_self]
  · intro ha
    have hz : (∑' k, complementTerm L a k) = 0 := by
      have ht (k : ℕ) : complementTerm L a k = 0 := by
        have hp := mod_predecessor_of_dvd (Nat.gcd_pos_of_pos_right k hLp)
          ((Nat.gcd_dvd_right k L).trans ha)
        have hc : ((a % k.gcd L : ℕ) : ℝ)+1=(k.gcd L : ℝ) := by exact_mod_cast hp
        have hzero : (k.gcd L : ℝ)-1-((a % k.gcd L : ℕ) : ℝ)=0 := by linarith
        simp only [complementTerm, hzero, mul_zero]
      simp only [ht, tsum_zero]
    have h := cylinderMean_upper_gap hLp a
    rw [hz] at h
    linarith

theorem cylinderMean_zero {L : ℕ} (hL : 2 ≤ L) :
    cylinderMean L 0 = -alignmentConstant L :=
  (cylinderMean_min_iff hL 0).mpr (dvd_zero L)

theorem cylinderMean_predecessor {L : ℕ} (hL : 2 ≤ L) :
    cylinderMean L (L-1) = alignmentConstant L := by
  apply (cylinderMean_max_iff hL (L-1)).mpr
  rw [Nat.sub_add_cancel (by omega : 1 ≤ L)]

/-- All clauses of the cylinder-mean proposition for the constructed potential. -/
theorem cylinder_means {L : ℕ} (hL : 2 ≤ L) (a : ℕ) :
    cylinderMean L a =
        (∫ x in residueEvent L a, collisionPotential x ∂phaseHaar) /
          phaseHaar.real (residueEvent L a) ∧
    cylinderMean L a = (2/3 : ℝ) *
        (∑' k, collisionWeight k * centeredRemainder (k.gcd L) a) ∧
    cylinderMean L a = (2/3 : ℝ) *
        (∑ q ∈ L.divisors, if 2 ≤ q then amplitude q * primitiveValue q a else 0) ∧
    alignmentConstant L = (1/3 : ℝ) *
        (∑ q ∈ L.divisors, if 2 ≤ q then (Nat.totient q : ℝ) * amplitude q else 0) ∧
    -alignmentConstant L ≤ cylinderMean L a ∧
    cylinderMean L a ≤ alignmentConstant L ∧
    (cylinderMean L a = -alignmentConstant L ↔ L ∣ a) ∧
    (cylinderMean L a = alignmentConstant L ↔ L ∣ a+1) ∧
    cylinderMean L a ≤ -alignmentConstant L + (2/3 : ℝ)*(a : ℝ) := by
  have hLp : 0 < L := by omega
  exact ⟨cylinderFunctional_normalized_integral hLp a collisionPotential,
    cylinderMean_series hLp a, cylinderMean_conductors_ge_two hLp a,
    alignmentConstant_conductors hLp, cylinderMean_lower hLp a,
    cylinderMean_upper hLp a, cylinderMean_min_iff hL a, cylinderMean_max_iff hL a,
    cylinderMean_near_zero hLp a⟩

end NField.Alignment.CollisionCylinderMeans
