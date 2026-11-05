/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCylinderMeans
import NField.Alignment.CollisionPotentialReflection
import NField.Alignment.ReducedHarmonicMobius
import NField.Alignment.CollisionRamanujan

/-!
# Even reset rows and odd collision carriers

All rows below are continuous functions on the actual profinite phase
space, embedded in Haar L2. Their norms follow from CRT and Mobius
inversion, independently of an assumed Fourier-completeness theorem.
-/

noncomputable section

set_option autoImplicit false

namespace NField.Alignment.CollisionParityRows

open scoped BigOperators Classical
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionConductorRows CollisionCylinderMeans
open CollisionDivisibilityCovariance CollisionJordanVariance
open CollisionPotentialCoboundary CollisionPotentialReflection

def resetRowMap (k : ℕ) : C(Phase, ℝ) := (k : ℝ) • residueMap k 0 - 1

def resetRow (k : ℕ) : HaarL2 := (k : ℝ) • residueVector k 0 - oneVector

theorem resetRow_toLp (k : ℕ) :
    resetRow k = ContinuousMap.toLp 2 phaseHaar ℝ (resetRowMap k) := by
  simp only [resetRow, resetRowMap, map_sub, map_smul, residueVector, oneVector]

theorem residueVector_mean {k : ℕ} (hk : 0 < k) (a : ℕ) :
    inner ℝ oneVector (residueVector k a) = 1/(k : ℝ) := by
  rw [mean_inner_eq_integral]
  have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (residueMap k a)
  change residueVector k a =ᵐ[phaseHaar] residueMap k a at he
  rw [integral_congr_ae he]
  simp only [residueMap_indicator]
  rw [integral_indicator_const (1 : ℝ) (residueEvent_measurable k a),
    smul_eq_mul, mul_one, residueEvent_measure hk]

theorem resetRow_mean {k : ℕ} (hk : 0 < k) : inner ℝ oneVector (resetRow k) = 0 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [resetRow, inner_sub_right, inner_smul_right, residueVector_mean hk,
    oneVector_inner_self]
  field_simp
  norm_num

theorem resetRow_inner {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    inner ℝ (resetRow k) (resetRow l) = (k.gcd l : ℝ)-1 := by
  have hkl := residueVector_pair_inner hk hl 0 0
  simp only [Nat.ModEq.refl, if_true] at hkl
  have hsym : inner ℝ (residueVector k 0) oneVector = 1/(k : ℝ) := by
    rw [real_inner_comm, residueVector_mean hk]
  simp only [resetRow, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial, hkl, hsym, residueVector_mean hl, oneVector_inner_self]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hL0 : (k.lcm l : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hk hl).ne'
  have hprod : (k.gcd l : ℝ)*(k.lcm l : ℝ)=(k : ℝ)*(l : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm k l
  field_simp
  nlinarith

theorem remainder_resetRow_inner {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    inner ℝ (remainderVector k) (resetRow l) = -((k.gcd l : ℝ)-1)/2 := by
  have hmean : inner ℝ (remainderVector k) oneVector = 0 := by
    rw [real_inner_comm]
    exact remainder_mean_inner hk
  have hr : inner ℝ (remainderVector k) (residueVector l 0) =
      centeredRemainder (k.gcd l) 0/(l : ℝ) := by
    rw [real_inner_comm, residue_remainder_inner hk hl]
  rw [resetRow, inner_sub_right, inner_smul_right, hr, hmean]
  simp only [centeredRemainder, Nat.zero_mod, Nat.cast_zero]
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  field_simp
  ring

def ramanujanRowMap (q : ℕ) : C(Phase, ℝ) :=
  ∑ p ∈ q.divisorsAntidiagonal, ArithmeticFunction.moebius p.1 • resetRowMap p.2

def ramanujanRow (q : ℕ) : HaarL2 :=
  ∑ p ∈ q.divisorsAntidiagonal, ArithmeticFunction.moebius p.1 • resetRow p.2

theorem ramanujanRow_toLp (q : ℕ) :
    ramanujanRow q = ContinuousMap.toLp 2 phaseHaar ℝ (ramanujanRowMap q) := by
  simp only [ramanujanRow, ramanujanRowMap, map_sum, map_zsmul, ← resetRow_toLp]

theorem resetRow_ramanujan_inner {k q : ℕ} (hk : 0 < k) (hq : 0 < q) :
    inner ℝ (resetRow k) (ramanujanRow q) =
      if 2 ≤ q ∧ q ∣ k then (Nat.totient q : ℝ) else 0 := by
  let f : ℕ → ℝ := fun d => if 2 ≤ d ∧ d ∣ k then (Nat.totient d : ℝ) else 0
  have hf : ∀ m > 0, (∑ d ∈ m.divisors, f d) =
      inner ℝ (resetRow k) (resetRow m) := by
    intro m hm
    rw [resetRow_inner hk hm]
    have he : (∑ d ∈ m.divisors, f d) =
        ∑ d ∈ (m.divisors.filter (fun d => d ∣ k)),
          if 2 ≤ d then (Nat.totient d : ℝ) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [f]
      split_ifs <;> simp_all
    rw [he, divisors_gcd_filter hm,
      totient_divisor_sum_ge_two (Nat.gcd_pos_of_pos_left m hk)]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := f) (g := fun m => inner ℝ (resetRow k) (resetRow m))).mp hf q hq
  unfold ramanujanRow
  simpa only [inner_sum, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, f] using hi

theorem ramanujanRow_inner {p q : ℕ} (hp : 0 < p) (hq : 2 ≤ q) :
    inner ℝ (ramanujanRow p) (ramanujanRow q) =
      if p=q then (Nat.totient q : ℝ) else 0 := by
  let f : ℕ → ℝ := fun m => if m=q then (Nat.totient q : ℝ) else 0
  have hf : ∀ m > 0, (∑ d ∈ m.divisors, f d) =
      inner ℝ (resetRow m) (ramanujanRow q) := by
    intro m hm
    rw [resetRow_ramanujan_inner hm (by omega)]
    simp only [f, Finset.sum_ite_eq']
    by_cases hqm : q ∣ m
    · rw [if_pos (Nat.mem_divisors.mpr ⟨hqm,hm.ne'⟩), if_pos ⟨hq,hqm⟩]
    · rw [if_neg (fun h => hqm (Nat.mem_divisors.mp h).1), if_neg (fun h => hqm h.2)]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := f) (g := fun m => inner ℝ (resetRow m) (ramanujanRow q))).mp hf p hp
  unfold ramanujanRow at ⊢
  change inner ℝ (∑ x ∈ p.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • resetRow x.2)
    (ramanujanRow q) = _
  simpa only [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, conj_trivial, f] using hi

theorem ramanujanRow_norm_sq {q : ℕ} (hq : 2 ≤ q) :
    ‖ramanujanRow q‖^2 = (Nat.totient q : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, ramanujanRow_inner (by omega) hq, if_pos rfl]

theorem remainder_ramanujan_inner {k q : ℕ} (hk : 0 < k) (hq : 0 < q) :
    inner ℝ (remainderVector k) (ramanujanRow q) =
      -(1/2 : ℝ) * inner ℝ (resetRow k) (ramanujanRow q) := by
  unfold ramanujanRow
  simp only [inner_sum, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hp2 : 0 < p.2 := by nlinarith
  rw [remainder_resetRow_inner hk hp2, resetRow_inner hk hp2]
  ring

theorem primitive_ramanujan_inner {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    inner ℝ (primitiveRow p) (ramanujanRow q) =
      -(1/2 : ℝ) * inner ℝ (ramanujanRow p) (ramanujanRow q) := by
  change inner ℝ (∑ x ∈ p.divisorsAntidiagonal,
    ArithmeticFunction.moebius x.1 • remainderVector x.2) (ramanujanRow q) =
      -(1/2 : ℝ) * inner ℝ (∑ x ∈ p.divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 • resetRow x.2) (ramanujanRow q)
  simp only [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, conj_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have he := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hx2 : 0 < x.2 := by nlinarith
  rw [remainder_ramanujan_inner hx2 hq]
  ring

def carrierRowMap (q : ℕ) : C(Phase, ℝ) :=
  primitiveRowMap q + (1/2 : ℝ) • ramanujanRowMap q

def carrierRow (q : ℕ) : HaarL2 := primitiveRow q + (1/2 : ℝ) • ramanujanRow q

theorem carrierRow_toLp (q : ℕ) :
    carrierRow q = ContinuousMap.toLp 2 phaseHaar ℝ (carrierRowMap q) := by
  simp only [carrierRow, carrierRowMap, map_add, map_smul,
    ← primitiveRow_toLp, ← ramanujanRow_toLp]

theorem primitiveRow_split (q : ℕ) :
    primitiveRow q = carrierRow q - (1/2 : ℝ) • ramanujanRow q := by
  simp only [carrierRow, add_sub_cancel_right]

theorem carrierRow_norm_sq {q : ℕ} (hq : 2 ≤ q) :
    ‖carrierRow q‖^2 = (jordanTwo q - 3*(Nat.totient q : ℝ))/12 := by
  rw [carrierRow, norm_add_sq_real, primitiveRow_norm_sq hq,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2), mul_pow,
    ramanujanRow_norm_sq hq, inner_smul_right,
    primitive_ramanujan_inner (by omega) (by omega),
    ramanujanRow_inner (by omega) hq, if_pos rfl]
  ring

theorem carrier_ramanujan_orthogonal {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    inner ℝ (carrierRow p) (ramanujanRow q) = 0 := by
  rw [carrierRow, inner_add_left, inner_smul_left, conj_trivial,
    primitive_ramanujan_inner hp hq]
  ring

theorem resetRowMap_apply (k : ℕ) (x : Phase) :
    resetRowMap k x = (k : ℝ) *
      (residueEvent k 0).indicator (fun _ => (1 : ℝ)) x - 1 := by
  simp only [resetRowMap, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, residueMap_indicator]

theorem ramanujanRowMap_formula {q : ℕ} (hq : 2 ≤ q) (x : Phase) :
    ramanujanRowMap q x = ∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius (q/d) : ℝ) * (d : ℝ) *
        (residueEvent d 0).indicator (fun _ => (1 : ℝ)) x := by
  rw [ramanujanRowMap, Nat.sum_divisorsAntidiagonal'
    (fun a b => ArithmeticFunction.moebius a • resetRowMap b)]
  simp only [ContinuousMap.sum_apply, ← Int.cast_smul_eq_zsmul ℝ,
    ContinuousMap.smul_apply, smul_eq_mul, resetRowMap_apply, mul_sub, mul_one,
    Finset.sum_sub_distrib]
  have hz : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d) : ℝ)) = 0 := by
    rw [Nat.sum_div_divisors q (fun d => (ArithmeticFunction.moebius d : ℝ)),
      ReducedHarmonicMobius.sum_moebius_divisors, if_neg (by omega : q ≠ 1)]
  rw [hz, sub_zero]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem residueMap_inverse (k : ℕ) (x : Phase) : residueMap k 0 x⁻¹ = residueMap k 0 x := by
  by_cases hk : 0 < k
  · letI : NeZero k := ⟨hk.ne'⟩
    have he : (residueHom k x⁻¹).toAdd = -(residueHom k x).toAdd := by
      rw [map_inv]; rfl
    simp only [residueMap, dif_pos hk, ContinuousMap.coe_mk, he, Nat.cast_zero, neg_eq_zero]
  · simp [residueMap, hk]

theorem resetRowMap_inverse (k : ℕ) (x : Phase) : resetRowMap k x⁻¹ = resetRowMap k x := by
  simp only [resetRowMap, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, residueMap_inverse]

theorem centered_inverse {k : ℕ} (hk : 0 < k) (x : Phase) :
    centered k x⁻¹ = -centered k x - resetRowMap k x := by
  classical
  letI : NeZero k := ⟨hk.ne'⟩
  let u := (residueHom k x).toAdd
  have he : (residueHom k x⁻¹).toAdd = -u := by rw [map_inv]; rfl
  have hm : x ∈ residueEvent k 0 ↔ u=0 := by
    simp only [residueEvent, dif_pos hk, Set.mem_setOf_eq, Nat.cast_zero, u]
  rw [centered_eq, centered_eq, he, resetRowMap_apply]
  change ((-u).val : ℝ) - ((k : ℝ)-1)/2 =
    -((u.val : ℝ)-((k : ℝ)-1)/2) -
      ((k : ℝ)*(residueEvent k 0).indicator (fun _ => (1 : ℝ)) x - 1)
  by_cases hu : u=0
  · rw [Set.indicator_of_mem (hm.mpr hu), hu]
    simp only [neg_zero, ZMod.val_zero, Nat.cast_zero]
    ring
  · rw [Set.indicator_of_notMem (fun hx => hu (hm.mp hx)), ZMod.neg_val, if_neg hu,
      Nat.cast_sub (ZMod.val_le u)]
    ring

def inverseL2 : HaarL2 →ₗᵢ[ℝ] HaarL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ Inv.inv (Measure.measurePreserving_inv phaseHaar)

theorem inverseL2_coe (Y : HaarL2) :
    inverseL2 Y =ᵐ[phaseHaar] (fun x => Y x⁻¹) :=
  Lp.coeFn_compMeasurePreserving Y (Measure.measurePreserving_inv phaseHaar)

def inverseMap (f : C(Phase, ℝ)) : C(Phase, ℝ) := f.comp ⟨Inv.inv, continuous_inv⟩

theorem inverse_toLp (f : C(Phase, ℝ)) :
    inverseL2 (ContinuousMap.toLp 2 phaseHaar ℝ f) =
      ContinuousMap.toLp 2 phaseHaar ℝ (inverseMap f) := by
  apply Lp.ext
  have hf := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar f
  have hi := (Measure.measurePreserving_inv phaseHaar).quasiMeasurePreserving.ae hf
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (inverseMap f)
  filter_upwards [inverseL2_coe (ContinuousMap.toLp 2 phaseHaar ℝ f),hi,hr]
    with x hx hix hrx
  exact hx.trans (hix.trans hrx.symm)

theorem inverse_resetRow (k : ℕ) : inverseL2 (resetRow k) = resetRow k := by
  rw [resetRow_toLp, inverse_toLp]
  congr 1
  ext x
  exact resetRowMap_inverse k x

theorem inverse_remainder {k : ℕ} (hk : 0 < k) :
    inverseL2 (remainderVector k) = -remainderVector k - resetRow k := by
  have he : inverseMap (remainderMap k) = -remainderMap k - resetRowMap k := by
    ext x
    exact centered_inverse hk x
  rw [remainderVector, inverse_toLp, he, map_sub, map_neg, ← resetRow_toLp]

theorem inverse_ramanujanRow (q : ℕ) : inverseL2 (ramanujanRow q) = ramanujanRow q := by
  simp only [ramanujanRow, map_sum, map_zsmul, inverse_resetRow]

theorem inverse_primitiveRow {q : ℕ} (hq : 0 < q) :
    inverseL2 (primitiveRow q) = -primitiveRow q - ramanujanRow q := by
  have he : (∑ p ∈ q.divisorsAntidiagonal,
      ArithmeticFunction.moebius p.1 • inverseL2 (remainderVector p.2)) =
      ∑ p ∈ q.divisorsAntidiagonal,
        ArithmeticFunction.moebius p.1 • (-remainderVector p.2 - resetRow p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpq := (Nat.mem_divisorsAntidiagonal.mp hp).1
    rw [inverse_remainder (by nlinarith : 0 < p.2)]
  simp only [primitiveRow, map_sum, map_zsmul]
  rw [he]
  simp only [smul_sub, smul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ramanujanRow]

theorem inverse_carrierRow {q : ℕ} (hq : 0 < q) :
    inverseL2 (carrierRow q) = -carrierRow q := by
  rw [carrierRow, map_add, map_smul, inverse_primitiveRow hq, inverse_ramanujanRow]
  module

theorem carrierRowMap_sawtooth (q : ℕ) (x : Phase) :
    carrierRowMap q x = ∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius (q/d) : ℝ) *
        (if x ∈ residueEvent d 0 then 0 else centered d x - (1/2 : ℝ)) := by
  rw [carrierRowMap, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    primitiveRowMap_formula, ramanujanRowMap, Nat.sum_divisorsAntidiagonal'
      (fun a b => ArithmeticFunction.moebius a • resetRowMap b)]
  simp only [ContinuousMap.sum_apply, ← Int.cast_smul_eq_zsmul ℝ,
    ContinuousMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp := Nat.pos_of_mem_divisors hd
  letI : NeZero d := ⟨hdp.ne'⟩
  rw [resetRowMap_apply]
  by_cases hx : x ∈ residueEvent d 0
  · rw [Set.indicator_of_mem hx, if_pos hx]
    have hr : (residueHom d x).toAdd = 0 := by
      simpa only [residueEvent, dif_pos hdp, Set.mem_setOf_eq, Nat.cast_zero] using hx
    rw [centered_eq, hr, ZMod.val_zero, Nat.cast_zero]
    ring
  · rw [Set.indicator_of_notMem hx, if_neg hx]
    ring

def sawtoothPhase (k : ℕ) (x : Phase) : ℝ :=
  if hk : 0 < k then
    letI : NeZero k := ⟨hk.ne'⟩
    let r := (residueHom k x).toAdd
    if r=0 then 0 else (r.val : ℝ)/(k : ℝ)-(1/2 : ℝ)
  else 0

theorem sawtoothPhase_scaled {k : ℕ} (hk : 0 < k) (x : Phase) :
    (k : ℝ) * sawtoothPhase k x =
      if x ∈ residueEvent k 0 then 0 else centered k x - (1/2 : ℝ) := by
  letI : NeZero k := ⟨hk.ne'⟩
  have hmem : x ∈ residueEvent k 0 ↔ (residueHom k x).toAdd=0 := by
    simp [residueEvent, hk]
  rw [sawtoothPhase, dif_pos hk]
  dsimp only
  rw [if_congr hmem rfl rfl]
  split_ifs with hx
  · simp
  · rw [centered_eq]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
    ring

theorem carrierRowMap_formula (q : ℕ) (x : Phase) :
    carrierRowMap q x = ∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius (q/d) : ℝ) * (d : ℝ) * sawtoothPhase d x := by
  rw [carrierRowMap_sawtooth]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc, sawtoothPhase_scaled (Nat.pos_of_mem_divisors hd)]

theorem centered_sawtooth_endpoint {k : ℕ} (hk : 0 < k) (x : Phase) :
    centered k x = (k : ℝ) * sawtoothPhase k x + (1/2 : ℝ) -
      ((k : ℝ)/2) * (residueEvent k 0).indicator (fun _ => (1 : ℝ)) x := by
  letI : NeZero k := ⟨hk.ne'⟩
  rw [sawtoothPhase_scaled hk]
  by_cases hx : x ∈ residueEvent k 0
  · have hr : (residueHom k x).toAdd = 0 := by
      simpa only [residueEvent, dif_pos hk, Set.mem_setOf_eq, Nat.cast_zero] using hx
    rw [if_pos hx, Set.indicator_of_mem hx, centered_eq, hr, ZMod.val_zero, Nat.cast_zero]
    ring
  · rw [if_neg hx, Set.indicator_of_notMem hx]
    ring

theorem carrierRow_two : carrierRow 2 = 0 := by
  have hj : jordanTwo 2 = 3 := by
    have h := jordanTwo_prime_power_succ Nat.prime_two 0
    norm_num at h
    exact h
  have h := carrierRow_norm_sq (by norm_num : 2 ≤ 2)
  rw [hj] at h
  norm_num at h
  exact h

theorem primitiveRow_two_ne_zero : primitiveRow 2 ≠ 0 := by
  intro hz
  have h := primitiveRow_norm_sq (by norm_num : 2 ≤ 2)
  have hj : jordanTwo 2 = 3 := by
    have h := jordanTwo_prime_power_succ Nat.prime_two 0
    norm_num at h
    exact h
  rw [hz, hj] at h
  norm_num at h

theorem inverseL2_involutive (Y : HaarL2) : inverseL2 (inverseL2 Y) = Y := by
  change Lp.compMeasurePreserving Inv.inv _ (Lp.compMeasurePreserving Inv.inv _ Y) = Y
  rw [← Lp.compMeasurePreserving_comp_apply]
  simp

theorem inverse_as_shift_reflect (Y : HaarL2) :
    inverseL2 Y = shift (-1) (reflectL2 Y) := by
  have he : reflection ∘ CollisionPotentialCoboundary.translate (-1) = (Inv.inv : Phase → Phase) := by
    funext x
    simp [reflection, CollisionPotentialCoboundary.translate, div_eq_mul_inv, mul_inv_rev]
  change Lp.compMeasurePreserving Inv.inv _ Y =
    Lp.compMeasurePreserving (CollisionPotentialCoboundary.translate (-1)) _
      (Lp.compMeasurePreserving reflection _ Y)
  simpa only [he] using Lp.compMeasurePreserving_comp_apply Y
    reflection_measurePreserving (translate_measurePreserving (-1))

theorem collisionPotential_inverse :
    inverseL2 collisionPotential = -shift (-1) collisionPotential := by
  rw [inverse_as_shift_reflect, collisionPotential_reflection, map_neg]

theorem incrementVector_even : inverseL2 incrementVector = incrementVector := by
  have he : incrementVector = collisionPotential + inverseL2 collisionPotential := by
    rw [collisionPotential_inverse]
    simp only [incrementVector, sub_eq_add_neg]
  rw [he, map_add, inverseL2_involutive, add_comm]

def oddPotential : HaarL2 := collisionPotential - (1/2 : ℝ) • incrementVector

theorem collisionPotential_parity_split :
    collisionPotential = oddPotential + (1/2 : ℝ) • incrementVector := by
  simp only [oddPotential, sub_add_cancel]

theorem oddPotential_odd : inverseL2 oddPotential = -oddPotential := by
  rw [oddPotential, map_sub, map_smul, collisionPotential_inverse, incrementVector_even]
  unfold incrementVector
  module

def ramanujanCutoff (M : ℕ) : HaarL2 :=
  (2/3 : ℝ) • ∑ q ∈ Finset.Icc 2 M, amplitude q • ramanujanRow q

def carrierCutoff (M : ℕ) : HaarL2 :=
  (2/3 : ℝ) • ∑ q ∈ Finset.Icc 2 M, amplitude q • carrierRow q

theorem ramanujanCutoff_eq (M : ℕ) :
    ramanujanCutoff M = -weightedRows amplitude M - inverseL2 (weightedRows amplitude M) := by
  simp only [weightedRows, map_smul, map_sum]
  have he : (∑ q ∈ Finset.Icc 2 M, amplitude q • inverseL2 (primitiveRow q)) =
      ∑ q ∈ Finset.Icc 2 M, amplitude q • (-primitiveRow q - ramanujanRow q) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [inverse_primitiveRow (by have := (Finset.mem_Icc.mp hq).1; omega)]
  rw [he]
  simp only [smul_sub, smul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ramanujanCutoff]
  module

theorem carrierCutoff_eq (M : ℕ) :
    carrierCutoff M = weightedRows amplitude M + (1/2 : ℝ) • ramanujanCutoff M := by
  simp only [carrierCutoff, carrierRow, smul_add, Finset.sum_add_distrib,
    weightedRows, ramanujanCutoff]
  congr 1
  simp only [smul_comm (amplitude _) (1/2 : ℝ), ← Finset.smul_sum,
    smul_comm (2/3 : ℝ) (1/2 : ℝ)]

theorem ramanujanCutoff_tendsto : Tendsto ramanujanCutoff atTop (nhds (-incrementVector)) := by
  have ht := conductor_expansion_tendsto.neg.sub
    (inverseL2.continuous.tendsto collisionPotential |>.comp conductor_expansion_tendsto)
  have he : -collisionPotential - inverseL2 collisionPotential = -incrementVector := by
    rw [collisionPotential_inverse]
    unfold incrementVector
    module
  simp only [Function.comp_def, he, ← ramanujanCutoff_eq] at ht
  exact ht

theorem carrierCutoff_tendsto : Tendsto carrierCutoff atTop (nhds oddPotential) := by
  have ht := conductor_expansion_tendsto.add
    (ramanujanCutoff_tendsto.const_smul (1/2 : ℝ))
  simpa only [← carrierCutoff_eq, smul_neg, ← sub_eq_add_neg, oddPotential] using ht

theorem oddPotential_odd_ae :
    (fun x => oddPotential x⁻¹) =ᵐ[phaseHaar] (fun x => -oddPotential x) := by
  have h := inverseL2_coe oddPotential
  rw [oddPotential_odd] at h
  exact h.symm.trans (Lp.coeFn_neg oddPotential)

theorem incrementVector_even_ae :
    (fun x => incrementVector x⁻¹) =ᵐ[phaseHaar] incrementVector := by
  have h := inverseL2_coe incrementVector
  rw [incrementVector_even] at h
  exact h.symm

theorem ramanujanRowMap_residue {q : ℕ} (hq : 2 ≤ q) (x : Phase) :
    letI : NeZero q := ⟨by omega⟩
    ramanujanRowMap q x = CollisionRamanujan.ramanujan q
      ((residueHom q x).toAdd.val : ℤ) := by
  letI : NeZero q := ⟨by omega⟩
  rw [ramanujanRowMap_formula hq, CollisionRamanujan.ramanujan]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp := Nat.pos_of_mem_divisors hd
  letI : NeZero d := ⟨hdp.ne'⟩
  have hm := mem_residueEvent_via (a := 0) (Nat.dvd_of_mem_divisors hd) x
  have he : x ∈ residueEvent d 0 ↔ (d : ℤ) ∣ ((residueHom q x).toAdd.val : ℤ) := by
    rw [hm, Nat.modEq_zero_iff_dvd, Int.natCast_dvd_natCast]
  by_cases hx : x ∈ residueEvent d 0
  · rw [Set.indicator_of_mem hx, if_pos (he.mp hx)]
    ring
  · rw [Set.indicator_of_notMem hx, if_neg (fun h => hx (he.mpr h))]
    simp

theorem ramanujanRowMap_primitiveSum {q : ℕ} (hq : 2 ≤ q) (x : Phase) :
    letI : NeZero q := ⟨by omega⟩
    (ramanujanRowMap q x : ℂ) = CollisionRamanujan.primitiveSum q
      ((residueHom q x).toAdd.val : ℤ) := by
  letI : NeZero q := ⟨by omega⟩
  rw [CollisionRamanujan.primitiveSum_eq_ramanujan, ramanujanRowMap_residue hq]

theorem carrierRows_orthogonal {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : p ≠ q) :
    inner ℝ (carrierRow p) (carrierRow q) = 0 := by
  have hcross : inner ℝ (ramanujanRow p) (primitiveRow q) = 0 := by
    rw [real_inner_comm, primitive_ramanujan_inner (by omega) (by omega),
      ramanujanRow_inner (by omega) hp, if_neg (Ne.symm hpq), mul_zero]
  simp only [carrierRow, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, conj_trivial, hcross,
    primitiveRows_orthogonal hp hq hpq,
    primitive_ramanujan_inner (by omega : 0 < p) (by omega : 0 < q),
    ramanujanRow_inner (by omega : 0 < p) hq, if_neg hpq, mul_zero, add_zero]

/-- The parity and L2 convergence clauses, without a primitive Fourier claim. -/
theorem carrier_parity_decomposition :
    Tendsto (weightedRows amplitude) atTop (nhds collisionPotential) ∧
    Tendsto carrierCutoff atTop (nhds oddPotential) ∧
    Tendsto ramanujanCutoff atTop (nhds (-incrementVector)) ∧
    collisionPotential = oddPotential + (1/2 : ℝ) • incrementVector ∧
    inverseL2 oddPotential = -oddPotential ∧
    inverseL2 incrementVector = incrementVector ∧
    (∀ q : ℕ, 2 ≤ q →
      ‖carrierRow q‖^2 = (jordanTwo q - 3*(Nat.totient q : ℝ))/12 ∧
      ‖primitiveRow q‖^2 = jordanTwo q/12 ∧
      ‖ramanujanRow q‖^2 = (Nat.totient q : ℝ)) ∧
    carrierRow 2 = 0 ∧ primitiveRow 2 ≠ 0 := by
  exact ⟨conductor_expansion_tendsto, carrierCutoff_tendsto,
    ramanujanCutoff_tendsto, collisionPotential_parity_split, oddPotential_odd,
    incrementVector_even, fun q hq => ⟨carrierRow_norm_sq hq, primitiveRow_norm_sq hq,
      ramanujanRow_norm_sq hq⟩, carrierRow_two, primitiveRow_two_ne_zero⟩

end NField.Alignment.CollisionParityRows
