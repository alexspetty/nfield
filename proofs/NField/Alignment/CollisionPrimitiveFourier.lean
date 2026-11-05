/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionParityRows
import NField.Alignment.DedekindFourierMoment

/-!
# Primitive Fourier coefficients of the collision potential

The finite transform is evaluated from the actual conditional means.
Primitive support follows from complete residue blocks and geometric sums.
-/

noncomputable section

set_option autoImplicit false

namespace NField.Alignment.CollisionPrimitiveFourier

open scoped BigOperators Classical
open Filter MeasureTheory
open CollisionRemainderDynamics CollisionCylinderMeans CollisionPotentialHilbert
open CollisionPotentialConvergence CollisionConductorRows CollisionJordanVariance
open ProfiniteRemainderMeasure DedekindFourierMoment CollisionParityRows

theorem negativeRoot_power_iff {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) (d : ℕ) :
    negativeRoot q a ^ d = 1 ↔ q ∣ d := by
  rw [negativeRoot, ← Complex.exp_nat_mul]
  have he : (d : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (q : ℂ))) =
      -(2 * (Real.pi : ℂ) * Complex.I * ((a*d : ℕ) : ℂ) / (q : ℂ)) := by
    push_cast
    ring
  rw [he, Complex.exp_neg, inv_eq_one,
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne', ha.symm.dvd_mul_left]

theorem negativeRoot_primitive_ne_one {q a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q) :
    negativeRoot q a ≠ 1 := by
  have h := negativeRoot_power_iff (by omega : 0 < q) ha 1
  simp only [pow_one] at h
  intro he
  have hd := Nat.le_of_dvd (by omega : 0 < 1) (h.mp he)
  omega

theorem complex_sum_range_product (m d : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range (m*d), f n) =
      ∑ j ∈ Finset.range m, ∑ t ∈ Finset.range d, f (t+d*j) := by
  have h := Equiv.sum_comp (@finProdFinEquiv m d) (fun n => f n.val)
  change (∑ p : Fin m × Fin d, f (p.2.val+d*p.1.val)) = _ at h
  rw [Fintype.sum_prod_type] at h
  calc
    _ = ∑ n : Fin (m*d), f n.val := (Fin.sum_univ_eq_sum_range f _).symm
    _ = ∑ j : Fin m, ∑ t : Fin d, f (t.val+d*j.val) := h.symm
    _ = ∑ j : Fin m, ∑ t ∈ Finset.range d, f (t+d*j.val) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Fin.sum_univ_eq_sum_range (fun t => f (t+d*j.val)) d
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun j => ∑ t ∈ Finset.range d, f (t+d*j)) m

theorem periodic_transform_factor {q d : ℕ} (hdq : d ∣ q) (f : ℕ → ℂ) (z : ℂ) :
    (∑ n ∈ Finset.range q, f (n%d) * z^n) =
      (∑ t ∈ Finset.range d, f t * z^t) *
        (∑ j ∈ Finset.range (q/d), (z^d)^j) := by
  have hfac := Nat.div_mul_cancel hdq
  calc
    _ = ∑ n ∈ Finset.range ((q/d)*d), f (n%d)*z^n := by rw [hfac]
    _ = ∑ t ∈ Finset.range d, ∑ j ∈ Finset.range (q/d),
        f ((t+d*j)%d)*z^(t+d*j) := by
      rw [complex_sum_range_product, Finset.sum_comm]
    _ = ∑ t ∈ Finset.range d, (f t*z^t) * ∑ j ∈ Finset.range (q/d), (z^d)^j := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp ht),
        pow_add, pow_mul]
      ring
    _ = _ := by rw [Finset.sum_mul]

theorem primitive_periodic_transform_zero {q d a : ℕ} (hq : 2 ≤ q)
    (ha : a.Coprime q) (hdq : d ∣ q) (hd : d < q) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range q, f (n%d) * negativeRoot q a ^ n) = 0 := by
  rw [periodic_transform_factor hdq]
  have hz : negativeRoot q a ^ d ≠ 1 := by
    intro h
    have hqd := (negativeRoot_power_iff (by omega : 0 < q) ha d).mp h
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq (by omega)
    have hle := Nat.le_of_dvd hd0 hqd
    omega
  have hp : (negativeRoot q a ^ d)^(q/d) = 1 := by
    rw [← pow_mul, Nat.mul_div_cancel' hdq]
    exact negativeRoot_pow_modulus (by omega)
  have hs : (∑ j ∈ Finset.range (q/d), (negativeRoot q a ^ d)^j) = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hz.symm)
    rw [mul_zero, mul_neg_geom_sum, hp, sub_self]
  rw [hs, mul_zero]

theorem centered_transform_own {q a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q) :
    (∑ n ∈ Finset.range q, (centeredRemainder q n : ℂ) * negativeRoot q a ^ n) =
      -(q : ℂ)/(1-negativeRoot q a) := by
  let z := negativeRoot q a
  have hz : z ≠ 1 := negativeRoot_primitive_ne_one hq ha
  have hp : z^q=1 := negativeRoot_pow_modulus (by omega)
  have hs : (∑ n ∈ Finset.range q, z^n) = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hz.symm)
    rw [mul_zero, mul_neg_geom_sum, hp, sub_self]
  have hpt (n : ℕ) (hn : n ∈ Finset.range q) :
      (centeredRemainder q n : ℂ)*z^n =
        (n : ℂ)*z^n - (((q : ℂ)-1)/2)*z^n := by
    rw [centeredRemainder, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
    push_cast
    ring
  change (∑ n ∈ Finset.range q, (centeredRemainder q n : ℂ)*z^n) = _
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero, sub_zero]
  apply (eq_div_iff (sub_ne_zero.mpr hz.symm)).mpr
  simpa only [mul_comm] using weighted_geometric_sum hp hz

theorem centered_primitive_transform {q d a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q)
    (hdq : d ∣ q) :
    (∑ n ∈ Finset.range q, (centeredRemainder d n : ℂ) * negativeRoot q a ^ n)/(q : ℂ) =
      if d=q then -1/(1-negativeRoot q a) else 0 := by
  by_cases hd : d=q
  · subst d
    rw [if_pos rfl, centered_transform_own hq ha]
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    field_simp
  · rw [if_neg hd]
    have hzero := primitive_periodic_transform_zero hq ha hdq
      (lt_of_le_of_ne (Nat.le_of_dvd (by omega : 0 < q) hdq) hd)
      (fun j => ((j : ℂ)-((d : ℂ)-1)/2))
    have he (j : ℕ) : (centeredRemainder d j : ℂ) =
        ((j%d : ℕ) : ℂ)-((d : ℂ)-1)/2 := by
      unfold centeredRemainder
      push_cast
      rfl
    simp only [he]
    rw [hzero, zero_div]

def fourierFunctional (q a : ℕ) : HaarL2 →L[ℝ] ℂ :=
  (1/(q : ℂ)) • ∑ j ∈ Finset.range q,
    negativeRoot q a ^ j • (Complex.ofRealCLM.comp (cylinderFunctional q j))

theorem fourierFunctional_apply (q a : ℕ) (Y : HaarL2) :
    fourierFunctional q a Y =
      (∑ j ∈ Finset.range q, (cylinderFunctional q j Y : ℂ) * negativeRoot q a ^ j)/(q : ℂ) := by
  simp only [fourierFunctional, _root_.smul_apply,
    _root_.sum_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  simp only [div_eq_mul_inv, one_mul]
  rw [mul_comm ((q : ℂ)⁻¹)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem remainderVector_fourier {k q a : ℕ} (hk : 0 < k) (hq : 2 ≤ q) (ha : a.Coprime q) :
    fourierFunctional q a (remainderVector k) =
      if q ∣ k then -1/(1-negativeRoot q a) else 0 := by
  rw [fourierFunctional_apply]
  simp_rw [cylinderFunctional_remainder hk (by omega : 0 < q)]
  rw [centered_primitive_transform hq ha (Nat.gcd_dvd_right k q)]
  simp only [Nat.gcd_eq_right_iff_dvd]

theorem primitiveRow_fourier {p q a : ℕ} (hp : 0 < p) (hq : 2 ≤ q) (ha : a.Coprime q) :
    fourierFunctional q a (primitiveRow p) =
      if p=q then -1/(1-negativeRoot q a) else 0 := by
  let f : ℕ → ℂ := fun m => if m=q then -1/(1-negativeRoot q a) else 0
  have hf : ∀ m > 0, (∑ d ∈ m.divisors, f d) = fourierFunctional q a (remainderVector m) := by
    intro m hm
    rw [remainderVector_fourier hm hq ha]
    simp only [f, Finset.sum_ite_eq']
    by_cases hqm : q ∣ m
    · rw [if_pos (Nat.mem_divisors.mpr ⟨hqm,hm.ne'⟩), if_pos hqm]
    · rw [if_neg (fun h => hqm (Nat.mem_divisors.mp h).1), if_neg hqm]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := f) (g := fun m => fourierFunctional q a (remainderVector m))).mp hf p hp
  simpa only [primitiveRow, map_sum, map_zsmul, f] using hi

theorem primitiveRow_fourier_support {p q a : ℕ} (hp : 0 < p) (hq : 2 ≤ q)
    (ha : a.Coprime q) : fourierFunctional q a (primitiveRow p) ≠ 0 ↔ p=q := by
  rw [primitiveRow_fourier hp hq ha]
  by_cases hpq : p=q
  · rw [if_pos hpq]
    exact iff_of_true (div_ne_zero (by norm_num)
      (sub_ne_zero.mpr (negativeRoot_primitive_ne_one hq ha).symm)) hpq
  · simp [hpq]

theorem finitePotential_fourier {q a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q)
    (v : ℕ → ℝ) (M : ℕ) :
    fourierFunctional q a (finitePotential v M) =
      (2/3 : ℂ)*(finiteAmplitude v q M : ℂ)*(-1/(1-negativeRoot q a)) := by
  simp only [finitePotential, map_smul, map_sum, Complex.real_smul]
  have he : (∑ k ∈ Finset.Icc 2 M, (v k : ℂ)*fourierFunctional q a (remainderVector k)) =
      (finiteAmplitude v q M : ℂ)*(-1/(1-negativeRoot q a)) := by
    rw [finiteAmplitude, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [remainderVector_fourier (by have := (Finset.mem_Icc.mp hk).1; omega) hq ha]
    split_ifs <;> simp
  rw [he]
  push_cast
  ring

theorem collisionPotential_fourier {q a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q) :
    fourierFunctional q a collisionPotential =
      -2*(amplitude q : ℂ)/(3*(1-negativeRoot q a)) := by
  have ht := (fourierFunctional q a).continuous.tendsto collisionPotential |>.comp
    tendsto_collisionPotential
  simp only [Function.comp_def, finitePotential_fourier hq ha] at ht
  have hs : Tendsto (fun M => (2/3 : ℂ)*(finiteAmplitude CollisionRemainderDynamics.collisionWeight q M : ℂ)*
      (-1/(1-negativeRoot q a))) atTop
      (nhds ((2/3 : ℂ)*(amplitude q : ℂ)*(-1/(1-negativeRoot q a)))) :=
    ((Complex.continuous_ofReal.tendsto _ |>.comp (finiteAmplitude_tendsto q)).const_mul _).mul_const _
  have he := tendsto_nhds_unique ht hs
  rw [he]
  have hz : 1-negativeRoot q a ≠ 0 := sub_ne_zero.mpr (negativeRoot_primitive_ne_one hq ha).symm
  field_simp

theorem cylinderFunctional_resetRow {k q : ℕ} (hk : 0 < k) (hq : 0 < q) (j : ℕ) :
    cylinderFunctional q j (resetRow k) =
      (if k.gcd q ∣ j then (k.gcd q : ℝ) else 0)-1 := by
  open CollisionDivisibilityCovariance in
  have hpair := residueVector_pair_inner hq hk j 0
  have hmean : inner ℝ (residueVector q j) oneVector = 1/(q : ℝ) := by
    rw [real_inner_comm, residueVector_mean hq]
  rw [cylinderFunctional_apply, resetRow, inner_sub_right, inner_smul_right, hpair, hmean]
  simp only [Nat.modEq_zero_iff_dvd, Nat.gcd_comm q k, Nat.lcm_comm q k]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hL0 : (k.lcm q : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hk hq).ne'
  have hprod : (k.gcd q : ℝ)*(k.lcm q : ℝ)=(k : ℝ)*(q : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm k q
  split_ifs
  · field_simp
    nlinarith
  · field_simp
    ring

theorem resetProfile_transform {q d a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q) (hdq : d ∣ q) :
    (∑ n ∈ Finset.range q,
      (((if d ∣ n then (d : ℝ) else 0)-1 : ℝ) : ℂ)*negativeRoot q a^n)/(q : ℂ) =
        if d=q then 1 else 0 := by
  by_cases hd : d=q
  · subst d
    rw [if_pos rfl]
    have hz : negativeRoot q a ≠ 1 := negativeRoot_primitive_ne_one hq ha
    have hp : negativeRoot q a ^ q = 1 := negativeRoot_pow_modulus (by omega)
    have hs : (∑ n ∈ Finset.range q, negativeRoot q a^n) = 0 := by
      apply mul_left_cancel₀ (sub_ne_zero.mpr hz.symm)
      rw [mul_zero, mul_neg_geom_sum, hp, sub_self]
    have he (n : ℕ) (hn : n ∈ Finset.range q) :
        (((if q ∣ n then (q : ℝ) else 0)-1 : ℝ) : ℂ)*negativeRoot q a^n =
        (if n=0 then (q : ℂ) else 0) - negativeRoot q a^n := by
      have hd : q ∣ n ↔ n=0 := by
        constructor
        · intro h
          by_contra h0
          have hl := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h
          have hnq := Finset.mem_range.mp hn
          omega
        · intro h; simp [h]
      simp only [hd]
      split_ifs with h0
      · subst n
        simp
      · simp
    rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, hs, sub_zero]
    simp [show 0 < q by omega, show (q : ℂ) ≠ 0 by exact_mod_cast (by omega : q ≠ 0)]
  · rw [if_neg hd]
    have hf : ∀ n : ℕ, (((if d ∣ n then (d : ℝ) else 0)-1 : ℝ) : ℂ) =
        (if n%d=0 then (d : ℂ) else 0)-1 := by
      intro n
      simp only [Nat.dvd_iff_mod_eq_zero]
      split_ifs <;> push_cast <;> rfl
    simp only [hf]
    rw [primitive_periodic_transform_zero hq ha hdq
      (lt_of_le_of_ne (Nat.le_of_dvd (by omega : 0 < q) hdq) hd)
      (fun n => (if n=0 then (d : ℂ) else 0)-1), zero_div]

theorem resetRow_fourier {k q a : ℕ} (hk : 0 < k) (hq : 2 ≤ q) (ha : a.Coprime q) :
    fourierFunctional q a (resetRow k) = if q ∣ k then 1 else 0 := by
  rw [fourierFunctional_apply]
  simp_rw [cylinderFunctional_resetRow hk (by omega : 0 < q)]
  rw [resetProfile_transform hq ha (Nat.gcd_dvd_right k q)]
  simp only [Nat.gcd_eq_right_iff_dvd]

theorem ramanujanRow_fourier {p q a : ℕ} (hp : 0 < p) (hq : 2 ≤ q) (ha : a.Coprime q) :
    fourierFunctional q a (ramanujanRow p) = if p=q then 1 else 0 := by
  let f : ℕ → ℂ := fun m => if m=q then 1 else 0
  have hf : ∀ m > 0, (∑ d ∈ m.divisors, f d) = fourierFunctional q a (resetRow m) := by
    intro m hm
    rw [resetRow_fourier hm hq ha]
    simp only [f, Finset.sum_ite_eq']
    by_cases hqm : q ∣ m
    · rw [if_pos (Nat.mem_divisors.mpr ⟨hqm,hm.ne'⟩), if_pos hqm]
    · rw [if_neg (fun h => hqm (Nat.mem_divisors.mp h).1), if_neg hqm]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := f) (g := fun m => fourierFunctional q a (resetRow m))).mp hf p hp
  simpa only [ramanujanRow, map_sum, map_zsmul, f] using hi

theorem ramanujanCutoff_fourier {q a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q) {M : ℕ} (hM : q ≤ M) :
    fourierFunctional q a (ramanujanCutoff M) = (2/3 : ℂ)*(amplitude q : ℂ) := by
  simp only [ramanujanCutoff, map_smul, map_sum, Complex.real_smul]
  have he : (∑ p ∈ Finset.Icc 2 M, (amplitude p : ℂ)*fourierFunctional q a (ramanujanRow p)) =
      (amplitude q : ℂ) := by
    have hp (p : ℕ) (hp : p ∈ Finset.Icc 2 M) :
        (amplitude p : ℂ)*fourierFunctional q a (ramanujanRow p) =
          if p=q then (amplitude q : ℂ) else 0 := by
      rw [ramanujanRow_fourier (by have := (Finset.mem_Icc.mp hp).1; omega) hq ha]
      split_ifs with h
      · simp [h]
      · simp
    rw [Finset.sum_congr rfl hp]
    simp [hq, hM]
  rw [he]
  push_cast
  rfl

theorem incrementVector_fourier {q a : ℕ} (hq : 2 ≤ q) (ha : a.Coprime q) :
    fourierFunctional q a CollisionPotentialCoboundary.incrementVector =
      -(2/3 : ℂ)*(amplitude q : ℂ) := by
  have ht := (fourierFunctional q a).continuous.tendsto
    (-CollisionPotentialCoboundary.incrementVector) |>.comp ramanujanCutoff_tendsto
  have he : (fun M => fourierFunctional q a (ramanujanCutoff M)) =ᶠ[atTop]
      (fun _ => (2/3 : ℂ)*(amplitude q : ℂ)) := by
    filter_upwards [eventually_ge_atTop q] with M hM
    exact ramanujanCutoff_fourier hq ha hM
  have hs : Tendsto (fun M => fourierFunctional q a (ramanujanCutoff M)) atTop
      (nhds ((2/3 : ℂ)*(amplitude q : ℂ))) := tendsto_const_nhds.congr' he.symm
  have h := tendsto_nhds_unique ht hs
  rw [map_neg] at h
  linear_combination -h

theorem fourierFunctional_integral {q : ℕ} (hq : 0 < q) (a : ℕ) (Y : HaarL2) :
    letI : NeZero q := ⟨hq.ne'⟩
    fourierFunctional q a Y = ∫ x, (Y x : ℂ) *
      negativeRoot q a ^ (residueHom q x).toAdd.val ∂phaseHaar := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hY : Integrable (fun x => (Y x : ℂ)) phaseHaar :=
    Complex.ofRealCLM.integrable_comp (MemLp.integrable (by norm_num) (Lp.memLp Y))
  have hint (j : ℕ) : Integrable
      ((CollisionDivisibilityCovariance.residueEvent q j).indicator
        (fun x => (Y x : ℂ)*negativeRoot q a^j)) phaseHaar :=
    (hY.mul_const _).indicator (CollisionDivisibilityCovariance.residueEvent_measurable q j)
  have hpoint (x : Phase) :
      (∑ j ∈ Finset.range q, (CollisionDivisibilityCovariance.residueEvent q j).indicator
        (fun x => (Y x : ℂ)*negativeRoot q a^j) x) =
        (Y x : ℂ)*negativeRoot q a^(residueHom q x).toAdd.val := by
    have he (j : ℕ) (hj : j ∈ Finset.range q) :
        (CollisionDivisibilityCovariance.residueEvent q j).indicator
          (fun x => (Y x : ℂ)*negativeRoot q a^j) x =
        if j=(residueHom q x).toAdd.val then (Y x : ℂ)*negativeRoot q a^j else 0 := by
      have hm := CollisionDivisibilityCovariance.mem_residueEvent_via (a := j) (dvd_refl q) x
      have heq : x ∈ CollisionDivisibilityCovariance.residueEvent q j ↔
          j=(residueHom q x).toAdd.val := by
        rw [hm]
        simp only [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt _),
          Nat.mod_eq_of_lt (Finset.mem_range.mp hj), eq_comm]
      by_cases h : x ∈ CollisionDivisibilityCovariance.residueEvent q j
      · rw [Set.indicator_of_mem h, if_pos (heq.mp h)]
      · rw [Set.indicator_of_notMem h, if_neg (fun h' => h (heq.mpr h'))]
    rw [Finset.sum_congr rfl he]
    simp [ZMod.val_lt]
  have hc (j : ℕ) : (cylinderFunctional q j Y : ℂ) =
      (q : ℂ) * ∫ x in CollisionDivisibilityCovariance.residueEvent q j, (Y x : ℂ) ∂phaseHaar := by
    rw [cylinderFunctional_integral]
    push_cast
    congr 1
    exact (integral_ofReal (f := fun x => Y x)).symm
  rw [fourierFunctional_apply]
  calc
    _ = ∑ j ∈ Finset.range q,
        (∫ x in CollisionDivisibilityCovariance.residueEvent q j, (Y x : ℂ) ∂phaseHaar) *
          negativeRoot q a^j := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc]
      have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp
    _ = ∫ x, ∑ j ∈ Finset.range q,
        (CollisionDivisibilityCovariance.residueEvent q j).indicator
          (fun x => (Y x : ℂ)*negativeRoot q a^j) x ∂phaseHaar := by
      rw [integral_finsetSum (Finset.range q) (fun j _ => hint j)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_indicator (CollisionDivisibilityCovariance.residueEvent_measurable q j),
        integral_mul_const]
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hpoint)

theorem primitiveRow_mean_zero {p : ℕ} (hp : 0 < p) :
    inner ℝ oneVector (primitiveRow p) = 0 := by
  simp only [primitiveRow, inner_sum, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right]
  apply Finset.sum_eq_zero
  intro d hd
  have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have hdp : 0 < d.2 := by nlinarith
  rw [remainder_mean_inner hdp, mul_zero]

/-- All stated primitive-frequency and parity clauses for the Haar observable. -/
theorem spectrum_and_parity :
    (∀ (p q a : ℕ), 0 < p → 2 ≤ q → a.Coprime q →
      fourierFunctional q a (primitiveRow p) =
        (if p=q then -1/(1-negativeRoot q a) else 0)) ∧
    (∀ (q a : ℕ), 2 ≤ q → a.Coprime q →
      fourierFunctional q a collisionPotential = -2*(amplitude q : ℂ)/(3*(1-negativeRoot q a)) ∧
      fourierFunctional q a CollisionPotentialCoboundary.incrementVector = -(2/3 : ℂ)*(amplitude q : ℂ)) ∧
    Tendsto (weightedRows amplitude) atTop (nhds collisionPotential) ∧
    Tendsto carrierCutoff atTop (nhds oddPotential) ∧
    collisionPotential = oddPotential + (1/2 : ℝ) • CollisionPotentialCoboundary.incrementVector ∧
    inverseL2 oddPotential = -oddPotential ∧
    inverseL2 CollisionPotentialCoboundary.incrementVector = CollisionPotentialCoboundary.incrementVector ∧
    (∀ q : ℕ, 2 ≤ q →
      ‖carrierRow q‖^2 = (jordanTwo q - 3*(Nat.totient q : ℝ))/12 ∧
      ‖primitiveRow q‖^2 = jordanTwo q/12) ∧
    carrierRow 2 = 0 ∧ primitiveRow 2 ≠ 0 := by
  exact ⟨fun p q a hp hq ha => primitiveRow_fourier hp hq ha,
    fun q a hq ha => ⟨collisionPotential_fourier hq ha, incrementVector_fourier hq ha⟩,
    conductor_expansion_tendsto, carrierCutoff_tendsto, collisionPotential_parity_split,
    oddPotential_odd, incrementVector_even,
    fun q hq => ⟨carrierRow_norm_sq hq, primitiveRow_norm_sq hq⟩,
    carrierRow_two, primitiveRow_two_ne_zero⟩

end NField.Alignment.CollisionPrimitiveFourier
