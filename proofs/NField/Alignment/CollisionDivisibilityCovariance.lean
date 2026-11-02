/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionOdometerRecurrence

/-!
# Exact Haar probabilities for pairs of divisibility events

The finite count uses the generalized Chinese remainder theorem, including
incompatible noncoprime moduli. Uniform profinite quotient measure then
gives the shifted joint probability used by the increment covariance.
-/

noncomputable section

namespace NField.Alignment.CollisionDivisibilityCovariance

open scoped BigOperators
open MeasureTheory Filter
open ProfiniteRemainderMeasure CollisionResetIntegrability CollisionPotentialCoboundary
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionRemainderDynamics
open CollisionMassReadout

theorem residue_pair_count {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (a b : ℕ) :
    (∑ n ∈ Finset.range (k.lcm l), if Nat.ModEq k n a ∧ Nat.ModEq l n b then (1 : ℝ) else 0) =
      if Nat.ModEq (k.gcd l) a b then 1 else 0 := by
  classical
  by_cases hab : Nat.ModEq (k.gcd l) a b
  · let c := Nat.chineseRemainder' hab
    have hc : c.val < k.lcm l := Nat.chineseRemainder'_lt_lcm hab hk.ne' hl.ne'
    have he (n : ℕ) (hn : n ∈ Finset.range (k.lcm l)) :
        (Nat.ModEq k n a ∧ Nat.ModEq l n b) ↔ n = c.val := by
      constructor
      · rintro ⟨hna, hnb⟩
        exact (Nat.mod_lcm (hna.trans c.property.1.symm) (hnb.trans c.property.2.symm)).eq_of_lt_of_lt
          (Finset.mem_range.mp hn) hc
      · intro hnc
        rw [hnc]
        exact c.property
    rw [if_pos hab]
    calc
      _ = ∑ n ∈ Finset.range (k.lcm l), if n = c.val then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl (fun n hn => if_congr (he n hn) rfl rfl)
      _ = 1 := by simp [hc]
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro n _
    apply if_neg
    rintro ⟨hna, hnb⟩
    exact hab ((hna.of_dvd (Nat.gcd_dvd_left k l)).symm.trans
      (hnb.of_dvd (Nat.gcd_dvd_right k l)))

def residueEvent (k a : ℕ) : Set Phase :=
  if hk : 0 < k then
    letI : NeZero k := ⟨hk.ne'⟩
    {x | (residueHom k x).toAdd = (a : ZMod k)}
  else ∅

theorem residueEvent_measurable (k a : ℕ) : MeasurableSet (residueEvent k a) := by
  unfold residueEvent
  split_ifs with hk
  · letI : NeZero k := ⟨hk.ne'⟩
    exact (isClosed_eq ((continuous_of_discreteTopology).comp
      (residueHom k).continuous_toFun) continuous_const).measurableSet
  · exact MeasurableSet.empty

theorem mem_residueEvent_via {k m a : ℕ} [NeZero k] [NeZero m]
    (hkm : k ∣ m) (x : Phase) :
    x ∈ residueEvent k a ↔ Nat.ModEq k (residueHom m x).toAdd.val a := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  simp only [residueEvent, dif_pos hk, Set.mem_setOf_eq, residue_compatible hkm,
    ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]

theorem residueEvent_pair_integral {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (a b : ℕ) :
    (∫ x, (residueEvent k a).indicator (fun _ => (1 : ℝ)) x *
      (residueEvent l b).indicator (fun _ => (1 : ℝ)) x ∂phaseHaar) =
      if Nat.ModEq (k.gcd l) a b then 1/(k.lcm l : ℝ) else 0 := by
  classical
  letI : NeZero k := ⟨hk.ne'⟩
  letI : NeZero l := ⟨hl.ne'⟩
  letI : NeZero (k.lcm l) := ⟨(Nat.lcm_pos hk hl).ne'⟩
  have he (x : Phase) : (residueEvent k a).indicator (fun _ => (1 : ℝ)) x *
      (residueEvent l b).indicator (fun _ => (1 : ℝ)) x =
        if Nat.ModEq k (residueHom (k.lcm l) x).toAdd.val a ∧
          Nat.ModEq l (residueHom (k.lcm l) x).toAdd.val b then 1 else 0 := by
    have hka := mem_residueEvent_via (a := a) (Nat.dvd_lcm_left k l) x
    have hlb := mem_residueEvent_via (a := b) (Nat.dvd_lcm_right k l) x
    by_cases h1 : x ∈ residueEvent k a
    · by_cases h2 : x ∈ residueEvent l b
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          if_pos ⟨hka.mp h1, hlb.mp h2⟩]
        norm_num
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
          if_neg (fun hh => h2 (hlb.mpr hh.2))]
        norm_num
    · by_cases h2 : x ∈ residueEvent l b
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
          if_neg (fun hh => h1 (hka.mpr hh.1))]
        norm_num
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
          if_neg (fun hh => h1 (hka.mpr hh.1))]
        norm_num
  simp_rw [he]
  rw [integral_residue (k.lcm l)
    (fun n => if Nat.ModEq k n a ∧ Nat.ModEq l n b then (1 : ℝ) else 0),
    residue_pair_count hk hl]
  split_ifs <;> simp

theorem resetEvent_eq (k : ℕ) : resetSet k = residueEvent k 0 := by
  unfold resetSet residueEvent
  split_ifs <;> simp

theorem reset_shift_event {l : ℕ} (hl : 0 < l) (h : ℕ) (x : Phase) :
    CollisionPotentialCoboundary.translate (-(h : ℤ)) x ∈ resetSet l ↔ x ∈ residueEvent l h := by
  letI : NeZero l := ⟨hl.ne'⟩
  simp only [resetSet, residueEvent, dif_pos hl, Set.mem_setOf_eq, residue_translate]
  push_cast
  rw [neg_add_eq_zero]
  exact eq_comm

theorem reset_pair_integral {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (h : ℕ) :
    (∫ x, (resetSet k).indicator (fun _ => (1 : ℝ)) x *
      (resetSet l).indicator (fun _ => (1 : ℝ))
        (CollisionPotentialCoboundary.translate (-(h : ℤ)) x) ∂phaseHaar) =
      if k.gcd l ∣ h then 1/(k.lcm l : ℝ) else 0 := by
  classical
  have he (x : Phase) : (resetSet k).indicator (fun _ => (1 : ℝ)) x *
      (resetSet l).indicator (fun _ => (1 : ℝ))
        (CollisionPotentialCoboundary.translate (-(h : ℤ)) x) =
      (residueEvent k 0).indicator (fun _ => (1 : ℝ)) x *
        (residueEvent l h).indicator (fun _ => (1 : ℝ)) x := by
    rw [resetEvent_eq k]
    have hp := reset_shift_event hl h x
    by_cases hh : x ∈ residueEvent l h
    · rw [Set.indicator_of_mem (hp.mpr hh), Set.indicator_of_mem hh]
    · rw [Set.indicator_of_notMem (fun hx => hh (hp.mp hx)), Set.indicator_of_notMem hh]
  simp_rw [he]
  rw [residueEvent_pair_integral hk hl]
  have hi : Nat.ModEq (k.gcd l) 0 h ↔ k.gcd l ∣ h := by
    exact ⟨fun h0 => Nat.modEq_zero_iff_dvd.mp h0.symm,
      fun hd => (Nat.modEq_zero_iff_dvd.mpr hd).symm⟩
  simp only [hi]

theorem resetTerm_indicator (k : ℕ) (x : Phase) :
    resetTerm k x = ((k : ℝ)*collisionWeight k) *
      (resetSet k).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ resetSet k <;> simp [resetTerm, hx]

theorem resetVector_pair_inner {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (h : ℕ) :
    inner ℝ (resetVector 2 k) (shift (-(h : ℤ)) (resetVector 2 l)) =
      ((k : ℝ)*collisionWeight k)*((l : ℝ)*collisionWeight l)*
        (if k.gcd l ∣ h then 1/(k.lcm l : ℝ) else 0) := by
  have ht := (translate_measurePreserving (-(h : ℤ))).quasiMeasurePreserving.ae
    (p := fun x => resetVector 2 l x = resetTerm l x) (resetVector_coe 2 l)
  calc
    _ = ((k : ℝ)*collisionWeight k)*((l : ℝ)*collisionWeight l)*
        (∫ x, (resetSet k).indicator (fun _ => (1 : ℝ)) x *
          (resetSet l).indicator (fun _ => (1 : ℝ))
            (CollisionPotentialCoboundary.translate (-(h : ℤ)) x) ∂phaseHaar) := by
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [resetVector_coe 2 k, shift_coe (-(h : ℤ)) (resetVector 2 l), ht]
        with x hkx hs hlt
      simp only [RCLike.inner_apply, conj_trivial]
      rw [hkx, hs, hlt, resetTerm_indicator, resetTerm_indicator]
      ring
    _ = _ := by rw [reset_pair_integral hk hl]

theorem shift_oneVector (z : ℤ) : shift z oneVector = oneVector := by
  apply Lp.ext
  have ho := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase, ℝ))
  have ht := (translate_measurePreserving z).quasiMeasurePreserving.ae
    (p := fun x => oneVector x = 1) ho
  filter_upwards [shift_coe z oneVector, ho, ht] with x hs hx htx
  exact hs.trans (htx.trans hx.symm)

theorem oneVector_inner_self : inner ℝ oneVector oneVector = 1 := by
  rw [mean_inner_eq_integral]
  have he : (∫ x, oneVector x ∂phaseHaar) = ∫ _x : Phase, (1 : ℝ) ∂phaseHaar :=
    integral_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase, ℝ)))
  rw [he, integral_const, probReal_univ, one_smul]

theorem resetVector_mean_inner (k : ℕ) : inner ℝ oneVector (resetVector 2 k) = collisionWeight k := by
  rw [mean_inner_eq_integral, integral_congr_ae (resetVector_coe 2 k), integral_resetTerm]

theorem shifted_resetVector_mean_inner (k : ℕ) (z : ℤ) :
    inner ℝ oneVector (shift z (resetVector 2 k)) = collisionWeight k := by
  rw [← shift_oneVector z, (shift z).inner_map_map, resetVector_mean_inner]

def centeredResetVector (k : ℕ) : HaarL2 := collisionWeight k • oneVector - resetVector 2 k

theorem centeredReset_pair_inner {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (h : ℕ) :
    inner ℝ (centeredResetVector k) (shift (-(h : ℤ)) (centeredResetVector l)) =
      ((k : ℝ)*collisionWeight k)*((l : ℝ)*collisionWeight l)*
        ((if k.gcd l ∣ h then 1/(k.lcm l : ℝ) else 0) - 1/((k : ℝ)*(l : ℝ))) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hsym : inner ℝ (resetVector 2 k) oneVector = collisionWeight k := by
    rw [real_inner_comm, resetVector_mean_inner]
  simp only [centeredResetVector, map_sub, map_smul, shift_oneVector,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_trivial,
    oneVector_inner_self, hsym, shifted_resetVector_mean_inner,
    resetVector_pair_inner hk hl h]
  field_simp
  ring

@[simp] theorem centeredResetVector_zero : centeredResetVector 0 = 0 := by
  simp [centeredResetVector]

@[simp] theorem centeredResetVector_one : centeredResetVector 1 = 0 := by
  simp [centeredResetVector]

theorem centeredReset_norm_summable : Summable (fun k => ‖centeredResetVector k‖) := by
  have hs := (collisionWeight_summable.mul_right ‖oneVector‖).add
    (resetVector_norm_summable 2 (by norm_num) (by norm_num))
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hs
  intro k
  have h := norm_sub_le (collisionWeight k • oneVector) (resetVector 2 k)
  simpa only [centeredResetVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (collisionWeight_nonneg k)] using h

theorem centeredReset_summable : Summable centeredResetVector := centeredReset_norm_summable.of_norm

theorem centeredReset_tsum :
    (∑' k, centeredResetVector k) = oneVector - ∑' k, resetVector 2 k := by
  have hw := collisionWeight_summable.smul_const oneVector
  have hr := (resetVector_norm_summable 2 (by norm_num) (by norm_num)).of_norm
  unfold centeredResetVector
  rw [hw.tsum_sub hr, collisionWeight_summable.tsum_smul_const, collisionWeight_tsum, one_smul]

theorem incrementVector_centeredReset :
    CollisionPotentialCoboundary.incrementVector = (2/3 : ℝ) • ∑' k, centeredResetVector k := by
  rw [centeredReset_tsum]
  exact collisionPotential_coboundary

def divisorCovarianceTerm (z : ℤ) (kl : ℕ × ℕ) : ℝ :=
  inner ℝ (centeredResetVector kl.1) (shift z (centeredResetVector kl.2))

theorem divisorCovarianceTerm_summable (z : ℤ) : Summable (divisorCovarianceTerm z) := by
  have hp : Summable (fun kl : ℕ × ℕ => ‖centeredResetVector kl.1‖ * ‖centeredResetVector kl.2‖) :=
    centeredReset_norm_summable.mul_of_nonneg centeredReset_norm_summable
      (fun k => norm_nonneg _) (fun k => norm_nonneg _)
  apply Summable.of_norm_bounded hp
  intro kl
  have h := norm_inner_le_norm (𝕜 := ℝ) (centeredResetVector kl.1)
    (shift z (centeredResetVector kl.2))
  simpa only [divisorCovarianceTerm, (shift z).norm_map] using h

theorem divisorCovarianceTerm_tsum (z : ℤ) :
    (∑' k, ∑' l, divisorCovarianceTerm z (k,l)) =
      inner ℝ (∑' k, centeredResetVector k) (shift z (∑' k, centeredResetVector k)) := by
  have hsh := centeredReset_summable.hasSum.mapL (shift z).toContinuousLinearMap
  have hcol (k : ℕ) : (∑' l, divisorCovarianceTerm z (k,l)) =
      inner ℝ (centeredResetVector k) (shift z (∑' l, centeredResetVector l)) :=
    (hsh.mapL (innerSL ℝ (centeredResetVector k))).tsum_eq
  simp_rw [hcol]
  exact (centeredReset_summable.hasSum.mapL
    (innerSLFlip ℝ (shift z (∑' l, centeredResetVector l)))).tsum_eq

theorem incrementCovariance_series (z : ℤ) :
    CollisionOdometerRecurrence.incrementCovariance z =
      (4/9 : ℝ) * ∑' k, ∑' l, divisorCovarianceTerm z (k,l) := by
  rw [CollisionOdometerRecurrence.incrementCovariance, incrementVector_centeredReset,
    map_smul, inner_smul_left, inner_smul_right, conj_trivial, divisorCovarianceTerm_tsum]
  ring

theorem incrementCovariance_even (z : ℤ) :
    CollisionOdometerRecurrence.incrementCovariance z =
      CollisionOdometerRecurrence.incrementCovariance (-z) := by
  unfold CollisionOdometerRecurrence.incrementCovariance
  have hi := (shift z).inner_map_map incrementVector (shift (-z) incrementVector)
  rw [← shift_add, add_neg_cancel, shift_zero] at hi
  rw [← hi, real_inner_comm]

def arithmeticCovarianceTerm (z : ℤ) (kl : ℕ × ℕ) : ℝ :=
  ((kl.1 : ℝ)*collisionWeight kl.1)*((kl.2 : ℝ)*collisionWeight kl.2)*
    ((if (kl.1.gcd kl.2 : ℤ) ∣ z then 1/(kl.1.lcm kl.2 : ℝ) else 0) -
      1/((kl.1 : ℝ)*(kl.2 : ℝ)))

theorem arithmeticCovarianceTerm_even (z : ℤ) (kl : ℕ × ℕ) :
    arithmeticCovarianceTerm (-z) kl = arithmeticCovarianceTerm z kl := by
  simp only [arithmeticCovarianceTerm, dvd_neg]

theorem divisorCovarianceTerm_nat (h : ℕ) (kl : ℕ × ℕ) :
    divisorCovarianceTerm (-(h : ℤ)) kl = arithmeticCovarianceTerm (h : ℤ) kl := by
  obtain ⟨k,l⟩ := kl
  by_cases hk : k = 0
  · simp [divisorCovarianceTerm, arithmeticCovarianceTerm, hk]
  by_cases hl : l = 0
  · simp [divisorCovarianceTerm, arithmeticCovarianceTerm, hl]
  unfold divisorCovarianceTerm arithmeticCovarianceTerm
  simp only [Int.natCast_dvd_natCast]
  exact centeredReset_pair_inner (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl) h

theorem arithmeticCovarianceTerm_summable (z : ℤ) : Summable (arithmeticCovarianceTerm z) := by
  have hn (n : ℕ) : Summable (arithmeticCovarianceTerm (n : ℤ)) :=
    (divisorCovarianceTerm_summable (-(n : ℤ))).congr (divisorCovarianceTerm_nat n)
  by_cases hz : 0 ≤ z
  · simpa only [Int.toNat_of_nonneg hz] using hn z.toNat
  · have he : z = -(((-z).toNat : ℕ) : ℤ) := by omega
    rw [he]
    exact (hn (-z).toNat).congr (fun kl => (arithmeticCovarianceTerm_even _ kl).symm)

theorem incrementCovariance_arithmetic (z : ℤ) :
    CollisionOdometerRecurrence.incrementCovariance z =
      (4/9 : ℝ) * ∑' k, ∑' l, arithmeticCovarianceTerm z (k,l) := by
  have hn (n : ℕ) : CollisionOdometerRecurrence.incrementCovariance (n : ℤ) =
      (4/9 : ℝ) * ∑' k, ∑' l, arithmeticCovarianceTerm (n : ℤ) (k,l) := by
    rw [incrementCovariance_even (n : ℤ), incrementCovariance_series]
    simp_rw [divisorCovarianceTerm_nat]
  by_cases hz : 0 ≤ z
  · simpa only [Int.toNat_of_nonneg hz] using hn z.toNat
  · have he : z = -(((-z).toNat : ℕ) : ℤ) := by omega
    rw [he, incrementCovariance_even, neg_neg]
    simp_rw [arithmeticCovarianceTerm_even]
    exact hn (-z).toNat

theorem divisorCovarianceTerm_neg_one_nonpos (k l : ℕ) :
    divisorCovarianceTerm (-1) (k,l) ≤ 0 := by
  by_cases hk : k = 0
  · simp [divisorCovarianceTerm, hk]
  by_cases hl : l = 0
  · simp [divisorCovarianceTerm, hl]
  have hkpos := Nat.pos_of_ne_zero hk
  have hlpos := Nat.pos_of_ne_zero hl
  change inner ℝ (centeredResetVector k) (shift (-(1 : ℕ) : ℤ) (centeredResetVector l)) ≤ 0
  rw [centeredReset_pair_inner hkpos hlpos]
  by_cases hc : k.gcd l = 1
  · have hcop : k.Coprime l := hc
    rw [if_pos (by simp [hc]), hcop.lcm_eq_mul, Nat.cast_mul, sub_self, mul_zero]
  · rw [if_neg (by simpa only [Nat.dvd_one] using hc), zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (collisionWeight_nonneg k))
        (mul_nonneg (Nat.cast_nonneg l) (collisionWeight_nonneg l)))
      (neg_nonpos.mpr (by positivity))

theorem divisorCovarianceTerm_two : divisorCovarianceTerm (-1) (2,2) = -(1/16 : ℝ) := by
  change inner ℝ (centeredResetVector 2) (shift (-(1 : ℕ) : ℤ) (centeredResetVector 2)) = _
  rw [centeredReset_pair_inner (by norm_num : 0 < 2) (by norm_num : 0 < 2)]
  norm_num [collisionWeight_two]

theorem incrementCovariance_one_neg : CollisionOdometerRecurrence.incrementCovariance 1 < 0 := by
  have hs := (divisorCovarianceTerm_summable (-1)).neg
  have hb : (1/16 : ℝ) ≤ ∑' kl, -divisorCovarianceTerm (-1) kl := by
    have h := hs.le_tsum (2,2) (fun kl _ => neg_nonneg.mpr
      (divisorCovarianceTerm_neg_one_nonpos kl.1 kl.2))
    simpa only [divisorCovarianceTerm_two, neg_neg] using h
  rw [tsum_neg] at hb
  have hsum := (divisorCovarianceTerm_summable (-1)).tsum_prod
  rw [hsum] at hb
  rw [incrementCovariance_even 1, incrementCovariance_series]
  linarith

end NField.Alignment.CollisionDivisibilityCovariance
