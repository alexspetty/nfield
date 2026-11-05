/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionCylinderOne
import NField.Alignment.CollisionMassInverse
import NField.Alignment.CollisionAmplitudeRefinement

/-!
# The address-one gap for full-amplitude finite conductor cutoffs

These are actual finite continuous values, not evaluations of the limiting
Haar equivalence class. The signed tail is controlled absolutely.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorOne

open scoped BigOperators Classical
open Filter
open CollisionRemainderDynamics CollisionMassReadout CollisionPotentialConvergence
open CollisionJordanVariance CollisionCylinderMeans CollisionReciprocalBudget
open CollisionMassInverse CollisionGeneralWeightCriterion CollisionAmplitudeRefinement
open CollisionAmplitudeTail CollisionCylinderOne

def fixedConductorValue (Q a : ℕ) : ℝ :=
  (2/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, amplitude q*primitiveValue q a
def conductorEndpoint (Q : ℕ) : ℝ :=
  (1/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, (q.totient : ℝ)*amplitude q
def mobiusAmplitude (q : ℕ) : ℝ := (ArithmeticFunction.moebius q : ℝ)*amplitude q
def mobiusAmplitudeTail (Q : ℕ) : ℝ := ∑' q : ℕ, if Q < q then mobiusAmplitude q else 0
def conductorOneError (Q : ℕ) : ℝ := fixedConductorValue Q 1+conductorEndpoint Q-(2/3 : ℝ)

theorem primitiveValue_at_zero {q : ℕ} (hq : 2 ≤ q) :
    primitiveValue q 0=-(q.totient : ℝ)/2 := by
  have h := divisor_sums_injective (fun q => primitiveValue q 0)
    (fun q => (-1/2 : ℝ)*(if 2 ≤ q then (q.totient : ℝ) else 0))
    (fun n hn => by
      rw [primitiveValue_divisor_sum hn,← Finset.mul_sum,totient_divisor_sum_ge_two hn]
      simp only [centeredRemainder,Nat.zero_mod,Nat.cast_zero]
      ring) q (by omega)
  rw [if_pos hq] at h
  calc
    _ = (-1/2 : ℝ)*(q.totient : ℝ) := h
    _ = _ := by ring

theorem primitiveValue_one_step {q : ℕ} (hq : 2 ≤ q) :
    primitiveValue q 1-primitiveValue q 0=-(ArithmeticFunction.moebius q : ℝ) := by
  have h := divisor_sums_injective (fun q => primitiveValue q 1-primitiveValue q 0)
    (fun q => (if q=1 then (1 : ℝ) else 0)-(ArithmeticFunction.moebius q : ℝ))
    (fun n hn => by
      rw [Finset.sum_sub_distrib,primitiveValue_divisor_sum hn 1,
        primitiveValue_divisor_sum hn 0,Finset.sum_sub_distrib,moebius_divisor_sum]
      have hone : (∑ d ∈ n.divisors, if d=1 then (1 : ℝ) else 0)=1 := by
        simp [Nat.one_mem_divisors.mpr hn.ne']
      rw [hone]
      by_cases hn1 : n=1
      · subst n
        norm_num [centeredRemainder]
      · have hn2 : 1 < n := by omega
        simp only [if_neg hn1,centeredRemainder,Nat.mod_eq_of_lt hn2,Nat.zero_mod,
          Nat.cast_zero,Nat.cast_one]
        ring) q (by omega)
  simpa only [if_neg (by omega : q≠1),zero_sub] using h

theorem fixedConductor_zero (Q : ℕ) : fixedConductorValue Q 0=-conductorEndpoint Q := by
  calc
    _ = ∑ q ∈ Finset.Icc 2 Q, (-1/3 : ℝ)*((q.totient : ℝ)*amplitude q) := by
      rw [fixedConductorValue,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [primitiveValue_at_zero (Finset.mem_Icc.mp hq).1]
      ring
    _ = (-1/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, (q.totient : ℝ)*amplitude q := by
      rw [← Finset.mul_sum]
    _ = _ := by unfold conductorEndpoint; ring

theorem fixedConductor_one_difference (Q : ℕ) :
    fixedConductorValue Q 1-fixedConductorValue Q 0=
      -(2/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, mobiusAmplitude q := by
  rw [fixedConductorValue,fixedConductorValue,← mul_sub,← Finset.sum_sub_distrib]
  have he : (∑ q ∈ Finset.Icc 2 Q, (amplitude q*primitiveValue q 1-amplitude q*primitiveValue q 0))=
      -(∑ q ∈ Finset.Icc 2 Q, mobiusAmplitude q) := by
    calc
      _ = ∑ q ∈ Finset.Icc 2 Q, -mobiusAmplitude q := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [← mul_sub,primitiveValue_one_step (Finset.mem_Icc.mp hq).1]
        unfold mobiusAmplitude
        ring
      _ = _ := Finset.sum_neg_distrib mobiusAmplitude
  rw [he]
  ring

theorem mobiusAmplitude_summable : Summable mobiusAmplitude := by
  have h := inverse_norm_summable collisionWeight collisionWeight_nonneg
    (show Summable (generalEnergy collisionWeight) from conductorEnergy_summable)
    (k := 1) (by norm_num)
  apply h.of_norm.congr
  intro q
  simp only [one_mul,mobiusAmplitude,generalAmplitude,amplitude]

theorem mobiusAmplitude_tsum_zero : (∑' q, mobiusAmplitude q)=0 := by
  have h := mass_moebius_inverse collisionWeight collisionWeight_nonneg collisionWeight_zero
    collisionWeight_summable (show Summable (generalEnergy collisionWeight) from conductorEnergy_summable)
    (k := 1) (by norm_num)
  simpa only [collisionWeight_one,one_mul,mobiusAmplitude,generalAmplitude,amplitude] using h.symm

theorem mobiusAmplitude_zero : mobiusAmplitude 0=0 := by simp [mobiusAmplitude]

theorem mobiusAmplitude_one : mobiusAmplitude 1=1 := by simp [mobiusAmplitude,amplitude_one]

theorem mobiusAmplitude_prefix {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.range (Q+1), mobiusAmplitude q)=
      1+∑ q ∈ Finset.Icc 2 Q, mobiusAmplitude q := by
  rw [Nat.range_succ_eq_Icc_zero Q,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le Q),Finset.sum_cons,mobiusAmplitude_zero,zero_add]
  have h := Finset.sum_Ioc_consecutive mobiusAmplitude (by norm_num : (0 : ℕ) ≤ 1) hQ
  have he : Finset.Ioc 1 Q=Finset.Icc 2 Q := by
    ext q
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hone : (∑ q ∈ Finset.Ioc 0 1, mobiusAmplitude q)=1 := by
    norm_num [mobiusAmplitude_one]
  rw [hone,he] at h
  exact h.symm

theorem mobiusAmplitude_split (Q : ℕ) :
    (∑ q ∈ Finset.range (Q+1), mobiusAmplitude q)+mobiusAmplitudeTail Q=0 := by
  have h := mobiusAmplitude_summable.sum_add_tsum_compl (s := Finset.range (Q+1))
  rw [tsum_subtype,mobiusAmplitude_tsum_zero] at h
  convert! h using 1
  congr 1
  apply tsum_congr
  intro q
  simp [Set.indicator]

theorem mobiusAmplitude_tail_summable (Q : ℕ) :
    Summable (fun q : ℕ => if Q < q then mobiusAmplitude q else 0) := by
  apply (mobiusAmplitude_summable.indicator {q : ℕ | Q < q}).congr
  intro q
  simp only [Set.indicator_apply,Set.mem_setOf_eq]

theorem mobiusAmplitude_norm_bound (q : ℕ) : ‖mobiusAmplitude q‖ ≤ amplitude q := by
  rw [mobiusAmplitude,norm_mul,Real.norm_of_nonneg (amplitude_nonneg q)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (moebius_real_norm_le q) (amplitude_nonneg q)

theorem mobiusAmplitude_tail_bound {Q : ℕ} (hQ : 1 ≤ Q) :
    ‖mobiusAmplitudeTail Q‖ ≤ amplitudeTail Q := by
  have hs := mobiusAmplitude_tail_summable Q
  have hbound : ∀ q : ℕ, ‖if Q < q then mobiusAmplitude q else 0‖ ≤
      if (Q : ℝ) < (q : ℝ) then amplitude q else 0 := by
    intro q
    simp only [Nat.cast_lt]
    split_ifs
    · exact mobiusAmplitude_norm_bound q
    · simp
  have h := hs.norm.tsum_le_tsum hbound (amplitude_tail_summable (by exact_mod_cast hQ))
  exact (norm_tsum_le_tsum_norm hs.norm).trans h

theorem conductorOneError_exact {Q : ℕ} (hQ : 1 ≤ Q) :
    conductorOneError Q=(2/3 : ℝ)*mobiusAmplitudeTail Q := by
  have hf := fixedConductor_one_difference Q
  rw [fixedConductor_zero] at hf
  have hs := mobiusAmplitude_split Q
  rw [mobiusAmplitude_prefix hQ] at hs
  unfold conductorOneError
  nlinarith

theorem conductorOneError_bound {Q : ℕ} (hQ : 1 ≤ Q) :
    ‖conductorOneError Q‖ ≤ (2/3 : ℝ)*amplitudeTail Q := by
  rw [conductorOneError_exact hQ,norm_mul]
  have hc : ‖(2/3 : ℝ)‖=(2/3 : ℝ) := by norm_num
  rw [hc]
  exact mul_le_mul_of_nonneg_left (mobiusAmplitude_tail_bound hQ) (by norm_num)

theorem conductor_address_one_asymptotic :
    Asymptotics.IsBigO atTop
      (fun Q : ℕ => fixedConductorValue Q 1+conductorEndpoint Q-(2/3 : ℝ))
      (fun Q : ℕ => Real.log (2*(Q : ℝ))/(Q : ℝ)) := by
  have hc : Asymptotics.IsBigO atTop conductorOneError (fun Q : ℕ => amplitudeTail Q) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨2/3,?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with Q hQ
    rw [Real.norm_of_nonneg (amplitude_tail_nonneg Q)]
    exact conductorOneError_bound hQ
  exact (hc.trans (amplitude_tail_isBigO.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ)))).trans log_over_nat_isBigO_log_double

end NField.Alignment.CollisionConductorOne
