/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorOne

/-!
# Exact finite Mobius regrouping of full conductor amplitudes

These are the manuscript's fixed full coefficients. The finite transform
identity is separate from the positive lower bound on its period weights.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionFiniteRegrouping

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionCylinderMeans CollisionJordanVariance
open CollisionConductorOne
open CollisionMassReadout

def beta (d Q : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (Q/d), (ArithmeticFunction.moebius j : ℝ)*amplitude (d*j)

theorem primitiveValue_within {q Q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) (a : ℕ) :
    primitiveValue q a=∑ d ∈ Finset.Icc 2 Q,
      if d ∣ q then (ArithmeticFunction.moebius (q/d) : ℝ)*centeredRemainder d a else 0 := by
  have he : (Finset.Icc 2 Q).filter (fun d => d ∣ q)=q.divisors.erase 1 := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_erase,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd2,_⟩,hdq⟩
      exact ⟨by omega,hdq,hq.ne'⟩
    · rintro ⟨hd1,hdq,_⟩
      have hdpos := Nat.pos_of_dvd_of_pos hdq hq
      exact ⟨⟨by omega,(Nat.le_of_dvd hq hdq).trans hqQ⟩,hdq⟩
  rw [← Finset.sum_filter,he,primitiveValue_formula]
  have h := Finset.sum_erase_add q.divisors
    (fun d => (ArithmeticFunction.moebius (q/d) : ℝ)*centeredRemainder d a)
    (Nat.one_mem_divisors.mpr hq.ne')
  simpa only [centeredRemainder,Nat.mod_one,Nat.cast_zero,Nat.cast_one,sub_self,
    zero_div,mul_zero,add_zero] using h.symm

theorem beta_conductor_sum {d : ℕ} (hd : 2 ≤ d) (Q : ℕ) :
    beta d Q=∑ q ∈ Finset.Icc 2 Q,
      if d ∣ q then (ArithmeticFunction.moebius (q/d) : ℝ)*amplitude q else 0 := by
  rw [← Finset.sum_filter]
  unfold beta
  apply Finset.sum_nbij' (fun j => d*j) (fun q => q/d)
  · intro j hj
    obtain ⟨hj1,hjQ⟩ := Finset.mem_Icc.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,Nat.dvd_mul_right d j⟩
    · nlinarith
    · have h := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hjQ
      simpa only [Nat.mul_comm j d] using h
  · intro q hq
    obtain ⟨hqI,hdq⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq2,hqQ⟩ := Finset.mem_Icc.mp hqI
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdq) (by omega),
      Nat.div_le_div_right hqQ⟩
  · intro j _
    exact Nat.mul_div_cancel_left j (by omega)
  · intro q hq
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hq).2
  · intro j _
    rw [Nat.mul_div_cancel_left j (by omega : 0 < d)]

theorem fixedConductor_regrouping (Q a : ℕ) :
    fixedConductorValue Q a=(2/3 : ℝ)*
      ∑ d ∈ Finset.Icc 2 Q, beta d Q*centeredRemainder d a := by
  unfold fixedConductorValue
  congr 1
  calc
    (∑ q ∈ Finset.Icc 2 Q, amplitude q*primitiveValue q a)=
        ∑ q ∈ Finset.Icc 2 Q, ∑ d ∈ Finset.Icc 2 Q,
          (if d ∣ q then (ArithmeticFunction.moebius (q/d) : ℝ)*amplitude q else 0)*
            centeredRemainder d a := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [primitiveValue_within (by have := (Finset.mem_Icc.mp hq).1; omega)
        (Finset.mem_Icc.mp hq).2,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> ring
    _ = ∑ d ∈ Finset.Icc 2 Q, (∑ q ∈ Finset.Icc 2 Q,
        if d ∣ q then (ArithmeticFunction.moebius (q/d) : ℝ)*amplitude q else 0)*
          centeredRemainder d a := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← beta_conductor_sum (Finset.mem_Icc.mp hd).1]

theorem beta_above_cutoff {d Q : ℕ} (hQ : Q < d) : beta d Q=0 := by
  simp [beta,Nat.div_eq_of_lt hQ]

theorem beta_top_range {d Q : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (hQ : Q < 2*d) :
    beta d Q=amplitude d := by
  have hdiv : Q/d=1 := by
    have h1 := Nat.div_pos hdQ hd
    have h2 := (Nat.div_lt_iff_lt_mul hd).mpr hQ
    omega
  simp [beta,hdiv]

theorem conductorEndpoint_beta (Q : ℕ) :
    conductorEndpoint Q=(1/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q, beta d Q*((d : ℝ)-1) := by
  have h := fixedConductor_regrouping Q 0
  rw [fixedConductor_zero] at h
  simp only [centeredRemainder,Nat.zero_mod,Nat.cast_zero,zero_sub] at h
  have he : (∑ d ∈ Finset.Icc 2 Q, beta d Q*(-(((d : ℝ)-1)/2)))=
      -(1/2 : ℝ)*∑ d ∈ Finset.Icc 2 Q, beta d Q*((d : ℝ)-1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he] at h
  linarith

theorem fixedConductor_beta_gap (Q a : ℕ) :
    fixedConductorValue Q a+conductorEndpoint Q=
      (2/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q, beta d Q*((a%d : ℕ) : ℝ) := by
  rw [fixedConductor_regrouping,conductorEndpoint_beta]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold centeredRemainder
  ring

def partialMobius (J m : ℕ) : ℝ :=
  ∑ j ∈ m.divisors, if j ≤ J then (ArithmeticFunction.moebius j : ℝ) else 0

theorem amplitude_multiple_summable {d : ℕ} (hd : 0 < d) (j : ℕ) :
    Summable (fun m : ℕ => if j ∣ m then collisionWeight (d*m) else 0) := by
  have hi : Function.Injective (fun m : ℕ => d*m) := fun _ _ => Nat.mul_left_cancel hd
  apply ((amplitude_summable (d*j)).comp_injective hi).congr
  intro m
  simp only [Function.comp_def,Nat.mul_dvd_mul_iff_left hd]

theorem amplitude_multiple_series {d : ℕ} (hd : 0 < d) (j : ℕ) :
    amplitude (d*j)=∑' m : ℕ, if j ∣ m then collisionWeight (d*m) else 0 := by
  have hi : Function.Injective (fun m : ℕ => d*m) := fun _ _ => Nat.mul_left_cancel hd
  have hs : Function.support (fun n : ℕ => if d*j ∣ n then collisionWeight n else 0) ⊆
      Set.range (fun m : ℕ => d*m) := by
    intro n hn
    have hn' : d*j ∣ n := by
      by_contra h
      simp only [Function.mem_support,if_neg h,ne_eq,not_true_eq_false] at hn
    obtain ⟨m,hm⟩ := (Nat.dvd_mul_right d j).trans hn'
    exact ⟨m,hm.symm⟩
  have h := hi.tsum_eq hs
  simpa only [Nat.mul_dvd_mul_iff_left hd,amplitude] using h.symm

theorem partialMobius_cutoff {m : ℕ} (hm : 0 < m) (J : ℕ) :
    partialMobius J m=∑ j ∈ Finset.Icc 1 J,
      if j ∣ m then (ArithmeticFunction.moebius j : ℝ) else 0 := by
  have he : m.divisors.filter (fun j => j ≤ J)=
      (Finset.Icc 1 J).filter (fun j => j ∣ m) := by
    ext j
    simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hjm,_⟩,hjJ⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hjm hm,hjJ⟩,hjm⟩
    · rintro ⟨⟨_,hjJ⟩,hjm⟩
      exact ⟨⟨hjm,hm.ne'⟩,hjJ⟩
  unfold partialMobius
  rw [← Finset.sum_filter,he,Finset.sum_filter]

theorem weighted_partialMobius (d J m : ℕ) :
    collisionWeight (d*m)*partialMobius J m=
      ∑ j ∈ Finset.Icc 1 J, (ArithmeticFunction.moebius j : ℝ)*
        (if j ∣ m then collisionWeight (d*m) else 0) := by
  by_cases hm : m=0
  · simp [hm,collisionWeight_zero]
  rw [partialMobius_cutoff (by omega : 0 < m),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem beta_period_series_summable {d : ℕ} (hd : 0 < d) (J : ℕ) :
    Summable (fun m : ℕ => collisionWeight (d*m)*partialMobius J m) := by
  have hs := summable_sum (s := Finset.Icc 1 J) (fun j _ =>
    (amplitude_multiple_summable hd j).mul_left (ArithmeticFunction.moebius j : ℝ))
  exact hs.congr (fun m => (weighted_partialMobius d J m).symm)

theorem beta_period_series {d : ℕ} (hd : 0 < d) (Q : ℕ) :
    beta d Q=∑' m : ℕ, collisionWeight (d*m)*partialMobius (Q/d) m := by
  simp_rw [weighted_partialMobius]
  rw [Summable.tsum_finsetSum (fun j _ =>
    (amplitude_multiple_summable hd j).mul_left (ArithmeticFunction.moebius j : ℝ))]
  unfold beta
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_mul_left,← amplitude_multiple_series hd]

theorem partialMobius_one {J : ℕ} (hJ : 1 ≤ J) : partialMobius J 1=1 := by
  simp [partialMobius,hJ]

theorem beta_period_split {d Q : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) :
    beta d Q=collisionWeight d+
      ∑' m : ℕ, collisionWeight (d*(m+2))*partialMobius (Q/d) (m+2) := by
  have h := (beta_period_series_summable hd (Q/d)).sum_add_tsum_nat_add 2
  rw [← beta_period_series hd Q] at h
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.mul_zero,
    collisionWeight_zero,zero_mul,Nat.mul_one,partialMobius_one (Nat.div_pos hdQ hd),
    mul_one] using h.symm

end NField.Alignment.CollisionFiniteRegrouping
