/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionDivisibilityCovariance
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Finite joint residue probabilities without coprimality assumptions

All pairwise gcd compatibility conditions are retained. A compatible
finite system has one residue modulo the common lcm, including the empty
system with modulus one. Uniform profinite quotients give its Haar mass.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionJointCRT

open scoped BigOperators Classical
open MeasureTheory
open ProfiniteRemainderMeasure CollisionDivisibilityCovariance
open CollisionResetIntegrability CollisionRemainderDynamics CollisionPotentialCoboundary

variable {ι : Type*}

theorem gcd_lcm_distrib (a b c : ℕ) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    a.gcd (b.lcm c)=(a.gcd b).lcm (a.gcd c) := by
  have hab : a.gcd b≠0 := (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)).ne'
  have hac : a.gcd c≠0 := (Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero ha)).ne'
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)).ne' (Nat.lcm_ne_zero hab hac)
  intro p
  rw [Nat.factorization_gcd ha (Nat.lcm_ne_zero hb hc), Nat.factorization_lcm hb hc,
    Nat.factorization_lcm hab hac, Nat.factorization_gcd ha hb, Nat.factorization_gcd ha hc]
  simp only [Finsupp.inf_apply, Finsupp.sup_apply, inf_sup_left]

theorem modEq_finset_lcm (S : Finset ι) (k : ι → ℕ) {a b : ℕ}
    (h : ∀ i∈S, Nat.ModEq (k i) a b) : Nat.ModEq (S.lcm k) a b := by
  induction S using Finset.induction_on with
  | empty => simpa using Nat.modEq_one (a := a) (b := b)
  | @insert i S hi ih =>
    rw [Finset.lcm_insert, lcm_eq_nat_lcm]
    exact Nat.mod_lcm (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem gcd_finset_lcm (S : Finset ι) (k : ι → ℕ) (a : ℕ) (ha : a≠0)
    (hk : ∀ i∈S, k i≠0) : a.gcd (S.lcm k)=S.lcm (fun i => a.gcd (k i)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hs : ∀ j∈S, k j≠0 := fun j hj => hk j (Finset.mem_insert_of_mem hj)
    rw [Finset.lcm_insert, lcm_eq_nat_lcm,
      gcd_lcm_distrib a (k i) (S.lcm k) ha (hk i (Finset.mem_insert_self _ _))
        (Finset.lcm_ne_zero_iff.mpr hs), ih hs, Finset.lcm_insert, lcm_eq_nat_lcm]

def Compatible (S : Finset ι) (k a : ι → ℕ) : Prop :=
  ∀ i∈S, ∀ j∈S, Nat.ModEq ((k i).gcd (k j)) (a i) (a j)

theorem joint_crt_exists (S : Finset ι) (k a : ι → ℕ) (hk : ∀ i∈S, 0<k i)
    (hc : Compatible S k a) : ∃ n<S.lcm k, ∀ i∈S, Nat.ModEq (k i) n (a i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | @insert i S hi ih =>
    have hs : ∀ j∈S, 0<k j := fun j hj => hk j (Finset.mem_insert_of_mem hj)
    have hcS : Compatible S k a := fun j hj l hl =>
      hc j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl)
    obtain ⟨n, hn, hres⟩ := ih hs hcS
    have hkI := hk i (Finset.mem_insert_self _ _)
    have hLCM : S.lcm k≠0 := Finset.lcm_ne_zero_iff.mpr (fun j hj => (hs j hj).ne')
    have hm : Nat.ModEq ((k i).gcd (S.lcm k)) (a i) n := by
      rw [gcd_finset_lcm S k (k i) hkI.ne' (fun j hj => (hs j hj).ne')]
      apply modEq_finset_lcm
      intro j hj
      exact (hc i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)).trans
        ((hres j hj).of_dvd (Nat.gcd_dvd_right (k i) (k j))).symm
    let c := Nat.chineseRemainder' hm
    refine ⟨c.val, ?_, ?_⟩
    · rw [Finset.lcm_insert, lcm_eq_nat_lcm]
      exact Nat.chineseRemainder'_lt_lcm hm hkI.ne' hLCM
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact c.property.1
      · exact (c.property.2.of_dvd (Finset.dvd_lcm hj)).trans (hres j hj)

theorem joint_crt_unique (S : Finset ι) (k a : ι → ℕ) {m n : ℕ}
    (hm : m<S.lcm k) (hn : n<S.lcm k)
    (hmr : ∀ i∈S, Nat.ModEq (k i) m (a i))
    (hnr : ∀ i∈S, Nat.ModEq (k i) n (a i)) : m=n :=
  (modEq_finset_lcm S k (fun i hi => (hmr i hi).trans (hnr i hi).symm)).eq_of_lt_of_lt hm hn

theorem joint_crt_compatible (S : Finset ι) (k a : ι → ℕ) {n : ℕ}
    (h : ∀ i∈S, Nat.ModEq (k i) n (a i)) : Compatible S k a := by
  intro i hi j hj
  exact ((h i hi).of_dvd (Nat.gcd_dvd_left (k i) (k j))).symm.trans
    ((h j hj).of_dvd (Nat.gcd_dvd_right (k i) (k j)))

theorem joint_residue_count (S : Finset ι) (k a : ι → ℕ) (hk : ∀ i∈S, 0<k i) :
    (∑ n ∈ Finset.range (S.lcm k), if ∀ i∈S, Nat.ModEq (k i) n (a i) then (1 : ℝ) else 0) =
      if Compatible S k a then 1 else 0 := by
  by_cases hc : Compatible S k a
  · obtain ⟨c, hcL, hres⟩ := joint_crt_exists S k a hk hc
    rw [if_pos hc]
    have he (n : ℕ) (hn : n∈Finset.range (S.lcm k)) :
        (∀ i∈S, Nat.ModEq (k i) n (a i)) ↔ n=c :=
      ⟨fun h => joint_crt_unique S k a (Finset.mem_range.mp hn) hcL h hres,
        fun h => h ▸ hres⟩
    calc
      _ = ∑ n ∈ Finset.range (S.lcm k), if n=c then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl (fun n hn => if_congr (he n hn) rfl rfl)
      _ = 1 := by simp [hcL]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro n _
    exact if_neg (fun h => hc (joint_crt_compatible S k a h))

theorem joint_residue_integral (S : Finset ι) (k a : ι → ℕ) (hk : ∀ i∈S, 0<k i) :
    (∫ x, ∏ i ∈ S, (residueEvent (k i) (a i)).indicator (fun _ => (1 : ℝ)) x ∂phaseHaar) =
      if Compatible S k a then 1/((S.lcm k : ℕ) : ℝ) else 0 := by
  letI : NeZero (S.lcm k) := ⟨Finset.lcm_ne_zero_iff.mpr (fun i hi => (hk i hi).ne')⟩
  have he (x : Phase) : (∏ i ∈ S,
      (residueEvent (k i) (a i)).indicator (fun _ => (1 : ℝ)) x) =
      if ∀ i∈S, Nat.ModEq (k i) (residueHom (S.lcm k) x).toAdd.val (a i) then 1 else 0 := by
    by_cases hall : ∀ i∈S, Nat.ModEq (k i) (residueHom (S.lcm k) x).toAdd.val (a i)
    · rw [if_pos hall]
      apply Finset.prod_eq_one
      intro i hi
      letI : NeZero (k i) := ⟨(hk i hi).ne'⟩
      exact Set.indicator_of_mem ((mem_residueEvent_via (Finset.dvd_lcm hi) x).mpr (hall i hi)) _
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨i, hi, hbad⟩ := hall
      letI : NeZero (k i) := ⟨(hk i hi).ne'⟩
      apply Finset.prod_eq_zero hi
      exact Set.indicator_of_notMem (fun hh => hbad
        ((mem_residueEvent_via (Finset.dvd_lcm hi) x).mp hh)) _
  simp_rw [he]
  rw [integral_residue (S.lcm k)
    (fun n => if ∀ i∈S, Nat.ModEq (k i) n (a i) then (1 : ℝ) else 0),
    joint_residue_count S k a hk]
  split_ifs <;> simp

theorem compatible_integer_difference (S : Finset ι) (k h : ι → ℕ) :
    Compatible S k h ↔ ∀ i∈S, ∀ j∈S,
      ((k i).gcd (k j) : ℤ) ∣ (h i : ℤ)-(h j : ℤ) := by
  simp only [Compatible, Nat.modEq_iff_dvd]
  constructor <;> intro H i hi j hj <;> exact dvd_sub_comm.mp (H i hi j hj)

theorem joint_reset_integral_negative (S : Finset ι) (k h : ι → ℕ)
    (hk : ∀ i∈S, 0<k i) :
    (∫ x, ∏ i ∈ S, resetTerm (k i)
      (CollisionPotentialCoboundary.translate (-(h i : ℤ)) x) ∂phaseHaar) =
      (∏ i ∈ S, (k i : ℝ)*collisionWeight (k i))*
        (if ∀ i∈S, ∀ j∈S, ((k i).gcd (k j) : ℤ) ∣ (h i : ℤ)-(h j : ℤ)
          then 1/((S.lcm k : ℕ) : ℝ) else 0) := by
  have he (x : Phase) : (∏ i ∈ S, resetTerm (k i)
      (CollisionPotentialCoboundary.translate (-(h i : ℤ)) x)) =
      (∏ i ∈ S, (k i : ℝ)*collisionWeight (k i))*
        ∏ i ∈ S, (residueEvent (k i) (h i)).indicator (fun _ => (1 : ℝ)) x := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [resetTerm_indicator]
    have hiE := reset_shift_event (hk i hi) (h i) x
    by_cases hx : x ∈ residueEvent (k i) (h i)
    · rw [Set.indicator_of_mem (hiE.mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun hh => hx (hiE.mp hh)), Set.indicator_of_notMem hx]
  simp_rw [he]
  rw [integral_const_mul, joint_residue_integral S k h hk, compatible_integer_difference]
  split_ifs <;> rfl

theorem resetTerm_shift_inv (k : ℕ) (z : ℤ) (x : Phase) :
    resetTerm k (CollisionPotentialCoboundary.translate z x⁻¹) =
      resetTerm k (CollisionPotentialCoboundary.translate (-z) x) := by
  by_cases hk : k=0
  · simp [hk]
  letI : NeZero k := ⟨hk⟩
  have hkpos := Nat.pos_of_ne_zero hk
  have hr : (residueHom k x⁻¹).toAdd= -(residueHom k x).toAdd := by
    rw [map_inv]
    rfl
  have he : (z : ZMod k)+ -(residueHom k x).toAdd=0 ↔
      (-z : ZMod k)+(residueHom k x).toAdd=0 := by
    constructor <;> intro h <;> linear_combination -h
  simp only [resetTerm, resetSet, dif_pos hkpos, Set.indicator_apply, Set.mem_setOf_eq,
    residue_translate, hr, Int.cast_neg, he]

theorem joint_reset_integral (S : Finset ι) (k h : ι → ℕ)
    (hk : ∀ i∈S, 0<k i) :
    (∫ x, ∏ i ∈ S, resetTerm (k i)
      (CollisionPotentialCoboundary.translate (h i : ℤ) x) ∂phaseHaar) =
      (∏ i ∈ S, (k i : ℝ)*collisionWeight (k i))*
        (if ∀ i∈S, ∀ j∈S, ((k i).gcd (k j) : ℤ) ∣ (h i : ℤ)-(h j : ℤ)
          then 1/((S.lcm k : ℕ) : ℝ) else 0) := by
  rw [← integral_inv_eq_self (fun x => ∏ i ∈ S,
    resetTerm (k i) (CollisionPotentialCoboundary.translate (h i : ℤ) x)) phaseHaar]
  simp only [resetTerm_shift_inv]
  exact joint_reset_integral_negative S k h hk

end NField.Alignment.CollisionJointCRT
