/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Fair-coordinate antichain estimates for Bernoulli activation

The central-binomial estimate is proved uniformly, including dimension
zero, using the exact recurrence. This is the fair-coordinate component
of the activation lemma, not the nonuniform Bernoulli theorem by itself.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionActivationSperner

open scoped BigOperators Classical

theorem centralBinomial_square_bound (n : ℕ) :
    (n.centralBinom : ℝ)^2*((n : ℝ)+1) ≤ (16 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hr : ((n : ℝ)+1)*((n+1).centralBinom : ℝ)=
        2*(2*(n : ℝ)+1)*(n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hp : 0 < ((n : ℝ)+1)^2 := by positivity
    have hf : (2*(n : ℝ)+1)^2*((n : ℝ)+2) ≤ 4*((n : ℝ)+1)^3 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [Nat.cast_add,Nat.cast_one]
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      (((n+1).centralBinom : ℝ)^2*((n : ℝ)+1+1))*((n : ℝ)+1)^2 =
          (((n : ℝ)+1)*((n+1).centralBinom : ℝ))^2*((n : ℝ)+2) := by ring
      _ = (2*(2*(n : ℝ)+1)*(n.centralBinom : ℝ))^2*((n : ℝ)+2) := by rw [hr]
      _ = (4*(n.centralBinom : ℝ)^2)*((2*(n : ℝ)+1)^2*((n : ℝ)+2)) := by ring
      _ ≤ (4*(n.centralBinom : ℝ)^2)*(4*((n : ℝ)+1)^3) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = 16*((n.centralBinom : ℝ)^2*((n : ℝ)+1))*((n : ℝ)+1)^2 := by ring
      _ ≤ 16*(16 : ℝ)^n*((n : ℝ)+1)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih (by norm_num)) (sq_nonneg _)
      _ = (16 : ℝ)^(n+1)*((n : ℝ)+1)^2 := by ring

theorem odd_middle_le_twice_central (n : ℕ) :
    ((2*n+1).choose n : ℝ) ≤ 2*(n.centralBinom : ℝ) := by
  have hr : (n.centralBinom : ℝ)*(2*(n : ℝ)+1)=
      ((2*n+1).choose n : ℝ)*((n : ℝ)+1) := by
    have h := Nat.choose_mul_succ_eq (2*n) n
    rw [show 2*n+1-n=n+1 by omega] at h
    exact_mod_cast h
  apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ)<(n : ℝ)+1)).mp
  rw [← hr]
  nlinarith [Nat.cast_nonneg (α := ℝ) n.centralBinom]

theorem middleBinomial_square_bound (n : ℕ) :
    (n.choose (n/2) : ℝ)^2*((n : ℝ)+1) ≤ 2*(4 : ℝ)^n := by
  obtain ⟨m,hm⟩ | ⟨m,hm⟩ := Nat.even_or_odd n
  · have hn : n=2*m := by omega
    rw [hn]
    have h := centralBinomial_square_bound m
    have hc : 0 ≤ (m.centralBinom : ℝ)^2 := sq_nonneg _
    rw [show (2*m)/2=m by omega,← Nat.centralBinom_eq_two_mul_choose]
    push_cast
    rw [pow_mul]
    norm_num
    nlinarith
  · have hn : n=2*m+1 := by omega
    rw [hn]
    have hc := odd_middle_le_twice_central m
    have hsq : ((2*m+1).choose m : ℝ)^2 ≤ 4*(m.centralBinom : ℝ)^2 := by
      nlinarith [mul_nonneg
        (show 0 ≤ 2*(m.centralBinom : ℝ)-((2*m+1).choose m : ℝ) by linarith)
        (show 0 ≤ 2*(m.centralBinom : ℝ)+((2*m+1).choose m : ℝ) by positivity)]
    have hh := centralBinomial_square_bound m
    have hs := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 2*(m : ℝ)+2 by positivity)
    have hi := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ)≤8)
    rw [show (2*m+1)/2=m by omega]
    push_cast
    rw [pow_add,pow_one,pow_mul]
    norm_num
    nlinarith

theorem middleBinomial_probability_bound (n : ℕ) :
    (n.choose (n/2) : ℝ)/(2 : ℝ)^n ≤ 2/Real.sqrt ((n : ℝ)+1) := by
  have hpos : 0<Real.sqrt ((n : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hp : (0 : ℝ)<(2 : ℝ)^n := by positivity
  have he : ((2 : ℝ)^n)^2=(4 : ℝ)^n := by
    rw [← pow_mul,mul_comm n 2,pow_mul]
    norm_num
  have hr : ((n.choose (n/2) : ℝ)/(2 : ℝ)^n)^2*((n : ℝ)+1) ≤ 2 := by
    rw [div_pow,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hp),he]
    exact middleBinomial_square_bound n
  apply (le_div_iff₀ hpos).mpr
  have hs : (((n.choose (n/2) : ℝ)/(2 : ℝ)^n)*Real.sqrt ((n : ℝ)+1))^2 ≤ 2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    exact hr
  nlinarith [sq_nonneg (((n.choose (n/2) : ℝ)/(2 : ℝ)^n)*Real.sqrt ((n : ℝ)+1)-2)]

def fairFamilyMass {α : Type*} [Fintype α] (A : Finset (Finset α)) : ℝ :=
  (A.card : ℝ)/(2 : ℝ)^(Fintype.card α)

theorem fair_antichain_bound {α : Type*} [Fintype α] (A : Finset (Finset α))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α))) :
    fairFamilyMass A ≤ 2/Real.sqrt ((Fintype.card α : ℝ)+1) := by
  have h := hA.sperner
  exact (div_le_div_of_nonneg_right (by exact_mod_cast h)
    (by positivity : (0 : ℝ)≤(2 : ℝ)^Fintype.card α)).trans
      (middleBinomial_probability_bound (Fintype.card α))

theorem coordinate_increase_monotone {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) {a : ℝ} (ha : 0<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) : Monotone F := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro s i hi
  have h := hF s i hi
  linarith

theorem strict_subset_increase {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) {a : ℝ} (ha : 0<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s))
    {s t : Finset α} (hst : s⊆t) (hne : s≠t) : F s+a ≤ F t := by
  have hnot : ¬t⊆s := by intro hts; exact hne (Finset.Subset.antisymm hst hts)
  obtain ⟨i,hit,his⟩ := Finset.not_subset.mp hnot
  exact (hF s i his).trans ((coordinate_increase_monotone F ha hF)
    (Finset.insert_subset hit hst))

theorem short_interval_antichain {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    IsAntichain (· ⊆ ·) {s : Finset α | F s ∈ Set.Icc u v} := by
  intro s hs t ht hne hst
  have h := strict_subset_increase F ha hF hst hne
  have hs' := hs.1
  have ht' := ht.2
  linarith

theorem fair_short_interval_bound {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α → ℝ) {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    fairFamilyMass (Finset.univ.filter (fun s => F s ∈ Set.Icc u v)) ≤
      2/Real.sqrt ((Fintype.card α : ℝ)+1) := by
  apply fair_antichain_bound
  convert! short_interval_antichain F ha huv hF using 1
  ext s
  simp

end NField.Alignment.CollisionActivationSperner
