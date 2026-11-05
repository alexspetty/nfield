/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionActivationSperner

/-!
# Finite Bernoulli product laws and activation coupling

The average is an explicit finite product probability law on subsets of a
finite coordinate set. Its recursion proves the coupling with activated
fair coordinates for arbitrary real observables, not only moments.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionBernoulliProduct

open scoped BigOperators Classical
variable {α : Type*} [DecidableEq α]

def weightOn (b : α → ℝ) (S A : Finset α) : ℝ :=
  (∏ i ∈ A, b i)*(∏ i ∈ S\A, (1-b i))

def bernoulliAverage (b : α → ℝ) (S : Finset α) (F : Finset α → ℝ) : ℝ :=
  ∑ A ∈ S.powerset, weightOn b S A*F A

def fairAverage (S : Finset α) (F : Finset α → ℝ) : ℝ :=
  bernoulliAverage (fun _ => (1/2 : ℝ)) S F

theorem bernoulliAverage_empty (b : α → ℝ) (F : Finset α → ℝ) :
    bernoulliAverage b ∅ F=F ∅ := by simp [bernoulliAverage,weightOn]

theorem weightOn_absent (b : α → ℝ) {S A : Finset α} {i : α}
    (hi : i∉S) (hA : A⊆S) : weightOn b (insert i S) A=(1-b i)*weightOn b S A := by
  have hiA : i∉A := fun h => hi (hA h)
  unfold weightOn
  rw [Finset.insert_sdiff_of_notMem S hiA,Finset.prod_insert (by simp [hi])]
  ring

theorem weightOn_present (b : α → ℝ) {S A : Finset α} {i : α}
    (hi : i∉S) (hA : A⊆S) : weightOn b (insert i S) (insert i A)=b i*weightOn b S A := by
  have hiA : i∉A := fun h => hi (hA h)
  unfold weightOn
  rw [Finset.prod_insert hiA,Finset.insert_sdiff_insert,Finset.sdiff_insert_of_notMem hi]
  ring

theorem powerset_insert_disjoint {S : Finset α} {i : α} (hi : i∉S) :
    Disjoint S.powerset (S.powerset.image (insert i)) := by
  apply Finset.disjoint_left.mpr
  intro A hA hAi
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hAi
  exact hi ((Finset.mem_powerset.mp hA) (Finset.mem_insert_self i B))

theorem bernoulliAverage_insert (b : α → ℝ) {S : Finset α} {i : α} (hi : i∉S)
    (F : Finset α → ℝ) :
    bernoulliAverage b (insert i S) F=(1-b i)*bernoulliAverage b S F+
      b i*bernoulliAverage b S (fun A => F (insert i A)) := by
  unfold bernoulliAverage
  rw [Finset.powerset_insert,Finset.sum_union (powerset_insert_disjoint hi),Finset.sum_image]
  · rw [Finset.mul_sum,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro A hA
      rw [weightOn_absent b hi (Finset.mem_powerset.mp hA)]
      ring
    · apply Finset.sum_congr rfl
      intro A hA
      rw [weightOn_present b hi (Finset.mem_powerset.mp hA)]
      ring
  · intro A hA B hB he
    have hiA : i∉A := fun h => hi ((Finset.mem_powerset.mp hA) h)
    have hiB : i∉B := fun h => hi ((Finset.mem_powerset.mp hB) h)
    have h := congrArg (fun C : Finset α => C.erase i) he
    simpa only [Finset.erase_insert hiA,Finset.erase_insert hiB] using h

theorem bernoulliAverage_congr (b : α → ℝ) (S : Finset α) {F G : Finset α → ℝ}
    (h : ∀ A⊆S, F A=G A) : bernoulliAverage b S F=bernoulliAverage b S G := by
  apply Finset.sum_congr rfl
  intro A hA
  rw [h A (Finset.mem_powerset.mp hA)]

theorem bernoulliAverage_add (b : α → ℝ) (S : Finset α) (F G : Finset α → ℝ) :
    bernoulliAverage b S (fun A => F A+G A)=bernoulliAverage b S F+bernoulliAverage b S G := by
  simp only [bernoulliAverage,mul_add,Finset.sum_add_distrib]

theorem bernoulliAverage_const_mul (b : α → ℝ) (S : Finset α)
    (c : ℝ) (F : Finset α → ℝ) :
    bernoulliAverage b S (fun A => c*F A)=c*bernoulliAverage b S F := by
  unfold bernoulliAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  ring

theorem bernoulliAverage_const (b : α → ℝ) (S : Finset α) (c : ℝ) :
    bernoulliAverage b S (fun _ => c)=c := by
  induction S using Finset.induction_on with
  | empty => exact bernoulliAverage_empty b _
  | @insert i S hi ih =>
    rw [bernoulliAverage_insert b hi]
    change (1-b i)*bernoulliAverage b S (fun _ => c)+b i*bernoulliAverage b S (fun _ => c)=c
    rw [ih]
    ring

theorem weightOn_nonneg (b : α → ℝ) {S A : Finset α} (hA : A⊆S)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) : 0 ≤ weightOn b S A := by
  unfold weightOn
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i hi => (hb i (hA hi)).1)
  · exact Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hb i (Finset.mem_sdiff.mp hi).1).2)

theorem bernoulliAverage_nonneg (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) (F : Finset α → ℝ) (hF : ∀ A⊆S, 0 ≤ F A) :
    0 ≤ bernoulliAverage b S F := by
  apply Finset.sum_nonneg
  intro A hA
  have hAS := Finset.mem_powerset.mp hA
  exact mul_nonneg (weightOn_nonneg b hAS hb) (hF A hAS)

theorem bernoulliAverage_mono (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1) {F G : Finset α → ℝ} (hFG : ∀ A⊆S, F A≤G A) :
    bernoulliAverage b S F ≤ bernoulliAverage b S G := by
  apply Finset.sum_le_sum
  intro A hA
  have hAS := Finset.mem_powerset.mp hA
  exact mul_le_mul_of_nonneg_left (hFG A hAS) (weightOn_nonneg b hAS hb)

theorem fairAverage_insert {S : Finset α} {i : α} (hi : i∉S) (F : Finset α → ℝ) :
    fairAverage (insert i S) F=(1/2 : ℝ)*fairAverage S F+
      (1/2 : ℝ)*fairAverage S (fun A => F (insert i A)) := by
  unfold fairAverage
  rw [bernoulliAverage_insert _ hi]
  norm_num

theorem activation_coupling (b : α → ℝ) (S : Finset α) (F : Finset α → ℝ) :
    bernoulliAverage (fun i => 2*b i) S (fun A => fairAverage A F)=bernoulliAverage b S F := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp [bernoulliAverage_empty,fairAverage]
  | @insert i S hi ih =>
    rw [bernoulliAverage_insert _ hi]
    have he : bernoulliAverage (fun j => 2*b j) S (fun A => fairAverage (insert i A) F)=
        (1/2 : ℝ)*bernoulliAverage (fun j => 2*b j) S (fun A => fairAverage A F)+
        (1/2 : ℝ)*bernoulliAverage (fun j => 2*b j) S (fun A => fairAverage A (fun B => F (insert i B))) := by
      rw [← bernoulliAverage_const_mul,← bernoulliAverage_const_mul,← bernoulliAverage_add]
      apply bernoulliAverage_congr
      intro A hA
      exact fairAverage_insert (fun h => hi (hA h)) F
    rw [he,ih F,ih (fun A => F (insert i A)),bernoulliAverage_insert b hi]
    ring

theorem weightOn_fair {S A : Finset α} (hA : A⊆S) :
    weightOn (fun _ : α => (1/2 : ℝ)) S A=(1/2 : ℝ)^S.card := by
  unfold weightOn
  norm_num only [show (1 : ℝ)-1/2=1/2 by norm_num,Finset.prod_const]
  have hc := Finset.card_sdiff_add_card_eq_card hA
  rw [← pow_add]
  congr 1
  omega

theorem fairAverage_uniform (S : Finset α) (F : Finset α → ℝ) :
    fairAverage S F=(∑ A ∈ S.powerset, F A)/(2 : ℝ)^S.card := by
  unfold fairAverage bernoulliAverage
  have he : (∑ A ∈ S.powerset, weightOn (fun _ : α => (1/2 : ℝ)) S A*F A)=
      (1/2 : ℝ)^S.card*∑ A ∈ S.powerset, F A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [weightOn_fair (Finset.mem_powerset.mp hA)]
  rw [he]
  simp [div_eq_mul_inv,mul_comm]

end NField.Alignment.CollisionBernoulliProduct
