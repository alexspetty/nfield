/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliActivationFinite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite conditional activation mixtures

Finite independent auxiliary coordinates are averaged separately from the
Bernoulli indicators. The mixture identity is proved for every observable;
it is not an assumption that the constructed law equals the target law.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionFiniteActivationMixture

open scoped BigOperators Classical
open CollisionBernoulliProduct CollisionBernoulliMoments CollisionBernoulliActivationFinite

variable {ι : Type*} [Fintype ι]

def productWeight {β : ι → Type*} (w : ∀ i, β i → ℝ) (x : ∀ i, β i) : ℝ :=
  ∏ i, w i (x i)

def productAverage {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (F : (∀ i, β i) → ℝ) : ℝ :=
  ∑ x, productWeight w x*F x

def select {β γ : ι → Type*} (lo hi : ∀ i, γ i → β i)
    (z : ∀ i, γ i) (A : Finset ι) : ∀ i, β i :=
  fun i => if i∈A then hi i (z i) else lo i (z i)

theorem productWeight_nonneg {β : ι → Type*} (w : ∀ i, β i → ℝ)
    (hw : ∀ i x, 0≤w i x) (x : ∀ i, β i) : 0≤productWeight w x :=
  Finset.prod_nonneg (fun i _ => hw i (x i))

theorem productWeight_sum {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (hw : ∀ i, ∑ x, w i x=1) :
    ∑ x, productWeight w x=1 := by
  change (∑ x : ∀ i, β i, ∏ i, w i (x i))=1
  rw [← Fintype.prod_sum]
  simp only [hw,Finset.prod_const_one]

theorem productAverage_const {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (hw : ∀ i, ∑ x, w i x=1) (c : ℝ) :
    productAverage w (fun _ => c)=c := by
  rw [productAverage,← Finset.sum_mul,productWeight_sum w hw,one_mul]

theorem productAverage_mono {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (hw : ∀ i x, 0≤w i x)
    {F G : (∀ i, β i) → ℝ} (hFG : ∀ x, F x≤G x) :
    productAverage w F≤productAverage w G :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hFG x) (productWeight_nonneg w hw x))

omit [Fintype ι] in
theorem bernoulli_product_expectation (b f g : ι → ℝ) (S : Finset ι) :
    bernoulliAverage b S (fun A => ∏ i∈S, if i∈A then f i else g i)=
      ∏ i∈S, (b i*f i+(1-b i)*g i) := by
  induction S using Finset.induction_on with
  | empty => simp [bernoulliAverage_empty]
  | @insert i S hi ih =>
    rw [bernoulliAverage_insert b hi,Finset.prod_insert hi]
    have hlo : bernoulliAverage b S (fun A => ∏ j∈insert i S, if j∈A then f j else g j)=
        g i*bernoulliAverage b S (fun A => ∏ j∈S, if j∈A then f j else g j) := by
      rw [← bernoulliAverage_const_mul]
      apply bernoulliAverage_congr
      intro A hA
      rw [Finset.prod_insert hi,if_neg (fun h => hi (hA h))]
    have hhi : bernoulliAverage b S
        (fun A => ∏ j∈insert i S, if j∈insert i A then f j else g j)=
        f i*bernoulliAverage b S (fun A => ∏ j∈S, if j∈A then f j else g j) := by
      rw [← bernoulliAverage_const_mul]
      apply bernoulliAverage_congr
      intro A _
      rw [Finset.prod_insert hi,if_pos (Finset.mem_insert_self i A)]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j≠i := by intro he; exact hi (he ▸ hj)
      simp only [Finset.mem_insert, hji,false_or]
    rw [hlo,hhi,ih]
    ring

theorem product_eq_indicator {β : ι → Type*} (x y : ∀ i, β i) :
    (∏ i, if x i=y i then (1 : ℝ) else 0)=if x=y then 1 else 0 := by
  by_cases h : x=y
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem selected_atom_expectation {β γ : ι → Type*}
    (b : ι → ℝ) (lo hi : ∀ i, γ i → β i) (z : ∀ i, γ i) (x : ∀ i, β i) :
    bernoulliAverage b Finset.univ (fun A => if select lo hi z A=x then 1 else 0)=
      ∏ i, (b i*(if hi i (z i)=x i then 1 else 0)+
        (1-b i)*(if lo i (z i)=x i then 1 else 0)) := by
  rw [← bernoulli_product_expectation b
    (fun i => if hi i (z i)=x i then 1 else 0)
    (fun i => if lo i (z i)=x i then 1 else 0) Finset.univ]
  apply bernoulliAverage_congr
  intro A _
  rw [← product_eq_indicator (select lo hi z A) x]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i∈A <;> simp [select,h]


theorem productAverage_const_mul {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (c : ℝ) (F : (∀ i, β i) → ℝ) :
    productAverage w (fun x => c*F x)=c*productAverage w F := by
  unfold productAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem productAverage_sum {β : ι → Type*} [∀ i, Fintype (β i)] {κ : Type*}
    (w : ∀ i, β i → ℝ) (s : Finset κ) (F : κ → (∀ i, β i) → ℝ) :
    productAverage w (fun x => ∑ j∈s, F j x)=∑ j∈s, productAverage w (F j) := by
  unfold productAverage
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype ι] in
theorem bernoulliAverage_sum {κ : Type*} (b : ι → ℝ) (S : Finset ι)
    (s : Finset κ) (F : κ → Finset ι → ℝ) :
    bernoulliAverage b S (fun A => ∑ j∈s, F j A)=∑ j∈s, bernoulliAverage b S (F j) := by
  unfold bernoulliAverage
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem conditional_mixture_atom {β γ : ι → Type*} [∀ i, Fintype (γ i)]
    (b : ι → ℝ) (q : ∀ i, γ i → ℝ) (lo hi : ∀ i, γ i → β i) (x : ∀ i, β i) :
    productAverage q (fun z => bernoulliAverage b Finset.univ
      (fun A => if select lo hi z A=x then 1 else 0))=
      ∏ i, ∑ z, q i z*(b i*(if hi i z=x i then 1 else 0)+
        (1-b i)*(if lo i z=x i then 1 else 0)) := by
  unfold productAverage
  simp_rw [selected_atom_expectation]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (Finset.prod_mul_distrib).symm

theorem conditional_mixture_observable {β γ : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
    (b : ι → ℝ) (q : ∀ i, γ i → ℝ) (lo hi : ∀ i, γ i → β i)
    (F : (∀ i, β i) → ℝ) :
    productAverage q (fun z => bernoulliAverage b Finset.univ
      (fun A => F (select lo hi z A)))=
      productAverage (fun i x => ∑ z, q i z*(b i*(if hi i z=x then 1 else 0)+
        (1-b i)*(if lo i z=x then 1 else 0))) F := by
  have he (z : ∀ i, γ i) (A : Finset ι) :
      F (select lo hi z A)=∑ x : ∀ i, β i, F x*(if select lo hi z A=x then 1 else 0) := by
    simp
  simp_rw [he,bernoulliAverage_sum,productAverage_sum,
    bernoulliAverage_const_mul,productAverage_const_mul,conditional_mixture_atom]
  unfold productAverage productWeight
  apply Finset.sum_congr rfl
  intro x _
  ring


theorem conditional_activation_bound {β γ : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
    (b : ι → ℝ) (q : ∀ i, γ i → ℝ) (lo hi : ∀ i, γ i → β i)
    (hb : ∀ i, 0≤b i ∧ b i≤1/2) (hq : ∀ i z, 0≤q i z)
    (hqn : ∀ i, ∑ z, q i z=1) (F : (∀ i, β i) → ℝ)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ z s i, i∉s → F (select lo hi z s)+a≤F (select lo hi z (insert i s))) :
    productAverage (fun i x => ∑ z, q i z*(b i*(if hi i z=x then 1 else 0)+
      (1-b i)*(if lo i z=x then 1 else 0)))
      (fun x => if F x∈Set.Icc u v then 1 else 0)≤
        20/Real.sqrt (1+∑ i, b i) := by
  rw [← conditional_mixture_observable b q lo hi]
  calc
    _ ≤ productAverage q (fun _ => 20/Real.sqrt (1+∑ i, b i)) := by
      apply productAverage_mono q hq
      intro z
      exact bernoulli_product_short_interval_bound b Finset.univ (fun i _ => hb i)
        (fun A => F (select lo hi z A)) ha huv (hF z)
    _ = _ := productAverage_const q hqn _

omit [Fintype ι] in
theorem subtype_indicator_sum {α : Type*} [Fintype α] (P : α → Prop) (x : α) :
    (∑ y : {x // P x}, if (y : α)=x then (1 : ℝ) else 0)=if P x then 1 else 0 := by
  by_cases hx : P x
  · rw [if_pos hx]
    calc
      _ = ∑ y : {x // P x}, if y=⟨x,hx⟩ then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [Subtype.ext_iff]
      _ = 1 := by simp
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (show (y : α)≠x from fun he => hx (he ▸ y.property))]


def conditionalPair {α : Type*} (P : α → Prop) := {x // ¬P x} × {x // P x}

def conditionalPairWeight {α : Type*} [Fintype α] (P : α → Prop)
    (_ : conditionalPair P) : ℝ :=
  1/((Fintype.card {x // ¬P x} : ℝ)*Fintype.card {x // P x})

def hitRatio {α : Type*} [Fintype α] (P : α → Prop) : ℝ :=
  (Fintype.card {x // P x} : ℝ)/Fintype.card α

instance {α : Type*} [Fintype α] (P : α → Prop) : Fintype (conditionalPair P) :=
  inferInstanceAs (Fintype ({x // ¬P x} × {x // P x}))

theorem conditionalPairWeight_nonneg {α : Type*} [Fintype α]
    (P : α → Prop) (z : conditionalPair P) : 0≤conditionalPairWeight P z := by
  unfold conditionalPairWeight
  positivity

theorem conditionalPairWeight_sum {α : Type*} [Fintype α] (P : α → Prop)
    (h0 : Nonempty {x // ¬P x}) (h1 : Nonempty {x // P x}) :
    ∑ z : conditionalPair P, conditionalPairWeight P z=1 := by
  letI := h0
  letI := h1
  have hc0 : (Fintype.card {x // ¬P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc1 : (Fintype.card {x // P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [conditionalPairWeight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change ((Fintype.card ({x // ¬P x} × {x // P x}) : ℕ) : ℝ)*_=1
  rw [Fintype.card_prod,Nat.cast_mul]
  field_simp

theorem conditionalPair_active_marginal {α : Type*} [Fintype α] (P : α → Prop)
    (h0 : Nonempty {x // ¬P x}) (h1 : Nonempty {x // P x}) (x : α) :
    (∑ z : conditionalPair P, conditionalPairWeight P z*
      (if z.2.val=x then (1 : ℝ) else 0))=
      (if P x then 1 else 0)/(Fintype.card {x // P x} : ℝ) := by
  letI := h0
  letI := h1
  have hc0 : (Fintype.card {x // ¬P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc1 : (Fintype.card {x // P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  change (∑ z : {x // ¬P x} × {x // P x}, _)=_
  rw [Fintype.sum_prod_type]
  simp only [conditionalPairWeight,← Finset.mul_sum,subtype_indicator_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem conditionalPair_inactive_marginal {α : Type*} [Fintype α] (P : α → Prop)
    (h0 : Nonempty {x // ¬P x}) (h1 : Nonempty {x // P x}) (x : α) :
    (∑ z : conditionalPair P, conditionalPairWeight P z*
      (if z.1.val=x then (1 : ℝ) else 0))=
      (if ¬P x then 1 else 0)/(Fintype.card {x // ¬P x} : ℝ) := by
  letI := h0
  letI := h1
  have hc0 : (Fintype.card {x // ¬P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc1 : (Fintype.card {x // P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  change (∑ z : {x // ¬P x} × {x // P x}, _)=_
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  change (∑ _z1 : {y // P y}, ∑ z0 : {y // ¬P y},
    (1/((Fintype.card {y // ¬P y} : ℝ)*Fintype.card {y // P y}))*
      (if z0.val=x then (1 : ℝ) else 0))=_
  have hs : (∑ z0 : {y // ¬P y}, if z0.val=x then (1 : ℝ) else 0)=
      if ¬P x then 1 else 0 := by
    convert subtype_indicator_sum (fun y => ¬P y) x using 1 <;> congr 1
    ext y
    simp
  simp_rw [← Finset.mul_sum]
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem conditionalPair_mixture_uniform {α : Type*} [Fintype α] (P : α → Prop)
    (h0 : Nonempty {x // ¬P x}) (h1 : Nonempty {x // P x}) (x : α) :
    (∑ z : conditionalPair P, conditionalPairWeight P z*
      (hitRatio P*(if z.2.val=x then 1 else 0)+
        (1-hitRatio P)*(if z.1.val=x then 1 else 0)))=1/(Fintype.card α : ℝ) := by
  letI := h0
  letI := h1
  letI : Nonempty α := ⟨Classical.choice h0 |>.val⟩
  have hc0 : (Fintype.card {x // ¬P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc1 : (Fintype.card {x // P x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card α : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card {x // ¬P x} : ℝ)+(Fintype.card {x // P x} : ℝ)=Fintype.card α := by
    exact_mod_cast (show Fintype.card {x // ¬P x}+Fintype.card {x // P x}=Fintype.card α by
      rw [Fintype.card_subtype_compl]
      exact Nat.sub_add_cancel (Fintype.card_subtype_le P))
  have he : (∑ z : conditionalPair P, conditionalPairWeight P z*
      (hitRatio P*(if z.2.val=x then 1 else 0)+
        (1-hitRatio P)*(if z.1.val=x then 1 else 0)))=
      hitRatio P*(∑ z : conditionalPair P, conditionalPairWeight P z*
        (if z.2.val=x then 1 else 0))+
      (1-hitRatio P)*(∑ z : conditionalPair P, conditionalPairWeight P z*
        (if z.1.val=x then 1 else 0)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he,conditionalPair_active_marginal P h0 h1 x,
    conditionalPair_inactive_marginal P h0 h1 x]
  unfold hitRatio
  by_cases hx : P x
  · simp only [hx,not_true_eq_false,if_true,if_false,mul_zero,zero_div,add_zero]
    field_simp
  · simp only [hx,not_false_eq_true,if_true,if_false,mul_zero,zero_div,zero_add]
    field_simp
    nlinarith

theorem uniform_productAverage {β : ι → Type*} [∀ i, Fintype (β i)]
    (F : (∀ i, β i) → ℝ) :
    productAverage (fun i _ => 1/(Fintype.card (β i) : ℝ)) F=
      (∑ x, F x)/(Fintype.card (∀ i, β i) : ℝ) := by
  unfold productAverage productWeight
  simp only [Finset.prod_div_distrib,Finset.prod_const_one,← Nat.cast_prod,Fintype.card_pi]
  rw [← Finset.mul_sum]
  ring

theorem uniform_conditional_mixture {β : ι → Type*} [∀ i, Fintype (β i)]
    (P : ∀ i, β i → Prop) (h0 : ∀ i, Nonempty {x // ¬P i x})
    (h1 : ∀ i, Nonempty {x // P i x}) (F : (∀ i, β i) → ℝ) :
    productAverage (fun i => conditionalPairWeight (P i))
      (fun z => bernoulliAverage (fun i => hitRatio (P i)) Finset.univ
        (fun A => F (select (fun _ z => z.1.val) (fun _ z => z.2.val) z A)))=
        (∑ x, F x)/(Fintype.card (∀ i, β i) : ℝ) := by
  rw [conditional_mixture_observable]
  simp_rw [conditionalPair_mixture_uniform _ (h0 _) (h1 _)]
  exact uniform_productAverage F

theorem uniform_conditional_activation_bound {β : ι → Type*} [∀ i, Fintype (β i)]
    (P : ∀ i, β i → Prop) (h0 : ∀ i, Nonempty {x // ¬P i x})
    (h1 : ∀ i, Nonempty {x // P i x}) (hb : ∀ i, hitRatio (P i)≤1/2)
    (F : (∀ i, β i) → ℝ) {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ (z : ∀ i, conditionalPair (P i)) s i, i∉s →
      F (select (fun _ z => z.1.val) (fun _ z => z.2.val) z s)+a≤
      F (select (fun _ z => z.1.val) (fun _ z => z.2.val) z (insert i s))) :
    (∑ x, if F x∈Set.Icc u v then (1 : ℝ) else 0)/(Fintype.card (∀ i, β i) : ℝ)≤
      20/Real.sqrt (1+∑ i, hitRatio (P i)) := by
  rw [← uniform_conditional_mixture P h0 h1]
  calc
    _ ≤ productAverage (fun i => conditionalPairWeight (P i))
        (fun _ => 20/Real.sqrt (1+∑ i, hitRatio (P i))) := by
      apply productAverage_mono _ (fun i => conditionalPairWeight_nonneg (P i))
      intro z
      apply bernoulli_product_short_interval_bound _ Finset.univ _ _ ha huv (hF z)
      intro i _
      exact ⟨by unfold hitRatio; positivity, hb i⟩
    _ = _ := productAverage_const _ (fun i => conditionalPairWeight_sum _ (h0 i) (h1 i)) _


theorem hitRatio_uniform_event {α : Type*} [Fintype α] (P : α → Prop) :
    hitRatio P=(∑ x : α, if P x then (1 : ℝ) else 0)/(Fintype.card α : ℝ) := by
  simp only [hitRatio,Fintype.card_subtype,Finset.sum_boole]

omit [Fintype ι] in
theorem select_insert_update {β γ : ι → Type*} (lo hi : ∀ i, γ i → β i)
    (z : ∀ i, γ i) (S : Finset ι) (i : ι) :
    select lo hi z (insert i S)=Function.update (select lo hi z S) i (hi i (z i)) := by
  funext j
  by_cases hji : j=i
  · subst j
    simp [select]
  · simp [select,hji]

theorem uniform_coordinate_activation_bound {β : ι → Type*} [∀ i, Fintype (β i)]
    (P : ∀ i, β i → Prop) (h0 : ∀ i, Nonempty {x // ¬P i x})
    (h1 : ∀ i, Nonempty {x // P i x}) (hb : ∀ i, hitRatio (P i)≤1/2)
    (F : (∀ i, β i) → ℝ) {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ (x : ∀ i, β i) i y, ¬P i (x i) → P i y → F x+a≤F (Function.update x i y)) :
    (∑ x, if F x∈Set.Icc u v then (1 : ℝ) else 0)/(Fintype.card (∀ i, β i) : ℝ)≤
      20/Real.sqrt (1+∑ i, hitRatio (P i)) := by
  apply uniform_conditional_activation_bound P h0 h1 hb F ha huv
  intro z S i hi
  rw [select_insert_update]
  apply hF _ i _
  · simpa only [select,if_neg hi] using (z i).1.property
  · exact (z i).2.property

end NField.Alignment.CollisionFiniteActivationMixture
