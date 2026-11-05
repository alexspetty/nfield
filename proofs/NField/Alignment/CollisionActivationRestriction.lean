/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliProduct

/-!
# Sperner bounds on the actually active coordinate set

The ambient coordinate type need not be finite. The denominator in the
bound uses exactly the cardinality of the selected finite active set.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionActivationRestriction

open scoped BigOperators Classical
open CollisionActivationSperner CollisionBernoulliProduct
variable {α : Type*} [DecidableEq α]

theorem antichain_card_on (S : Finset α) (A : Finset (Finset α))
    (hAS : A⊆S.powerset) (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α))) :
    A.card ≤ S.card.choose (S.card/2) := by
  let e : S ↪ α := Function.Embedding.subtype (fun i => i∈S)
  let L : Finset (Finset S) := Finset.univ.filter (fun B => B.map e∈A)
  have hL : IsAntichain (· ⊆ ·) (L : Set (Finset S)) := by
    intro B hB C hC hne hBC
    exact hA (Finset.mem_filter.mp hB).2 (Finset.mem_filter.mp hC).2
      (fun he => hne (Finset.map_injective e he)) (Finset.map_subset_map.mpr hBC)
  have himage : L.image (Finset.map e)=A := by
    ext B
    constructor
    · intro hB
      obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hB
      exact (Finset.mem_filter.mp hC).2
    · intro hB
      have hBS := Finset.mem_powerset.mp (hAS hB)
      have he : (B.subtype (fun i => i∈S)).map e=B :=
        Finset.subtype_map_of_mem (fun i hi => hBS hi)
      refine Finset.mem_image.mpr ⟨B.subtype (fun i => i∈S),?_,he⟩
      simp only [L,Finset.mem_filter,Finset.mem_univ,true_and,he]
      exact hB
  have hc := Finset.card_image_of_injective L (Finset.map_injective e)
  rw [himage] at hc
  rw [hc]
  simpa only [Fintype.card_coe] using hL.sperner

theorem fair_antichain_on (S : Finset α) (A : Finset (Finset α))
    (hAS : A⊆S.powerset) (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α))) :
    fairAverage S (fun B => if B∈A then 1 else 0) ≤ 2/Real.sqrt ((S.card : ℝ)+1) := by
  rw [fairAverage_uniform]
  have he : S.powerset.filter (fun B => B∈A)=A := by
    ext B
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hAS h,h⟩⟩
  rw [Finset.sum_boole,he]
  exact (div_le_div_of_nonneg_right (by exact_mod_cast antichain_card_on S A hAS hA)
    (by positivity : (0 : ℝ)≤(2 : ℝ)^S.card)).trans (middleBinomial_probability_bound S.card)

theorem fair_short_interval_on (S : Finset α) (F : Finset α → ℝ)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    fairAverage S (fun A => if F A∈Set.Icc u v then 1 else 0) ≤
      2/Real.sqrt ((S.card : ℝ)+1) := by
  let A := S.powerset.filter (fun B => F B∈Set.Icc u v)
  have hAS : A⊆S.powerset := Finset.filter_subset _ _
  have hA : IsAntichain (· ⊆ ·) (A : Set (Finset α)) :=
    (short_interval_antichain F ha huv hF).subset (fun B hB => (Finset.mem_filter.mp hB).2)
  have he : fairAverage S (fun B => if F B∈Set.Icc u v then 1 else 0)=
      fairAverage S (fun B => if B∈A then 1 else 0) := by
    apply bernoulliAverage_congr
    intro B hB
    simp only [A,Finset.mem_filter,Finset.mem_powerset,hB,true_and]
  rw [he]
  exact fair_antichain_on S A hAS hA

end NField.Alignment.CollisionActivationRestriction
