/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliActivationFinite

/-!
# Exact finite certificates for the activation interface

The computable conditional bound is the actual mixture of middle-binomial
ratios. The squared universal bound avoids a numerical square root.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionBernoulliCertificate

open scoped BigOperators Classical
open CollisionActivationSperner CollisionActivationRestriction
open CollisionBernoulliProduct CollisionBernoulliMoments CollisionBernoulliActivationFinite
variable {α : Type*} [DecidableEq α]

def spernerMixture (b : α → ℝ) (S : Finset α) : ℝ :=
  bernoulliAverage (fun i => 2*b i) S
    (fun A => (A.card.choose (A.card/2) : ℝ)/(2 : ℝ)^A.card)

theorem fair_short_interval_sperner (S : Finset α) (F : Finset α → ℝ)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    fairAverage S (fun A => if F A∈Set.Icc u v then 1 else 0) ≤
      (S.card.choose (S.card/2) : ℝ)/(2 : ℝ)^S.card := by
  rw [fairAverage_uniform,Finset.sum_boole]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast antichain_card_on S _ (Finset.filter_subset _ _)
    ((short_interval_antichain F ha huv hF).subset
      (fun B hB => (Finset.mem_filter.mp hB).2))

theorem bernoulli_product_sperner (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1/2) (F : Finset α → ℝ)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    bernoulliAverage b S (fun A => if F A∈Set.Icc u v then 1 else 0) ≤
      spernerMixture b S := by
  rw [← activation_coupling b S]
  apply bernoulliAverage_mono
  · intro i hi
    obtain ⟨h0,h1⟩ := hb i hi
    constructor <;> linarith
  · intro A _
    exact fair_short_interval_sperner A F ha huv hF

theorem bernoulli_product_squared_bound (b : α → ℝ) (S : Finset α)
    (hb : ∀ i∈S, 0 ≤ b i ∧ b i ≤ 1/2) (F : Finset α → ℝ)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hF : ∀ s i, i∉s → F s+a ≤ F (insert i s)) :
    (bernoulliAverage b S (fun A => if F A∈Set.Icc u v then 1 else 0))^2 ≤
      400/(1+countMean b S) := by
  let p := bernoulliAverage b S (fun A => if F A∈Set.Icc u v then 1 else 0)
  have hm := countMean_nonneg b S (fun i hi => (hb i hi).1)
  have hp : 0≤p := bernoulliAverage_nonneg b S
    (fun i hi => ⟨(hb i hi).1,(hb i hi).2.trans (by norm_num)⟩) _
    (fun _ _ => by split_ifs <;> norm_num)
  have hroot : 0<Real.sqrt (1+countMean b S) := Real.sqrt_pos.mpr (by positivity)
  have h := (le_div_iff₀ hroot).mp (bernoulli_product_short_interval_bound b S hb F ha huv hF)
  change p*Real.sqrt (1+countMean b S) ≤ 20 at h
  have hs : (p*Real.sqrt (1+countMean b S))^2 ≤ 400 := by
    nlinarith [mul_nonneg (show 0≤20-p*Real.sqrt (1+countMean b S) by linarith)
      (show 0≤20+p*Real.sqrt (1+countMean b S) by positivity)]
  rw [mul_pow,Real.sq_sqrt (by positivity)] at hs
  exact (le_div_iff₀ (by positivity : 0<1+countMean b S)).mpr hs

end NField.Alignment.CollisionBernoulliCertificate
