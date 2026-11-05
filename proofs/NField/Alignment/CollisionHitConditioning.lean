/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimeHit

/-!
# Conditional hit locations and positive valuation probabilities

These are ratios of actual Haar event measures. Divisibility nesting is
proved from the compatible quotient maps, before subtracting measures.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHitConditioning

open scoped BigOperators Classical
open MeasureTheory
open ProfiniteRemainderMeasure CollisionResetIntegrability CollisionPotentialCoboundary
open CollisionPrimeHit

def locationSet (k j : ℕ) : Set Phase :=
  translate ((j : ℤ)+1) ⁻¹' resetSet k

def valuationSet (p e j : ℕ) : Set Phase :=
  locationSet (p^e) j \ locationSet (p^(e+1)) j

theorem locationSet_measurable (k j : ℕ) : MeasurableSet (locationSet k j) :=
  (resetSet_measurable k).preimage (translate_measurePreserving _).measurable

theorem locationSet_probability {k : ℕ} (hk : 0<k) (j : ℕ) :
    phaseHaar.real (locationSet k j)=1/(k : ℝ) := by
  have hm := translate_measurePreserving ((j : ℤ)+1)
  have he := congrArg (fun μ : Measure Phase => μ (resetSet k)) hm.map_eq
  rw [Measure.map_apply hm.measurable (resetSet_measurable k)] at he
  exact (congrArg ENNReal.toReal he).trans (resetSet_measure_real hk)

theorem mem_locationSet {p : ℕ} [NeZero p] (j : ℕ) (x : Phase) :
    x∈locationSet p j ↔ (residueHom p x).toAdd+((j : ZMod p)+1)=0 := by
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  simp only [locationSet,Set.mem_preimage,resetSet,dif_pos hp,Set.mem_setOf_eq,
    residue_translate,Int.cast_add,Int.cast_natCast,Int.cast_one]
  rw [add_comm]

theorem hitCoordinate_locations {p h : ℕ} [NeZero p] (x : Phase) :
    hitCoordinate p h x=true ↔ ∃ j<h, x∈locationSet p j := by
  simp only [hitCoordinate_iff,mem_locationSet]

theorem location_given_hit {p h j : ℕ} [NeZero p] (hh : h≤p) (hj : j<h) :
    phaseHaar.real (locationSet p j ∩ {x | hitCoordinate p h x=true}) /
      phaseHaar.real {x | hitCoordinate p h x=true}=1/(h : ℝ) := by
  have hsub : locationSet p j⊆{x | hitCoordinate p h x=true} := by
    intro x hx
    exact (hitCoordinate_locations x).mpr ⟨j,hj,hx⟩
  rw [Set.inter_eq_left.mpr hsub,locationSet_probability
    (Nat.pos_of_ne_zero (NeZero.ne p)),hitCoordinate_probability hh]
  have hp : (p : ℝ)≠0 := by exact_mod_cast NeZero.ne p
  have hh0 : (h : ℝ)≠0 := by exact_mod_cast (by omega : h≠0)
  field_simp

theorem locationSet_subset_of_dvd {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (hkm : k∣m) (j : ℕ) : locationSet m j⊆locationSet k j := by
  letI : NeZero k := ⟨hk.ne'⟩
  letI : NeZero m := ⟨hm.ne'⟩
  intro x hx
  have hx' : (residueHom m (translate ((j : ℤ)+1) x)).toAdd=0 := by
    simpa only [locationSet,Set.mem_preimage,resetSet,dif_pos hm,Set.mem_setOf_eq] using hx
  simp only [locationSet,Set.mem_preimage,resetSet,dif_pos hk,Set.mem_setOf_eq,
    residue_compatible hkm,hx',map_zero]

theorem valuationSet_measurable (p e j : ℕ) : MeasurableSet (valuationSet p e j) :=
  (locationSet_measurable _ _).diff (locationSet_measurable _ _)

theorem valuationSet_probability {p : ℕ} (hp : 0<p) (e j : ℕ) :
    phaseHaar.real (valuationSet p e j)=1/(p : ℝ)^e-1/(p : ℝ)^(e+1) := by
  rw [valuationSet,measureReal_sdiff
    (locationSet_subset_of_dvd (pow_pos hp e) (pow_pos hp (e+1)) (pow_dvd_pow p (by omega)) j)
    (locationSet_measurable _ _),locationSet_probability (pow_pos hp e),
    locationSet_probability (pow_pos hp (e+1))]
  simp only [Nat.cast_pow]

theorem valuationSet_subset_location {p e : ℕ} (hp : 0<p) (he : 1≤e) (j : ℕ) :
    valuationSet p e j⊆locationSet p j := by
  have hdiv : p∣p^e := by simpa only [pow_one] using pow_dvd_pow p he
  exact Set.Subset.trans Set.sdiff_subset (locationSet_subset_of_dvd hp (pow_pos hp e) hdiv j)

theorem valuation_given_hitLocation {p e : ℕ} (hp : 1<p) (he : 1≤e) (j : ℕ) :
    phaseHaar.real (valuationSet p e j ∩ locationSet p j) /
      phaseHaar.real (locationSet p j)=((p : ℝ)-1)/(p : ℝ)^e := by
  have hp0 : 0<p := by omega
  rw [Set.inter_eq_left.mpr (valuationSet_subset_location hp0 he j),
    valuationSet_probability hp0,locationSet_probability hp0,pow_succ]
  have hpR : (p : ℝ)≠0 := by exact_mod_cast hp0.ne'
  field_simp

theorem positive_valuation_mass_one {p : ℕ} (hp : 1<p) :
    (∑' e : ℕ, ((p : ℝ)-1)/(p : ℝ)^(e+1))=1 := by
  have hpR : (1 : ℝ)<p := by exact_mod_cast hp
  have hp0 : (0 : ℝ)<p := by linarith
  have hg : ‖(1/(p : ℝ))‖<1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (div_lt_one hp0).mpr hpR
  have hs := (hasSum_geometric_of_norm_lt_one hg).mul_left (((p : ℝ)-1)/p)
  have hterm (e : ℕ) : ((p : ℝ)-1)/p*(1/(p : ℝ))^e=((p : ℝ)-1)/(p : ℝ)^(e+1) := by
    rw [pow_succ,div_pow,one_pow]
    ring
  simp_rw [hterm] at hs
  have he : ((p : ℝ)-1)/p*(1-1/(p : ℝ))⁻¹=1 := by
    field_simp [show (p : ℝ)-1≠0 by linarith]
  rw [he] at hs
  exact hs.tsum_eq

def hitValuationSet (p h e : ℕ) : Set Phase :=
  ⋃ j : Fin h, valuationSet p e j.val

theorem location_valuation_given_hit {p h e j : ℕ} [NeZero p]
    (hp : 1<p) (hh : h≤p) (he : 1≤e) (hj : j<h) :
    phaseHaar.real (valuationSet p e j ∩ {x | hitCoordinate p h x=true}) /
      phaseHaar.real {x | hitCoordinate p h x=true}=
        (1/(h : ℝ))*(((p : ℝ)-1)/(p : ℝ)^e) := by
  have hp0 : 0<p := by omega
  have hsub : valuationSet p e j⊆{x | hitCoordinate p h x=true} := by
    intro x hx
    exact (hitCoordinate_locations x).mpr ⟨j,hj,valuationSet_subset_location hp0 he j hx⟩
  rw [Set.inter_eq_left.mpr hsub,valuationSet_probability hp0,hitCoordinate_probability hh,
    pow_succ]
  have hpR : (p : ℝ)≠0 := by exact_mod_cast hp0.ne'
  have hhR : (h : ℝ)≠0 := by exact_mod_cast (by omega : h≠0)
  field_simp

theorem hitValuationSet_probability {p h e : ℕ} [NeZero p]
    (hh : h≤p) (he : 1≤e) :
    phaseHaar.real (hitValuationSet p h e)=
      (h : ℝ)*(1/(p : ℝ)^e-1/(p : ℝ)^(e+1)) := by
  have hp0 : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hd : Pairwise (fun i j : Fin h => Disjoint (valuationSet p e i.val) (valuationSet p e j.val)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi := (mem_locationSet i.val x).mp (valuationSet_subset_location hp0 he i.val hxi)
    have hj := (mem_locationSet j.val x).mp (valuationSet_subset_location hp0 he j.val hxj)
    exact hij (Fin.ext (hit_location_unique hh x i.isLt j.isLt hi hj))
  rw [hitValuationSet,measureReal_iUnion_fintype hd (fun j => valuationSet_measurable p e j.val)]
  simp only [valuationSet_probability hp0,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul]

theorem valuation_given_any_hit {p h e : ℕ} [NeZero p]
    (hp : 1<p) (hh0 : 0<h) (hh : h≤p) (he : 1≤e) :
    phaseHaar.real (hitValuationSet p h e ∩ {x | hitCoordinate p h x=true}) /
      phaseHaar.real {x | hitCoordinate p h x=true}=((p : ℝ)-1)/(p : ℝ)^e := by
  have hp0 : 0<p := by omega
  have hsub : hitValuationSet p h e⊆{x | hitCoordinate p h x=true} := by
    intro x hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    exact (hitCoordinate_locations x).mpr ⟨j.val,j.isLt,valuationSet_subset_location hp0 he j.val hj⟩
  rw [Set.inter_eq_left.mpr hsub,hitValuationSet_probability hh he,hitCoordinate_probability hh,
    pow_succ]
  have hpR : (p : ℝ)≠0 := by exact_mod_cast hp0.ne'
  have hhR : (h : ℝ)≠0 := by exact_mod_cast hh0.ne'
  field_simp

end NField.Alignment.CollisionHitConditioning
