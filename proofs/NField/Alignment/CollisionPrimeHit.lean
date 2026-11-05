/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResidueIndependence
import NField.Alignment.CollisionBernoulliActivation

/-!
# Exact prime-hit events under the actual Haar measure

The finite residue calculation works for every positive modulus. Distinct
prime coordinates are a special case of the proved coprime independence.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimeHit

open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
open ProfiniteRemainderMeasure CollisionResidueIndependence

def hitResidues (p h : ℕ) : Finset (ZMod p) :=
  (Finset.range h).image (fun j : ℕ => -((j : ZMod p)+1))

def hitCoordinate (p h : ℕ) [NeZero p] (x : Phase) : Bool :=
  decide ((residueHom p x).toAdd∈hitResidues p h)

theorem hitResidues_card {p h : ℕ} [NeZero p] (hh : h≤p) :
    (hitResidues p h).card=h := by
  rw [hitResidues,Finset.card_image_of_injOn,Finset.card_range]
  intro i hi j hj he
  have he' : (i : ZMod p)=(j : ZMod p) := add_right_cancel (neg_injective he)
  have hv := congrArg ZMod.val he'
  simpa only [ZMod.val_natCast,
    Nat.mod_eq_of_lt ((Finset.mem_range.mp hi).trans_le hh),
    Nat.mod_eq_of_lt ((Finset.mem_range.mp hj).trans_le hh)] using hv

theorem hitCoordinate_iff {p h : ℕ} [NeZero p] (x : Phase) :
    hitCoordinate p h x=true ↔
      ∃ j<h, (residueHom p x).toAdd+((j : ZMod p)+1)=0 := by
  simp only [hitCoordinate,decide_eq_true_eq,hitResidues,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by rw [← he]; abel⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,(eq_neg_of_add_eq_zero_left he).symm⟩

theorem hitCoordinate_measurable (p h : ℕ) [NeZero p] : Measurable (hitCoordinate p h) :=
  (measurable_of_countable (f := fun r : Multiplicative (ZMod p) =>
    decide (r.toAdd∈hitResidues p h))).comp (residueHom p).continuous_toFun.measurable

theorem hitCoordinate_probability {p h : ℕ} [NeZero p] (hh : h≤p) :
    phaseHaar.real {x | hitCoordinate p h x=true}=(h : ℝ)/(p : ℝ) := by
  have hmeas : MeasurableSet {x | hitCoordinate p h x=true} :=
    (measurableSet_singleton true).preimage (hitCoordinate_measurable p h)
  rw [← integral_indicator_one hmeas]
  have he : ({x | hitCoordinate p h x=true}).indicator (1 : Phase → ℝ)=
      fun x => if (residueHom p x).toAdd∈hitResidues p h then 1 else 0 := by
    funext x
    simp [hitCoordinate,Set.indicator_apply]
  rw [he]
  have hm := residue_measurePreserving p
  have hi := integral_map_of_stronglyMeasurable (μ := phaseHaar) hm.measurable
    (f := fun r : Multiplicative (ZMod p) => if r.toAdd∈hitResidues p h then (1 : ℝ) else 0)
    continuous_of_discreteTopology.stronglyMeasurable
  rw [hm.map_eq] at hi
  rw [← hi,finite_haar_integral]
  have hs := Equiv.sum_comp (@Multiplicative.toAdd (ZMod p))
    (fun j => if j∈hitResidues p h then (1 : ℝ) else 0)
  rw [hs]
  simp only [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter,
    Fintype.card_multiplicative,ZMod.card,hitResidues_card hh]

theorem hit_location_unique {p h : ℕ} [NeZero p] (hh : h≤p)
    (x : Phase) {i j : ℕ} (hi : i<h) (hj : j<h)
    (hxi : (residueHom p x).toAdd+((i : ZMod p)+1)=0)
    (hxj : (residueHom p x).toAdd+((j : ZMod p)+1)=0) : i=j := by
  have he : (i : ZMod p)=(j : ZMod p) :=
    add_right_cancel (add_left_cancel (hxi.trans hxj.symm))
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (hi.trans_le hh),
    Nat.mod_eq_of_lt (hj.trans_le hh)] using hv

theorem hit_coordinates_independent {ι : Type*} [Fintype ι] (p : ι → ℕ)
    [∀ i, NeZero (p i)] (h : ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    iIndepFun (fun i => hitCoordinate (p i) h) phaseHaar := by
  exact (coprime_residue_independence p hc).comp
    (fun i r => decide (r.toAdd∈hitResidues (p i) h))
    (fun _ => measurable_of_countable _)

theorem hit_probability_at_most_half {p h : ℕ} [NeZero p] (hh : 2*h≤p) :
    phaseHaar.real {x | hitCoordinate p h x=true} ≤ 1/2 := by
  rw [hitCoordinate_probability (by omega : h≤p)]
  have hp : (0 : ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (div_le_iff₀ hp).mpr
  have hr : 2*(h : ℝ)≤p := by exact_mod_cast hh
  linarith

theorem hitCoordinate_zero (p : ℕ) [NeZero p] (x : Phase) :
    hitCoordinate p 0 x=false := by simp [hitCoordinate,hitResidues]

theorem hitCoordinate_integer (p h : ℕ) [NeZero p] (z : ℤ) :
    hitCoordinate p h (integerPhase z)=true ↔
      ∃ j<h, (p : ℤ)∣z+(j : ℤ)+1 := by
  rw [hitCoordinate_iff]
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  have he : (residueHom p (integerPhase z)).toAdd+((j : ZMod p)+1)=
      ((z+(j : ℤ)+1 : ℤ) : ZMod p) := by
    rw [residue_integer]
    push_cast
    ring
  rw [he,ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem prime_hit_law {ι : Type*} [Fintype ι] (p : ι → ℕ)
    [∀ i, NeZero (p i)] (hp : ∀ i, (p i).Prime) (hi : Function.Injective p)
    (h : ℕ) (hh : ∀ i, 2*h≤p i) :
    iIndepFun (fun i => hitCoordinate (p i) h) phaseHaar ∧
      ∀ i, phaseHaar.real {x | hitCoordinate (p i) h x=true}=(h : ℝ)/(p i : ℝ) ∧
        phaseHaar.real {x | hitCoordinate (p i) h x=true} ≤ 1/2 := by
  refine ⟨hit_coordinates_independent p h ?_,?_⟩
  · intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun he => hij (hi he))
  · intro i
    exact ⟨hitCoordinate_probability (by have := hh i; omega),hit_probability_at_most_half (hh i)⟩

end NField.Alignment.CollisionPrimeHit
