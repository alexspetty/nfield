/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionActivationCRT
import NField.Alignment.CollisionActivationSubfamily

/-!
# Prime activation on actual finite Haar quotients

The finite conditional mixture has the h/p biases of the actual Haar
prime hits, independent of the size of the prime-power quotient.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionActivationQuotient

open scoped BigOperators Classical
open MeasureTheory ProfiniteRemainderMeasure CollisionPrimeHit
open CollisionFiniteActivationMixture CollisionActivationCRT CollisionActivationArithmetic
open CollisionActivationSubfamily

def quotientHit (p k h : ℕ) (hpk : p∣k) (r : Multiplicative (ZMod k)) : Prop :=
  ZMod.castHom hpk (ZMod p) r.toAdd∈hitResidues p h

theorem quotientHit_phase {p k h : ℕ} [NeZero p] [NeZero k] (hpk : p∣k) (x : Phase) :
    quotientHit p k h hpk (residueHom k x) ↔ hitCoordinate p h x=true := by
  unfold quotientHit hitCoordinate
  rw [← residue_compatible hpk]
  simp only [decide_eq_true_eq]

theorem quotientHit_ratio {p k h : ℕ} [NeZero p] [NeZero k] (hpk : p∣k) (hh : h≤p) :
    hitRatio (quotientHit p k h hpk)=(h : ℝ)/(p : ℝ) := by
  have hm := residue_measurePreserving k
  have hi := integral_map_of_stronglyMeasurable (μ := phaseHaar) hm.measurable
    (f := fun r : Multiplicative (ZMod k) => if quotientHit p k h hpk r then (1 : ℝ) else 0)
    continuous_of_discreteTopology.stronglyMeasurable
  rw [hm.map_eq,finite_haar_integral] at hi
  have hmeas : MeasurableSet {x | hitCoordinate p h x=true} :=
    (measurableSet_singleton true).preimage (hitCoordinate_measurable p h)
  calc
    _ = (∑ r : Multiplicative (ZMod k), if quotientHit p k h hpk r then (1 : ℝ) else 0)/
        (Fintype.card (Multiplicative (ZMod k)) : ℝ) := hitRatio_uniform_event _
    _ = ∫ x, if hitCoordinate p h x=true then (1 : ℝ) else 0 ∂phaseHaar := by
      simpa only [quotientHit_phase] using hi
    _ = phaseHaar.real {x | hitCoordinate p h x=true} := by
      rw [← integral_indicator_one hmeas]
      simp only [Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply]
    _ = _ := hitCoordinate_probability hh

theorem quotientHit_nonempty {p k h : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (hh0 : 0<h) (hh : h≤p) :
    Nonempty {r // quotientHit p k h hpk r} := by
  have hp : (0 : ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hr : 0<hitRatio (quotientHit p k h hpk) := by
    rw [quotientHit_ratio hpk hh]
    exact div_pos (by exact_mod_cast hh0) hp
  apply Fintype.card_pos_iff.mp
  by_contra hn
  have hc : Fintype.card {r // quotientHit p k h hpk r}=0 := by omega
  simp [hitRatio,hc] at hr

theorem quotientHit_complement_nonempty {p k h : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (hh : h<p) :
    Nonempty {r // ¬quotientHit p k h hpk r} := by
  have hp : (0 : ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hr : hitRatio (quotientHit p k h hpk)<1 := by
    rw [quotientHit_ratio hpk hh.le]
    apply (div_lt_one hp).mpr
    exact_mod_cast hh
  apply Fintype.card_pos_iff.mp
  by_contra hn
  have hc : Fintype.card {r // ¬quotientHit p k h hpk r}=0 := by omega
  rw [Fintype.card_subtype_compl] at hc
  have he : Fintype.card {r // quotientHit p k h hpk r}=Fintype.card (Multiplicative (ZMod k)) := by
    have := Fintype.card_subtype_le (quotientHit p k h hpk)
    omega
  simp [hitRatio,he] at hr

theorem quotientHit_representative {ι : Type*} [Fintype ι] (k : ι → ℕ)
    [∀ i, NeZero (k i)] (hc : Pairwise (fun i j => (k i).Coprime (k j)))
    {p h : ℕ} [NeZero p] (i : ι) (hpk : p∣k i)
    (r : ∀ i, Multiplicative (ZMod (k i))) :
    hitCoordinate p h (representativePhase k hc r)=true ↔ quotientHit p (k i) h hpk (r i) := by
  rw [← quotientHit_phase hpk]
  unfold quotientHit
  rw [representative_coordinate]


theorem prime_power_cutoff_concentration {ι : Type*} [Fintype ι]
    (p e : ι → ℕ) (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (he : ∀ i, 0<e i) (S : ι → Prop) {h M : ℕ} (hh0 : 0<h)
    (hM : ∀ d, 0<d → d≤M → d∣∏ i, p i^e i)
    (hsp : ∀ i, S i → p i≤M) (hsh : ∀ i, S i → 2*h≤p i)
    {a u v : ℝ} (ha : 0<a) (huv : v-u<a)
    (hsa : ∀ i, S i → a≤(p i : ℝ)*CollisionRemainderDynamics.collisionWeight (p i)) :
    phaseHaar.real {x | forcingCutoff h M x∈Set.Icc u v}≤
      20/Real.sqrt (1+∑ i : {i // S i}, (h : ℝ)/(p i : ℝ)) := by
  let k : ι → ℕ := fun i => p i^e i
  letI (i : ι) : NeZero (p i) := ⟨(hp i).ne_zero⟩
  letI (i : ι) : NeZero (k i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have hpk (i : ι) : p i∣k i := dvd_pow_self _ (he i).ne'
  have hc : Pairwise (fun i j => (k i).Coprime (k j)) := by
    intro i j hij
    exact ((Nat.coprime_primes (hp i) (hp j)).mpr (fun ht => hij (hpi ht))).pow _ _
  have hlt (i : ι) (hi : S i) : h<p i := by have := hsh i hi; omega
  rw [forcingCutoff_crt_probability k hc h M hM u v]
  have hb := uniform_subfamily_activation_bound S (fun i => quotientHit (p i) (k i) h (hpk i))
    (fun i hi => quotientHit_complement_nonempty (hpk i) (hlt i hi))
    (fun i hi => quotientHit_nonempty (hpk i) hh0 (hlt i hi).le)
    (fun i hi => show hitRatio (quotientHit (p i) (k i) h (hpk i))≤1/2 from by
      rw [quotientHit_ratio (hpk i) (hlt i hi).le]
      have hpos : (0 : ℝ)<p i := by exact_mod_cast (hp i).pos
      apply (div_le_iff₀ hpos).mpr
      have ht : (2 : ℝ)*h≤p i := by exact_mod_cast hsh i hi
      linarith)
    (fun r => forcingCutoff h M (representativePhase k hc r)) ha huv
    (fun r i hi y hr hy => show
      forcingCutoff h M (representativePhase k hc r)+a≤
        forcingCutoff h M (representativePhase k hc (Function.update r i y)) from by
      have hx : hitCoordinate (p i) h (representativePhase k hc r)=false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        exact hr ((quotientHit_representative k hc i (hpk i) r).mp ht)
      have hy' : hitCoordinate (p i) h (representativePhase k hc (Function.update r i y))=true := by
        apply (quotientHit_representative k hc i (hpk i) _).mpr
        simpa only [Function.update_self] using hy
      have hxy := representative_agrees_away k hc i (hp i) rfl hM r (Function.update r i y)
        (fun j hj => (Function.update_of_ne hj y r).symm)
      exact (add_le_add le_rfl (hsa i hi)).trans
        (forcingCutoff_prime_activation (hsp i hi) hx hy' hxy))
  have hs : (∑ i : {i // S i}, hitRatio (quotientHit (p i) (k i) h (hpk i)))=
      ∑ i : {i // S i}, (h : ℝ)/(p i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact quotientHit_ratio (hpk i) (hlt i i.property).le
  simpa only [hs] using hb

end NField.Alignment.CollisionActivationQuotient
