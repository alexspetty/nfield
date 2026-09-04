/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FloorDigitBinDistribution
import NField.Alignment.SpectralPower

/-!
# Floor-digit bins as additive spectral intervals

This module closes the reusable arithmetic bridge between the intrinsic
long-division digit word and the cyclic-interval model used by additive
spectral power.
-/

namespace NField.Alignment.SpectralPower

open scoped BigOperators
open NField.Alignment
open NField.CollisionDefinition
open ZMod

private lemma ceilDiv_mono_local {x y m : ℕ} (hm : 0 < m)
    (hxy : x ≤ y) : x ⌈/⌉ m ≤ y ⌈/⌉ m :=
  (gc_mul_ceilDiv hm).monotone_l hxy

private lemma ceilDiv_pos_local {x m : ℕ} (hm : 0 < m)
    (hx : 0 < x) : 0 < x ⌈/⌉ m := by
  by_contra h
  have hz : x ⌈/⌉ m = 0 := Nat.eq_zero_of_not_pos h
  have hle : x ≤ m * 0 := by
    rw [← ceilDiv_le_iff_le_mul hm, hz]
  omega

/-- A nonwrapping natural interval below the modulus becomes a translate of
the initial cyclic interval after coercion to `ZMod`. -/
theorem boundary_image_isCyclicInterval {p lower upper : ℕ} [NeZero p]
    (hlower : lower ≤ upper) :
    IsCyclicInterval
      ((Finset.Ico lower upper).image (fun x : ℕ => (x : ZMod p)))
      (upper - lower) := by
  classical
  refine ⟨(lower : ZMod p), ?_⟩
  unfold translateSet initialIntervalSet
  rw [Finset.image_image]
  ext r
  simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_range,
    Function.comp_apply]
  constructor
  · rintro ⟨x, ⟨hlx, hxu⟩, rfl⟩
    refine ⟨x - lower, ?_, ?_⟩
    · omega
    · rw [← Nat.cast_add, Nat.add_sub_of_le hlx]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨lower + j, ?_, ?_⟩
    · constructor <;> omega
    · rw [Nat.cast_add]

/-- The intrinsic `ZMod` digit bin is the cast of its exact natural boundary
interval. -/
theorem primeDigitWord_binSet_eq_boundary_image {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (d : Fin b) :
    binSet (primeDigitWord b p hb hp) d =
      (Finset.Ico (max 1 (digitBinBoundary b p d.val))
        (digitBinBoundary b p (d.val + 1))).image
          (fun x : ℕ => (x : ZMod p)) := by
  classical
  ext r
  simp only [binSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Ico]
  rw [primeDigitWord_some_iff hb hp]
  constructor
  · rintro ⟨hr0, hdigit⟩
    refine ⟨r.val, ?_, ?_⟩
    · have hinter := (digitBin_eq_iff_boundary_interval hb hp).mp hdigit
      exact ⟨by
        rw [max_le_iff]
        exact ⟨(ZMod.val_pos.mpr hr0), hinter.1⟩,
        hinter.2⟩
    · exact ZMod.natCast_zmod_val r
  · rintro ⟨x, ⟨hlower, hupper⟩, hx⟩
    have hboundary_le : digitBinBoundary b p (d.val + 1) ≤ p := by
      apply (ceilDiv_le_iff_le_mul hb).2
      have hdle : d.val + 1 ≤ b := by omega
      exact Nat.mul_le_mul_right p hdle
    have hxlt : x < p := lt_of_lt_of_le hupper hboundary_le
    have hrval : r.val = x := by
      rw [← hx]
      exact ZMod.val_natCast_of_lt hxlt
    constructor
    · rw [← ZMod.val_ne_zero, hrval]
      exact Nat.ne_of_gt
        (lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hlower))
    · apply (digitBin_eq_iff_boundary_interval hb hp).mpr
      exact ⟨by
        rw [hrval]
        exact le_trans (le_max_right _ _) hlower,
        by simpa [hrval] using hupper⟩

/-- Every intrinsic floor-digit bin is a cyclic interval of its exact
population. -/
theorem primeDigitWord_bin_isCyclicInterval {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (d : Fin b) :
    IsCyclicInterval (binSet (primeDigitWord b p hb hp) d)
      (binSet (primeDigitWord b p hb hp) d).card := by
  let lower := max 1 (digitBinBoundary b p d.val)
  let upper := digitBinBoundary b p (d.val + 1)
  have hupper_le : upper ≤ p := by
    apply (ceilDiv_le_iff_le_mul hb).2
    have hdle : d.val + 1 ≤ b := by omega
    exact Nat.mul_le_mul_right p hdle
  have hlower_le : lower ≤ upper := by
    have hmono : digitBinBoundary b p d.val ≤
        digitBinBoundary b p (d.val + 1) := by
      apply ceilDiv_mono_local hb
      exact Nat.mul_le_mul_right p (Nat.le_succ d.val)
    by_cases hd0 : d.val = 0
    · have hpositive : 0 < digitBinBoundary b p (d.val + 1) := by
        apply ceilDiv_pos_local hb
        exact Nat.mul_pos (by omega) hp
      dsimp [lower, upper]
      rw [show digitBinBoundary b p d.val = 0 by
        simp [digitBinBoundary, hd0],
        max_eq_left (by decide : 1 ≥ 0)]
      exact hpositive
    · have hpositive : 1 ≤ digitBinBoundary b p d.val := by
        exact ceilDiv_pos_local hb (Nat.mul_pos (Nat.pos_of_ne_zero hd0) hp)
      dsimp [lower, upper]
      rw [max_eq_right hpositive]
      exact hmono
  rw [primeDigitWord_binSet_eq_boundary_image hb hp d]
  have hcard :
      ((Finset.Ico lower upper).image (fun x : ℕ => (x : ZMod p))).card =
        upper - lower := by
    rw [Finset.card_image_iff.mpr]
    · exact Nat.card_Ico lower upper
    · intro x hx y hy hxy
      have hxIco := Finset.mem_Ico.mp hx
      have hyIco := Finset.mem_Ico.mp hy
      have hxlt : x < p := lt_of_lt_of_le hxIco.2 hupper_le
      have hylt : y < p := lt_of_lt_of_le hyIco.2 hupper_le
      have := congrArg ZMod.val hxy
      simpa [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] using this
  rw [hcard]
  exact boundary_image_isCyclicInterval hlower_le

/-- Every intrinsic bin has one of the two quotient/remainder lengths. -/
theorem primeDigitWord_bin_card_eq_quotient_or_succ {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (d : Fin b) :
    (binSet (primeDigitWord b p hb hp) d).card = (p - 1) / b ∨
      (binSet (primeDigitWord b p hb hp) d).card = (p - 1) / b + 1 := by
  rw [primeDigitWord_bin_card hb hp d]
  exact digitBinPopulation_eq_quotient_or_succ hb hp d.isLt

/-- The intrinsic floor-digit word realizes the complete two-length cyclic
interval model. -/
theorem primeDigitWord_twoLengthIntervalModel {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    TwoLengthIntervalModel (primeDigitWord b p hb hp)
      ((p - 1) / b) ((p - 1) % b) := by
  let word := primeDigitWord b p hb hp
  let q := (p - 1) / b
  let ρ := (p - 1) % b
  have hlength : ∀ d, (binSet word d).card = q ∨
      (binSet word d).card = q + 1 := by
    intro d
    exact primeDigitWord_bin_card_eq_quotient_or_succ hb hp d
  have htotal : ∑ d, (binSet word d).card = b * q + ρ := by
    rw [primeDigitWord_total_bin_size hb hp]
    have hdivision := Nat.mod_add_div (p - 1) b
    dsimp [q, ρ]
    omega
  have hcounts := two_length_count_certificate
    (fun d => (binSet word d).card) hlength htotal
  refine
    { length_cases := hlength
      small_count := hcounts.1
      large_count := hcounts.2
      interval_power := ?_ }
  intro d k
  apply setFourier_power_eq_intervalPower_of_isCyclicInterval
  · simpa [ZMod.card] using
      (Finset.card_le_card (Finset.subset_univ (binSet word d)))
  · exact primeDigitWord_bin_isCyclicInterval hb hp d

/-- The manuscript's two-kernel formula now applied to the intrinsic
floor-digit word, with no interval hypotheses left to the reader. -/
theorem prime_spectralPower_eq_two_interval_kernels {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (k : ZMod p) :
    spectralPower (primeDigitWord b p hb hp) k =
      (b - (p - 1) % b : ℕ) * intervalPower p ((p - 1) / b) k +
        ((p - 1) % b : ℕ) * intervalPower p ((p - 1) / b + 1) k :=
  spectralPower_eq_two_interval_kernels _
    (primeDigitWord_twoLengthIntervalModel hb hp) k

/-- Closed quotient/remainder form of the zero spectral mode. -/
theorem prime_spectralPower_zero_closed {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    spectralPower (primeDigitWord b p hb hp) 0 =
      (b * ((p - 1) / b) ^ 2 +
        ((p - 1) % b) * (2 * ((p - 1) / b) + 1) : ℕ) := by
  rw [prime_spectralPower_zero hb hp,
    digitBinSquareSum_eq_quotient_remainder hb hp]

/-! ## Exact short-interval overlap -/

/-- Membership in the initial interval is the expected inequality on the
canonical representative. -/
theorem mem_initialIntervalSet_iff_val_lt {p n : ℕ} [NeZero p]
    (hn : n ≤ p) (r : ZMod p) :
    r ∈ initialIntervalSet p n ↔ r.val < n := by
  classical
  unfold initialIntervalSet
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa [ZMod.val_natCast_of_lt (lt_of_lt_of_le hj hn)] using hj
  · intro hr
    exact ⟨r.val, hr, ZMod.natCast_zmod_val r⟩

private theorem add_mod_lt_iff_interval_ends {p n j h : ℕ}
    (hn : n ≤ p) (hj : j < n) (hh : h < p) :
    (j + h) % p < n ↔ j < n - h ∨ p - h ≤ j := by
  by_cases hsum : j + h < p
  · rw [Nat.mod_eq_of_lt hsum]
    constructor
    · intro hlt
      left
      omega
    · rintro (hleft | hright)
      · omega
      · omega
  · have hge : p ≤ j + h := by omega
    have hsublt : j + h - p < p := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsublt]
    constructor
    · intro _
      right
      omega
    · intro _
      omega

/-- The exact cyclic overlap of an initial interval, before imposing the
short-interval simplification. -/
theorem setOverlap_initialInterval {p n : ℕ} [NeZero p]
    (hn : n ≤ p) (h : ZMod p) :
    setOverlap (initialIntervalSet p n) h =
      (n - h.val) + (n - (p - h.val)) := by
  classical
  unfold setOverlap
  rw [initialIntervalSet, Finset.filter_image]
  rw [Finset.card_image_iff.mpr]
  · change ((Finset.range n).filter
        (fun j : ℕ => (j : ZMod p) + h ∈ initialIntervalSet p n)).card = _
    have hfilter :
        (Finset.range n).filter
            (fun j : ℕ => (j : ZMod p) + h ∈ initialIntervalSet p n) =
          Finset.Ico 0 (n - h.val) ∪ Finset.Ico (p - h.val) n := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
        Finset.mem_Ico, Nat.zero_le, true_and]
      constructor
      · rintro ⟨hj, hmem⟩
        rw [mem_initialIntervalSet_iff_val_lt hn, ZMod.val_add,
          ZMod.val_natCast_of_lt (lt_of_lt_of_le hj hn)] at hmem
        rcases (add_mod_lt_iff_interval_ends hn hj h.val_lt).mp hmem with
          hleft | hright
        · exact Or.inl hleft
        · exact Or.inr ⟨hright, hj⟩
      · intro hcases
        have hj : j < n := by
          rcases hcases with hleft | hright
          · omega
          · exact hright.2
        constructor
        · exact hj
        · rw [mem_initialIntervalSet_iff_val_lt hn, ZMod.val_add,
            ZMod.val_natCast_of_lt (lt_of_lt_of_le hj hn)]
          apply (add_mod_lt_iff_interval_ends hn hj h.val_lt).mpr
          rcases hcases with hleft | hright
          · exact Or.inl hleft
          · exact Or.inr hright.1
    rw [hfilter, Finset.card_union_of_disjoint]
    · simp only [Nat.card_Ico, Nat.sub_zero]
    · rw [Finset.disjoint_left]
      intro j hjleft hjright
      have hleft := (Finset.mem_Ico.mp hjleft).2
      have hright := (Finset.mem_Ico.mp hjright).1
      have hsub : n - h.val ≤ p - h.val := Nat.sub_le_sub_right hn h.val
      omega
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hival : (i : ZMod p).val = i :=
      ZMod.val_natCast_of_lt (lt_of_lt_of_le hi' hn)
    have hjval : (j : ZMod p).val = j :=
      ZMod.val_natCast_of_lt (lt_of_lt_of_le hj' hn)
    have hval := congrArg ZMod.val hij
    simpa [hival, hjval] using hval

/-- Membership in a translated set can be pulled back by the same shift. -/
theorem mem_translateSet_iff {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a r : ZMod p) :
    r ∈ translateSet a S ↔ r - a ∈ S := by
  classical
  unfold translateSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxr⟩
    have heq : x = r - a := by
      rw [← hxr]
      abel
    simpa [heq] using hx
  · intro hr
    refine ⟨r - a, hr, ?_⟩
    abel

/-- Cyclic translation does not change self-overlap at a declared shift. -/
theorem setOverlap_translate {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a h : ZMod p) :
    setOverlap (translateSet a S) h = setOverlap S h := by
  classical
  unfold setOverlap
  apply Finset.card_bij (fun r _ => r - a)
  · intro r hr
    rw [Finset.mem_filter] at hr ⊢
    constructor
    · exact (mem_translateSet_iff S a r).mp hr.1
    · have htranslated := (mem_translateSet_iff S a (r + h)).mp hr.2
      simpa only [show r + h - a = (r - a) + h by abel] using htranslated
  · intro r _ s _ hrs
    exact sub_left_injective hrs
  · intro s hs
    rw [Finset.mem_filter] at hs
    let r := a + s
    have hr : r ∈ (translateSet a S).filter
        (fun x => x + h ∈ translateSet a S) := by
      rw [Finset.mem_filter]
      constructor
      · apply (mem_translateSet_iff S a r).mpr
        simpa [r] using hs.1
      · apply (mem_translateSet_iff S a (r + h)).mpr
        have heq : r + h - a = s + h := by
          dsimp [r]
          abel
        rw [heq]
        exact hs.2
    refine ⟨r, hr, ?_⟩
    simp [r]

private theorem two_overlap_terms_eq_short_triangle {p n h : ℕ}
    (hshort : 2 * n ≤ p) (hh : h < p) :
    (n - h) + (n - (p - h)) = n - min h (p - h) := by
  by_cases hside : h ≤ p - h
  · rw [min_eq_left hside]
    have hnle : n ≤ p - h := by omega
    rw [Nat.sub_eq_zero_of_le hnle, Nat.add_zero]
  · have hside' : p - h ≤ h := by omega
    rw [min_eq_right hside']
    have hnle : n ≤ h := by omega
    rw [Nat.sub_eq_zero_of_le hnle, Nat.zero_add]

/-- A cyclic interval of length at most half the modulus has the triangular
self-overlap profile. -/
theorem setOverlap_eq_short_triangle_of_isCyclicInterval
    {p n : ℕ} [NeZero p] {S : Finset (ZMod p)}
    (hshort : 2 * n ≤ p) (hinterval : IsCyclicInterval S n)
    (h : ZMod p) :
    setOverlap S h = n - circularDistance p h := by
  have hn : n ≤ p := by omega
  rcases hinterval with ⟨a, rfl⟩
  rw [setOverlap_translate, setOverlap_initialInterval hn]
  exact two_overlap_terms_eq_short_triangle hshort h.val_lt

/-- Every intrinsic floor-digit bin has length at most half the modulus when
the base is at least two. -/
theorem primeDigitWord_bin_twice_card_le {b p : ℕ}
    (hb : 2 ≤ b) (hp : 0 < p) [NeZero p] (d : Fin b) :
    2 * (binSet (primeDigitWord b p (by omega) hp) d).card ≤ p := by
  rw [primeDigitWord_bin_card (by omega) hp d]
  have hpopulation := digitBinPopulation_le_ceil (by omega) hp d.isLt
  have hceil : (p - 1) ⌈/⌉ b ≤ p / 2 := by
    apply (ceilDiv_le_iff_le_mul (by omega : 0 < b)).2
    have hmod := Nat.mod_lt p (by decide : 0 < 2)
    have hdivision := Nat.mod_add_div p 2
    have hpbound : p - 1 ≤ 2 * (p / 2) := by omega
    exact le_trans hpbound (Nat.mul_le_mul_right (p / 2) hb)
  have hhalf : 2 * (p / 2) ≤ p := Nat.mul_div_le p 2
  exact le_trans (Nat.mul_le_mul_left 2 (le_trans hpopulation hceil)) hhalf

/-- The intrinsic floor-digit word realizes the short two-length interval
model used by the exact additive collision profile. -/
theorem primeDigitWord_shortTwoLengthIntervalModel {b p : ℕ}
    (hb : 2 ≤ b) (hp : 0 < p) [NeZero p] :
    ShortTwoLengthIntervalModel
      (primeDigitWord b p (by omega) hp) ((p - 1) / b) ((p - 1) % b) := by
  let word := primeDigitWord b p (by omega) hp
  let baseModel := primeDigitWord_twoLengthIntervalModel (by omega : 0 < b) hp
  refine
    { toTwoLengthIntervalModel := baseModel
      overlap_profile := ?_ }
  intro d h
  apply setOverlap_eq_short_triangle_of_isCyclicInterval
  · exact primeDigitWord_bin_twice_card_le hb hp d
  · exact primeDigitWord_bin_isCyclicInterval (by omega) hp d

/-- The exact two-triangular additive collision profile for the intrinsic
floor-digit word. -/
theorem prime_additiveCollision_eq_two_triangles {b p : ℕ}
    (hb : 2 ≤ b) (hp : 0 < p) [NeZero p] (h : ZMod p) :
    additiveCollision (primeDigitWord b p (by omega) hp) h =
      (b - (p - 1) % b) * ((p - 1) / b - circularDistance p h) +
        (p - 1) % b * ((p - 1) / b + 1 - circularDistance p h) :=
  additiveCollision_eq_two_triangles _
    (primeDigitWord_shortTwoLengthIntervalModel hb hp) h

end NField.Alignment.SpectralPower
