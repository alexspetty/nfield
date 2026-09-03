/-
Author: Alexander S. Petty
-/

import NField.Alignment.BinDerangements
import NField.Alignment.AutocorrelationClosure
import NField.Alignment.FloorDigitSpectralModel

/-!
# Publication closure for bin derangements and gate width

This module supplies the exact floor-cardinality, ratio-set, special-range,
and asymptotic bridges used by the manuscript-facing theorem map.  It extends
the reusable gate machinery without changing the cumulative proof sequence.
-/

namespace NField.Alignment.BinDerangementsClosure

open scoped BigOperators
open ZMod
open NField.CollisionDefinition
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.BinDerangements
open NField.Alignment.AutocorrelationFormula

private theorem ceilDiv_eq_div_add_one_of_mod_ne_zero
    {x m : ℕ} (hm : 0 < m) (hmod : x % m ≠ 0) :
    x ⌈/⌉ m = x / m + 1 := by
  apply Nat.le_antisymm
  · rw [ceilDiv_le_iff_le_mul hm]
    have hrem : x % m ≤ m := (Nat.mod_lt x hm).le
    calc
      x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
      _ ≤ m * (x / m) + m := Nat.add_le_add_left hrem _
      _ = m * (x / m + 1) := by ring
  · apply Nat.succ_le_of_lt
    rw [show x / m < x ⌈/⌉ m ↔ m * (x / m) < x by
      rw [← not_le, ← not_le]
      exact not_congr (ceilDiv_le_iff_le_mul hm)]
    have hrem : 0 < x % m := Nat.pos_of_ne_zero hmod
    calc
      m * (x / m) < m * (x / m) + x % m :=
        Nat.lt_add_of_pos_right hrem
      _ = x := Nat.div_add_mod x m

private theorem coprime_factor_mod_ne_zero
    {a m n : ℕ} (ha : a.Coprime m) (hn0 : n ≠ 0) (hnm : n < m) :
    (n * a) % m ≠ 0 := by
  intro hzero
  have hdvd : m ∣ n * a := Nat.dvd_of_mod_eq_zero hzero
  have hmn : m ∣ n := ha.symm.dvd_of_dvd_mul_right hdvd
  have hnle : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hmn
  omega

/-- Exact floor-difference formula for one nonzero digit bin, including the
last-bin correction for the excluded endpoint `p`. -/
theorem digitBinPopulation_floor_formula {b p d : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) (hd : d < b) :
    digitBinPopulation b p d =
      ((d + 1) * p) / b - (d * p) / b -
        (if d = b - 1 then 1 else 0) := by
  have hb : 0 < b := by omega
  have hcop : p.Coprime b := (hp.coprime_iff_not_dvd).mpr (by
    intro hpb
    have hle := Nat.le_of_dvd hb hpb
    omega)
  rw [digitBinPopulation_eq_boundary_sub hb hp.pos hd]
  unfold digitBinBoundary
  by_cases hd0 : d = 0
  · subst d
    have hmod : p % b ≠ 0 := by
      simpa using coprime_factor_mod_ne_zero hcop (by omega : 1 ≠ 0)
        (by omega : 1 < b)
    simp only [zero_add, one_mul, zero_mul, zero_ceilDiv]
    rw [ceilDiv_eq_div_add_one_of_mod_ne_zero hb hmod]
    have hnotlast : (0 : ℕ) ≠ b - 1 := by omega
    simp [hnotlast]
  · by_cases hlast : d = b - 1
    · subst d
      have hmod : ((b - 1) * p) % b ≠ 0 :=
        coprime_factor_mod_ne_zero hcop (by omega) (by omega)
      rw [ceilDiv_eq_div_add_one_of_mod_ne_zero hb hmod]
      have hbmul : (b * p) ⌈/⌉ b = p := by
        apply Nat.le_antisymm
        · exact (ceilDiv_le_iff_le_mul hb).2 (by rfl)
        · have hcover := le_smul_ceilDiv (α := ℕ) (β := ℕ)
              (a := b) (b := b * p) hb
          change b * p ≤ b * ((b * p) ⌈/⌉ b) at hcover
          exact Nat.le_of_mul_le_mul_left hcover hb
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ b)]
      rw [hbmul]
      rw [Nat.mul_comm b p, Nat.mul_div_left p hb]
      simp
      omega
    · have hdnext : d + 1 < b := by omega
      have hmodLower : (d * p) % b ≠ 0 :=
        coprime_factor_mod_ne_zero hcop hd0 hd
      have hmodUpper : ((d + 1) * p) % b ≠ 0 :=
        coprime_factor_mod_ne_zero hcop (by omega) hdnext
      rw [ceilDiv_eq_div_add_one_of_mod_ne_zero hb hmodLower,
        ceilDiv_eq_div_add_one_of_mod_ne_zero hb hmodUpper]
      simp [hlast]

/-! ## Within-bin ratios -/

/-- The multipliers represented by a ratio of two residues from one bin.  The
positive-collision definition is equivalent to the literal ratio-set
description below and makes the complement count transparent. -/
def withinBinRatioSet {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) : Finset (ZMod N) :=
  (nonzeroSet N).filter fun g => 0 < collisionCount word g

/-- Membership in the positive-collision set is exactly representation as
`a * r⁻¹` with `a` and `r` in one bin. -/
theorem mem_withinBinRatioSet_iff {p κ : ℕ}
    (hp : Nat.Prime p) [NeZero p]
    (word : ZMod p → Option (Fin κ)) (hzero : word 0 = none)
    (g : ZMod p) :
    g ∈ withinBinRatioSet word ↔
      ∃ d : Fin κ, ∃ a r : ZMod p,
        a ∈ binSet word d ∧ r ∈ binSet word d ∧ g = a * r⁻¹ := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  constructor
  · intro hg
    have hg' := Finset.mem_filter.mp hg
    have hpositive := hg'.2
    have hnotzero : collisionCount word g ≠ 0 := Nat.ne_of_gt hpositive
    have hnotdisjoint :
        ¬∀ d : Fin κ, ∀ r ∈ binSet word d,
          g * r ∉ binSet word d := by
      intro hdisjoint
      exact hnotzero ((collisionCount_eq_zero_iff_bins_disjoint word g).2
        hdisjoint)
    push Not at hnotdisjoint
    obtain ⟨d, r, hr, hgr⟩ := hnotdisjoint
    have hr0 : r ≠ 0 := by
      intro hre
      subst r
      simp [binSet, hzero] at hr
    refine ⟨d, g * r, r, hgr, hr, ?_⟩
    calc
      g = g * 1 := (mul_one g).symm
      _ = g * (r * r⁻¹) := by rw [mul_inv_cancel₀ hr0]
      _ = (g * r) * r⁻¹ := by ring
  · rintro ⟨d, a, r, ha, hr, rfl⟩
    have ha0 : a ≠ 0 := by
      intro hae
      subst a
      simp [binSet, hzero] at ha
    have hr0 : r ≠ 0 := by
      intro hre
      subst r
      simp [binSet, hzero] at hr
    have hg0 : a * r⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hr0)
    apply Finset.mem_filter.mpr
    refine ⟨by simp [nonzeroSet, hg0], ?_⟩
    have hcollision : collisionCount word (a * r⁻¹) ≠ 0 := by
      intro hzeroCollision
      have hdisjoint :=
        (collisionCount_eq_zero_iff_bins_disjoint word (a * r⁻¹)).1
          hzeroCollision
      apply hdisjoint d r hr
      have hproduct : (a * r⁻¹) * r = a := by
        rw [mul_assoc, inv_mul_cancel₀ hr0, mul_one]
      simpa [hproduct] using ha
    omega

/-- The intrinsic within-bin ratio set for the prime digit partition. -/
def intrinsicWithinBinRatioSet (b p : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) : Finset (ZMod p) :=
  withinBinRatioSet (primeDigitWord b p hb hp.pos)

/-- The union of all within-bin ratios has exactly `p-b` elements. -/
theorem intrinsicWithinBinRatioSet_card {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p] :
    (intrinsicWithinBinRatioSet b p (by omega) hp).card = p - b := by
  classical
  let word := primeDigitWord b p (by omega) hp.pos
  have hset : intrinsicWithinBinRatioSet b p (by omega) hp =
      nonzeroSet p \ derangingFamily b p := by
    ext g
    simp only [intrinsicWithinBinRatioSet, withinBinRatioSet,
      Finset.mem_filter, Finset.mem_sdiff]
    rw [mem_derangingFamily_iff hb2 hp hbp g]
    simp only [nonzeroSet, Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases hg0 : g = 0
    · simp [hg0]
    · by_cases hcollision :
        collisionCount (primeDigitWord b p (by omega) hp.pos) g = 0
      · simp [hg0, hcollision]
      · have hpositive := Nat.pos_of_ne_zero hcollision
        simp [hg0, hcollision, hpositive]
  have hsubset : derangingFamily b p ⊆ nonzeroSet p := by
    intro g hg
    have hg0 := (mem_derangingFamily_iff hb2 hp hbp g).1 hg |>.1
    simp [nonzeroSet, hg0]
  rw [hset, Finset.card_sdiff_of_subset hsubset,
    derangingFamily_card (by omega) hp hbp]
  have hnonzeroCard : (nonzeroSet p).card = p - 1 := by
    simp [nonzeroSet, ZMod.card]
  rw [hnonzeroCard]
  omega

/-- Positive-collision multipliers with the identity removed. -/
def constructiveMultiplierSet (b p : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) : Finset (ZMod p) :=
  Finset.univ.filter fun g =>
    g ≠ 1 ∧ 0 < collisionCount (primeDigitWord b p hb hp.pos) g

/-- The number of constructive multipliers is `p-b-1`. -/
theorem constructiveMultiplierSet_card {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp1 : b + 1 < p) [NeZero p] :
    (constructiveMultiplierSet b p (by omega) hp).card = p - b - 1 := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hbp : b < p := by omega
  have honePositive :
      0 < collisionCount (primeDigitWord b p (by omega) hp.pos) 1 := by
    rw [collisionCount_one, prime_assignedMass (by omega) hp.pos]
    omega
  have hset : constructiveMultiplierSet b p (by omega) hp =
      (intrinsicWithinBinRatioSet b p (by omega) hp).erase 1 := by
    ext g
    simp only [constructiveMultiplierSet, intrinsicWithinBinRatioSet,
      withinBinRatioSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    simp only [nonzeroSet, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hg1, hpositive⟩
      have hg0 : g ≠ 0 := by
        intro hg
        subst g
        have hzeroCollision :
            collisionCount (primeDigitWord b p (by omega) hp.pos) 0 = 0 := by
          simp [collisionCount, primeDigitWord_zero]
        omega
      exact ⟨hg1, hg0, hpositive⟩
    · rintro ⟨hg1, hg0, hpositive⟩
      exact ⟨hg1, hpositive⟩
  have honeMem : 1 ∈ intrinsicWithinBinRatioSet b p (by omega) hp := by
    apply Finset.mem_filter.mpr
    exact ⟨by simp [nonzeroSet], honePositive⟩
  rw [hset, Finset.card_erase_of_mem honeMem,
    intrinsicWithinBinRatioSet_card hb2 hp hbp]

/-- The exact total collision mass over constructive multipliers. -/
theorem constructiveMultiplierSet_collision_sum {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (_hbp1 : b + 1 < p) [NeZero p] :
    ∑ g ∈ constructiveMultiplierSet b p (by omega) hp,
        collisionCount (primeDigitWord b p (by omega) hp.pos) g =
      b * ((p - 1) / b) ^ 2 +
        ((p - 1) % b) * (2 * ((p - 1) / b) + 1) - (p - 1) := by
  classical
  let word := primeDigitWord b p (by omega) hp.pos
  let f : ZMod p → ℕ := fun g => collisionCount word g
  have hsubset : constructiveMultiplierSet b p (by omega) hp ⊆
      (Finset.univ.erase 1 : Finset (ZMod p)) := by
    intro g hg
    have hg' := Finset.mem_filter.mp hg
    exact Finset.mem_erase.mpr ⟨hg'.2.1, Finset.mem_univ g⟩
  have hsumSubset :
      ∑ g ∈ constructiveMultiplierSet b p (by omega) hp, f g =
        ∑ g ∈ (Finset.univ.erase 1 : Finset (ZMod p)), f g := by
    apply Finset.sum_subset hsubset
    intro g hgErase hgNot
    have hnotPositive : ¬0 < f g := by
      intro hpositive
      apply hgNot
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g,
        (Finset.mem_erase.mp hgErase).1, hpositive⟩
    have hzero : f g = 0 := Nat.eq_zero_of_not_pos hnotPositive
    simp [hzero]
  have hone : f 1 = p - 1 := by
    dsimp [f, word]
    rw [collisionCount_one, prime_assignedMass (by omega) hp.pos]
  have hfull : ∑ g : ZMod p, f g = digitBinSquareSum b p := by
    dsimp [f, word]
    exact prime_collisionCount_sum_rule (by omega) hp
  have herase := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (1 : ZMod p))
  have hclosed : digitBinSquareSum b p =
      b * ((p - 1) / b) ^ 2 +
        ((p - 1) % b) * (2 * ((p - 1) / b) + 1) :=
    digitBinSquareSum_eq_quotient_remainder (by omega) hp.pos
  rw [hsumSubset]
  omega

/-! ## Pairing and shorter orbits -/

/-- For an even base, the middle parameter gives the self-inverse multiplier
`-1` exactly. -/
theorem derangingMultiplier_half_eq_neg_one {b p : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (heven : Even b) :
    derangingMultiplier b p (b / 2) = -1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨k, rfl⟩ := heven
  have hk : 0 < k := by omega
  have hkltp : k < p := by omega
  have hk0 : (k : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hkltp]
    exact hk.ne'
  have hhalf : (k + k) / 2 = k := by omega
  rw [hhalf]
  have hsub : k + k - k = k := by omega
  simp only [derangingMultiplier, hsub]
  calc
    -(k : ZMod p) * (k : ZMod p)⁻¹ =
        -((k : ZMod p) * (k : ZMod p)⁻¹) := by ring
    _ = -1 := by rw [mul_inv_cancel₀ hk0]

/-- Collision count restricted to a selected residue orbit. -/
def restrictedCollisionCount {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) (orbit : Finset (ZMod N))
    (g : ZMod N) : ℕ :=
  ∑ r ∈ orbit,
    if word r = word (g * r) ∧ word r ≠ none then 1 else 0

/-- A full-group derangement remains collision-free on every restricted
orbit. -/
theorem restrictedCollisionCount_eq_zero_of_collisionCount_eq_zero
    {N κ : ℕ} [NeZero N]
    (word : ZMod N → Option (Fin κ)) (orbit : Finset (ZMod N))
    (g : ZMod N) (hzero : collisionCount word g = 0) :
    restrictedCollisionCount word orbit g = 0 := by
  classical
  have hfull :
      (∑ r : ZMod N,
        if word r = word (g * r) ∧ word r ≠ none then 1 else 0) = 0 := by
    simpa [collisionCount] using hzero
  have hterms := Finset.sum_eq_zero_iff.mp hfull
  unfold restrictedCollisionCount
  rw [Finset.sum_eq_zero_iff]
  intro r hr
  exact hterms r (Finset.mem_univ r)

/-- Nonzero lags whose associated nonzero multiplier has collision count
zero. -/
def zeroLagSet {G : Type*} [Fintype G] [DecidableEq G] [Zero G]
    {p κ : ℕ} [NeZero p]
    (word : ZMod p → Option (Fin κ)) (multiplier : G ≃ NonzeroResidue p) :
    Finset G :=
  Finset.univ.filter fun lag =>
    lag ≠ 0 ∧ collisionCount word (multiplier lag).val = 0

/-- Any exact exponent-to-multiplier equivalence sending zero to the identity
has exactly `b-1` nonzero zero-collision lags. -/
theorem zeroLagSet_card {G : Type*} [Fintype G] [DecidableEq G] [Zero G]
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (multiplier : G ≃ NonzeroResidue p)
    (hidentity : (multiplier 0).val = 1) :
    (zeroLagSet (primeDigitWord b p (by omega) hp.pos) multiplier).card =
      b - 1 := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let word := primeDigitWord b p (by omega) hp.pos
  let f : G → ZMod p := fun lag => (multiplier lag).val
  have hinj : Set.InjOn f (zeroLagSet word multiplier) := by
    intro x hx y hy hxy
    apply multiplier.injective
    apply Subtype.ext
    exact hxy
  have himage :
      (zeroLagSet word multiplier).image f = derangingFamily b p := by
    ext g
    constructor
    · intro hg
      obtain ⟨lag, hlag, rfl⟩ := Finset.mem_image.mp hg
      have hlag' := Finset.mem_filter.mp hlag
      apply (mem_derangingFamily_iff hb2 hp hbp _).2
      exact ⟨(multiplier lag).property, hlag'.2.2⟩
    · intro hg
      have hg' := (mem_derangingFamily_iff hb2 hp hbp g).1 hg
      let ng : NonzeroResidue p := ⟨g, hg'.1⟩
      let lag : G := multiplier.symm ng
      have hlagImage : f lag = g := by
        dsimp [f, lag, ng]
        simp
      have hg1 : g ≠ 1 := by
        intro hgone
        have hcollision := hg'.2
        rw [hgone, collisionCount_one,
          prime_assignedMass (by omega) hp.pos] at hcollision
        omega
      have hlag0 : lag ≠ 0 := by
        intro hzeroLag
        have hval := congrArg (fun z : G => (multiplier z).val) hzeroLag
        dsimp [lag, ng] at hval
        simp only [Equiv.apply_symm_apply] at hval
        rw [hidentity] at hval
        exact hg1 hval
      apply Finset.mem_image.mpr
      refine ⟨lag, Finset.mem_filter.mpr ⟨Finset.mem_univ lag,
        hlag0, ?_⟩, hlagImage⟩
      change collisionCount word (f lag) = 0
      rw [hlagImage]
      exact hg'.2
  calc
    (zeroLagSet word multiplier).card =
        ((zeroLagSet word multiplier).image f).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ = (derangingFamily b p).card := congrArg Finset.card himage
    _ = b - 1 := derangingFamily_card (by omega) hp hbp

/-- On the four-element orbit generated by eight modulo thirteen, lag one is
collision-free although the full base-eight collision count is two.  This is
the manuscript's exact shorter-orbit counterexample boundary. -/
theorem baseEight_thirteen_short_orbit_counterexample :
    let word := primeDigitWord 8 13 (by norm_num) (by norm_num)
    let orbit : Finset (ZMod 13) := {1, 5, 8, 12}
    restrictedCollisionCount word orbit 8 = 0 ∧
      collisionCount word 8 = 2 := by
  dsimp
  constructor
  · decide
  · rw [collisionCount_eq_transformedCollisionCount
      (b := 8) (p := 13) (g := 8)
      (by norm_num) (by norm_num) (by norm_num) (by decide)]
    norm_num [transformedCollisionCount]; decide

/-! ## Exact constructive ranges and asymptotic control -/

/-- The manuscript's exact rational mean as a reusable arithmetic object. -/
def constructiveMeanValue (b Q R : ℕ) : ℚ :=
  (Q * (b * (Q - 1) + 2 * R) : ℕ) /
    (b * (Q - 1) + R : ℕ)

/-- The mean is `Q` plus its exact bounded correction. -/
theorem constructiveMeanValue_eq_quotient_plus_correction {b Q R : ℕ}
    (hden : 0 < b * (Q - 1) + R) :
    constructiveMeanValue b Q R =
      Q + (Q * R : ℕ) / (b * (Q - 1) + R : ℕ) := by
  have hdenQ : ((b * (Q - 1) + R : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hden.ne'
  unfold constructiveMeanValue
  field_simp
  push_cast
  ring

/-- The cross-multiplied mean-two identity is equivalent to the complete
first constructive range. -/
theorem constructiveMean_cross_eq_two_iff {b p Q R : ℕ}
    (hb : 0 < b) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) (hpgt : b + 1 < p) :
    Q * (b * (Q - 1) + 2 * R) = 2 * (b * (Q - 1) + R) ↔
      p ≤ 2 * b + 1 := by
  have hpform : p = b * Q + R + 1 := by omega
  have hQpos : 1 ≤ Q := by
    by_contra hnot
    have hQzero : Q = 0 := by omega
    subst Q
    simp at hpform
    omega
  constructor
  · intro heq
    by_cases hQone : Q = 1
    · subst Q
      simp at hpform
      omega
    by_cases hQtwo : Q = 2
    · subst Q
      norm_num at heq
      have hRzero : R = 0 := by omega
      subst R
      omega
    have hQthree : 3 ≤ Q := by omega
    have hQsub : Q - 1 + 1 = Q := Nat.sub_add_cancel hQpos
    exfalso
    nlinarith
  · intro hrange
    have hQle : Q ≤ 2 := by
      by_contra hnot
      have hQthree : 3 ≤ Q := by omega
      nlinarith
    have hcases : Q = 1 ∨ Q = 2 := by omega
    rcases hcases with rfl | rfl
    · norm_num
    · have hRzero : R = 0 := by omega
      subst R
      norm_num

/-- The rational constructive mean equals two exactly on
`b+1 < p ≤ 2b+1`. -/
theorem constructiveMeanValue_eq_two_iff {b p Q R : ℕ}
    (hb : 0 < b) (hdivision : p - 1 = b * Q + R)
    (hR : R < b) (hpgt : b + 1 < p) :
    constructiveMeanValue b Q R = 2 ↔ p ≤ 2 * b + 1 := by
  have hQpos : 1 ≤ Q := by
    by_contra hnot
    have hQzero : Q = 0 := by omega
    subst Q
    simp at hdivision
    omega
  have hden : 0 < b * (Q - 1) + R := by
    by_cases hQone : Q = 1
    · subst Q
      simp
      omega
    · have hQtwo : 2 ≤ Q := by omega
      have hQminus : 0 < Q - 1 := Nat.sub_pos_of_lt (by omega)
      have hmul : 0 < b * (Q - 1) := Nat.mul_pos hb hQminus
      omega
  unfold constructiveMeanValue
  have hdenQ : ((b * (Q - 1) + R : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hden.ne'
  rw [div_eq_iff hdenQ]
  have hcross := constructiveMean_cross_eq_two_iff hb hdivision hR hpgt
  constructor
  · intro heq
    apply hcross.1
    exact_mod_cast heq
  · intro hrange
    have heq := hcross.2 hrange
    exact_mod_cast heq

/-- When the Euclidean remainder vanishes, the exact mean is `Q`. -/
theorem constructiveMeanValue_eq_quotient_of_remainder_zero {b Q : ℕ}
    (hb : 0 < b) (hQ : 1 < Q) :
    constructiveMeanValue b Q 0 = Q := by
  have hQminus : 0 < Q - 1 := Nat.sub_pos_of_lt hQ
  have hden : 0 < b * (Q - 1) + 0 := by
    exact Nat.mul_pos hb hQminus
  simpa using
    (constructiveMeanValue_eq_quotient_plus_correction
      (b := b) (Q := Q) (R := 0) hden)

/-- The correction to `Q` is always between zero and one.  This uniform exact
bound supplies both `Q + O_b(1)` and the ratio limit in the manuscript. -/
theorem constructiveMeanValue_correction_bounds {b Q R : ℕ}
    (_hb : 0 < b) (hQ : 1 ≤ Q) (hR : R < b)
    (hden : 0 < b * (Q - 1) + R) :
    0 ≤ constructiveMeanValue b Q R - Q ∧
      constructiveMeanValue b Q R - Q ≤ 1 := by
  have hQsub : Q - 1 + 1 = Q := Nat.sub_add_cancel hQ
  have hnumle : Q * R ≤ b * (Q - 1) + R := by
    nlinarith
  have hdenQ : (0 : ℚ) < (b * (Q - 1) + R : ℕ) := by
    exact_mod_cast hden
  have hnumQ : (0 : ℚ) ≤ (Q * R : ℕ) := by positivity
  have hnumleQ : ((Q * R : ℕ) : ℚ) ≤
      (b * (Q - 1) + R : ℕ) := by
    exact_mod_cast hnumle
  have hfrac_nonneg :
      (0 : ℚ) ≤ (Q * R : ℕ) / (b * (Q - 1) + R : ℕ) :=
    div_nonneg hnumQ hdenQ.le
  have hfrac_le :
      ((Q * R : ℕ) : ℚ) / (b * (Q - 1) + R : ℕ) ≤ 1 :=
    (div_le_one hdenQ).2 hnumleQ
  rw [constructiveMeanValue_eq_quotient_plus_correction hden]
  constructor <;> linarith

/-- The normalized error is bounded by `1/Q`; this is a uniform finite
certificate for convergence of the mean-to-quotient ratio to one. -/
theorem constructiveMeanValue_ratio_error_bound {b Q R : ℕ}
    (hb : 0 < b) (hQ : 1 ≤ Q) (hR : R < b)
    (hden : 0 < b * (Q - 1) + R) :
    |constructiveMeanValue b Q R / Q - 1| ≤ (1 : ℚ) / Q := by
  obtain ⟨hlower, hupper⟩ :=
    constructiveMeanValue_correction_bounds hb hQ hR hden
  have hQR : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hrewrite : constructiveMeanValue b Q R / Q - 1 =
      (constructiveMeanValue b Q R - Q) / Q := by
    field_simp
  rw [hrewrite, abs_of_nonneg (div_nonneg hlower hQR.le)]
  exact (div_le_div_iff_of_pos_right hQR).2 hupper

/-- With the base fixed and the Euclidean remainder allowed to vary through
its finite range, the normalized constructive mean tends to one. -/
theorem constructiveMeanValue_ratio_tendsto_one
    {b : ℕ} (hb : 0 < b) (R : ℕ → ℕ) (hR : ∀ Q, R Q < b) :
    Filter.Tendsto
      (fun Q : ℕ => constructiveMeanValue b Q (R Q) / Q)
      Filter.atTop (nhds 1) := by
  have honeDiv : Filter.Tendsto (fun Q : ℕ => (1 : ℚ) / Q)
      Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlower : Filter.Tendsto (fun Q : ℕ => (1 : ℚ) - 1 / Q)
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub honeDiv)
  have hupper : Filter.Tendsto (fun Q : ℕ => (1 : ℚ) + 1 / Q)
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add honeDiv)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [Filter.eventually_atTop.2 ⟨2, fun Q hQ => hQ⟩] with Q hQ
    have hQpos : 1 ≤ Q := by omega
    have hQminus : 0 < Q - 1 := Nat.sub_pos_of_lt hQ
    have hden : 0 < b * (Q - 1) + R Q := by
      have hmul := Nat.mul_pos hb hQminus
      omega
    have habs := constructiveMeanValue_ratio_error_bound
      hb hQpos (hR Q) hden
    rw [abs_le] at habs
    linarith
  · filter_upwards [Filter.eventually_atTop.2 ⟨2, fun Q hQ => hQ⟩] with Q hQ
    have hQpos : 1 ≤ Q := by omega
    have hQminus : 0 < Q - 1 := Nat.sub_pos_of_lt hQ
    have hden : 0 < b * (Q - 1) + R Q := by
      have hmul := Nat.mul_pos hb hQminus
      omega
    have habs := constructiveMeanValue_ratio_error_bound
      hb hQpos (hR Q) hden
    rw [abs_le] at habs
    linarith

end NField.Alignment.BinDerangementsClosure
