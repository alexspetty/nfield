/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CosetAlignment

/-!
# Exact floor-digit bin distribution

The long-division digit map cuts the nonzero residues into consecutive floor
intervals.  This module proves that their sizes differ by at most one, counts
the larger intervals exactly, derives the closed square-sum formula, and gives
the sharp ceiling used by the uniform alignment bound.
-/

namespace NField.Alignment

open scoped BigOperators
open NField.CollisionDefinition

/-- The first integer whose base-scaled value reaches the `d`-th threshold. -/
def digitBinBoundary (b p d : ℕ) : ℕ := (d * p) ⌈/⌉ b

/-- The floor-digit equation is exactly membership in two consecutive ceiling
boundaries. -/
theorem digitBin_eq_iff_boundary_interval {b p d x : ℕ}
    (hb : 0 < b) (hp : 0 < p) :
    digitBin b p x = d ↔
      digitBinBoundary b p d ≤ x ∧ x < digitBinBoundary b p (d + 1) := by
  unfold digitBin digitBinBoundary
  constructor
  · intro hdigit
    have hlower : d * p ≤ b * x := by
      calc
        d * p = p * ((b * x) / p) := by rw [hdigit]; exact Nat.mul_comm _ _
        _ ≤ b * x := Nat.mul_div_le _ _
    have hupper : b * x < (d + 1) * p := by
      exact (Nat.div_lt_iff_lt_mul hp).mp (by omega)
    constructor
    · exact (ceilDiv_le_iff_le_mul hb).2 hlower
    · by_contra hnot
      have hceil : ((d + 1) * p) ⌈/⌉ b ≤ x := by omega
      have := (ceilDiv_le_iff_le_mul hb).1 hceil
      omega
  · rintro ⟨hlower, hupper⟩
    apply Nat.div_eq_of_lt_le
    · exact (ceilDiv_le_iff_le_mul hb).1 hlower
    · by_contra hnot
      have hle : (d + 1) * p ≤ b * x := by omega
      have hceil : ((d + 1) * p) ⌈/⌉ b ≤ x :=
        (ceilDiv_le_iff_le_mul hb).2 hle
      omega

/-- A digit population is the cardinality of its explicit nonzero boundary
interval. -/
theorem digitBinPopulation_eq_boundary_card {b p d : ℕ}
    (hb : 0 < b) (hp : 0 < p) (hd : d < b) :
    digitBinPopulation b p d =
      (Finset.Ico (max 1 (digitBinBoundary b p d))
        (digitBinBoundary b p (d + 1))).card := by
  classical
  unfold digitBinPopulation nonzeroResidues
  apply congrArg Finset.card
  ext x
  have hupper_le : digitBinBoundary b p (d + 1) ≤ p := by
    apply (ceilDiv_le_iff_le_mul hb).2
    have hdle : d + 1 ≤ b := by omega
    exact Nat.mul_le_mul_right p hdle
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range,
    Finset.mem_Ico]
  rw [digitBin_eq_iff_boundary_interval hb hp]
  constructor
  · rintro ⟨⟨hx0, hxp⟩, hlower, hupper⟩
    exact ⟨by simpa [max_le_iff] using And.intro (Nat.one_le_iff_ne_zero.mpr hx0) hlower,
      hupper⟩
  · rintro ⟨hlower, hupper⟩
    have hxone : 1 ≤ x := le_trans (le_max_left 1 _) hlower
    have hxboundary : digitBinBoundary b p d ≤ x :=
      le_trans (le_max_right 1 _) hlower
    exact ⟨⟨by omega, lt_of_lt_of_le hupper hupper_le⟩, hxboundary, hupper⟩

/-- Closed boundary-difference formula for one digit population. -/
theorem digitBinPopulation_eq_boundary_sub {b p d : ℕ}
    (hb : 0 < b) (hp : 0 < p) (hd : d < b) :
    digitBinPopulation b p d =
      digitBinBoundary b p (d + 1) - max 1 (digitBinBoundary b p d) := by
  rw [digitBinPopulation_eq_boundary_card hb hp hd, Nat.card_Ico]

/-- The first digit bin contains exactly `floor((p-1)/b)` nonzero
remainders. -/
theorem digitBinPopulation_zero {b p : ℕ} (hb : 0 < b) (hp : 0 < p) :
    digitBinPopulation b p 0 = (p - 1) / b := by
  have hd : 0 < b := hb
  rw [digitBinPopulation_eq_boundary_sub hb hp hd]
  simp only [digitBinBoundary, zero_mul, zero_ceilDiv,
    max_eq_left (by decide : 1 ≥ 0), Nat.ceilDiv_eq_add_pred_div]
  simp only [Nat.zero_add, Nat.one_mul]
  have hpone : 1 ≤ p := hp
  have hrewrite : p + b - 1 = (p - 1) + b := by omega
  rw [hrewrite, Nat.add_div_right (p - 1) hb]
  simp

/-- For a nonzero digit index, consecutive ceiling boundaries differ by
either `q` or `q+1`, where `q=floor((p-1)/b)`. -/
theorem digitBinBoundary_gap {b p d : ℕ} (hb : 0 < b) (hp : 0 < p)
    (hd0 : 0 < d) :
    let q := (p - 1) / b
    digitBinBoundary b p (d + 1) - digitBinBoundary b p d = q ∨
      digitBinBoundary b p (d + 1) - digitBinBoundary b p d = q + 1 := by
  let q := (p - 1) / b
  let r := (p - 1) % b
  let A := digitBinBoundary b p d
  let B := digitBinBoundary b p (d + 1)
  have hrlt : r < b := Nat.mod_lt _ hb
  have hdecomp : p = b * q + r + 1 := by
    have h := Nat.mod_add_div (p - 1) b
    dsimp [q, r]
    omega
  have hApos : 0 < A := by
    by_contra hnot
    have hAzero : A = 0 := by omega
    have hreach : d * p ≤ b * A := by
      exact le_smul_ceilDiv hb
    have hdp : 0 < d * p := Nat.mul_pos hd0 hp
    rw [hAzero] at hreach
    simp only [Nat.mul_zero] at hreach
    exact (Nat.not_le_of_gt hdp) hreach
  have hAminimal : b * (A - 1) < d * p := by
    by_contra hnot
    have hle : d * p ≤ b * (A - 1) := by omega
    have hceil : digitBinBoundary b p d ≤ A - 1 := by
      exact (ceilDiv_le_iff_le_mul hb).2 hle
    dsimp [A] at hceil
    omega
  have hBupper : B ≤ A + q + 1 := by
    apply (ceilDiv_le_iff_le_mul hb).2
    change (d + 1) * p ≤ b * (A + q + 1)
    have hreach : d * p ≤ b * A := by
      have := le_smul_ceilDiv (b := d * p) hb
      simpa [A, digitBinBoundary] using this
    calc
      (d + 1) * p = d * p + p := by ring
      _ ≤ b * A + (b * q + b) := by
        apply Nat.add_le_add hreach
        omega
      _ = b * (A + q + 1) := by ring
  have hBlower : A + q ≤ B := by
    by_contra hnot
    have hBle : B ≤ A + q - 1 := by omega
    have hreach : (d + 1) * p ≤ b * B := by
      have := le_smul_ceilDiv (b := (d + 1) * p) hb
      simpa [B, digitBinBoundary] using this
    have hstrict : b * (A + q - 1) < d * p + p := by
      have hqstrict : b * q < p := by omega
      have hadd := Nat.add_lt_add hAminimal hqstrict
      have hsub : A + q - 1 = (A - 1) + q := by omega
      rw [hsub]
      simpa [Nat.mul_add] using hadd
    have : (d + 1) * p < (d + 1) * p := by
      calc
        (d + 1) * p ≤ b * B := hreach
        _ ≤ b * (A + q - 1) := Nat.mul_le_mul_left b hBle
        _ < d * p + p := hstrict
        _ = (d + 1) * p := by ring
    exact (lt_irrefl _ this)
  have hcases : B = A + q ∨ B = A + q + 1 := by omega
  rcases hcases with hcase | hcase
  · left
    have hsub : B - A = q := by
      rw [hcase]
      exact Nat.add_sub_cancel_left A q
    simpa [A, B, q] using hsub
  · right
    have hsub : B - A = q + 1 := by
      rw [hcase]
      simp [Nat.add_assoc]
    simpa [A, B, q] using hsub

/-- Every digit bin has one of the two sizes claimed in the manuscript. -/
theorem digitBinPopulation_eq_quotient_or_succ {b p d : ℕ}
    (hb : 0 < b) (hp : 0 < p) (hd : d < b) :
    digitBinPopulation b p d = (p - 1) / b ∨
      digitBinPopulation b p d = (p - 1) / b + 1 := by
  by_cases hd0 : d = 0
  · subst d
    exact Or.inl (digitBinPopulation_zero hb hp)
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    rw [digitBinPopulation_eq_boundary_sub hb hp hd]
    have hboundaryPos : 1 ≤ digitBinBoundary b p d := by
      have hreach : d * p ≤ b * digitBinBoundary b p d := le_smul_ceilDiv hb
      by_contra hnot
      have : digitBinBoundary b p d = 0 := by omega
      have hdp : 0 < d * p := Nat.mul_pos hdpos hp
      rw [this] at hreach
      simp only [Nat.mul_zero] at hreach
      exact (Nat.not_le_of_gt hdp) hreach
    rw [max_eq_right hboundaryPos]
    exact digitBinBoundary_gap hb hp hdpos

/-- The digit indices whose bins have the larger of the two possible sizes. -/
def enlargedDigitBins (b p : ℕ) : Finset ℕ :=
  (Finset.range b).filter
    (fun d => digitBinPopulation b p d = (p - 1) / b + 1)

/-- Exactly `(p-1) mod b` bins have the larger size. -/
theorem enlargedDigitBins_card {b p : ℕ} (hb : 0 < b) (hp : 0 < p) :
    (enlargedDigitBins b p).card = (p - 1) % b := by
  classical
  let q := (p - 1) / b
  let r := (p - 1) % b
  have hdecomp : p - 1 = b * q + r := by
    have h := Nat.mod_add_div (p - 1) b
    dsimp [q, r]
    omega
  have hsum := digitBinPopulation_sum hb hp
  have hterm : ∀ d ∈ Finset.range b,
      digitBinPopulation b p d =
        q + if d ∈ enlargedDigitBins b p then 1 else 0 := by
    intro d hd
    have hdlt := Finset.mem_range.mp hd
    rcases digitBinPopulation_eq_quotient_or_succ hb hp hdlt with hsmall | hlarge
    · have hnot : d ∉ enlargedDigitBins b p := by
        intro hmem
        have h := (Finset.mem_filter.mp hmem).2
        omega
      simp [hnot, q, hsmall]
    · have hmem : d ∈ enlargedDigitBins b p := by
        exact Finset.mem_filter.mpr ⟨hd, hlarge⟩
      rw [if_pos hmem]
      simpa [q] using hlarge
  have hsum' :
      ∑ d ∈ Finset.range b, digitBinPopulation b p d =
        b * q + (enlargedDigitBins b p).card := by
    calc
      ∑ d ∈ Finset.range b, digitBinPopulation b p d =
          ∑ d ∈ Finset.range b,
            (q + if d ∈ enlargedDigitBins b p then 1 else 0) := by
              apply Finset.sum_congr rfl
              exact hterm
      _ = b * q + (enlargedDigitBins b p).card := by
        rw [Finset.sum_add_distrib]
        have hfilter :
            (Finset.range b).filter (fun d => d ∈ enlargedDigitBins b p) =
              enlargedDigitBins b p := by
          ext d
          simp [enlargedDigitBins]
        rw [Finset.sum_boole, hfilter]
        simp
  rw [hsum] at hsum'
  dsimp [q, r] at hdecomp hsum' ⊢
  omega

/-- Exact closed form for the sum of squared digit-bin populations. -/
theorem digitBinSquareSum_eq_quotient_remainder {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) :
    digitBinSquareSum b p =
      b * ((p - 1) / b) ^ 2 +
        ((p - 1) % b) * (2 * ((p - 1) / b) + 1) := by
  classical
  let q := (p - 1) / b
  let r := (p - 1) % b
  have hlargeCard : (enlargedDigitBins b p).card = r := by
    exact enlargedDigitBins_card hb hp
  have hterm : ∀ d ∈ Finset.range b,
      (digitBinPopulation b p d) ^ 2 =
        q ^ 2 + if d ∈ enlargedDigitBins b p then (2 * q + 1) else 0 := by
    intro d hd
    have hdlt := Finset.mem_range.mp hd
    rcases digitBinPopulation_eq_quotient_or_succ hb hp hdlt with hsmall | hlarge
    · have hnot : d ∉ enlargedDigitBins b p := by
        intro hmem
        have h := (Finset.mem_filter.mp hmem).2
        omega
      simp [hnot, q, hsmall]
    · have hmem : d ∈ enlargedDigitBins b p := by
        exact Finset.mem_filter.mpr ⟨hd, hlarge⟩
      rw [if_pos hmem, hlarge]
      dsimp [q]
      ring
  unfold digitBinSquareSum
  calc
    ∑ d ∈ Finset.range b, (digitBinPopulation b p d) ^ 2 =
        ∑ d ∈ Finset.range b,
          (q ^ 2 + if d ∈ enlargedDigitBins b p then (2 * q + 1) else 0) := by
            apply Finset.sum_congr rfl
            exact hterm
    _ = b * q ^ 2 + (enlargedDigitBins b p).card * (2 * q + 1) := by
      rw [Finset.sum_add_distrib]
      have hfilter :
          (Finset.range b).filter (fun d => d ∈ enlargedDigitBins b p) =
            enlargedDigitBins b p := by
        ext d
        simp [enlargedDigitBins]
      rw [← Finset.sum_filter]
      rw [hfilter]
      simp [Nat.mul_comm]
    _ = b * ((p - 1) / b) ^ 2 +
        ((p - 1) % b) * (2 * ((p - 1) / b) + 1) := by
      simp [q, r, hlargeCard]

/-- Summing the population of each residue's own bin gives the global square
sum.  This is the ordered same-bin collision interpretation. -/
theorem digitBinSquareSum_eq_sum_population_at_residue {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) :
    digitBinSquareSum b p =
      ∑ r ∈ nonzeroResidues p,
        digitBinPopulation b p (digitBin b p r) := by
  classical
  have hmaps : ∀ r ∈ nonzeroResidues p,
      digitBin b p r ∈ Finset.range b := by
    intro r hr
    have hrp : r < p := Finset.mem_range.mp (Finset.mem_erase.mp hr).2
    exact Finset.mem_range.mpr (digitBin_lt_base hb hp hrp)
  unfold digitBinSquareSum
  calc
    ∑ d ∈ Finset.range b, (digitBinPopulation b p d) ^ 2 =
        ∑ d ∈ Finset.range b,
          ∑ r ∈ (nonzeroResidues p).filter (fun r => digitBin b p r = d),
            digitBinPopulation b p d := by
              apply Finset.sum_congr rfl
              intro d _
              simp [digitBinPopulation, pow_two]
    _ = ∑ r ∈ nonzeroResidues p,
        digitBinPopulation b p (digitBin b p r) := by
          rw [show (∑ d ∈ Finset.range b,
              ∑ r ∈ (nonzeroResidues p).filter (fun r => digitBin b p r = d),
                digitBinPopulation b p d) =
            ∑ d ∈ Finset.range b,
              ∑ r ∈ (nonzeroResidues p).filter (fun r => digitBin b p r = d),
                digitBinPopulation b p (digitBin b p r) by
              apply Finset.sum_congr rfl
              intro d _
              apply Finset.sum_congr rfl
              intro r hr
              rw [(Finset.mem_filter.mp hr).2]]
          exact Finset.sum_fiberwise_of_maps_to hmaps
            (fun r => digitBinPopulation b p (digitBin b p r))

/-- Every population is bounded by the ceiling of `(p-1)/b`. -/
theorem digitBinPopulation_le_ceil {b p d : ℕ} (hb : 0 < b)
    (hp : 0 < p) (hd : d < b) :
    digitBinPopulation b p d ≤ (p - 1) ⌈/⌉ b := by
  let q := (p - 1) / b
  let r := (p - 1) % b
  rcases digitBinPopulation_eq_quotient_or_succ hb hp hd with hsmall | hlarge
  · rw [hsmall]
    exact floorDiv_le_ceilDiv (a := b) (b := p - 1)
  · by_cases hr0 : r = 0
    · have hlargeMem : d ∈ enlargedDigitBins b p := by
        simp [enlargedDigitBins, hd, hlarge]
      have hcard0 : (enlargedDigitBins b p).card = 0 := by
        rw [enlargedDigitBins_card hb hp]
        exact hr0
      have hempty : enlargedDigitBins b p = ∅ := Finset.card_eq_zero.mp hcard0
      rw [hempty] at hlargeMem
      simp at hlargeMem
    · have hceil : (p - 1) ⌈/⌉ b = q + 1 := by
        apply le_antisymm
        · apply (ceilDiv_le_iff_le_mul hb).2
          have hdecomp := Nat.mod_add_div (p - 1) b
          have hrlt : r < b := Nat.mod_lt _ hb
          have hrle : r ≤ b := by omega
          calc
            p - 1 = b * q + r := by
              dsimp [q, r]
              omega
            _ ≤ b * q + b := Nat.add_le_add_left hrle _
            _ = b * (q + 1) := by ring
        · by_contra hnot
          have hle : (p - 1) ⌈/⌉ b ≤ q := by omega
          have hmul := (ceilDiv_le_iff_le_mul hb).1 hle
          have hdecomp := Nat.mod_add_div (p - 1) b
          dsimp [q, r] at hdecomp hmul hr0
          omega
      rw [hlarge, hceil]

/-- For odd `p>=5` and `b>=2`, the ceiling is at most `(p-1)/2`. -/
theorem twice_ceil_digitBinCapacity_le {b p : ℕ}
    (hb : 2 ≤ b) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    2 * ((p - 1) ⌈/⌉ b) ≤ p - 1 := by
  have hpos : 0 < b := by omega
  rcases hp.odd_of_ne_two (by omega) with ⟨k, hk⟩
  have htwo : 2 * ((p - 1) / 2) = p - 1 := by omega
  have htarget : (p - 1) ⌈/⌉ b ≤ (p - 1) / 2 := by
    apply (ceilDiv_le_iff_le_mul hpos).2
    calc
      p - 1 = 2 * ((p - 1) / 2) := htwo.symm
      _ ≤ b * ((p - 1) / 2) := Nat.mul_le_mul_right _ hb
  calc
    2 * ((p - 1) ⌈/⌉ b) ≤ 2 * ((p - 1) / 2) :=
      Nat.mul_le_mul_left 2 htarget
    _ = p - 1 := htwo

end NField.Alignment
