/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.DiagonalSlice
import NField.Alignment.CollisionFluctuationClosure
import NField.Alignment.CollisionTransform
import NField.Alignment.PrimeCarryFiberCentering
import NField.Alignment.SilentPrimesClosure

/-!
# Closure for all-lag collision centering

This module joins the intrinsic digit collision at an arbitrary positive lag
to the endpoint-corrected finite table.  It then exposes the natural coarse
reduction, the concrete spectral gate, the prime-base column law, and the
finite algebra used when classical prime-progression limits are supplied.
-/

namespace NField.Alignment.CenteredCollisionClosure

open scoped BigOperators ComplexConjugate Topology
open Filter
open NField.CollisionDefinition
open NField.DiagonalSlice
open NField.Alignment.SpectralPower
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.BinDerangementsClosure
open NField.Alignment.SilentPrimes
open NField.Alignment.SilentPrimesClosure
open NField.Alignment.FinitePrefixCarryReduction
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionFluctuationClosure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionInvariant
open NField.Alignment.NeutralityTheorem
open NField.Alignment.PrimeCarryTableColumnLaw
open NField.Alignment.PrimeCarryFiberCentering

/-! ## The intrinsic all-lag diagonal -/

/-- The encoded first/last-digit diagonal is exactly the quotient-remainder
condition used in the manuscript. -/
theorem mem_allLagDiagonal_iff_quotient_eq_remainder
    {b ell n : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hn : n < allLagModulus b ell) :
    n ∈ allLagDiagonal b ell ↔ n / b ^ ell = n % b := by
  have hb : 0 < b := by omega
  have hmodulus : allLagModulus b ell = b ^ (ell + 1) := rfl
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨⟨d, k⟩, hdk, rfl⟩
    have hd : d < b := Finset.mem_range.mp (Finset.mem_product.mp hdk).1
    have hk : k < b ^ (ell - 1) :=
      Finset.mem_range.mp (Finset.mem_product.mp hdk).2
    have hdiag := diagonalParam_member b ell d k hb hell hd hk
    have hparam :
        (b ^ ell + 1) * d + b * k = diagonalParam b ell d k := by
      simp [diagonalParam]
      ring
    rw [hparam]
    simpa [diagonalMember] using hdiag
  · intro hdiag
    have hbool : diagonalMember b ell n = true := by
      simpa [diagonalMember] using hdiag
    obtain ⟨d, k, hd, hk, hnparam⟩ :=
      diagonalMember_param_exists b ell n hb hell (by simpa [hmodulus] using hn)
        hbool
    apply Finset.mem_image.mpr
    refine ⟨(d, k), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hd, Finset.mem_range.mpr hk⟩, ?_⟩
    rw [hnparam]
    simp [diagonalParam]
    ring

/-- The leading digit of an `(ell+1)`-digit cell code is its quotient by
`b^ell`. -/
theorem encodedPrefixDigit_allLag_first
    {b ell n : ℕ} (hb : 0 < b)
    (hn : n < b ^ (ell + 1)) :
    encodedPrefixDigit b (ell + 1) n 0 = n / b ^ ell := by
  have hpow : 0 < b ^ ell := pow_pos hb ell
  have hquot : n / b ^ ell < b := by
    rw [Nat.div_lt_iff_lt_mul hpow]
    simpa [pow_succ, Nat.mul_comm] using hn
  unfold encodedPrefixDigit
  simp [Nat.mod_eq_of_lt hquot]

/-- The trailing digit of an `(ell+1)`-digit cell code is its remainder
modulo the base. -/
theorem encodedPrefixDigit_allLag_last (b ell n : ℕ) :
    encodedPrefixDigit b (ell + 1) n ell = n % b := by
  simp [encodedPrefixDigit]

/-- The digit at lag `ell` is the leading digit of the transported
remainder. -/
theorem digitReadout_eq_transported_digitBin (b p r ell : ℕ) :
    digitReadout b p r ell = digitBin b p ((b ^ ell * r) % p) := by
  rfl

/-- A direct lagged digit collision is exactly membership in the intrinsic
first/last-digit diagonal cell. -/
theorem direct_allLag_collision_iff_prefix_cell_mem
    {b ell p r : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : 0 < p) (hr : r < p) :
    digitBin b p r = digitBin b p ((b ^ ell * r) % p) ↔
      allLagModulus b ell * r / p ∈ allLagDiagonal b ell := by
  have hb : 0 < b := by omega
  have hm : 0 < allLagModulus b ell := pow_pos hb _
  have hn : allLagModulus b ell * r / p < allLagModulus b ell :=
    prefixCell_lt hm hp hr
  rw [mem_allLagDiagonal_iff_quotient_eq_remainder hb2 hell hn]
  rw [← encodedPrefixDigit_allLag_first hb (by simpa [allLagModulus] using hn),
    ← encodedPrefixDigit_allLag_last b ell
      (allLagModulus b ell * r / p)]
  rw [show allLagModulus b ell = b ^ (ell + 1) by rfl]
  rw [prefixIndex_digit hb hp (show 0 < ell + 1 by omega),
    prefixIndex_digit hb hp (show ell < ell + 1 by omega)]
  rw [digitReadout_zero_eq_digitBin hr,
    digitReadout_eq_transported_digitBin]

/-- Indicator of the intrinsic all-lag diagonal. -/
def allLagDiagonalWeight (b ell n : ℕ) : ℂ :=
  if n ∈ allLagDiagonal b ell then 1 else 0

/-- The direct all-lag collision count is the diagonal-weighted prefix
count. -/
theorem directAllLagCollisionCount_cast_eq_prefixWeightedCount
    {b ell p : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (hp : 0 < p) :
    (directAllLagCollisionCount b ell p : ℂ) =
      prefixWeightedCount (allLagModulus b ell) p
        (allLagDiagonalWeight b ell) := by
  classical
  unfold directAllLagCollisionCount prefixWeightedCount allLagDiagonalWeight
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  have hrp : r < p := (Finset.mem_Ico.mp hr).2
  have hiff := direct_allLag_collision_iff_prefix_cell_mem
    hb2 hell hp hrp
  by_cases hcollision :
      digitBin b p r = digitBin b p ((b ^ ell * r) % p)
  · have hmem := hiff.mp hcollision
    simp [hcollision, hmem]
  · have hnotmem :
        allLagModulus b ell * r / p ∉ allLagDiagonal b ell := by
      exact fun hmem => hcollision (hiff.mpr hmem)
    simp [hcollision, hnotmem]

/-- The diagonal indicator has total mass `b^ell` on the full cell range. -/
theorem allLagDiagonalWeight_sum {b ell : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    ∑ n ∈ Finset.range (allLagModulus b ell),
        allLagDiagonalWeight b ell n = (b ^ ell : ℂ) := by
  classical
  unfold allLagDiagonalWeight
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.range (allLagModulus b ell)).filter
          (fun n => n ∈ allLagDiagonal b ell) =
        allLagDiagonal b ell := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hmem
      exact ⟨allLagDiagonal_index_lt hb2 hell hmem, hmem⟩
  rw [hfilter]
  simp [allLagDiagonal_card hb2 hell]

/-- On the diagonal indicator, the generic weighted carry count is the
manuscript's all-lag floor-jump sum. -/
theorem weightedCarryCount_allLagDiagonalWeight
    {b ell a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    weightedCarryCount (allLagModulus b ell) a
        (allLagDiagonalWeight b ell) =
      ((∑ n ∈ allLagDiagonal b ell,
        floorJump (allLagModulus b ell) a n : ℤ) : ℂ) := by
  classical
  unfold weightedCarryCount allLagDiagonalWeight
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.range (allLagModulus b ell)).filter
          (fun n => n ∈ allLagDiagonal b ell) =
        allLagDiagonal b ell := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hmem
      exact ⟨allLagDiagonal_index_lt hb2 hell hmem, hmem⟩
  rw [hfilter]
  calc
    (∑ n ∈ allLagDiagonal b ell,
        ((((n + 1) * a / allLagModulus b ell -
          n * a / allLagModulus b ell : ℕ) : ℂ))) =
        ∑ n ∈ allLagDiagonal b ell,
          ((floorJump (allLagModulus b ell) a n : ℤ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro n _hn
      have hle :
          n * a / allLagModulus b ell ≤
            (n + 1) * a / allLagModulus b ell :=
        Nat.div_le_div_right (Nat.mul_le_mul_right a (Nat.le_succ n))
      have hjump :
          floorJump (allLagModulus b ell) a n =
            ((((n + 1) * a / allLagModulus b ell -
              n * a / allLagModulus b ell : ℕ) : ℤ)) := by
        unfold floorJump
        exact (Nat.cast_sub hle).symm
      rw [hjump]
      norm_num
    _ = ((∑ n ∈ allLagDiagonal b ell,
        floorJump (allLagModulus b ell) a n : ℤ) : ℂ) := by
      norm_cast

/-- The intrinsic digit collision count is exactly the endpoint-corrected
all-lag diagonal slice score throughout every coprime progression. -/
theorem directAllLagCollisionCount_eq_allLagSliceScore
    {b ell p t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : p = allLagModulus b ell * t + a)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    (directAllLagCollisionCount b ell p : ℤ) =
      allLagSliceScore b ell p := by
  have hb : 0 < b := by omega
  have hm : 0 < allLagModulus b ell := pow_pos hb _
  have hppos : 0 < p := by omega
  have hprefix :=
    directAllLagCollisionCount_cast_eq_prefixWeightedCount hb2 hell hppos
  have hp' : p = t * allLagModulus b ell + a := by
    rw [hp]
    ring
  have hslice := finitePrefixSliceIdentity hm hp' ha halt hcop
    (allLagDiagonalWeight b ell)
  rw [hslice, allLagDiagonalWeight_sum hb2 hell,
    weightedCarryCount_allLagDiagonalWeight hb2 hell] at hprefix
  rw [show allLagDiagonalWeight b ell (allLagModulus b ell - 1) = 1 by
    simp [allLagDiagonalWeight, allLagDiagonal_last_mem hb2 hell]] at hprefix
  have hprefixZ :
      (directAllLagCollisionCount b ell p : ℤ) =
        ((t * b ^ ell : ℕ) : ℤ) +
          ∑ n ∈ allLagDiagonal b ell,
            floorJump (allLagModulus b ell) a n - 1 := by
    exact_mod_cast hprefix
  rw [hp] at hprefixZ
  rw [hp, allLagSliceScore_add_modulus_mul hb]
  rw [allLagDiagonal_card hb2 hell]
  unfold allLagSliceScore
  rw [hprefixZ]
  push_cast
  ring

/-- The direct digit-collision deviation is therefore the exact all-lag
finite table, not merely a bounded numerical agreement. -/
theorem directAllLagDeviation_eq_allLagTable
    {b ell t a : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) (halt : a < allLagModulus b ell)
    (hcop : a.Coprime (allLagModulus b ell)) :
    directAllLagDeviation b ell (allLagModulus b ell * t + a) =
      allLagTable b ell a := by
  unfold directAllLagDeviation
  rw [directAllLagCollisionCount_eq_allLagSliceScore hb2 hell rfl ha halt hcop]
  change allLagSliceDeviation b ell (allLagModulus b ell * t + a) =
    allLagTable b ell a
  exact allLagSliceDeviation_eq_table hb2 hell ha hcop

/-! ## The concrete centered unit table -/

/-- Reflection fixes the grand mean of the literal all-lag unit table at
`-1/2`. -/
theorem allLagUnitTable_grand_mean
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) :
    (Fintype.card (UnitClass (allLagModulus b ell)) : ℂ)⁻¹ *
        ∑ a : UnitClass (allLagModulus b ell), allLagUnitTable b ell a =
      -1 / 2 :=
  collisionInvariant_grand_mean hb2 hell

/-- Natural reduction to the base unit group is the intrinsic centering map,
and every one of its fibers has centered sum zero. -/
theorem natural_centering_fiber_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (u : UnitClass b) :
    ∑ a : Fiber (coarseUnitReduction b ell) u,
        centeredCollisionTransform b ell a = 0 := by
  unfold centeredCollisionTransform
  exact centeredSignal_fiber_sum_zero
    (coarseUnitReduction b ell) (allLagUnitTable b ell) u
    ⟨⟨(coarseUnitReduction_surjective b ell u).choose,
      (coarseUnitReduction_surjective b ell u).choose_spec⟩⟩

/-- The exact means of two reflected coarse fibers sum to `-1`. -/
theorem natural_fiber_mean_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell) (u : UnitClass b) :
    fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) u +
        fiberMean (coarseUnitReduction b ell) (allLagUnitTable b ell) (-u) =
      -1 := by
  apply fiberMean_reflection
    (coarseUnitReduction b ell) (allLagUnitTable b ell)
    (fun a => -a) (fun v => -v)
  · intro a
    exact neg_neg a
  · intro v
    exact neg_neg v
  · exact coarseUnitReduction_neg
  · exact allLagUnitTable_reflection hb2 hell
  · exact ⟨⟨(coarseUnitReduction_surjective b ell u).choose,
      (coarseUnitReduction_surjective b ell u).choose_spec⟩⟩

/-- Concrete reflection makes the naturally centered all-lag table odd. -/
theorem natural_centered_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTransform b ell (-a) =
      -centeredCollisionTransform b ell a :=
  centeredCollisionTransform_odd hb2 hell a

/-- Every even Dirichlet-character channel vanishes on the concrete centered
table. -/
theorem natural_even_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (heven : χ.Even) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  centeredCollisionTransform_even_zero hb2 hell χ heven

/-- Every character descending to the base unit group vanishes on the
concrete centered table. -/
theorem natural_base_factored_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (χ : Character (allLagModulus b ell)) (hfactor : BaseFactored χ) :
    collisionCoefficient (centeredCollisionTransform b ell) χ = 0 :=
  centeredCollisionTransform_baseFactored_zero χ hfactor

/-! ## Constructive all-lag multiplier -/

/-- Above the all-lag modulus, the power multiplier is nonidentity and has
positive collision count, so it belongs to the literal constructive
population used by the manuscript. -/
theorem powerMultiplier_mem_constructiveMultiplierSet
    {b p ell : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : Nat.Prime p) [NeZero p]
    (hlarge : b ^ (ell + 1) < p) :
    powerMultiplier b p ell ∈
      constructiveMultiplierSet b p (by omega) hp := by
  have hbpos : 0 < b := by omega
  have hpowpos : 0 < b ^ ell := pow_pos hbpos ell
  have hbpow : b ≤ b ^ ell := Nat.le_pow hell
  have hbase_lt_next : b < b ^ (ell + 1) := by
    rw [pow_succ]
    nlinarith
  have hbp : b < p := hbase_lt_next.trans hlarge
  have hpowlt_next : b ^ ell < b ^ (ell + 1) := by
    rw [pow_succ]
    nlinarith
  have hpowlt : b ^ ell < p := hpowlt_next.trans hlarge
  have hpowgt : 1 < b ^ ell :=
    Nat.one_lt_pow (by omega : ell ≠ 0) (by omega : 1 < b)
  have hg1 : powerMultiplier b p ell ≠ 1 := by
    intro hg
    change ((b ^ ell : ℕ) : ZMod p) = 1 at hg
    have hg' : ((b ^ ell : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa using hg
    rw [ZMod.natCast_eq_natCast_iff] at hg'
    have hmod : b ^ ell % p = 1 % p := by
      simpa [Nat.ModEq] using hg'
    rw [Nat.mod_eq_of_lt hpowlt,
      Nat.mod_eq_of_lt hp.one_lt] at hmod
    exact hpowgt.ne' hmod
  have hpositive :
      0 < collisionCount (primeDigitWord b p (by omega) hp.pos)
        (powerMultiplier b p ell) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hsilent : GloballySilentAt b p ell (by omega) hp := by
      simpa [GloballySilentAt, powerMultiplier] using hzero
    have hbound := globallySilentAt_bound hb2 hp hbp hsilent
    omega
  simp only [constructiveMultiplierSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨hg1, hpositive⟩

/-! ## Prime-base columns -/

/-- The floor sum used to aggregate one lag-one reduction column. -/
def columnFloorSum (b c s : ℕ) : ℕ :=
  ∑ k ∈ Finset.range b, c * (b * k + s) / b ^ 2

/-- The unit-multiplier floor sum at the exceptional prime base two. -/
theorem columnFloorSum_unit_base_two
    {c s : ℕ} (hspos : 1 ≤ s) (hslt : s < 2) (hc : ¬2 ∣ c) :
    columnFloorSum 2 c s =
      (c - 1) * (2 - 1) / 2 + c * s / 2 := by
  have hs : s = 1 := by omega
  subst s
  have hcmod : c % 2 = 1 := by
    have hlt := Nat.mod_lt c (by omega : 0 < 2)
    have hne : c % 2 ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp hc
    omega
  unfold columnFloorSum
  simp [Finset.sum_range_succ, pow_two]
  omega

/-- The manuscript's unit-multiplier floor-sum formula for every prime
base, including base two. -/
theorem columnFloorSum_unit_prime
    {b c s : ℕ} (hb : Nat.Prime b)
    (hspos : 1 ≤ s) (hslt : s < b) (hc : ¬b ∣ c) :
    columnFloorSum b c s =
      (c - 1) * (b - 1) / 2 + c * s / b := by
  by_cases hb2 : b = 2
  · subst b
    exact columnFloorSum_unit_base_two hspos hslt hc
  · have hbodd : Odd b := hb.odd_of_ne_two hb2
    have hcop : c.Coprime b := by
      rw [Nat.coprime_comm, hb.coprime_iff_not_dvd]
      exact hc
    have hsum := sum_square_floor_column hb.pos hbodd hcop (s := s)
    have htwo : 2 * ((b - 1) / 2) = b - 1 := by
      rcases hbodd with ⟨t, ht⟩
      omega
    have hdiv : 2 ∣ b - 1 :=
      ⟨(b - 1) / 2, htwo.symm⟩
    have hfactor :
        (c - 1) * (b - 1) / 2 = (c - 1) * ((b - 1) / 2) := by
      exact Nat.mul_div_assoc (c - 1) hdiv
    unfold columnFloorSum
    rw [hsum, hfactor]

/-- The manuscript's base-multiple floor-sum formula. -/
theorem columnFloorSum_base_multiple
    {b h s : ℕ} (hb : 0 < b) :
    columnFloorSum b (b * h) s =
      h * b * (b - 1) / 2 + b * (h * s / b) := by
  have hpoint (k : ℕ) :
      (b * h) * (b * k + s) / b ^ 2 = h * k + h * s / b := by
    rw [square_floor_depth_reduction hb]
    have hcs : (b * h) * s / b = h * s := by
      rw [show (b * h) * s = b * (h * s) by ring]
      exact Nat.mul_div_right (h * s) hb
    rw [hcs]
    rw [show (b * h) * k + h * s = b * (h * k) + h * s by ring]
    rw [Nat.mul_add_div hb]
  unfold columnFloorSum
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_range_id]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Nat.mul_div_assoc h (Nat.even_mul_pred_self b).two_dvd]
  ac_rfl

/-- At lag one the natural-valued all-lag table is the earlier square carry
table definition. -/
theorem allLagTable_one_eq_fluctuationTable (b a : ℕ) :
    allLagTable b 1 a = fluctuationTable b a := by
  unfold allLagTable fluctuationTable
  simp only [allLagModulus, Nat.reduceAdd, pow_two]
  rw [NField.Alignment.AnalyticCollisionTransform.allLagDiagonal_one_eq_diagonalSlices]

/-- Every nonzero column of a prime-base lag-one table has exact sum `s-p`.
The base-two column is included. -/
theorem primeBase_tableFiberSum
    {p s : ℕ} (hp : p.Prime) (hspos : 0 < s) (hslt : s < p) :
    tableFiberSum p 1 s = (s : ℤ) - p := by
  by_cases hp2 : p = 2
  · subst p
    have hs : s = 1 := by omega
    subst s
    decide
  · have hp2le : 2 ≤ p := hp.two_le
    have hcop : s.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hdiv
      have hle := Nat.le_of_dvd (by omega : 0 < s) hdiv
      omega
    have hunit : s ∈ reducedResidues p := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨hspos, hslt⟩, hcop⟩
    rw [tableFiberSum, tableFiber_eq_coordinates hp2le hunit]
    unfold fiberCoordinates
    simp only [pow_one]
    rw [Finset.sum_image]
    · calc
        (∑ k ∈ Finset.range p, allLagTable p 1 (s + p * k)) =
            ∑ k ∈ Finset.range p,
              fluctuationTable p (p * k + s) := by
                apply Finset.sum_congr rfl
                intro k _hk
                rw [allLagTable_one_eq_fluctuationTable,
                  Nat.add_comm s (p * k)]
        _ = (s : ℤ) - p :=
          fluctuationTable_column_sum hp hp2 hspos hslt
    · intro k _hk j _hj hkj
      have hmul : p * k = p * j := Nat.add_left_cancel hkj
      exact Nat.mul_left_cancel hp.pos hmul

/-- Hence the exact prime-base reduction-fiber mean is `s/p-1`. -/
theorem primeBase_tableFiberMean
    {p s : ℕ} (hp : p.Prime) (hspos : 0 < s) (hslt : s < p) :
    (p : ℚ)⁻¹ * (tableFiberSum p 1 s : ℚ) =
      (s : ℚ) / p - 1 := by
  rw [primeBase_tableFiberSum hp hspos hslt]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast
  field_simp [hpq]

/-! ## Conditional prime-progression assembly -/

/-- A finite centered signal cancels any common class term.  Once the
classwise residual limits are supplied, only their finite weighted constant
remains. -/
theorem centered_progression_residual_limit
    {α ι : Type*} [Fintype α]
    {lfilter : Filter ι}
    (f : α → ℝ) (A : ι → α → ℝ) (common : ι → ℝ)
    (K : α → ℝ) (hzero : ∑ a, f a = 0)
    (hclass : ∀ a,
      Tendsto (fun x => A x a - common x) lfilter (𝓝 (K a))) :
    Tendsto (fun x => ∑ a, f a * A x a) lfilter
      (𝓝 (∑ a, f a * K a)) := by
  have hsum :
      Tendsto (fun x => ∑ a, f a * (A x a - common x)) lfilter
        (𝓝 (∑ a, f a * K a)) := by
    apply tendsto_finsetSum
    intro a _ha
    exact (hclass a).const_mul (f a)
  have hrewrite (x : ι) :
      (∑ a, f a * A x a) =
        ∑ a, f a * (A x a - common x) := by
    calc
      (∑ a, f a * A x a) =
          ∑ a, ((f a * (A x a - common x)) + f a * common x) := by
            apply Finset.sum_congr rfl
            intro a _ha
            ring
      _ = (∑ a, f a * (A x a - common x)) +
          ∑ a, f a * common x := Finset.sum_add_distrib
      _ = (∑ a, f a * (A x a - common x)) +
          (∑ a, f a) * common x := by rw [Finset.sum_mul]
      _ = ∑ a, f a * (A x a - common x) := by rw [hzero, zero_mul, add_zero]
  rw [show (fun x => ∑ a, f a * A x a) =
      fun x => ∑ a, f a * (A x a - common x) by
        funext x
        exact hrewrite x]
  exact hsum

/-- If every progression has the same limiting density, a finite centered
signal has limiting average zero. -/
theorem centered_progression_common_limit
    {α ι : Type*} [Fintype α]
    {lfilter : Filter ι}
    (f : α → ℝ) (A : ι → α → ℝ) (c : ℝ)
    (hzero : ∑ a, f a = 0)
    (hclass : ∀ a, Tendsto (fun x => A x a) lfilter (𝓝 c)) :
    Tendsto (fun x => ∑ a, f a * A x a) lfilter (𝓝 0) := by
  have hresidual (a : α) :
      Tendsto (fun x => A x a - c) lfilter (𝓝 0) := by
    have hc : Tendsto (fun _ : ι => c) lfilter (𝓝 c) :=
      tendsto_const_nhds
    simpa using (hclass a).sub hc
  simpa using centered_progression_residual_limit f A (fun _ => c)
    (fun _ => 0) hzero hresidual

end NField.Alignment.CenteredCollisionClosure
