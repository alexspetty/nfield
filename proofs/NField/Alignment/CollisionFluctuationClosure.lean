/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPeriodicTable
import NField.Alignment.FinitePrefixCarryReduction

/-!
# Closure for the collision fluctuation sum

This module joins the intrinsic lag-one digit collision count to the finite
diagonal table.  It also specializes the two abstract finite means to the
literal reduced-residue systems used in the manuscript and records the exact
algebra by which two residual limits combine.
-/

namespace NField.Alignment.CollisionFluctuationClosure

open scoped BigOperators Topology
open Filter
open NField.CollisionDefinition
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionPeriodicTable
open NField.Alignment.FinitePrefixCarryReduction

/-! ## The intrinsic two-digit diagonal -/

/-- A cell below `b^2` lies on the two-digit diagonal exactly when its
quotient and remainder on division by `b` agree. -/
theorem mem_diagonalSlices_iff_quotient_eq_remainder
    {b n : ℕ} (hb : 0 < b) (hn : n < b ^ 2) :
    n ∈ diagonalSlices b ↔ n / b = n % b := by
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨d, hd, rfl⟩
    have hdlt : d < b := Finset.mem_range.mp hd
    rw [show (b + 1) * d = d + b * d by ring]
    rw [Nat.add_mul_div_left d d hb, Nat.add_mul_mod_self_left]
    simp [Nat.div_eq_of_lt hdlt, Nat.mod_eq_of_lt hdlt]
  · intro heq
    apply Finset.mem_image.mpr
    refine ⟨n % b, Finset.mem_range.mpr (Nat.mod_lt n hb), ?_⟩
    calc
      (b + 1) * (n % b) = n % b + b * (n % b) := by ring
      _ = n % b + b * (n / b) := by rw [heq]
      _ = n := Nat.mod_add_div n b

/-- The first digit read from long division is the manuscript's digit map. -/
theorem digitReadout_zero_eq_digitBin
    {b q r : ℕ} (hr : r < q) :
    digitReadout b q r 0 = digitBin b q r := by
  simp [digitReadout, remainderAfter, digitBin, Nat.mod_eq_of_lt hr]

/-- The second digit read from long division is the digit of the transported
remainder. -/
theorem digitReadout_one_eq_transported_digitBin (b q r : ℕ) :
    digitReadout b q r 1 = digitBin b q ((b * r) % q) := by
  simp [digitReadout, remainderAfter, digitBin]

/-- The leading digit of a two-digit cell code is its quotient by `b`. -/
theorem encodedPrefixDigit_two_zero
    {b n : ℕ} (hb : 0 < b) (hn : n < b ^ 2) :
    encodedPrefixDigit b 2 n 0 = n / b := by
  unfold encodedPrefixDigit
  simp only [Nat.reduceSub, pow_one]
  rw [Nat.mod_eq_of_lt]
  exact (Nat.div_lt_iff_lt_mul hb).2 (by simpa [pow_two] using hn)

/-- The trailing digit of a two-digit cell code is its remainder modulo `b`. -/
theorem encodedPrefixDigit_two_one (b n : ℕ) :
    encodedPrefixDigit b 2 n 1 = n % b := by
  simp [encodedPrefixDigit]

/-- The direct lag-one digit collision is exactly membership in the diagonal
cell set. -/
theorem direct_collision_iff_prefix_cell_mem
    {b q r : ℕ} (hb : 0 < b) (hq : 0 < q) (hr : r < q) :
    digitBin b q r = digitBin b q ((b * r) % q) ↔
      b ^ 2 * r / q ∈ diagonalSlices b := by
  let n := b ^ 2 * r / q
  have hn : n < b ^ 2 := prefixCell_lt (pow_pos hb 2) hq hr
  rw [mem_diagonalSlices_iff_quotient_eq_remainder hb hn]
  rw [← encodedPrefixDigit_two_zero hb hn,
    ← encodedPrefixDigit_two_one b n]
  rw [prefixIndex_digit hb hq (show 0 < 2 by omega),
    prefixIndex_digit hb hq (show 1 < 2 by omega)]
  rw [digitReadout_zero_eq_digitBin hr,
    digitReadout_one_eq_transported_digitBin]

/-- Indicator of the two-digit diagonal. -/
def diagonalWeight (b n : ℕ) : ℂ :=
  if n ∈ diagonalSlices b then 1 else 0

/-- The direct collision count is the diagonal-weighted prefix count. -/
theorem directLagOneCollisionCount_cast_eq_prefixWeightedCount
    {b q : ℕ} (hb : 0 < b) (hq : 0 < q) :
    (directLagOneCollisionCount b q : ℂ) =
      prefixWeightedCount (b ^ 2) q (diagonalWeight b) := by
  classical
  unfold directLagOneCollisionCount prefixWeightedCount diagonalWeight
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  have hrq : r < q := (Finset.mem_Ico.mp hr).2
  have hiff := direct_collision_iff_prefix_cell_mem hb hq hrq
  by_cases hcollision :
      digitBin b q r = digitBin b q ((b * r) % q)
  · have hmem := hiff.mp hcollision
    simp [hcollision, hmem]
  · have hnotmem : b ^ 2 * r / q ∉ diagonalSlices b := by
      exact fun hmem => hcollision (hiff.mpr hmem)
    simp [hcollision, hnotmem]

/-- Every diagonal cell lies below `b^2`. -/
theorem diagonalSlice_lt_square
    {b n : ℕ} (hb : 0 < b) (hn : n ∈ diagonalSlices b) :
    n < b ^ 2 := by
  rcases Finset.mem_image.mp hn with ⟨d, hd, rfl⟩
  have hdlt : d < b := Finset.mem_range.mp hd
  have hdle : d ≤ b - 1 := by omega
  have hprod : (b + 1) * (b - 1) + 1 = b ^ 2 := by
    let k := b - 1
    have hbk : b = k + 1 := by dsimp [k]; omega
    rw [hbk]
    simp
    ring
  calc
    (b + 1) * d ≤ (b + 1) * (b - 1) := Nat.mul_le_mul_left _ hdle
    _ < b ^ 2 := by omega

/-- Summing the diagonal indicator over the square gives exactly `b`. -/
theorem diagonalWeight_sum {b : ℕ} (hb : 0 < b) :
    ∑ n ∈ Finset.range (b ^ 2), diagonalWeight b n = (b : ℂ) := by
  classical
  unfold diagonalWeight
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.range (b ^ 2)).filter (fun n => n ∈ diagonalSlices b) =
        diagonalSlices b := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hmem
      exact ⟨diagonalSlice_lt_square hb hmem, hmem⟩
  rw [hfilter]
  simp [diagonalSlices_card]

/-- The terminal cell of the square lies on the diagonal. -/
theorem square_pred_mem_diagonalSlices {b : ℕ} (hb : 0 < b) :
    b ^ 2 - 1 ∈ diagonalSlices b := by
  apply Finset.mem_image.mpr
  refine ⟨b - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hprod : (b + 1) * (b - 1) + 1 = b ^ 2 := by
    let k := b - 1
    have hbk : b = k + 1 := by dsimp [k]; omega
    rw [hbk]
    simp
    ring
  omega

/-- On the diagonal indicator, the generic weighted carry count is exactly
the manuscript's sum of floor jumps. -/
theorem weightedCarryCount_diagonalWeight
    {b a : ℕ} (hb : 0 < b) :
    weightedCarryCount (b ^ 2) a (diagonalWeight b) =
      ((∑ n ∈ diagonalSlices b, floorJump (b ^ 2) a n : ℤ) : ℂ) := by
  classical
  unfold weightedCarryCount diagonalWeight
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.range (b ^ 2)).filter (fun n => n ∈ diagonalSlices b) =
        diagonalSlices b := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hmem
      exact ⟨diagonalSlice_lt_square hb hmem, hmem⟩
  rw [hfilter]
  calc
    (∑ n ∈ diagonalSlices b,
        (((n + 1) * a / b ^ 2 - n * a / b ^ 2 : ℕ) : ℂ)) =
        ∑ n ∈ diagonalSlices b,
          ((floorJump (b ^ 2) a n : ℤ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro n _hn
      have hle : n * a / b ^ 2 ≤ (n + 1) * a / b ^ 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul_right a (Nat.le_succ n))
      have hjump :
          floorJump (b ^ 2) a n =
            (((n + 1) * a / b ^ 2 - n * a / b ^ 2 : ℕ) : ℤ) := by
        unfold floorJump
        exact (Nat.cast_sub hle).symm
      rw [hjump]
      norm_num
    _ = ((∑ n ∈ diagonalSlices b,
        floorJump (b ^ 2) a n : ℤ) : ℂ) := by norm_cast

/-- The direct digit collision count is exactly the endpoint-corrected
diagonal slice score for every coprime square residue. -/
theorem directLagOneCollisionCount_eq_sliceCollisionScore
    {b q h a : ℕ} (hb2 : 2 ≤ b) (hq : q = b ^ 2 * h + a)
    (ha1 : 1 ≤ a) (halt : a < b ^ 2) (hcop : a.Coprime (b ^ 2)) :
    (directLagOneCollisionCount b q : ℤ) = sliceCollisionScore b q := by
  have hb : 0 < b := by omega
  have hm : 0 < b ^ 2 := pow_pos hb 2
  have hqpos : 0 < q := by omega
  have hprefix :=
    directLagOneCollisionCount_cast_eq_prefixWeightedCount hb hqpos
  have hq' : q = h * b ^ 2 + a := by rw [hq]; ring
  have hslice :=
    finitePrefixSliceIdentity hm hq' ha1 halt hcop (diagonalWeight b)
  rw [hslice, diagonalWeight_sum hb,
    weightedCarryCount_diagonalWeight hb] at hprefix
  rw [show diagonalWeight b (b ^ 2 - 1) = 1 by
    simp [diagonalWeight, square_pred_mem_diagonalSlices hb]] at hprefix
  have hprefixZ :
      (directLagOneCollisionCount b q : ℤ) =
        ((h * b : ℕ) : ℤ) +
          ∑ n ∈ diagonalSlices b, floorJump (b ^ 2) a n - 1 := by
    exact_mod_cast hprefix
  rw [hq] at hprefixZ
  rw [hq, sliceCollisionScore_add_square_mul hb]
  unfold sliceCollisionScore
  rw [hprefixZ]
  push_cast
  ring

/-- Hence the direct integer deviation is the finite table throughout the
full coprime square progression, not merely on a bounded decimal sample. -/
theorem directIntegerDeviation_eq_fluctuationTable
    {b h a : ℕ} (hb2 : 2 ≤ b) (ha1 : 1 ≤ a)
    (halt : a < b ^ 2) (hcop : a.Coprime (b ^ 2)) :
    directIntegerDeviation b (b ^ 2 * h + a) = fluctuationTable b a := by
  unfold directIntegerDeviation
  rw [directLagOneCollisionCount_eq_sliceCollisionScore hb2 rfl ha1 halt hcop]
  exact sliceDeviation_eq_fluctuationTable hb2 ha1 hcop

/-- The earlier bounded decimal regression is a corollary of the universal
intrinsic collision-to-table theorem. -/
theorem decimal_direct_collision_regression :
    ∀ p ∈ decimalRegressionPrimes,
      directIntegerDeviation 10 p = fluctuationTable 10 (p % 100) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpprime⟩
  have hpBounds := Finset.mem_Icc.mp hpIcc
  have hnotdvd : ¬p ∣ 100 := by
    intro hdiv
    have hple : p ≤ 100 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hpcop : p.Coprime 100 := hpprime.coprime_iff_not_dvd.mpr hnotdvd
  have hcop : (p % 100).Coprime 100 :=
    (ZMod.coprime_mod_iff_coprime p 100).2 hpcop
  have hapos : 1 ≤ p % 100 := by
    have hne : p % 100 ≠ 0 := by
      intro hzero
      rw [hzero] at hcop
      norm_num at hcop
    omega
  have halt : p % 100 < 10 ^ 2 := by
    simpa using Nat.mod_lt p (by norm_num : 0 < 100)
  have hpdecomp : p = 10 ^ 2 * (p / 100) + p % 100 := by
    have hdiv := Nat.mod_add_div p 100
    norm_num [pow_two] at hdiv ⊢
    omega
  have hresult := directIntegerDeviation_eq_fluctuationTable
    (b := 10) (h := p / 100) (a := p % 100)
    (by norm_num) hapos halt (by norm_num [pow_two] at hcop ⊢; exact hcop)
  rw [← hpdecomp] at hresult
  exact hresult

/-! ## The literal reduced-residue means -/

/-- The reduced residue representatives modulo `b`. -/
abbrev BaseUnit (b : ℕ) :=
  {u : ℕ // u ∈ reducedResidues b}

/-- Complementation on the literal reduced residue system. -/
def baseUnitComplement (b : ℕ) (_hb2 : 2 ≤ b) : BaseUnit b ≃ BaseUnit b where
  toFun u := ⟨b - u, by
    rcases Finset.mem_filter.mp u.property with ⟨hurange, hcop⟩
    have huIco := Finset.mem_Ico.mp hurange
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · exact (Nat.coprime_self_sub_left (by omega)).2 hcop⟩
  invFun u := ⟨b - u, by
    rcases Finset.mem_filter.mp u.property with ⟨hurange, hcop⟩
    have huIco := Finset.mem_Ico.mp hurange
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · exact (Nat.coprime_self_sub_left (by omega)).2 hcop⟩
  left_inv u := by
    apply Subtype.ext
    have huIco := Finset.mem_Ico.mp (Finset.mem_filter.mp u.property).1
    change b - (b - (u : ℕ)) = (u : ℕ)
    omega
  right_inv u := by
    apply Subtype.ext
    have huIco := Finset.mem_Ico.mp (Finset.mem_filter.mp u.property).1
    change b - (b - (u : ℕ)) = (u : ℕ)
    omega

/-- Complementary reduced representatives add to the base. -/
theorem baseUnit_complement_sum {b : ℕ} (hb2 : 2 ≤ b) (u : BaseUnit b) :
    (u : ℚ) + (baseUnitComplement b hb2 u : ℕ) = b := by
  rcases Finset.mem_filter.mp u.property with ⟨hurange, _hcop⟩
  have huIco := Finset.mem_Ico.mp hurange
  change (u.val : ℚ) + ((b - u.val : ℕ) : ℚ) = (b : ℚ)
  rw [Nat.cast_sub (by omega : u.val ≤ b)]
  ring

/-- The manuscript's remainder mean on the actual reduced residue system. -/
theorem baseUnit_remainder_mean {b : ℕ} (hb2 : 2 ≤ b) :
    (Fintype.card (BaseUnit b) : ℚ)⁻¹ *
        ∑ u : BaseUnit b, ((u : ℚ) - 1) / b =
      1 / 2 - 1 / b := by
  let witness : BaseUnit b := ⟨1, by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Nat.coprime_one_left b⟩⟩
  letI : Nonempty (BaseUnit b) := ⟨witness⟩
  apply remainder_mean_of_complement
    (baseUnitComplement b hb2) (fun u : BaseUnit b => (u : ℕ)) b
    (by exact_mod_cast (show b ≠ 0 by omega))
  exact baseUnit_complement_sum hb2

/-! ## Conditional analytic assembly -/

/-- Subtracting two residual limits subtracts both their leading coefficients
and their limiting constants. -/
theorem subtract_residual_limits
    {α : Type*} {l f g : α → ℝ} {s r κf κg d : ℝ}
    {lfilter : Filter α} (hcoeff : s - r = d)
    (hf : Tendsto (fun x => f x - s * l x) lfilter (𝓝 κf))
    (hg : Tendsto (fun x => g x - r * l x) lfilter (𝓝 κg)) :
    Tendsto (fun x => (f x - g x) - d * l x)
      lfilter (𝓝 (κf - κg)) := by
  convert hf.sub hg using 1
  funext x
  rw [← hcoeff]
  ring

/-- Once the two Mertens-progression residual limits used in the manuscript
are supplied, their exact finite means force the coefficient `-(b-1)/b`. -/
theorem collision_drift_limit_from_component_limits
    {α : Type*} {l integerPart correction : α → ℝ}
    {κS κR : ℝ} {lfilter : Filter α} (b : ℕ) (hb2 : 2 ≤ b)
    (hS : Tendsto
      (fun x => integerPart x - (-1 / 2) * l x) lfilter (𝓝 κS))
    (hR : Tendsto
      (fun x => correction x - (1 / 2 - 1 / (b : ℝ)) * l x)
      lfilter (𝓝 κR)) :
    Tendsto
      (fun x => (integerPart x - correction x) -
        (-(b - 1 : ℝ) / b) * l x) lfilter (𝓝 (κS - κR)) := by
  apply subtract_residual_limits
    (s := (-1 / 2 : ℝ)) (r := 1 / 2 - 1 / (b : ℝ))
    (d := -(b - 1 : ℝ) / b)
  · have hb : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    field_simp [hb]
    ring
  · exact hS
  · exact hR

end NField.Alignment.CollisionFluctuationClosure
