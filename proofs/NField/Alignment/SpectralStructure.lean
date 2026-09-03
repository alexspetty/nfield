/-
Author: Alexander S. Petty
-/

import Mathlib
import NField.Alignment.CrossAlignmentMatrix
import NField.Alignment.CosetAlignment

namespace NField.Alignment.SpectralStructure

open scoped BigOperators
open NField.Alignment
open NField.Alignment.CrossAlignmentMatrix
open NField.CollisionDefinition

def occupiedDigits (b p : ℕ) : Finset ℕ :=
  (nonzeroResidues p).image (digitBin b p)

theorem occupiedDigits_subset_range {b p : ℕ} (hb : 0 < b) (hp : 0 < p) :
    occupiedDigits b p ⊆ Finset.range b := by
  intro d hd
  rw [occupiedDigits, Finset.mem_image] at hd
  rcases hd with ⟨r, hr, rfl⟩
  apply Finset.mem_range.mpr
  apply digitBin_lt_base hb hp
  exact Finset.mem_range.mp (Finset.mem_erase.mp hr).2

theorem digitBin_witness {b p d : ℕ} (hb : 0 < b) (hbp : b < p)
    (hd : d < b) :
    let r := d * p / b + 1
    0 < r ∧ r < p ∧ digitBin b p r = d := by
  dsimp
  have hfloor : b * (d * p / b) ≤ d * p := by
      simpa [mul_comm] using Nat.mul_div_le (d * p) b
  have hupper : b * (d * p / b + 1) < (d + 1) * p := by
    calc
      b * (d * p / b + 1) = b * (d * p / b) + b := by ring
      _ ≤ d * p + b := Nat.add_le_add_right hfloor b
      _ < d * p + p := Nat.add_lt_add_left hbp (d * p)
      _ = (d + 1) * p := by ring
  have hrp : d * p / b + 1 < p := by
    have hdle : d + 1 ≤ b := by omega
    have hprod : b * (d * p / b + 1) < b * p :=
      lt_of_lt_of_le hupper (Nat.mul_le_mul_right p hdle)
    exact (Nat.mul_lt_mul_left hb).mp hprod
  refine ⟨Nat.zero_lt_succ _, hrp, ?_⟩
  unfold digitBin
  apply Nat.div_eq_of_lt_le
  · have hdecomp := Nat.mod_add_div (d * p) b
    have hmod : d * p % b < b := Nat.mod_lt _ hb
    apply Nat.le_of_lt
    calc
      d * p = d * p % b + b * (d * p / b) := hdecomp.symm
      _ < b + b * (d * p / b) := Nat.add_lt_add_right hmod _
      _ = b * (d * p / b + 1) := by ring
  · exact hupper

theorem occupiedDigits_eq_range_of_base_lt_prime {b p : ℕ}
    (hb : 0 < b) (hbp : b < p) : occupiedDigits b p = Finset.range b := by
  apply Finset.Subset.antisymm
  · exact occupiedDigits_subset_range hb (by omega)
  · intro d hd
    have hdl : d < b := Finset.mem_range.mp hd
    obtain ⟨hr0, hrp, heq⟩ := digitBin_witness hb hbp hdl
    rw [occupiedDigits, Finset.mem_image]
    exact ⟨d * p / b + 1, by simp [nonzeroResidues, hrp], heq⟩

theorem occupiedDigits_card_of_base_lt_prime {b p : ℕ}
    (hb : 0 < b) (hbp : b < p) : (occupiedDigits b p).card = b := by
  rw [occupiedDigits_eq_range_of_base_lt_prime hb hbp, Finset.card_range]

theorem occupiedDigits_card_of_digitPartitioning {b p : ℕ}
    (hp : 0 < p) (hdp : DigitPartitioning b p) :
    (occupiedDigits b p).card = p - 1 := by
  rw [occupiedDigits, Finset.card_image_iff.mpr]
  · have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr hp
    simp [nonzeroResidues, Finset.card_erase_of_mem hzero]
  · intro r hr s hs heq
    have rr := Finset.mem_erase.mp hr
    have ss := Finset.mem_erase.mp hs
    exact hdp (Nat.pos_of_ne_zero rr.1) (Finset.mem_range.mp rr.2)
      (Nat.pos_of_ne_zero ss.1) (Finset.mem_range.mp ss.2) heq

theorem occupiedDigits_card {b p : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬ p ∣ b) : (occupiedDigits b p).card = min b (p - 1) := by
  by_cases hbp : b < p
  · rw [occupiedDigits_card_of_base_lt_prime hb hbp]
    simp [show b ≤ p - 1 by omega]
  · have hle : p ≤ b + 1 := by omega
    rw [occupiedDigits_card_of_digitPartitioning hp.pos
      (digitPartitioning_of_le hp.pos hpb hle)]
    simp [show p - 1 ≤ b by omega]

/-! ## Rank loss forced by partitioned unity -/

def coordinateSum (ν : ℕ) : (Fin ν → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ d, v d
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem coordinateSum_surjective {ν : ℕ} (hν : 0 < ν) :
    Function.Surjective (coordinateSum ν) := by
  intro z
  let d : Fin ν := ⟨0, hν⟩
  refine ⟨Pi.single d z, ?_⟩
  classical
  simp [coordinateSum, d]

theorem coordinateSum_ker_finrank {ν : ℕ} (hν : 0 < ν) :
    Module.finrank ℂ (coordinateSum ν).ker = ν - 1 := by
  have hrange : (coordinateSum ν).range = ⊤ :=
    LinearMap.range_eq_top.mpr (coordinateSum_surjective hν)
  have h := LinearMap.finrank_range_add_finrank_ker (coordinateSum ν)
  rw [hrange, finrank_top, Module.finrank_self,
    Module.finrank_pi] at h
  simp only [Fintype.card_fin] at h
  omega

noncomputable def symbolRank {ν C : ℕ} (Y : Matrix (Fin ν) (Fin C) ℂ) : ℕ :=
  Y.rank

theorem symbolRank_le_cosets {ν C : ℕ} (Y : Matrix (Fin ν) (Fin C) ℂ) :
    symbolRank Y ≤ C := by
  simpa [symbolRank] using Matrix.rank_le_card_width Y

theorem symbolRank_le_digits {ν C : ℕ} (Y : Matrix (Fin ν) (Fin C) ℂ) :
    symbolRank Y ≤ ν := by
  simpa [symbolRank] using Matrix.rank_le_card_height Y

theorem symbolRank_le_min {ν C : ℕ} (Y : Matrix (Fin ν) (Fin C) ℂ) :
    symbolRank Y ≤ min C ν := by
  exact le_min (symbolRank_le_cosets Y) (symbolRank_le_digits Y)

theorem symbolRank_le_digits_sub_one_of_column_sum_zero
    {ν C : ℕ} (hν : 0 < ν) (Y : Matrix (Fin ν) (Fin C) ℂ)
    (hzero : ∀ a, ∑ d, Y d a = 0) :
    symbolRank Y ≤ ν - 1 := by
  rw [symbolRank, Matrix.rank_eq_finrank_span_cols]
  calc
    Module.finrank ℂ (Submodule.span ℂ (Set.range Y.col)) ≤
        Module.finrank ℂ (coordinateSum ν).ker := by
      apply Submodule.finrank_mono
      rw [Submodule.span_le]
      intro v hv
      rcases hv with ⟨a, rfl⟩
      simpa [coordinateSum, Matrix.col_apply] using hzero a
    _ = ν - 1 := coordinateSum_ker_finrank hν

theorem symbolRank_le_nonzero_bound
    {ν C : ℕ} (hν : 0 < ν) (Y : Matrix (Fin ν) (Fin C) ℂ)
    (hzero : ∀ a, ∑ d, Y d a = 0) :
    symbolRank Y ≤ min C (ν - 1) := by
  exact le_min (symbolRank_le_cosets Y)
    (symbolRank_le_digits_sub_one_of_column_sum_zero hν Y hzero)

/-! ## The frequency-by-frequency rank ledger -/

noncomputable def spectralRank {L ν C : ℕ}
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ) : ℕ :=
  ∑ j, symbolRank (Y j)

noncomputable def spectralNullity {L ν C : ℕ}
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ) : ℕ :=
  ∑ j, (C - symbolRank (Y j))

theorem spectralRank_bound {L ν C : ℕ} (hL : 0 < L) (hν : 0 < ν)
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ)
    (hpartition : ∀ j : Fin L, j.val ≠ 0 → ∀ a, ∑ d, Y j d a = 0) :
    spectralRank Y ≤ min C ν + (L - 1) * min C (ν - 1) := by
  let zero : Fin L := ⟨0, hL⟩
  have hsplit : spectralRank Y = symbolRank (Y zero) +
      ∑ j ∈ Finset.univ.erase zero, symbolRank (Y j) := by
    rw [spectralRank]
    rw [← Finset.sum_erase_add Finset.univ (fun j => symbolRank (Y j))
      (Finset.mem_univ zero)]
    omega
  rw [hsplit]
  calc
    symbolRank (Y zero) +
        ∑ j ∈ Finset.univ.erase zero, symbolRank (Y j) ≤
      min C ν + ∑ _j ∈ Finset.univ.erase zero, min C (ν - 1) := by
        apply Nat.add_le_add
        · exact symbolRank_le_min (Y zero)
        · apply Finset.sum_le_sum
          intro j hj
          apply symbolRank_le_nonzero_bound hν
          apply hpartition j
          intro h
          have hjne : j ≠ zero := Finset.ne_of_mem_erase hj
          exact hjne (Fin.ext (by simpa [zero] using h))
    _ = min C ν + (L - 1) * min C (ν - 1) := by
      simp [zero]

theorem spectralRank_add_spectralNullity {L ν C : ℕ}
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ) :
    spectralRank Y + spectralNullity Y = C * L := by
  rw [spectralNullity, spectralRank, ← Finset.sum_add_distrib]
  calc
    ∑ j, (symbolRank (Y j) + (C - symbolRank (Y j))) =
        ∑ _j : Fin L, C := by
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.add_sub_of_le (symbolRank_le_cosets (Y j))
    _ = C * L := by simp [Nat.mul_comm]

theorem forcedNullityBound_eq {L ν C : ℕ}
    (hL : 0 < L) (hν : 0 < ν) (hνC : ν ≤ C) :
    C * L - (min C ν + (L - 1) * min C (ν - 1)) =
      L * (C - ν + 1) - 1 := by
  rw [min_eq_right hνC]
  have hsub : ν - 1 ≤ C := by omega
  rw [min_eq_right hsub]
  have hL1 : 1 ≤ L := by omega
  have hν1 : 1 ≤ ν := by omega
  have hinner : ν + (L - 1) * (ν - 1) ≤ C * L := by
    calc
      ν + (L - 1) * (ν - 1) ≤ ν + (L - 1) * ν := by
        gcongr
        exact Nat.sub_le ν 1
      _ = ν * L := by
        have hdecomp : 1 + (L - 1) = L := by omega
        calc
          ν + (L - 1) * ν = ν * (1 + (L - 1)) := by ring
          _ = ν * L := by rw [hdecomp]
      _ ≤ C * L := Nat.mul_le_mul_right L hνC
  have hright : 1 ≤ L * (C - ν + 1) := by
    have hone : 1 ≤ C - ν + 1 := by omega
    have hpos := Nat.mul_pos (by omega : 0 < L)
      (by omega : 0 < C - ν + 1)
    omega
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hinner, Nat.cast_sub hright]
  push_cast [Nat.cast_sub hL1, Nat.cast_sub hν1, Nat.cast_sub hνC]
  ring

theorem spectralNullity_forced {L ν C : ℕ}
    (hL : 0 < L) (hν : 0 < ν) (hνC : ν ≤ C)
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ)
    (hpartition : ∀ j : Fin L, j.val ≠ 0 → ∀ a, ∑ d, Y j d a = 0) :
    L * (C - ν + 1) - 1 ≤ spectralNullity Y := by
  have hrank := spectralRank_bound hL hν Y hpartition
  have htotal := spectralRank_add_spectralNullity Y
  rw [← forcedNullityBound_eq hL hν hνC]
  omega

theorem spectralNullity_positive {L ν C : ℕ}
    (hL : 1 < L) (hν : 0 < ν) (hνC : ν ≤ C)
    (Y : Fin L → Matrix (Fin ν) (Fin C) ℂ)
    (hpartition : ∀ j : Fin L, j.val ≠ 0 → ∀ a, ∑ d, Y j d a = 0) :
    0 < spectralNullity Y := by
  have hbound := spectralNullity_forced (by omega) hν hνC Y hpartition
  have hone : 1 ≤ C - ν + 1 := by omega
  have htwo : 2 ≤ L * (C - ν + 1) := by
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ L * (C - ν + 1) := Nat.mul_le_mul (by omega) hone
  have hpositive : 0 < L * (C - ν + 1) - 1 := by omega
  omega

/-! ## Exact local kernel of a Fourier Gram block -/

theorem frequencyGram_mulVec_eq_zero_iff
    {a d : Type*} [Fintype a] [Fintype d]
    {length : ℕ} (hlength : 0 < length)
    (X : a → EuclideanSpace ℂ d) (z : a → ℂ) :
    Matrix.mulVec (frequencyGram length X) z = 0 ↔
      ∑ i, z i • X i = 0 := by
  constructor
  · intro hkernel
    have hq := frequencyGram_quadratic_eq_normSq length X z
    rw [hkernel] at hq
    simp only [dotProduct, Pi.star_apply, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at hq
    have hinv : 0 < (length : ℝ)⁻¹ := by positivity
    have hnorm : ‖∑ i, z i • X i‖ ^ 2 = 0 := by
      have hproduct : (length : ℝ)⁻¹ * ‖∑ i, z i • X i‖ ^ 2 = 0 := by
        simpa using hq.symm
      exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hinv)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  · intro hsynthesis
    funext i
    rw [frequencyGram, Matrix.smul_mulVec]
    simp only [Pi.smul_apply]
    have hentry : (Matrix.gram ℂ X).mulVec z i =
        inner ℂ (X i) (∑ j, z j • X j) := by
      rw [inner_sum]
      simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply,
        inner_smul_right]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hentry, hsynthesis]
    simp

/-! ## Primitive one-channel energy -/

/-- Normalized energy of one orbit-frequency digit vector. -/
noncomputable def primitiveFiberEnergy {d : Type*} [Fintype d]
    (length : ℕ) (X : d → ℂ) : ℝ :=
  (length : ℝ)⁻¹ * ∑ digit, ‖X digit‖ ^ 2

/-- Primitive one-channel energy is nonnegative. -/
theorem primitiveFiberEnergy_nonnegative {d : Type*} [Fintype d]
    (length : ℕ) (X : d → ℂ) :
    0 ≤ primitiveFiberEnergy length X := by
  unfold primitiveFiberEnergy
  positivity

/-- The zero-frequency digit counts dominate every primitive frequency whose
coordinate magnitudes obey the termwise triangle bound. -/
theorem primitiveFiberEnergy_le_countEnergy
    {d : Type*} [Fintype d] (length : ℕ) (X : d → ℂ) (counts : d → ℝ)
    (hbound : ∀ digit, ‖X digit‖ ≤ counts digit) :
    primitiveFiberEnergy length X ≤
      (length : ℝ)⁻¹ * ∑ digit, (counts digit) ^ 2 := by
  unfold primitiveFiberEnergy
  gcongr with digit
  exact hbound digit

/-! ## Closed algebra of a two-coset frequency block -/

def twoCosetDiscriminant (q₁ q₂ zSq : ℝ) : ℝ :=
  (q₁ - q₂) ^ 2 + 4 * zSq

noncomputable def twoCosetPlus (length q₁ q₂ zSq : ℝ) : ℝ :=
  (q₁ + q₂ + Real.sqrt (twoCosetDiscriminant q₁ q₂ zSq)) /
    (2 * length)

noncomputable def twoCosetMinus (length q₁ q₂ zSq : ℝ) : ℝ :=
  (q₁ + q₂ - Real.sqrt (twoCosetDiscriminant q₁ q₂ zSq)) /
    (2 * length)

theorem twoCosetDiscriminant_nonnegative {q₁ q₂ zSq : ℝ}
    (hz : 0 ≤ zSq) : 0 ≤ twoCosetDiscriminant q₁ q₂ zSq := by
  unfold twoCosetDiscriminant
  positivity

theorem twoCoset_branches_sum {length q₁ q₂ zSq : ℝ}
    (hlength : length ≠ 0) :
    twoCosetPlus length q₁ q₂ zSq +
      twoCosetMinus length q₁ q₂ zSq = (q₁ + q₂) / length := by
  unfold twoCosetPlus twoCosetMinus
  field_simp
  ring

theorem twoCoset_branches_product {length q₁ q₂ zSq : ℝ}
    (hlength : length ≠ 0) (hz : 0 ≤ zSq) :
    twoCosetPlus length q₁ q₂ zSq *
      twoCosetMinus length q₁ q₂ zSq = (q₁ * q₂ - zSq) / length ^ 2 := by
  have hsqrt := Real.sq_sqrt
    (twoCosetDiscriminant_nonnegative (q₁ := q₁) (q₂ := q₂) hz)
  unfold twoCosetPlus twoCosetMinus
  field_simp
  unfold twoCosetDiscriminant at *
  nlinarith

theorem twoCoset_branch_characteristic {length q₁ q₂ zSq : ℝ}
    (hlength : length ≠ 0) (hz : 0 ≤ zSq) :
    ∀ branch ∈ [twoCosetPlus length q₁ q₂ zSq,
        twoCosetMinus length q₁ q₂ zSq],
      branch ^ 2 - ((q₁ + q₂) / length) * branch +
        (q₁ * q₂ - zSq) / length ^ 2 = 0 := by
  intro branch hbranch
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbranch
  rcases hbranch with rfl | rfl
  · have hsum := twoCoset_branches_sum (q₁ := q₁) (q₂ := q₂)
      (zSq := zSq) hlength
    have hprod := twoCoset_branches_product (q₁ := q₁) (q₂ := q₂)
      hlength hz
    rw [← hsum, ← hprod]
    ring
  · have hsum := twoCoset_branches_sum (q₁ := q₁) (q₂ := q₂)
      (zSq := zSq) hlength
    have hprod := twoCoset_branches_product (q₁ := q₁) (q₂ := q₂)
      hlength hz
    rw [← hsum, ← hprod]
    ring

/-! ## Nonnegative overlap rigidity -/

section Rigidity

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

def overlapMass (Q : G → ℕ) (shift : G) : ℕ :=
  ∑ t, Q t * Q (t + shift)

theorem overlap_zero_support_unique (Q : G → ℕ)
    (hoff : ∀ shift : G, shift ≠ 0 → overlapMass Q shift = 0)
    {a b : G} (ha : 0 < Q a) (hb : 0 < Q b) : a = b := by
  by_contra hab
  have hshift : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hsum := hoff (b - a) hshift
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (f := fun t => Q t * Q (t + (b - a)))
    (fun _ _ => Nat.zero_le _)).mp hsum
  have hat := hterms a (Finset.mem_univ a)
  have hindex : a + (b - a) = b := by abel
  rw [hindex] at hat
  have hpos : 0 < Q a * Q b := Nat.mul_pos ha hb
  omega

theorem overlap_zero_iff_point_mass (Q : G → ℕ)
    (hmass : 0 < ∑ t, Q t) :
    (∀ shift : G, shift ≠ 0 → overlapMass Q shift = 0) ↔
      ∃ s : G, ∃ mass : ℕ, mass = ∑ u, Q u ∧
        Q = fun t => if t = s then mass else 0 := by
  constructor
  · intro hoff
    obtain ⟨s, _hs, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := Q) (Nat.ne_of_gt hmass)
    have hspos : 0 < Q s := Nat.pos_of_ne_zero hs
    refine ⟨s, ∑ u, Q u, rfl, funext fun t => ?_⟩
    by_cases hts : t = s
    · subst t
      rw [if_pos rfl]
      symm
      apply Finset.sum_eq_single s
      · intro u _ hus
        by_contra hu
        exact hus (overlap_zero_support_unique Q hoff
          (Nat.pos_of_ne_zero hu) hspos)
      · simp
    · rw [if_neg hts]
      by_contra ht
      exact hts (overlap_zero_support_unique Q hoff
        (Nat.pos_of_ne_zero ht) hspos)
  · rintro ⟨s, mass, _hmassEq, hQ⟩ shift hshift
    rw [hQ]
    unfold overlapMass
    apply Finset.sum_eq_zero
    intro t _
    by_cases hts : t = s
    · subst t
      have hne : s + shift ≠ s := by
        intro heq
        apply hshift
        have : shift = 0 := by
          apply add_left_cancel (a := s)
          simpa using heq
        exact this
      simp [hne]
    · simp [hts]

end Rigidity

/-! ## Off-diagonal energy and digit partitioning -/

section Energy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def offDiagonalSquareEnergy (A : Matrix ι ι ℚ) : ℚ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (A i j) ^ 2

theorem offDiagonalSquareEnergy_eq_zero_iff (A : Matrix ι ι ℚ) :
    offDiagonalSquareEnergy A = 0 ↔ ∀ i j, i ≠ j → A i j = 0 := by
  constructor
  · intro hzero i j hij
    have houter := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i => ∑ j ∈ Finset.univ.erase i, (A i j) ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j))).mp hzero
    have hinner := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ.erase i) (f := fun j => (A i j) ^ 2)
      (fun j _ => sq_nonneg (A i j))).mp
        (houter i (Finset.mem_univ i))
    have hsquare := hinner j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    exact sq_eq_zero_iff.mp hsquare
  · intro hoff
    unfold offDiagonalSquareEnergy
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j hj
    rw [hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))]
    norm_num

theorem offDiagonalSquareEnergy_eq_zero_iff_matrix_one
    (A : Matrix ι ι ℚ) (hdiag : ∀ i, A i i = 1) :
    offDiagonalSquareEnergy A = 0 ↔ A = 1 := by
  rw [offDiagonalSquareEnergy_eq_zero_iff]
  constructor
  · intro hoff
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp [hij, hoff i j hij]
  · intro hA i j hij
    rw [hA]
    simp [hij]

end Energy

def finitePrimeResidueEquiv (p : ℕ) :
    {r : Fin p // 0 < r.val} ≃ PrimeResidue p where
  toFun r := ⟨r.val.val, r.property, r.val.isLt⟩
  invFun r := ⟨⟨r.val, r.property.2⟩, r.property.1⟩
  left_inv r := by rfl
  right_inv r := by rfl

noncomputable instance primeResidueFintype (p : ℕ) :
    Fintype (PrimeResidue p) :=
  Fintype.ofEquiv {r : Fin p // 0 < r.val} (finitePrimeResidueEquiv p)

theorem primeCrossAlignmentMatrix_diagonal
    {b p length : ℕ} (hlength : 0 < length)
    (r : PrimeResidue p) :
    primeCrossAlignmentMatrix b p length r r = 1 := by
  simp [primeCrossAlignmentMatrix, primePairPositionMatchCount_self,
    hlength.ne']

theorem prime_offDiagonalEnergy_eq_zero_iff_le
    {b p length : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hpb : ¬p ∣ b) (hlength : 0 < length) :
    offDiagonalSquareEnergy (primeCrossAlignmentMatrix b p length) = 0 ↔
      p ≤ b + 1 := by
  rw [offDiagonalSquareEnergy_eq_zero_iff_matrix_one _
    (primeCrossAlignmentMatrix_diagonal hlength)]
  exact primeCrossAlignmentMatrix_eq_one_iff_le hb hp hpb hlength

/-! ## Exact finite fixtures -/

def baseTwoSevenLeft : Fin 3 → Fin 2 := ![0, 0, 1]

def baseTwoSevenRight : Fin 3 → Fin 2 := ![0, 1, 1]

def baseFourSevenLeft : Fin 3 → Fin 4 := ![0, 2, 1]

def baseFourSevenRight : Fin 3 → Fin 4 := ![1, 2, 3]

/-- The four displayed base-seven orbit words are the literal long-division
digits of representatives `1` and `3`. -/
theorem baseSeven_orbit_words_actual :
    (List.ofFn fun t : Fin 3 => digitAt 2 7 1 t.val) = [0, 0, 1] ∧
    (List.ofFn fun t : Fin 3 => digitAt 2 7 3 t.val) = [0, 1, 1] ∧
    (List.ofFn fun t : Fin 3 => digitAt 4 7 1 t.val) = [0, 2, 1] ∧
    (List.ofFn fun t : Fin 3 => digitAt 4 7 3 t.val) = [1, 2, 3] := by
  decide

theorem baseTwoSeven_word_certificate :
    (List.ofFn fun shift : Fin 3 =>
      crossCorrelation baseTwoSevenLeft baseTwoSevenLeft shift) = [3, 1, 1] ∧
    (List.ofFn fun shift : Fin 3 =>
      crossCorrelation baseTwoSevenRight baseTwoSevenRight shift) = [3, 1, 1] ∧
    (List.ofFn fun shift : Fin 3 =>
      crossCorrelation baseTwoSevenLeft baseTwoSevenRight shift) = [2, 2, 0] := by
  decide

theorem baseFourSeven_word_certificate :
    (List.ofFn fun shift : Fin 3 =>
      crossCorrelation baseFourSevenLeft baseFourSevenLeft shift) = [3, 0, 0] ∧
    (List.ofFn fun shift : Fin 3 =>
      crossCorrelation baseFourSevenRight baseFourSevenRight shift) = [3, 0, 0] ∧
    (List.ofFn fun shift : Fin 3 =>
      crossCorrelation baseFourSevenRight baseFourSevenLeft shift) = [1, 1, 0] := by
  decide

theorem exact_two_coset_levels :
    (twoCosetPlus 6 6 6 4 = (4 : ℝ) / 3 ∧
      twoCosetMinus 6 6 6 4 = (2 : ℝ) / 3) ∧
    (twoCosetPlus 3 3 3 4 = (5 : ℝ) / 3 ∧
      twoCosetMinus 3 3 3 4 = (1 : ℝ) / 3) ∧
    (twoCosetPlus 3 3 3 1 = (4 : ℝ) / 3 ∧
      twoCosetMinus 3 3 3 1 = (2 : ℝ) / 3) := by
  norm_num [twoCosetPlus, twoCosetMinus, twoCosetDiscriminant]

theorem baseTwoSeven_rank_bound_certificate :
    min 2 2 + (3 - 1) * min 2 (2 - 1) = 4 ∧
      3 * (2 - 2 + 1) - 1 = 2 := by
  norm_num

end NField.Alignment.SpectralStructure
