/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareReducedRatio
import NField.Alignment.RademacherThreeTerm

/-!
# Complementary partition of the fresh carrier sum

The finite anti-diagonal identity behind the floor-state description of the
secondary collision term.  The proof starts from the already formalized
three-term Dedekind reciprocity law, pairs the primitive residues `k` and
`X-k`, evaluates both elementary reciprocal sums, and leaves the primitive
prime-square packet as the only non-elementary term.
-/

namespace NField.Alignment.ComplementaryPartition

open scoped BigOperators ZMod
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.DedekindReciprocity
open NField.Alignment.PrimeSquareReducedRatio
open NField.Alignment.RademacherThreeTerm

/-- Adding the modulus to the first coefficient does not change a finite
Dedekind coefficient term. -/
theorem coefficient_add_modulus_left (x y m : ℕ) :
    arithmeticCoefficientDedekindTerm (x + m) y m =
      arithmeticCoefficientDedekindTerm x y m := by
  unfold arithmeticCoefficientDedekindTerm
  apply Finset.sum_congr rfl
  intro t _ht
  congr 1
  unfold rationalSawtooth
  simp [Nat.add_mul, Nat.add_mod]

/-- Adding the modulus to the second coefficient does not change a finite
Dedekind coefficient term. -/
theorem coefficient_add_modulus_right (x y m : ℕ) :
    arithmeticCoefficientDedekindTerm x (y + m) m =
      arithmeticCoefficientDedekindTerm x y m := by
  unfold arithmeticCoefficientDedekindTerm
  apply Finset.sum_congr rfl
  intro t _ht
  congr 1
  unfold rationalSawtooth
  simp [Nat.add_mul, Nat.add_mod]

/-- The two coefficient slots are symmetric. -/
theorem coefficient_comm (x y m : ℕ) :
    arithmeticCoefficientDedekindTerm x y m =
      arithmeticCoefficientDedekindTerm y x m := by
  unfold arithmeticCoefficientDedekindTerm
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- A common coefficient scale that is a unit modulo `m` cancels from the
finite Dedekind Gram kernel. -/
theorem coefficient_common_scale
    {m g a b : ℕ} [NeZero m]
    (hg : g.Coprime m) (ha : a.Coprime m) (hb : b.Coprime m) :
    arithmeticCoefficientDedekindTerm (g * a) (g * b) m =
      arithmeticCoefficientDedekindTerm a b m := by
  have hga : (g * a).Coprime m := hg.mul_left ha
  have hgb : (g * b).Coprime m := hg.mul_left hb
  have hleft := arithmeticCoefficientDedekindTerm_eq_ratio hga hgb
  have hright := arithmeticCoefficientDedekindTerm_eq_ratio ha hb
  have hug : ZMod.unitOfCoprime (g * a) hga =
      ZMod.unitOfCoprime g hg * ZMod.unitOfCoprime a ha := by
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime]
  have hub : ZMod.unitOfCoprime (g * b) hgb =
      ZMod.unitOfCoprime g hg * ZMod.unitOfCoprime b hb := by
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime]
  rw [hug, hub, dedekindSum_ratio_cancel] at hleft
  have hc : coefficientDedekindTerm (g * a) (g * b) hga hgb =
      coefficientDedekindTerm a b ha hb := hleft.trans hright.symm
  unfold coefficientDedekindTerm at hc
  exact_mod_cast hc

/-- Three-term reciprocity after replacing the complementary coefficient
`X-k` by `X` in each of the two lower-modulus terms. -/
theorem complementary_reciprocity_point
    {m X k : ℕ} (hm : 0 < m)
    (hk : 0 < k) (hkX : k < X) (hcop : k.Coprime X)
    (hmk : m.Coprime k) (hml : m.Coprime (X - k)) :
    arithmeticCoefficientDedekindTerm m X k +
        arithmeticCoefficientDedekindTerm m X (X - k) +
        arithmeticCoefficientDedekindTerm k (X - k) m =
      -1 / 4 + (1 / 12) *
        ((m : ℚ) / ((k : ℚ) * ((X - k : ℕ) : ℚ)) +
          (k : ℚ) / (((X - k : ℕ) : ℚ) * (m : ℚ)) +
          ((X - k : ℕ) : ℚ) / ((m : ℚ) * (k : ℚ))) := by
  have hl : 0 < X - k := Nat.sub_pos_of_lt hkX
  have hkl : k.Coprime (X - k) :=
    (Nat.coprime_sub_self_right (Nat.le_of_lt hkX)).mpr hcop
  have hthree := arithmeticCoefficientDedekindTerm_threeTerm
    hm hk hl hmk hml hkl
  have hXeq : X - k + k = X := Nat.sub_add_cancel (Nat.le_of_lt hkX)
  have hXeq' : k + (X - k) = X := Nat.add_sub_of_le (Nat.le_of_lt hkX)
  have hfirst :
      arithmeticCoefficientDedekindTerm m X k =
        arithmeticCoefficientDedekindTerm (X - k) m k := by
    calc
      _ = arithmeticCoefficientDedekindTerm X m k := coefficient_comm _ _ _
      _ = arithmeticCoefficientDedekindTerm ((X - k) + k) m k := by rw [hXeq]
      _ = _ := coefficient_add_modulus_left _ _ _
  have hsecond :
      arithmeticCoefficientDedekindTerm m X (X - k) =
        arithmeticCoefficientDedekindTerm m k (X - k) := by
    calc
      _ = arithmeticCoefficientDedekindTerm m (k + (X - k)) (X - k) := by
        rw [hXeq']
      _ = _ := coefficient_add_modulus_right _ _ _
  calc
    _ = arithmeticCoefficientDedekindTerm (X - k) m k +
        arithmeticCoefficientDedekindTerm m k (X - k) +
        arithmeticCoefficientDedekindTerm k (X - k) m := by
          rw [hfirst, hsecond]
    _ = _ := by linear_combination hthree

/-- Negation permutes the primitive residues modulo `X`. -/
def negUnitEquiv {X : ℕ} : (ZMod X)ˣ ≃ (ZMod X)ˣ where
  toFun u := -u
  invFun u := -u
  left_inv u := by simp
  right_inv u := by simp

/-- The full fresh sum over primitive lower moduli. -/
noncomputable def freshCarrierSum (m X : ℕ) [NeZero X] : ℚ :=
  ∑ u : (ZMod X)ˣ,
    arithmeticCoefficientDedekindTerm m X u.val.val

/-- Half of the primitive anti-diagonal packet.  Symmetry identifies this
with the manuscript's representative sum over `k < X-k`. -/
noncomputable def partitionPacket (m X : ℕ) [NeZero X] : ℚ :=
  (1 / 2 : ℚ) * ∑ u : (ZMod X)ˣ,
    arithmeticCoefficientDedekindTerm u.val.val (-u).val.val m

/-- The reciprocal sum over primitive residues modulo `X`. -/
noncomputable def reducedHarmonic (X : ℕ) [NeZero X] : ℚ :=
  ∑ u : (ZMod X)ˣ, ((u.val.val : ℚ)⁻¹)

/-- The elementary side of the complementary three-term relation before
summing and dividing by two. -/
noncomputable def pairedElementary (m X : ℕ) [NeZero X] : ℚ :=
  ∑ u : (ZMod X)ˣ,
    (-1 / 4 + (1 / 12) *
      ((m : ℚ) / ((u.val.val : ℚ) * ((-u).val.val : ℚ)) +
        (u.val.val : ℚ) / (((-u).val.val : ℚ) * (m : ℚ)) +
        ((-u).val.val : ℚ) / ((m : ℚ) * (u.val.val : ℚ))))

theorem negUnit_val {X : ℕ} [NeZero X] (hX : 2 ≤ X)
    (u : (ZMod X)ˣ) : (-u).val.val = X - u.val.val := by
  letI : Fact (1 < X) := ⟨by omega⟩
  change (- (u.val : ZMod X)).val = X - u.val.val
  rw [ZMod.neg_val]
  simp [u.ne_zero]

theorem neg_reciprocal_sum {X : ℕ} [NeZero X] :
    (∑ u : (ZMod X)ˣ, (((-u).val.val : ℚ)⁻¹)) = reducedHarmonic X := by
  exact (negUnitEquiv (X := X)).sum_comp
    (fun u : (ZMod X)ˣ => ((u.val.val : ℚ)⁻¹))

theorem reciprocal_pair_identity {X : ℕ} [NeZero X]
    (hX : 2 ≤ X) (u : (ZMod X)ˣ) :
    (1 : ℚ) / ((u.val.val : ℚ) * ((-u).val.val : ℚ)) =
      (1 / (X : ℚ)) *
        (((u.val.val : ℚ)⁻¹) + (((-u).val.val : ℚ)⁻¹)) := by
  letI : Fact (1 < X) := ⟨by omega⟩
  have hk : 0 < u.val.val := ZMod.val_pos.mpr u.ne_zero
  have hl : 0 < (-u).val.val := ZMod.val_pos.mpr (-u).ne_zero
  have hsum : u.val.val + (-u).val.val = X := by
    rw [negUnit_val hX]
    exact Nat.add_sub_of_le (Nat.le_of_lt u.val.val_lt)
  have hsumQ : (u.val.val : ℚ) + ((-u).val.val : ℚ) = (X : ℚ) := by
    exact_mod_cast hsum
  have hkQ : (u.val.val : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlQ : ((-u).val.val : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have hXQ : (X : ℚ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  field_simp [hkQ, hlQ, hXQ]
  linarith

theorem ratio_pair_identity {X : ℕ} [NeZero X]
    (hX : 2 ≤ X) (u : (ZMod X)ˣ) :
    (u.val.val : ℚ) / ((-u).val.val : ℚ) +
        ((-u).val.val : ℚ) / (u.val.val : ℚ) =
      (X : ℚ) *
          (((u.val.val : ℚ)⁻¹) + (((-u).val.val : ℚ)⁻¹)) - 2 := by
  letI : Fact (1 < X) := ⟨by omega⟩
  have hk : 0 < u.val.val := ZMod.val_pos.mpr u.ne_zero
  have hl : 0 < (-u).val.val := ZMod.val_pos.mpr (-u).ne_zero
  have hsum : u.val.val + (-u).val.val = X := by
    rw [negUnit_val hX]
    exact Nat.add_sub_of_le (Nat.le_of_lt u.val.val_lt)
  have hsumQ : (u.val.val : ℚ) + ((-u).val.val : ℚ) = (X : ℚ) := by
    exact_mod_cast hsum
  have hkQ : (u.val.val : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlQ : ((-u).val.val : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  field_simp [hkQ, hlQ]
  nlinarith [hsumQ]

/-- Exact evaluation of all elementary terms in the paired reciprocity sum. -/
theorem pairedElementary_closed
    {m X : ℕ} [NeZero X] (hm : 0 < m) (hX : 2 ≤ X) :
    pairedElementary m X =
      (m : ℚ) / (6 * (X : ℚ)) * reducedHarmonic X +
        ((X : ℚ) * reducedHarmonic X - (X.totient : ℚ)) /
          (6 * (m : ℚ)) - (X.totient : ℚ) / 4 := by
  letI : Fact (1 < X) := ⟨by omega⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hrecip :
      (∑ u : (ZMod X)ˣ,
          (1 : ℚ) / ((u.val.val : ℚ) * ((-u).val.val : ℚ))) =
        2 / (X : ℚ) * reducedHarmonic X := by
    calc
      _ = ∑ u : (ZMod X)ˣ, (1 / (X : ℚ)) *
          (((u.val.val : ℚ)⁻¹) + (((-u).val.val : ℚ)⁻¹)) := by
            apply Finset.sum_congr rfl
            intro u _hu
            exact reciprocal_pair_identity hX u
      _ = (1 / (X : ℚ)) *
          ((∑ u : (ZMod X)ˣ, ((u.val.val : ℚ)⁻¹)) +
            ∑ u : (ZMod X)ˣ, (((-u).val.val : ℚ)⁻¹)) := by
            rw [mul_add, Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro u _hu
            ring
      _ = 2 / (X : ℚ) * reducedHarmonic X := by
            rw [neg_reciprocal_sum]
            unfold reducedHarmonic
            ring
  have hratio :
      (∑ u : (ZMod X)ˣ,
          ((u.val.val : ℚ) / ((-u).val.val : ℚ) +
            ((-u).val.val : ℚ) / (u.val.val : ℚ))) =
        2 * ((X : ℚ) * reducedHarmonic X - (X.totient : ℚ)) := by
    calc
      _ = ∑ u : (ZMod X)ˣ,
          ((X : ℚ) *
            ((u.val.val : ℚ)⁻¹ + (((-u).val.val : ℚ)⁻¹)) - 2) := by
              apply Finset.sum_congr rfl
              intro u _hu
              exact ratio_pair_identity hX u
      _ = (X : ℚ) *
            ((∑ u : (ZMod X)ˣ, ((u.val.val : ℚ)⁻¹)) +
              ∑ u : (ZMod X)ˣ, (((-u).val.val : ℚ)⁻¹)) -
          2 * Fintype.card ((ZMod X)ˣ) := by
            rw [Finset.sum_sub_distrib]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            congr 1
            · rw [mul_add, Finset.mul_sum, Finset.mul_sum,
                ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro u _hu
              ring
            · ring
      _ = 2 * ((X : ℚ) * reducedHarmonic X - (X.totient : ℚ)) := by
            rw [neg_reciprocal_sum, ZMod.card_units_eq_totient]
            unfold reducedHarmonic
            ring
  have hsplit :
      (∑ u : (ZMod X)ˣ,
        ((m : ℚ) / ((u.val.val : ℚ) * ((-u).val.val : ℚ)) +
          (u.val.val : ℚ) / (((-u).val.val : ℚ) * (m : ℚ)) +
          ((-u).val.val : ℚ) / ((m : ℚ) * (u.val.val : ℚ)))) =
        (m : ℚ) *
            (∑ u : (ZMod X)ˣ,
              (1 : ℚ) / ((u.val.val : ℚ) * ((-u).val.val : ℚ))) +
          (1 / (m : ℚ)) *
            (∑ u : (ZMod X)ˣ,
              ((u.val.val : ℚ) / ((-u).val.val : ℚ) +
                ((-u).val.val : ℚ) / (u.val.val : ℚ))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _hu
    field_simp [hmQ]
    ring
  unfold pairedElementary
  calc
    (∑ u : (ZMod X)ˣ,
        (-1 / 4 + (1 / 12) *
          ((m : ℚ) / ((u.val.val : ℚ) * ((-u).val.val : ℚ)) +
            (u.val.val : ℚ) / (((-u).val.val : ℚ) * (m : ℚ)) +
            ((-u).val.val : ℚ) / ((m : ℚ) * (u.val.val : ℚ))))) =
        (∑ _u : (ZMod X)ˣ, (-1 / 4 : ℚ)) +
          (1 / 12 : ℚ) *
            (∑ u : (ZMod X)ˣ,
              ((m : ℚ) / ((u.val.val : ℚ) * ((-u).val.val : ℚ)) +
                (u.val.val : ℚ) / (((-u).val.val : ℚ) * (m : ℚ)) +
                ((-u).val.val : ℚ) / ((m : ℚ) * (u.val.val : ℚ)))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = -(X.totient : ℚ) / 4 +
          (1 / 12 : ℚ) *
            ((m : ℚ) * (2 / (X : ℚ) * reducedHarmonic X) +
              (1 / (m : ℚ)) *
                (2 * ((X : ℚ) * reducedHarmonic X - (X.totient : ℚ)))) := by
          rw [show (∑ _u : (ZMod X)ˣ, (-1 / 4 : ℚ)) =
              -(X.totient : ℚ) / 4 by
                simp [ZMod.card_units_eq_totient]
                ring,
            hsplit, hrecip, hratio]
    _ = _ := by
          field_simp [hmQ,
            show (X : ℚ) ≠ 0 by exact_mod_cast (by omega : X ≠ 0)]
          ring

/-- The paired pointwise reciprocity identities summed over all primitive
residues. -/
theorem paired_reciprocity_sum
    {p X : ℕ} [NeZero X] (hp : p.Prime) (hX : 3 ≤ X) (hXp : X < p) :
    2 * freshCarrierSum (p ^ 2) X + 2 * partitionPacket (p ^ 2) X =
      pairedElementary (p ^ 2) X := by
  letI : Fact (1 < X) := ⟨by omega⟩
  have hpoint : ∀ u : (ZMod X)ˣ,
      arithmeticCoefficientDedekindTerm (p ^ 2) X u.val.val +
          arithmeticCoefficientDedekindTerm (p ^ 2) X (-u).val.val +
          arithmeticCoefficientDedekindTerm u.val.val (-u).val.val (p ^ 2) =
        -1 / 4 + (1 / 12) *
          (((p ^ 2 : ℕ) : ℚ) /
              ((u.val.val : ℚ) * ((-u).val.val : ℚ)) +
            (u.val.val : ℚ) /
              (((-u).val.val : ℚ) * ((p ^ 2 : ℕ) : ℚ)) +
            ((-u).val.val : ℚ) /
              (((p ^ 2 : ℕ) : ℚ) * (u.val.val : ℚ))) := by
    intro u
    have hk : 0 < u.val.val := ZMod.val_pos.mpr u.ne_zero
    have hkX : u.val.val < X := u.val.val_lt
    have hcop : u.val.val.Coprime X := ZMod.val_coe_unit_coprime u
    have hneg : (-u).val.val = X - u.val.val := negUnit_val (by omega) u
    have hmk : (p ^ 2).Coprime u.val.val :=
      (smallNatUnit_coprime hp hk (hkX.trans hXp)).symm
    have hl : 0 < X - u.val.val := Nat.sub_pos_of_lt hkX
    have hlt : X - u.val.val < p :=
      (Nat.sub_lt (by omega) hk).trans hXp
    have hml : (p ^ 2).Coprime (X - u.val.val) :=
      (smallNatUnit_coprime hp hl hlt).symm
    rw [hneg]
    exact complementary_reciprocity_point (pow_pos hp.pos 2)
      hk hkX hcop hmk hml
  have hsum := congrArg (fun z : ((ZMod X)ˣ → ℚ) => ∑ u, z u)
    (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hnegSum :
      (∑ u : (ZMod X)ˣ,
          arithmeticCoefficientDedekindTerm (p ^ 2) X (-u).val.val) =
        freshCarrierSum (p ^ 2) X := by
    exact (negUnitEquiv (X := X)).sum_comp
      (fun u : (ZMod X)ˣ =>
        arithmeticCoefficientDedekindTerm (p ^ 2) X u.val.val)
  unfold freshCarrierSum partitionPacket pairedElementary
  rw [Finset.sum_add_distrib]
  rw [hnegSum] at hsum
  simp only [freshCarrierSum] at hsum
  linear_combination hsum

/-- Manuscript Proposition `Complementary-partition identity`, with every
finite sum instantiated. -/
theorem complementary_partition_identity
    {p X : ℕ} [NeZero X] (hp : p.Prime) (hX : 3 ≤ X) (hXp : X < p) :
    freshCarrierSum (p ^ 2) X =
      ((p ^ 2 : ℕ) : ℚ) / (12 * (X : ℚ)) * reducedHarmonic X +
        ((X : ℚ) * reducedHarmonic X - (X.totient : ℚ)) /
          (12 * (((p ^ 2 : ℕ) : ℚ))) -
        (X.totient : ℚ) / 8 - partitionPacket (p ^ 2) X := by
  have hpair := paired_reciprocity_sum hp hX hXp
  have hclosed := pairedElementary_closed (pow_pos hp.pos 2) (by omega : 2 ≤ X)
  rw [hclosed] at hpair
  linear_combination (1 / 2 : ℚ) * hpair

end NField.Alignment.ComplementaryPartition
