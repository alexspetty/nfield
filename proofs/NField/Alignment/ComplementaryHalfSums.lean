/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.ComplementaryHalfPacket
import NField.Alignment.CarrierTriangularIdentity

/-! # The two elementary sums over strict complementary pairs -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ComplementaryHalfSums
open scoped BigOperators Classical
open ComplementaryPartition ComplementaryHalfPacket PrimitiveAdditiveConvolution

def primitiveHalf (X : ℕ) : Finset ℕ :=
  (Finset.Ico 1 X).filter (fun k => k.Coprime X ∧ 2*k<X)

theorem primitive_half_sum {X : ℕ} [NeZero X] (hX : 3 ≤ X)
    (f : ℕ → ℕ → ℚ) (hf : ∀ a b, f a b=f b a) :
    (∑ u : (ZMod X)ˣ, f u.val.val (-u).val.val)=
      2*∑ k ∈ primitiveHalf X, f k (X-k) := by
  have hs := unit_half_sum hX
    (fun u : (ZMod X)ˣ => f u.val.val (-u).val.val)
    (by intro u; simp only [neg_neg]; exact hf _ _)
  rw [hs]
  congr 1
  have hX2 : 2 ≤ X := by omega
  simp_rw [negUnit_val hX2]
  rw [CarrierTriangularIdentity.sum_units_as_primitive_naturals hX2
    (fun a => if 2*a<X then f a (X-a) else 0)]
  simp only [primitiveHalf,Finset.sum_filter,ite_and]

theorem reciprocal_full_sum {X : ℕ} [NeZero X] (hX : 2 ≤ X) :
    (∑ u : (ZMod X)ˣ, (1 : ℚ)/((u.val.val : ℚ)*((-u).val.val : ℚ)))=
      2/(X : ℚ)*reducedHarmonic X := by
  simp_rw [reciprocal_pair_identity hX]
  rw [← Finset.mul_sum,Finset.sum_add_distrib,neg_reciprocal_sum]
  change 1/(X : ℚ)*(reducedHarmonic X+reducedHarmonic X)=_
  ring

theorem ratio_full_sum {X : ℕ} [NeZero X] (hX : 2 ≤ X) :
    (∑ u : (ZMod X)ˣ,
      ((u.val.val : ℚ)/((-u).val.val : ℚ)+((-u).val.val : ℚ)/(u.val.val : ℚ)))=
      2*((X : ℚ)*reducedHarmonic X-(X.totient : ℚ)) := by
  simp_rw [ratio_pair_identity hX]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_add_distrib,
    neg_reciprocal_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient]
  change (X : ℚ)*(reducedHarmonic X+reducedHarmonic X)- (X.totient : ℚ)*2=_
  ring

/-- Title: `Reciprocal sum over strict complementary pairs`. -/
theorem reciprocal_half_sum {X : ℕ} [NeZero X] (hX : 3 ≤ X) :
    (∑ k ∈ primitiveHalf X, (1 : ℚ)/((k : ℚ)*((X-k : ℕ) : ℚ)))=
      reducedHarmonic X/(X : ℚ) := by
  have hs := primitive_half_sum hX (fun k l => (1 : ℚ)/((k : ℚ)*(l : ℚ)))
    (by intro k l; rw [mul_comm])
  have he := reciprocal_full_sum (X:=X) (by omega : 2 ≤ X)
  rw [hs] at he
  linear_combination he/2

/-- Title: `Ratio sum over strict complementary pairs`. -/
theorem ratio_half_sum {X : ℕ} [NeZero X] (hX : 3 ≤ X) :
    (∑ k ∈ primitiveHalf X,
      ((k : ℚ)/((X-k : ℕ) : ℚ)+((X-k : ℕ) : ℚ)/(k : ℚ)))=
      (X : ℚ)*reducedHarmonic X-(X.totient : ℚ) := by
  have hs := primitive_half_sum hX
    (fun k l => (k : ℚ)/(l : ℚ)+(l : ℚ)/(k : ℚ)) (by intro k l; ring)
  have he := ratio_full_sum (X:=X) (by omega : 2 ≤ X)
  rw [hs] at he
  linarith

theorem primitive_half_card {X : ℕ} [NeZero X] (hX : 3 ≤ X) :
    2*(primitiveHalf X).card=X.totient := by
  have hs := primitive_half_sum hX (fun _ _ => (1 : ℚ)) (by intro a b; rfl)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    ZMod.card_units_eq_totient] at hs
  exact_mod_cast hs.symm

end NField.Alignment.ComplementaryHalfSums
