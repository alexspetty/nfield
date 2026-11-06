/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.TriangularAdditiveConvolution
import NField.Alignment.ComplementaryHalfPacket
import NField.Alignment.LiveCarrierDamping

/-! # The manuscript's weighted triangular carrier identity, including depth two -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CarrierTriangularIdentity
open scoped BigOperators Classical
open ComplementaryPartition PrimitiveAdditiveConvolution RademacherThreeTerm
  TriangularAdditiveConvolution LiveCarrierDamping DedekindReciprocity

theorem sum_units_as_primitive_naturals {X : ℕ} [NeZero X] (hX : 2≤X) (f : ℕ → ℚ) :
    (∑ u : (ZMod X)ˣ,f u.val.val)=∑ k ∈ (Finset.Ico 1 X).filter (fun k => k.Coprime X),f k := by
  have he := (primitiveNatEquiv X hX).sum_comp (fun u : (ZMod X)ˣ => f u.val.val)
  rw [← he,Finset.sum_subtype ((Finset.Ico 1 X).filter (fun k => k.Coprime X))
    (by intro; rfl) f]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  change (ZMod.unitOfCoprime a.val (Finset.mem_filter.mp a.property).2).val.val=a.val
  simp only [ZMod.coe_unitOfCoprime,ZMod.val_natCast,
    Nat.mod_eq_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]

def primitiveHarmonic (X : ℕ) : ℚ :=
  ∑ k ∈ (Finset.Ico 1 X).filter (fun k => k.Coprime X),(k:ℚ)⁻¹
def elementaryCarrier (p X : ℕ) : ℚ :=
  (p:ℚ)^2/(12*X)*primitiveHarmonic X+
    ((X:ℚ)*primitiveHarmonic X-(X.totient:ℚ))/(12*(p:ℚ)^2)-(X.totient:ℚ)/8

theorem reduced_harmonic_natural {X : ℕ} [NeZero X] (hX : 2≤X) :
    reducedHarmonic X=primitiveHarmonic X := by
  unfold reducedHarmonic primitiveHarmonic
  exact sum_units_as_primitive_naturals hX (fun k => (k:ℚ)⁻¹)

theorem full_fresh_sum_natural {p X : ℕ} [NeZero X] (hX : 3≤X) (hXp : X<p) :
    (∑ k ∈ fullCarrierSet p,if 2≤k ∧ k<X ∧ k.Coprime X then
      arithmeticCoefficientDedekindTerm (p^2) X k else 0)=freshCarrierSum (p^2) X := by
  rw [freshCarrierSum,sum_units_as_primitive_naturals (by omega)]
  rw [← Finset.sum_filter]
  have hset : (fullCarrierSet p).filter (fun k => 2≤k ∧ k<X ∧ k.Coprime X)=
      (Finset.Ico 2 X).filter (fun k => k.Coprime X) := by
    ext k
    simp only [fullCarrierSet,Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [hset]
  have hI : Finset.Ico 1 X=insert 1 (Finset.Ico 2 X) := by
    ext k
    simp only [Finset.mem_Ico,Finset.mem_insert]
    omega
  rw [hI,Finset.filter_insert]
  rw [if_pos (by simp : Nat.Coprime 1 X)]
  rw [Finset.sum_insert (by simp)]
  have hz : arithmeticCoefficientDedekindTerm (p^2) X 1=0 := by
    simp [arithmeticCoefficientDedekindTerm,rationalSawtooth]
  rw [hz,zero_add]

theorem full_fresh_elementary {p X : ℕ} (hp : p.Prime) (hX : 3≤X) (hXp : X<p) :
    (∑ k ∈ fullCarrierSet p,if 2≤k ∧ k<X ∧ k.Coprime X then
      arithmeticCoefficientDedekindTerm (p^2) X k else 0)=
      elementaryCarrier p X-(1/2:ℚ)*primitiveAdditiveConvolution p X := by
  letI : NeZero X := ⟨by omega⟩
  rw [full_fresh_sum_natural hX hXp,complementary_partition_identity hp hX hXp,
    reduced_harmonic_natural (by omega),primitive_convolution_eq_packet (by omega)]
  unfold elementaryCarrier
  push_cast
  ring

theorem primitive_convolution_one (p : ℕ) : primitiveAdditiveConvolution p 1=0 := by
  simp [primitiveAdditiveConvolution]

theorem primitive_convolution_two (p : ℕ) :
    primitiveAdditiveConvolution p 2=arithmeticDedekindSum 1 (p^2) := by
  norm_num [primitiveAdditiveConvolution]
  norm_num [Finset.filter_singleton,show Odd (1:ℕ) by decide]
  simp only [arithmeticCoefficientDedekindTerm,arithmeticDedekindSum,one_mul]

theorem primitive_lifetime_from_three {p N : ℕ} (hp : p.Prime) (hN : 2≤N) (hNp : N<p) :
    (∑ X ∈ Finset.Icc 3 N,(N/X:ℕ)*primitiveAdditiveConvolution p X)=
      triangularDedekindConvolution p N-(N/2:ℕ)*arithmeticDedekindSum 1 (p^2) := by
  have ht := primitive_lifetime_triangle hp hNp
  have hI : Finset.Icc 1 N=insert 1 (insert 2 (Finset.Icc 3 N)) := by
    ext X
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  rw [hI,Finset.sum_insert (by simp),Finset.sum_insert (by simp),
    primitive_convolution_one,primitive_convolution_two,mul_zero,zero_add] at ht
  linarith

/-- Title: `Exact triangular carrier identity with the depth-two correction`. -/
theorem triangular_carrier_identity {p : ℕ} (hp : p.Prime) (hpodd : p≠2) :
    fullCarrierWeightedPairSum p=
      (∑ X ∈ Finset.Icc 3 (p-1),((p-1)/X:ℕ)*elementaryCarrier p X)-
      (1/2:ℚ)*triangularDedekindConvolution p (p-1)+
      ((p-1)/2:ℕ)/2*arithmeticDedekindSum 1 (p^2) := by
  have hp3 : 3≤p := by have := hp.two_le; omega
  have hsum : fullCarrierWeightedPairSum p=
      (∑ X ∈ Finset.Icc 3 (p-1),((p-1)/X:ℕ)*elementaryCarrier p X)-
      (1/2:ℚ)*(∑ X ∈ Finset.Icc 3 (p-1),((p-1)/X:ℕ)*primitiveAdditiveConvolution p X) := by
    unfold fullCarrierWeightedPairSum
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro X hX
    have hXI := Finset.mem_Icc.mp hX
    rw [full_fresh_elementary hp hXI.1 (by omega)]
    ring
  rw [hsum,primitive_lifetime_from_three hp (by omega) (by omega)]
  ring

/-- Title: `Triangular convolution of the literal carrier collars`. -/
theorem literal_collar_triangular_identity {p : ℕ} (hp : p.Prime) (hpodd : p≠2) :
    (∑ k ∈ fullCarrierSet p,∑ h ∈ Finset.Icc 1 ((p-1)/(k+1)),
      (CarrierStateSwitching.carrierPrefix p k ((p-1)/h):ℝ))=
      (∑ X ∈ Finset.Icc 3 (p-1),((p-1)/X:ℕ)*(elementaryCarrier p X:ℝ))-
      (1/2:ℝ)*(triangularDedekindConvolution p (p-1):ℝ)+
      ((p-1)/2:ℕ)/2*(arithmeticDedekindSum 1 (p^2):ℝ) := by
  have he : (∑ k ∈ fullCarrierSet p,(PrimeSquareCubicEnergy.modulusKSlice p k).re)=
      (fullCarrierWeightedPairSum p:ℝ) := by
    have h := congrArg Complex.re (sum_modulusKSlice_eq_carrierFamilyWeightedPairSum
      hp (fullCarrierSet p) (Finset.Subset.refl _))
    simpa only [Complex.re_sum,Complex.ratCast_re,carrierFamilyWeightedPairSum,
      fullCarrierWeightedPairSum] using h
  calc
    _ = ∑ k ∈ fullCarrierSet p,(PrimeSquareCubicEnergy.modulusKSlice p k).re := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      exact (SquareLockCarrierMass.modulusKSlice_re_eq_prefixLayers hp hkI.1 (by omega)).symm
    _ = (fullCarrierWeightedPairSum p:ℝ) := he
    _ = _ := by
      rw [triangular_carrier_identity hp hpodd]
      push_cast
      rfl

end NField.Alignment.CarrierTriangularIdentity
