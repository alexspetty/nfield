/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.PrimitiveAdditiveConvolution

/-! # The literal half anti-diagonal partition packet -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ComplementaryHalfPacket
open scoped BigOperators Classical
open ComplementaryPartition PrimitiveAdditiveConvolution RademacherThreeTerm

theorem primitive_not_midpoint {X k : ℕ} (hX : 3 ≤ X)
    (hcop : k.Coprime X) : 2*k ≠ X := by
  intro he
  have hd : k ∣ X := ⟨2, by omega⟩
  have hk : k=1 := by
    have hc := hcop.gcd_eq_one
    rwa [Nat.gcd_eq_left hd] at hc
  omega

theorem unit_half_sum {X : ℕ} [NeZero X] (hX : 3 ≤ X)
    (f : (ZMod X)ˣ → ℚ) (hf : ∀ u, f (-u)=f u) :
    (∑ u, f u)=2*∑ u, if 2*u.val.val<X then f u else 0 := by
  have hn (u : (ZMod X)ˣ) : 2*u.val.val≠X :=
    primitive_not_midpoint hX (ZMod.val_coe_unit_coprime u)
  have hflip (u : (ZMod X)ˣ) :
      (if 2*(-u).val.val<X then f (-u) else 0)=
      (if 2*u.val.val<X then 0 else f u) := by
    rw [negUnit_val (by omega), hf]
    have hu := u.val.val_lt
    have hne := hn u
    split_ifs <;> first | rfl | omega
  have he := (negUnitEquiv (X:=X)).sum_comp
    (fun u : (ZMod X)ˣ => if 2*u.val.val<X then f u else 0)
  change (∑ u, if 2*(-u).val.val<X then f (-u) else 0)=_ at he
  simp_rw [hflip] at he
  have hs : (∑ u, f u)=
      (∑ u, if 2*u.val.val<X then f u else 0)+
      (∑ u, if 2*u.val.val<X then 0 else f u) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> simp
  rw [hs,he]
  ring

def halfPartitionPacket (m X : ℕ) : ℚ :=
  ∑ k ∈ (Finset.Ico 1 X).filter (fun k => k.Coprime X ∧ 2*k<X),
    arithmeticCoefficientDedekindTerm k (X-k) m

set_option maxHeartbeats 800000 in
/-- Title: `The partition packet equals its strict half anti-diagonal sum`. -/
theorem partition_packet_half {m X : ℕ} [NeZero X] (hX : 3 ≤ X) :
    partitionPacket m X=halfPartitionPacket m X := by
  have hX2 : 2 ≤ X := by omega
  have hs := unit_half_sum hX
    (fun u : (ZMod X)ˣ => arithmeticCoefficientDedekindTerm u.val.val (-u).val.val m)
    (by intro u; simp only [neg_neg]; exact coefficient_comm _ _ _)
  unfold partitionPacket
  rw [hs]
  have he := (primitiveNatEquiv X hX2).sum_comp
    (fun u : (ZMod X)ˣ => if 2*u.val.val<X then
      arithmeticCoefficientDedekindTerm u.val.val (-u).val.val m else 0)
  rw [← he]
  have hterm (a : ↑((Finset.Ico 1 X).filter fun a => a.Coprime X)) :
      (if 2*(primitiveNatEquiv X hX2 a).val.val<X then
        arithmeticCoefficientDedekindTerm (primitiveNatEquiv X hX2 a).val.val
          (-(primitiveNatEquiv X hX2 a)).val.val m else 0)=
      if 2*a.val<X then arithmeticCoefficientDedekindTerm a.val (X-a.val) m else 0 := by
    rw [negUnit_val hX2]
    simp [primitiveNatEquiv,ZMod.coe_unitOfCoprime,ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]
  simp_rw [hterm]
  rw [← Finset.sum_subtype ((Finset.Ico 1 X).filter fun a => a.Coprime X)
    (by intro; rfl) (f := fun a : ℕ =>
      if 2*a<X then arithmeticCoefficientDedekindTerm a (X-a) m else 0)]
  unfold halfPartitionPacket
  simp only [Finset.sum_filter,ite_and]
  ring

end NField.Alignment.ComplementaryHalfPacket
