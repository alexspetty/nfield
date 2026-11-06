/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.PrimeSquareReducedRatio

/-! # Opposite prime-square ratios cannot occur in the strict half packet -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HalfPacketSignGeometry
open PrimeSquareReducedRatio

theorem cross_numerator_bounds {X k l : ℕ} (hk : 0<k) (hl : 0<l)
    (hkX : 2*k<X) (hlX : 2*l<X) :
    0<X*(k+l)-2*k*l ∧ X*(k+l)-2*k*l<X^2 := by
  have hX0 : 0<X := by omega
  have hsum : k+l<X := by omega
  have hkl : 2*k*l<X*k := by nlinarith
  have hXl : 0<X*l := Nat.mul_pos hX0 hl
  have hlt : X*(k+l)<X^2 := by nlinarith
  have hpos : 2*k*l<X*(k+l) := by nlinarith
  constructor <;> omega

def partitionRatio {p : ℕ} (hp : p.Prime) (X k : ℕ) : (ZMod (p^2))ˣ :=
  smallNatUnit hp k*(smallNatUnit hp (X-k))⁻¹

theorem opposite_ratio_forces_divisibility {p X k l : ℕ} (hp : p.Prime)
    (hXp : X<p) (hk : 0<k) (hl : 0<l) (hkX : 2*k<X) (hlX : 2*l<X)
    (hop : partitionRatio hp X k= -partitionRatio hp X l) :
    p^2 ∣ X*(k+l)-2*k*l := by
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hkp : k<p := by omega
  have hlp : l<p := by omega
  have hXk0 : 0<X-k := by omega
  have hXl0 : 0<X-l := by omega
  have hXkp : X-k<p := by omega
  have hXlp : X-l<p := by omega
  have hu (n : ℕ) (hn0 : 0<n) (hnp : n<p) :
      (smallNatUnit hp n).val=(n:ZMod (p^2)) := by
    rw [smallNatUnit_eq_unitOfCoprime hp (smallNatUnit_coprime hp hn0 hnp),
      ZMod.coe_unitOfCoprime]
  have hc : smallNatUnit hp k*smallNatUnit hp (X-l)=
      -(smallNatUnit hp l*smallNatUnit hp (X-k)) := by
    calc
      _ = partitionRatio hp X k*(smallNatUnit hp (X-k)*smallNatUnit hp (X-l)) := by
        simp [partitionRatio,mul_assoc,mul_left_comm]
      _ = (-partitionRatio hp X l)*(smallNatUnit hp (X-k)*smallNatUnit hp (X-l)) := by rw [hop]
      _ = _ := by simp [partitionRatio,mul_assoc,mul_comm,mul_left_comm]
  have hz := congrArg (fun u : (ZMod (p^2))ˣ => u.val) hc
  simp only [Units.val_mul,Units.val_neg,hu k hk hkp,hu l hl hlp,
    hu (X-k) hXk0 hXkp,hu (X-l) hXl0 hXlp,
    Nat.cast_sub (by omega : l≤X),Nat.cast_sub (by omega : k≤X)] at hz
  have hle : 2*k*l≤X*(k+l) := by nlinarith
  apply (CharP.cast_eq_zero_iff (ZMod (p^2)) (p^2) _).mp
  rw [Nat.cast_sub hle]
  push_cast
  linear_combination hz

/-- Title: `The strict half packet has no opposite prime-square partner`. -/
theorem half_packet_no_opposite {p X k l : ℕ} (hp : p.Prime)
    (hXp : X<p) (hk : 0<k) (hl : 0<l) (hkX : 2*k<X) (hlX : 2*l<X) :
    partitionRatio hp X k≠ -partitionRatio hp X l := by
  intro hop
  have hb := cross_numerator_bounds hk hl hkX hlX
  have hd := opposite_ratio_forces_divisibility hp hXp hk hl hkX hlX hop
  have hpX : X^2<p^2 := by nlinarith
  exact (Nat.not_dvd_of_pos_of_lt hb.1 (hb.2.trans hpX)) hd

end NField.Alignment.HalfPacketSignGeometry
