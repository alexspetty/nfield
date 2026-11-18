/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Carry
import NField.ResetForests.Sampling
import NField.Alignment.BernoulliCurvature
/-! # The actual unit-root carry work

The integer lift determines the transported fractional phase. Unit-root
permutations then cancel the complete potential sums, leaving the actual
source energy and nonnegative carry moment.
-/

noncomputable section

namespace NField.ResetForests.CarryWork

open scoped BigOperators
open NField.Alignment
open CollisionRampEnergy Core PrimitiveAdditiveConvolution

theorem integer_phase_lift_count (s : ℕ) (x : ℝ) :
    (s : ℝ)*((s : ℝ)+1)*x-boundaryResponse s x =
      (((s : ℤ)+2*(∑ j ∈ Finset.Icc 1 s, ⌊(j : ℝ)*x⌋)-
        (((Finset.Icc 1 s).filter (fun j : ℕ => Int.fract ((j : ℝ)*x)=0)).card : ℤ) : ℤ) : ℝ) := by
  rw [integer_phase_lift]
  congr 1
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc : (∑ j ∈ Finset.Icc 1 s, if Int.fract ((j : ℝ)*x)=0 then (1 : ℤ) else 0) =
      (((Finset.Icc 1 s).filter (fun j : ℕ => Int.fract ((j : ℝ)*x)=0)).card : ℤ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hc]
  simp

theorem sum_primitive_real_eq_units {k : ℕ} [NeZero k] (hk : 2 ≤ k) (f : ℕ → ℝ) :
    (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k), f a) =
      ∑ u : (ZMod k)ˣ, f u.val.val := by
  have he := (primitiveNatEquiv k hk).sum_comp (fun u : (ZMod k)ˣ => f u.val.val)
  rw [← he, Finset.sum_subtype ((Finset.Ico 1 k).filter (fun a => a.Coprime k))
    (by intro; rfl) f]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  symm
  change (ZMod.unitOfCoprime a.val (Finset.mem_filter.mp a.property).2).val.val=a.val
  simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]

theorem potential_rational_mod (a k : ℕ) :
    periodicPotential ((a : ℝ)/(k : ℝ)) =
      periodicPotential (((a%k : ℕ) : ℝ)/(k : ℝ)) := by
  unfold periodicPotential
  simp only [Int.fract_div_natCast_eq_div_natCast_mod, Nat.mod_mod]

theorem potential_unit_permutation {k P : ℕ} (hk : 2 ≤ k) (hP : P.Coprime k) :
    (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
      periodicPotential ((P : ℝ)*((a : ℝ)/(k : ℝ)))) =
    ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
      periodicPotential ((a : ℝ)/(k : ℝ)) := by
  letI : NeZero k := ⟨by omega⟩
  rw [sum_primitive_real_eq_units hk, sum_primitive_real_eq_units hk]
  let e := Equiv.mulLeft (ZMod.unitOfCoprime P hP)
  have he := Equiv.sum_comp e (fun u : (ZMod k)ˣ => periodicPotential ((u.val.val : ℝ)/(k : ℝ)))
  have ht (u : (ZMod k)ˣ) :
      periodicPotential ((P : ℝ)*((u.val.val : ℝ)/(k : ℝ))) =
        periodicPotential ((((e u).val.val : ℕ) : ℝ)/(k : ℝ)) := by
    have hv : (e u).val.val = (P*u.val.val)%k := by
      change ((ZMod.unitOfCoprime P hP*u).val).val=_
      rw [Units.val_mul, ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val u.val,
        ← Nat.cast_mul, ZMod.val_natCast]
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt u.val.val_lt]
    rw [← mul_div_assoc, ← Nat.cast_mul, potential_rational_mod, hv]
  simp_rw [ht]
  exact he

theorem prime_square_fractional_lift {p : ℕ} (hp : 1 ≤ p) (x : ℝ) :
    Int.fract (Int.fract ((p : ℝ)*x)+boundaryResponse (p-1) x) =
      Int.fract ((p : ℝ)^2*x) := by
  let z : ℤ := ∑ j ∈ Finset.Icc 1 (p-1),
    (1+2*⌊(j : ℝ)*x⌋-(if Int.fract ((j : ℝ)*x)=0 then 1 else 0))
  have hl := integer_phase_lift (p-1) x
  change ((p-1 : ℕ) : ℝ)*(((p-1 : ℕ) : ℝ)+1)*x-boundaryResponse (p-1) x=(z : ℝ) at hl
  rw [Nat.cast_sub hp, Nat.cast_one] at hl
  apply Int.fract_eq_fract.mpr
  refine ⟨-(⌊(p : ℝ)*x⌋+z), ?_⟩
  push_cast
  rw [Int.fract]
  nlinarith

theorem coprime_grid_nonintegral {k M a : ℕ} (hk : 2 ≤ k)
    (hM : M.Coprime k) (ha : a.Coprime k) :
    Int.fract ((M : ℝ)*((a : ℝ)/(k : ℝ))) ≠ 0 := by
  have hcop : (M*a).Coprime k := hM.mul_left ha
  have hnot : ¬k ∣ M*a := by
    intro hd
    have ht := Nat.dvd_gcd hd (dvd_refl k)
    rw [hcop.gcd_eq_one] at ht
    have := Nat.le_of_dvd (by decide : 0 < 1) ht
    omega
  rw [← mul_div_assoc, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod]
  exact div_ne_zero (by exact_mod_cast (fun hz => hnot (Nat.dvd_of_mod_eq_zero hz)))
    (by exact_mod_cast (by omega : k ≠ 0))

theorem actual_carry_point {p k a : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k)
    (hpk : p.Coprime k) (ha : a.Coprime k) :
    boundaryResponse (p-1) ((a : ℝ)/(k : ℝ))*midpointRow (p^2) ((a : ℝ)/(k : ℝ)) =
      periodicPotential ((p : ℝ)^2*((a : ℝ)/(k : ℝ)))-
      periodicPotential ((p : ℝ)*((a : ℝ)/(k : ℝ))) +
      (boundaryResponse (p-1) ((a : ℝ)/(k : ℝ)))^2/2 -
      carryMoment (Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ))))
        ⌊Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ)))+boundaryResponse (p-1) ((a : ℝ)/(k : ℝ))⌋ := by
  let x : ℝ := (a : ℝ)/(k : ℝ)
  have hf := prime_square_fractional_lift hp x
  have hn : Int.fract ((p : ℝ)^2*x) ≠ 0 := by
    simpa only [Nat.cast_pow] using coprime_grid_nonintegral hk (hpk.pow_left 2) ha
  have hs := carry_potential_identity (Int.fract_nonneg ((p : ℝ)*x))
    (Int.fract_lt_one ((p : ℝ)*x)) (boundaryResponse (p-1) x)
  have hrow : midpointRow 1 (Int.fract ((p : ℝ)*x)+boundaryResponse (p-1) x) =
      midpointRow (p^2) x := by
    simp only [midpointRow, affineRow, Nat.cast_one, one_mul, Nat.cast_pow]
    rw [hf]
  have hpot : periodicPotential (Int.fract ((p : ℝ)*x)+boundaryResponse (p-1) x) =
      periodicPotential ((p : ℝ)^2*x) := by simp only [periodicPotential, hf]
  have hbase : periodicPotential (Int.fract ((p : ℝ)*x)) = periodicPotential ((p : ℝ)*x) := by
    simp only [periodicPotential, Int.fract_fract]
  rw [hrow, hpot, hbase, hf, if_neg hn, add_zero] at hs
  exact hs

theorem actual_carry_clock {p k : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k) (hpk : p.Coprime k) :
    4*clockReading (p-1) (p^2) k =
      2*(((p-1)/k : ℕ) : ℝ)*
        (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
          (boundaryResponse (p-1) ((a : ℝ)/(k : ℝ)))^2) -
      4*(((p-1)/k : ℕ) : ℝ)*
        (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
          carryMoment (Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ))))
            ⌊Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ)))+
              boundaryResponse (p-1) ((a : ℝ)/(k : ℝ))⌋) := by
  have ht (a : ℕ) (ha : a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k)) :=
    actual_carry_point hp hk hpk (Finset.mem_filter.mp ha).2
  unfold clockReading
  rw [Finset.sum_congr rfl ht]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hp2 := potential_unit_permutation hk (hpk.pow_left 2)
  simp only [Nat.cast_pow] at hp2
  rw [hp2, potential_unit_permutation hk hpk]
  rw [← Finset.sum_div]
  simp only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  ring

theorem prime_carry_nonnegative {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    p.Coprime k ∧
      (∀ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
        0 ≤ carryMoment (Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ))))
          ⌊Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ)))+
            boundaryResponse (p-1) ((a : ℝ)/(k : ℝ))⌋) := by
  refine ⟨hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkp), ?_⟩
  intro a _
  exact carry_moment_nonneg (Int.fract_nonneg _) (Int.fract_lt_one _).le _

theorem prime_carry_clock_identity {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    4*clockReading (p-1) (p^2) k =
      2*(((p-1)/k : ℕ) : ℝ)*
        (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
          (boundaryResponse (p-1) ((a : ℝ)/(k : ℝ)))^2) -
      4*(((p-1)/k : ℕ) : ℝ)*
        (∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
          carryMoment (Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ))))
            ⌊Int.fract ((p : ℝ)*((a : ℝ)/(k : ℝ)))+
              boundaryResponse (p-1) ((a : ℝ)/(k : ℝ))⌋) :=
  actual_carry_clock (by have := hp.two_le; omega) hk (prime_carry_nonnegative hp hk hkp).1

end NField.ResetForests.CarryWork
