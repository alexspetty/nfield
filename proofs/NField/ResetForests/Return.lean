/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Opening
/-! # The literal return-window forest

The divisor parameter retains every printed factor. Congruence rules are
sufficient selections, not a claim that they exhaust all divisor roots.
-/

noncomputable section

namespace NField.ResetForests.ReturnWindows

open scoped BigOperators
open AbsoluteForestWork SignedForestWork

def oddReturnSteps (L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 L).filter (fun j => j % 2 = 1)

def returnDivisor (p L : ℕ) : ℕ :=
  15*((p-1)*p^2+1)*((p-1)^2-(p-1)-1)*
    ∏ j ∈ oddReturnSteps L, ((p^2)^j-(p-1)^j)

theorem square_minus_linear_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < N^2-N-1 := by
  have : N+2 ≤ N^2 := by nlinarith
  omega

theorem return_step_pos {p j : ℕ} (hp : 3 ≤ p) (hj : 1 ≤ j) :
    0 < (p^2)^j-(p-1)^j := by
  have hbase : p-1 < p^2 := by nlinarith [Nat.sub_le p 1]
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hbase (by omega))

theorem return_divisor_pos {p : ℕ} (hp : 3 ≤ p) (L : ℕ) :
    0 < returnDivisor p L := by
  unfold returnDivisor
  apply Nat.mul_pos
  · exact Nat.mul_pos (by positivity) (square_minus_linear_pos (by omega))
  · apply Finset.prod_pos
    intro j hj
    exact return_step_pos hp (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1

theorem antireturn_factor_dvd (p L : ℕ) :
    (p-1)*p^2+1 ∣ returnDivisor p L := by
  unfold returnDivisor
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _

theorem recurrence_factor_dvd (p L : ℕ) :
    (p-1)^2-(p-1)-1 ∣ returnDivisor p L := by
  unfold returnDivisor
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem return_factor_dvd (p L : ℕ) {j : ℕ} (hj : j ∈ oddReturnSteps L) :
    (p^2)^j-(p-1)^j ∣ returnDivisor p L := by
  unfold returnDivisor
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hj) _

theorem antireturn_selects (p L k : ℕ)
    (h : ((p-1 : ℕ) : ZMod k)*(p^2 : ℕ) = -1) :
    k ∣ returnDivisor p L := by
  apply dvd_trans _ (antireturn_factor_dvd p L)
  apply (ZMod.natCast_eq_zero_iff _ k).mp
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, h]
  ring

theorem recurrence_selects {p : ℕ} (hp : 3 ≤ p) (L k : ℕ)
    (h : (((p-1 : ℕ) : ZMod k))^2 = (p-1 : ℕ)+1) :
    k ∣ returnDivisor p L := by
  apply dvd_trans _ (recurrence_factor_dvd p L)
  apply (ZMod.natCast_eq_zero_iff _ k).mp
  have hN : 2 ≤ p-1 := by omega
  have hsq : p-1+1 ≤ (p-1)^2 := by nlinarith
  rw [Nat.cast_sub (by omega : 1 ≤ (p-1)^2-(p-1)),
    Nat.cast_sub (by omega : p-1 ≤ (p-1)^2), Nat.cast_pow, h]
  ring

theorem odd_return_selects {p j : ℕ} (hp : 3 ≤ p) (L k : ℕ)
    (hj : j ∈ oddReturnSteps L) (hunit : IsUnit ((p^2 : ℕ) : ZMod k))
    (hreturn : (((p-1 : ℕ) : ZMod k)*((p^2 : ℕ) : ZMod k)⁻¹)^j = 1) :
    k ∣ returnDivisor p L := by
  have hj1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
  have heq : (((p-1 : ℕ) : ZMod k))^j = (((p^2 : ℕ) : ZMod k))^j := by
    calc
      _ = ((((p-1 : ℕ) : ZMod k)*((p^2 : ℕ) : ZMod k)⁻¹)^j)*
          (((p^2 : ℕ) : ZMod k))^j := by
        rw [← mul_pow, mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]
      _ = _ := by rw [hreturn, one_mul]
  apply dvd_trans _ (return_factor_dvd p L hj)
  apply (ZMod.natCast_eq_zero_iff _ k).mp
  have hle : (p-1)^j ≤ (p^2)^j := by have := return_step_pos hp hj1; omega
  rw [Nat.cast_sub hle]
  simp only [Nat.cast_pow] at heq ⊢
  rw [heq, sub_self]

theorem sampler_unit_below_prime {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p) :
    IsUnit ((p^2 : ℕ) : ZMod k) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  apply Nat.Coprime.pow_left
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk hkp)

theorem return_divisor_height {p : ℕ} (hp : 3 ≤ p) (L : ℕ) :
    returnDivisor p L ≤ 15*p^(5+2*L^2) := by
  have hp1 : 1 ≤ p := by omega
  have hN : p-1+1=p := by omega
  have hfront : (p-1)*p^2+1 ≤ p^3 := by
    have hsq : 1 ≤ p^2 := Nat.one_le_pow _ _ hp1
    calc
      _ ≤ (p-1)*p^2+p^2 := Nat.add_le_add_left hsq _
      _ = (p-1+1)*p^2 := by ring
      _ = p^3 := by rw [hN]; ring
  have hsecond : (p-1)^2-(p-1)-1 ≤ p^2 :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 2))
  have hcard : (oddReturnSteps L).card ≤ L := by
    calc
      _ ≤ (Finset.Icc 1 L).card := Finset.card_filter_le _ _
      _ = L := by simp
  have hprod : (∏ j ∈ oddReturnSteps L, ((p^2)^j-(p-1)^j)) ≤ p^(2*L^2) := by
    calc
      _ ≤ (p^(2*L))^(oddReturnSteps L).card := by
        apply Finset.prod_le_pow_card
        intro j hj
        calc
          _ ≤ (p^2)^j := Nat.sub_le _ _
          _ = p^(2*j) := (pow_mul _ _ _).symm
          _ ≤ p^(2*L) := Nat.pow_le_pow_right hp1 (by
            have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
            omega)
      _ ≤ (p^(2*L))^L := Nat.pow_le_pow_right (by positivity) hcard
      _ = p^(2*L^2) := by rw [← pow_mul]; congr 1; ring
  unfold returnDivisor
  calc
    _ ≤ 15*p^3*p^2*p^(2*L^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hfront) hsecond) hprod
    _ = _ := by rw [show 15*p^3*p^2*p^(2*L^2)=15*(p^3*p^2*p^(2*L^2)) by ring,
        ← pow_add, ← pow_add]

def unitForestRoots (N D : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter (fun k => k.Coprime N ∧ k ∣ D)

theorem rough_part_of_coprime {N k : ℕ} (hk : k ≠ 0) (hcop : k.Coprime N) :
    Core.roughPart N k=k := by
  unfold Core.roughPart
  rw [Finset.filter_true_of_mem (fun q hq => ?_)]
  · exact (Nat.prod_primeFactors_pow_factorization hk).symm
  · intro hd
    have hqk := (Nat.mem_primeFactors.mp hq).2.1
    have hq1 : q ∣ 1 := by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hqk hd
    exact (Nat.prime_of_mem_primeFactors hq).ne_one (Nat.dvd_one.mp hq1)

theorem unit_roots_are_actual_forest (N D : ℕ) :
    unitForestRoots N D = (forestClocks N D).filter (fun k => k.Coprime N) := by
  ext k
  simp only [unitForestRoots, forestClocks, Finset.mem_filter]
  constructor
  · rintro ⟨hk, hc, hd⟩
    refine ⟨⟨hk, ?_⟩, hc⟩
    rw [rough_part_of_coprime (by have := (Finset.mem_Icc.mp hk).1; omega) hc]
    exact hd
  · rintro ⟨⟨hk, hd⟩, hc⟩
    refine ⟨hk, hc, ?_⟩
    rwa [rough_part_of_coprime (by have := (Finset.mem_Icc.mp hk).1; omega) hc] at hd

theorem fixed_window_absolute (L : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      Core.absoluteForestReading (p-1) (p^2) (returnDivisor p L) ≤
        C*(p : ℝ)^(3/2+ε) := by
  obtain ⟨C, hC, hc⟩ := polynomial_forest_absolute_any_exponent
    ((5+2*L^2 : ℕ) : ℝ) 15 ε (by norm_num) hε
  refine ⟨C, hC, ?_⟩
  intro p hp hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  apply hc p _ hp (return_divisor_pos hp3 L)
  simpa only [Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    using (Nat.cast_le (α := ℝ)).mpr (return_divisor_height hp3 L)

theorem fixed_window_sampling (L : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      |4*Core.selectedReading (p-1) (p^2) (Core.forestMask (p-1) (returnDivisor p L))/(p : ℝ)^2| ≤
        C*(p : ℝ)^(-1/2+ε) := by
  obtain ⟨C, hC, hc⟩ := polynomial_forest_sampling_any_exponent
    ((5+2*L^2 : ℕ) : ℝ) 15 ε (by norm_num) hε
  refine ⟨C, hC, ?_⟩
  intro p hp hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  apply hc p _ hp (return_divisor_pos hp3 L)
  simpa only [Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    using (Nat.cast_le (α := ℝ)).mpr (return_divisor_height hp3 L)

theorem return_divisor_lower {p : ℕ} (hp : 3 ≤ p) (L : ℕ) :
    p ≤ returnDivisor p L := by
  have hfactor := Nat.le_of_dvd (return_divisor_pos hp L) (antireturn_factor_dvd p L)
  have hN : 1 ≤ p-1 := by omega
  have hmul := Nat.mul_le_mul_right (p^2) hN
  nlinarith

theorem return_divisor_log_height {p : ℕ} (hp : 3 ≤ p) (L : ℕ) :
    Real.log (returnDivisor p L : ℝ) ≤
      Real.log 15+((5 : ℝ)+2*(L : ℝ)^2)*Real.log (p : ℝ) := by
  have hD : (0 : ℝ) < returnDivisor p L := by exact_mod_cast return_divisor_pos hp L
  have hh : (returnDivisor p L : ℝ) ≤ 15*(p : ℝ)^(5+2*L^2) := by
    exact_mod_cast return_divisor_height hp L
  have hl := Real.log_le_log hD hh
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hl
  exact hl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem prime31_unit_roots :
    unitForestRoots 30 (returnDivisor 31 3) = {7,11,13,19} := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem prime31_forest :
    forestClocks 30 (returnDivisor 31 3) = (Finset.Icc 2 30) \ {17,23,29} := by
  have he : forestClocks 30 (returnDivisor 31 3) =
      (Finset.Icc 2 30).filter (fun k => k ∣ forestCarrier 30 (returnDivisor 31 3)) := by
    apply Finset.filter_congr
    intro k hk
    have hb := Finset.mem_Icc.mp hk
    exact forest_carrier_selection (by norm_num) (by omega) hb.2 _
  rw [he]
  decide

end NField.ResetForests.ReturnWindows
