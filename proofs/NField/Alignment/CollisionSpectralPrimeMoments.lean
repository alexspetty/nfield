/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralEuler

/-!
# The two convergent prime series for logarithmic conductor moments

The diagonal of the second moment uses a single prime divisor. Its
convergent series is kept separate from the product of first moments.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionSpectralPrimeMoments

open scoped BigOperators Classical
open CollisionConductorArithmetic CollisionZetaMoments

def primeLogWeight (n : ℕ) : ℝ := Real.log n/((n : ℝ)-1)
def firstPrimeTerm (n : ℕ) : ℝ := if n.Prime then primeLogWeight n/(n : ℝ) else 0
def secondPrimeTerm (n : ℕ) : ℝ := if n.Prime then (primeLogWeight n)^2/(n : ℝ) else 0
def firstPrimeMoment : ℝ := ∑' n, firstPrimeTerm n
def secondPrimeMoment : ℝ := ∑' n, secondPrimeTerm n

theorem primeLogWeight_nonneg (n : ℕ) : 0≤primeLogWeight n := by
  by_cases hn : n=0
  · simp [primeLogWeight,hn]
  have hnR : (1 : ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  exact div_nonneg (Real.log_natCast_nonneg n) (sub_nonneg.mpr hnR)

theorem firstPrimeTerm_nonneg (n : ℕ) : 0≤firstPrimeTerm n := by
  unfold firstPrimeTerm
  split_ifs
  · exact div_nonneg (primeLogWeight_nonneg n) (Nat.cast_nonneg n)
  · rfl

theorem secondPrimeTerm_nonneg (n : ℕ) : 0 ≤ secondPrimeTerm n := by
  unfold secondPrimeTerm
  split_ifs <;> positivity

theorem primeLogWeight_bound {p : ℕ} (hp : p.Prime) :
    primeLogWeight p≤2*Real.log p/(p : ℝ) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hrat : 1/((p : ℝ)-1)≤2/(p : ℝ) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    linarith
  have h := mul_le_mul_of_nonneg_left hrat (Real.log_natCast_nonneg p)
  change Real.log p/((p : ℝ)-1)≤2*Real.log p/(p : ℝ)
  calc
    _ ≤ Real.log p*(2/(p : ℝ)) := by simpa only [mul_one_div] using h
    _ = _ := by ring

theorem firstPrimeTerm_bound (n : ℕ) : firstPrimeTerm n≤2*logSquareTerm n := by
  by_cases hn : n.Prime
  · rw [firstPrimeTerm,if_pos hn]
    have h := div_le_div_of_nonneg_right (primeLogWeight_bound hn) (Nat.cast_nonneg n)
    convert! h using 1
    unfold logSquareTerm
    ring
  · simp only [firstPrimeTerm,if_neg hn]
    unfold logSquareTerm
    positivity

theorem log_nat_square_bound (n : ℕ) : (Real.log n)^2≤4*(n : ℝ) := by
  by_cases hn : n=0
  · simp [hn]
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hnR)
  rw [Real.log_sqrt hnR.le] at h
  have hb : Real.log n≤2*Real.sqrt n := by linarith
  have hs := pow_le_pow_left₀ (Real.log_natCast_nonneg n) hb 2
  nlinarith [Real.sq_sqrt hnR.le]

theorem secondPrimeTerm_bound (n : ℕ) : secondPrimeTerm n≤16*powerKernel 2 n := by
  by_cases hn : n.Prime
  · have hnR : (2 : ℝ)≤n := by exact_mod_cast hn.two_le
    have hnp : (0 : ℝ)<n := by linarith
    have hnm : 0<(n : ℝ)-1 := by linarith
    rw [secondPrimeTerm,if_pos hn,primeLogWeight,div_pow,div_div]
    change (Real.log n)^2/(((n : ℝ)-1)^2*(n : ℝ))≤16*(1/(n : ℝ)^2)
    rw [mul_one_div]
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hnm) hnp) (sq_pos_of_pos hnp)).mpr
    have hb := mul_le_mul_of_nonneg_right (log_nat_square_bound n) hnp.le
    have hs := pow_le_pow_left₀ hnp.le (by linarith : (n : ℝ)≤2*((n : ℝ)-1)) 2
    have hshort : (Real.log n)^2*(n : ℝ)≤16*((n : ℝ)-1)^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hshort hnp.le
    convert! hmul using 1 <;> ring
  · simp only [secondPrimeTerm,if_neg hn]
    exact mul_nonneg (by norm_num) (powerKernel_nonneg 2 n)

theorem firstPrimeTerm_summable : Summable firstPrimeTerm :=
  Summable.of_nonneg_of_le firstPrimeTerm_nonneg firstPrimeTerm_bound
    (logSquareTerm_summable.mul_left 2)

theorem secondPrimeTerm_summable : Summable secondPrimeTerm :=
  Summable.of_nonneg_of_le secondPrimeTerm_nonneg secondPrimeTerm_bound
    ((powerKernel_summable (by norm_num : 1<(2 : ℕ))).mul_left 16)

theorem firstPrimeMoment_nonneg : 0≤firstPrimeMoment := tsum_nonneg firstPrimeTerm_nonneg
theorem secondPrimeMoment_nonneg : 0 ≤ secondPrimeMoment := tsum_nonneg secondPrimeTerm_nonneg

theorem first_prime_series_hasSum :
    HasSum (fun p : Nat.Primes => Real.log p.val/((p.val : ℝ)*((p.val : ℝ)-1)))
      firstPrimeMoment := by
  have hi : {n : ℕ | n.Prime}.indicator firstPrimeTerm=firstPrimeTerm := by
    funext n
    by_cases hn : n.Prime <;> simp [Set.indicator,firstPrimeTerm,hn]
  have h := (hasSum_subtype_iff_indicator (s := {n : ℕ | n.Prime})
    (f := firstPrimeTerm) (a := firstPrimeMoment)).mpr (by rw [hi]; exact firstPrimeTerm_summable.hasSum)
  convert! h using 1
  funext p
  simp only [Function.comp_def,firstPrimeTerm,if_pos p.property,primeLogWeight]
  rw [div_div]
  congr 1
  ring

theorem second_prime_series_hasSum :
    HasSum (fun p : Nat.Primes => (Real.log p.val)^2/
      ((p.val : ℝ)*((p.val : ℝ)-1)^2)) secondPrimeMoment := by
  have hi : {n : ℕ | n.Prime}.indicator secondPrimeTerm=secondPrimeTerm := by
    funext n
    by_cases hn : n.Prime <;> simp [Set.indicator,secondPrimeTerm,hn]
  have h := (hasSum_subtype_iff_indicator (s := {n : ℕ | n.Prime})
    (f := secondPrimeTerm) (a := secondPrimeMoment)).mpr (by rw [hi]; exact secondPrimeTerm_summable.hasSum)
  convert! h using 1
  funext p
  simp only [Function.comp_def,secondPrimeTerm,if_pos p.property,primeLogWeight]
  rw [div_pow,div_div]
  congr 1
  ring

theorem literal_prime_series_converge :
    Summable (fun p : Nat.Primes => Real.log p.val/((p.val : ℝ)*((p.val : ℝ)-1))) ∧
    Summable (fun p : Nat.Primes => (Real.log p.val)^2/
      ((p.val : ℝ)*((p.val : ℝ)-1)^2)) :=
  ⟨first_prime_series_hasSum.summable,second_prime_series_hasSum.summable⟩

end NField.Alignment.CollisionSpectralPrimeMoments
