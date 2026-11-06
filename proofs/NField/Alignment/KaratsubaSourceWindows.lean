/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaNormalizedBilinear
import NField.Alignment.KorolevSourceWindowDensity
import NField.Alignment.KaratsubaWindowMomentRange

/-! # The normalized finite bound for the literal source prime windows -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSourceWindows
open scoped BigOperators
open KorolevPrimeWindows KorolevPrimeIntervals KorolevQuadraticWindowDensity
  KorolevWindowMass KorolevSourceWindowDensity KaratsubaWindowMomentRange

def pPrimes (m k : ℕ) : Finset ℕ :=
  (windowPrimes (Real.log m) k).filter (fun p => p.Coprime m)

def qPrimes (m s : ℕ) : Finset ℕ :=
  (intervalPrimes (upperEndpoint (Real.log m) (s+1))
    (upperEndpoint (Real.log m) s)).filter (fun p => p.Coprime m)

/-- The lower endpoint of a full contiguous step exceeds its moment index. -/
theorem step_lower_ge_index {L : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hsize : 36*(s : ℝ)^2 ≤ L) : (s : ℝ) ≤ upperEndpoint L (s+1) := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hd : 0 < 2*(s : ℝ)+1 := by positivity
  have hq : 12*(s : ℝ) ≤ L/(2*(s : ℝ)+1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have he := Real.add_one_le_exp (L/(2*(s : ℝ)+1))
  rw [upperEndpoint, Nat.cast_add, Nat.cast_one]
  rw [show 2*((s : ℝ)+1)-1 = 2*(s : ℝ)+1 by ring]
  linarith

/-- Both source upper endpoints are at least one under the quadratic index condition. -/
theorem upper_ge_one {L : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hsize : 36*(k : ℝ)^2 ≤ L) : 1 ≤ upperEndpoint L k := by
  have hL : 0 ≤ L := (by positivity : 0 ≤ 36*(k : ℝ)^2).trans hsize
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact hkR.trans ((step_lower_ge_index hk hsize).trans (upper_antitone hL hk (Nat.le_succ k)))

/-- The separated source primes satisfy every finite moment membership condition. -/
theorem pPrimes_data {m k : ℕ} (hk : 1 ≤ k)
    (hsize : 36*(k : ℝ)^2 ≤ Real.log m) {p : ℕ} (hp : p ∈ pPrimes m k) :
    p.Prime ∧ p.Coprime m ∧ k < p ∧ (p : ℝ) ≤ upperEndpoint (Real.log m) k := by
  obtain ⟨hwin, hcop⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprime, hlo, hhi⟩ := intervalPrimes_mem.mp hwin
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he := endpoint_ge_of_quadratic_size hk hsize
  have hlt : (k : ℝ) < p := by nlinarith
  exact ⟨hprime, hcop, by exact_mod_cast hlt, hhi⟩

/-- The contiguous source primes satisfy every finite moment membership condition. -/
theorem qPrimes_data {m s : ℕ} (hs : 1 ≤ s)
    (hsize : 36*(s : ℝ)^2 ≤ Real.log m) {q : ℕ} (hq : q ∈ qPrimes m s) :
    q.Prime ∧ q.Coprime m ∧ s < q ∧ (q : ℝ) ≤ upperEndpoint (Real.log m) s := by
  obtain ⟨hwin, hcop⟩ := Finset.mem_filter.mp hq
  obtain ⟨hprime, hlo, hhi⟩ := intervalPrimes_mem.mp hwin
  have hlt := (step_lower_ge_index hs hsize).trans_lt hlo
  exact ⟨hprime, hcop, by exact_mod_cast hlt, hhi⟩

/-- The actual two prime populations have their explicit endpoint lower bounds. -/
theorem populations_lower {m k s : ℕ} (hm : 0 < m) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hK : 8*(k : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hK' : 16*lossConstant*(k : ℝ)^2 ≤ Real.log m)
    (hK'' : 36*(k : ℝ)^2 ≤ Real.log m)
    (hS : 8*(s : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hS' : 16*lossConstant*(s : ℝ)^2 ≤ Real.log m)
    (hS'' : 36*(s : ℝ)^2 ≤ Real.log m) :
    lowerEndpoint (Real.log m) k/(8*(k : ℝ)) ≤ (pPrimes m k).card ∧
      lowerEndpoint (Real.log m) s/(8*(s : ℝ)) ≤ (qPrimes m s).card := by
  refine ⟨coprime_window_population_ge_quadratic hm hk hK hK' hK'', ?_⟩
  have hL : 0 ≤ Real.log (m : ℝ) := (by positivity : 0 ≤ 36*(k : ℝ)^2).trans hK''
  exact (coprime_window_population_ge_quadratic hm hs hS hS' hS'').trans
    (coprime_step_card_ge_window m hL hs)

/-- The actual source windows satisfy the normalized bilinear estimate with their true populations. -/
theorem normalized_actual_populations {m k s : ℕ} [NeZero m] (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hK : 8*(k : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hK' : 16*lossConstant*(k : ℝ)^2 ≤ Real.log m)
    (hK'' : 36*(k : ℝ)^2 ≤ Real.log m)
    (hS : 8*(s : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hS' : 16*lossConstant*(s : ℝ)^2 ≤ Real.log m)
    (hS'' : 36*(s : ℝ)^2 ≤ Real.log m) (a b : ZMod m) :
    (‖KaratsubaBilinearReduction.bilinearPrimeSum (pPrimes m k) (qPrimes m s) a b‖ /
      (((pPrimes m k).card : ℝ)*((qPrimes m s).card : ℝ)))^(2*s*k) ≤
      ((s.factorial : ℝ)*((s : ℝ)*upperEndpoint (Real.log m) s)*(m : ℝ)*
        (a.val.gcd m : ℝ)*(k.factorial : ℝ)) /
          (((pPrimes m k).card : ℝ)^k*((qPrimes m s).card : ℝ)^s) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  obtain ⟨hpPop, hqPop⟩ := populations_lower hm hk hs hK hK' hK'' hS hS' hS''
  have hpPos : 0 < lowerEndpoint (Real.log m) k/(8*(k : ℝ)) :=
    div_pos (lowerEndpoint_pos _ _) (by positivity)
  have hqPos : 0 < lowerEndpoint (Real.log m) s/(8*(s : ℝ)) :=
    div_pos (lowerEndpoint_pos _ _) (by positivity)
  have hpCard : 0 < (pPrimes m k).card := by exact_mod_cast hpPos.trans_le hpPop
  have hqCard : 0 < (qPrimes m s).card := by exact_mod_cast hqPos.trans_le hqPop
  have hpData := fun (p : ℕ) (hp : p ∈ pPrimes m k) => pPrimes_data hk hK'' hp
  have hqData := fun (q : ℕ) (hq : q ∈ qPrimes m s) => qPrimes_data hs hS'' hq
  have raw := KaratsubaNormalizedBilinear.normalized_bilinear_power_bound
    (L := 0) (U := ⌊upperEndpoint (Real.log m) s⌋₊) hs hk
    (Finset.card_pos.mp hpCard) (Finset.card_pos.mp hqCard)
    (fun q hq => (hqData q hq).1.pos)
    (fun q hq => Nat.le_floor (hqData q hq).2.2.2)
    (upper_ge_one hk hK'') (fun p hp => (hpData p hp).1)
    (fun p hp => (hpData p hp).2.1) (fun p hp => (hpData p hp).2.2.1)
    (fun p hp => (hpData p hp).2.2.2) (upperEndpoint_short_moment hmR hk)
    (upper_ge_one hs hS'') (fun q hq => (hqData q hq).1)
    (fun q hq => (hqData q hq).2.1) (fun q hq => (hqData q hq).2.2.1)
    (fun q hq => (hqData q hq).2.2.2) (upperEndpoint_short_moment hmR hs) a b
  apply raw.trans
  have hwidth : ((s*(⌊upperEndpoint (Real.log m) s⌋₊-0) : ℕ) : ℝ) ≤
      (s : ℝ)*upperEndpoint (Real.log m) s := by
    simp only [Nat.sub_zero, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (upperEndpoint_pos _ _).le) (Nat.cast_nonneg s)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg s.factorial)) (Nat.cast_nonneg m))
      (Nat.cast_nonneg (a.val.gcd m))) (Nat.cast_nonneg k.factorial)

/-- Insert both proved population lower bounds, retaining every factorial, width and gcd factor. -/
theorem normalized_endpoint_bound {m k s : ℕ} [NeZero m] (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hK : 8*(k : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hK' : 16*lossConstant*(k : ℝ)^2 ≤ Real.log m)
    (hK'' : 36*(k : ℝ)^2 ≤ Real.log m)
    (hS : 8*(s : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hS' : 16*lossConstant*(s : ℝ)^2 ≤ Real.log m)
    (hS'' : 36*(s : ℝ)^2 ≤ Real.log m) (a b : ZMod m) :
    (‖KaratsubaBilinearReduction.bilinearPrimeSum (pPrimes m k) (qPrimes m s) a b‖ /
      (((pPrimes m k).card : ℝ)*((qPrimes m s).card : ℝ)))^(2*s*k) ≤
      ((s.factorial : ℝ)*((s : ℝ)*upperEndpoint (Real.log m) s)*(m : ℝ)*
        (a.val.gcd m : ℝ)*(k.factorial : ℝ)) /
          ((lowerEndpoint (Real.log m) k/(8*(k : ℝ)))^k*
            (lowerEndpoint (Real.log m) s/(8*(s : ℝ)))^s) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨hpPop, hqPop⟩ := populations_lower hm hk hs hK hK' hK'' hS hS' hS''
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hpPos : 0 < lowerEndpoint (Real.log m) k/(8*(k : ℝ)) :=
    div_pos (lowerEndpoint_pos _ _) (by positivity)
  have hqPos : 0 < lowerEndpoint (Real.log m) s/(8*(s : ℝ)) :=
    div_pos (lowerEndpoint_pos _ _) (by positivity)
  have hden := mul_le_mul (pow_le_pow_left₀ hpPos.le hpPop k)
    (pow_le_pow_left₀ hqPos.le hqPop s) (pow_nonneg hqPos.le s) (by positivity)
  apply (normalized_actual_populations hk hs hK hK' hK'' hS hS' hS'' a b).trans
  apply div_le_div_of_nonneg_left _ (by positivity) hden
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg s.factorial)
    (mul_nonneg (Nat.cast_nonneg s) (upperEndpoint_pos _ _).le)) (Nat.cast_nonneg m))
    (Nat.cast_nonneg (a.val.gcd m))) (Nat.cast_nonneg k.factorial)

end NField.Alignment.KaratsubaSourceWindows
