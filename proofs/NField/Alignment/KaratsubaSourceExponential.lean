/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaSourceWindows
import NField.Alignment.KaratsubaSourceExponentGap

/-! # The exponential margin for the actual source-window bilinear sum -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSourceExponential
open KaratsubaSourceWindows KorolevPrimeWindows KorolevWindowMass

def endpointExponent (k s : ℕ) : ℝ :=
  1 + 1/(2*(s : ℝ)-1) -
    (k : ℝ)*(2*(k : ℝ)/((2*(k : ℝ)-1)*(2*(k : ℝ)+1))) -
    (s : ℝ)*(2*(s : ℝ)/((2*(s : ℝ)-1)*(2*(s : ℝ)+1)))

def cost (k s : ℕ) : ℝ :=
  (s.factorial : ℝ)*(s : ℝ)*(8*(k : ℝ))^k*(8*(s : ℝ))^s*(k.factorial : ℝ)/4

/-- The source endpoint powers have this exact exponential ratio. -/
theorem endpoint_ratio (L : ℝ) (k s : ℕ) :
    (upperEndpoint L s * Real.exp L) /
      ((lowerEndpoint L k)^k*(lowerEndpoint L s)^s) =
        Real.exp (L*endpointExponent k s)/4 := by
  unfold upperEndpoint lowerEndpoint
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  calc
    _ = (Real.exp (L/(2*(s : ℝ)-1))*Real.exp L /
      (Real.exp ((k : ℝ)*(L*(2*(k : ℝ))/((2*(k : ℝ)-1)*(2*(k : ℝ)+1)))) *
        Real.exp ((s : ℝ)*(L*(2*(s : ℝ))/((2*(s : ℝ)-1)*(2*(s : ℝ)+1))))))/4 := by ring
    _ = Real.exp ((L/(2*(s : ℝ)-1)+L) -
      ((k : ℝ)*(L*(2*(k : ℝ))/((2*(k : ℝ)-1)*(2*(k : ℝ)+1))) +
        (s : ℝ)*(L*(2*(s : ℝ))/((2*(s : ℝ)-1)*(2*(s : ℝ)+1)))))/4 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
    _ = _ := by
      congr 2
      unfold endpointExponent
      ring

/-- Normalize the endpoint population factors using field identities only. -/
theorem endpoint_factorization (F G W U M D P Q K S : ℝ) (k s : ℕ) :
    (F*(W*U)*M*D*G)/((P/K)^k*(Q/S)^s) =
      (F*W*D*G*K^k*S^s)*((U*M)/(P^k*Q^s)) := by
  rw [div_pow, div_pow, div_mul_div_comm, div_div_eq_mul_div]
  ring

/-- The exact endpoint exponent is negative with the proved square-separation margin. -/
theorem endpointExponent_le {k s : ℕ} (hk : 1 ≤ k) (hsep : 8*(k : ℝ)^2 ≤ s) :
    endpointExponent k s ≤ -1/(24*(k : ℝ)^2) := by
  have h := KaratsubaSourceExponentGap.exponent_gap (by exact_mod_cast hk) hsep
  rw [neg_div]
  unfold endpointExponent
  linarith

/-- The retained factorial/index cost is nonnegative. -/
theorem cost_nonneg (k s : ℕ) : 0 ≤ cost k s := by unfold cost; positivity

/-- Actual source-window cancellation with every factorial, index and frequency gcd cost retained. -/
theorem normalized_exponential_bound {m k s : ℕ} [NeZero m] (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hK : 8*(k : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hK' : 16*lossConstant*(k : ℝ)^2 ≤ Real.log m)
    (hK'' : 36*(k : ℝ)^2 ≤ Real.log m)
    (hS : 8*(s : ℝ)^2*(Real.log 4+1) ≤ Real.log m)
    (hS' : 16*lossConstant*(s : ℝ)^2 ≤ Real.log m)
    (hS'' : 36*(s : ℝ)^2 ≤ Real.log m)
    (hsep : 8*(k : ℝ)^2 ≤ s) (a b : ZMod m) :
    (‖KaratsubaBilinearReduction.bilinearPrimeSum (pPrimes m k) (qPrimes m s) a b‖ /
      (((pPrimes m k).card : ℝ)*((qPrimes m s).card : ℝ)))^(2*s*k) ≤
        cost k s * (a.val.gcd m : ℝ) * Real.exp (-Real.log m/(24*(k : ℝ)^2)) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have raw := normalized_endpoint_bound hk hs hK hK' hK'' hS hS' hS'' a b
  have hid := endpoint_ratio (Real.log m) k s
  rw [Real.exp_log hmR] at hid
  rw [endpoint_factorization, hid] at raw
  have hcoef := endpointExponent_le hk hsep
  have hL : 0 ≤ Real.log (m : ℝ) := (by positivity : 0 ≤ 36*(k : ℝ)^2).trans hK''
  have hex : Real.log (m : ℝ)*endpointExponent k s ≤ -Real.log m/(24*(k : ℝ)^2) := by
    calc
      _ ≤ Real.log (m : ℝ)*(-1/(24*(k : ℝ)^2)) := mul_le_mul_of_nonneg_left hcoef hL
      _ = _ := by ring
  calc
    _ ≤ cost k s * (a.val.gcd m : ℝ) * Real.exp (Real.log m*endpointExponent k s) := by
      convert raw using 1
      unfold cost
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex)
      (mul_nonneg (cost_nonneg k s) (Nat.cast_nonneg _))

end NField.Alignment.KaratsubaSourceExponential
