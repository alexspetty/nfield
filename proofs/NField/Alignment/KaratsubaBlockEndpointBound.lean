/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevBlockCost
import NField.Alignment.KaratsubaContiguousExponentGap

/-! # Endpoint-normalized bilinear bounds at the full contiguous lower edge -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaBlockEndpointBound
open KorolevPrimeWindows

def endpointExponent (k s : ℕ) : ℝ :=
  1+1/(2*(s : ℝ)-1) -
    (k : ℝ)*(2*(k : ℝ)/((2*(k : ℝ)-1)*(2*(k : ℝ)+1))) -
    (s : ℝ)/(2*(s : ℝ)+1)

/-- The genuine contiguous lower endpoint retains its exact factor 4^s. -/
theorem endpoint_ratio (L : ℝ) (k s : ℕ) :
    (upperEndpoint L s*Real.exp L)/
      ((lowerEndpoint L k)^k*(upperEndpoint L (s+1))^s) =
        (4 : ℝ)^s/4 * Real.exp (L*endpointExponent k s) := by
  have hp : (lowerEndpoint L k)^k = Real.exp
      ((k : ℝ)*(L*(2*(k : ℝ))/((2*(k : ℝ)-1)*(2*(k : ℝ)+1)))) := by
    rw [lowerEndpoint, ← Real.exp_nat_mul]
  have hq : (upperEndpoint L (s+1))^s =
      Real.exp ((s : ℝ)*(L/(2*(s : ℝ)+1)))/(4 : ℝ)^s := by
    unfold upperEndpoint
    rw [div_pow, ← Real.exp_nat_mul]
    push_cast
    congr 3
    ring
  rw [hp, hq, upperEndpoint]
  calc
    _ = (4 : ℝ)^s/4 * ((Real.exp (L/(2*(s : ℝ)-1))*Real.exp L)/
        (Real.exp ((k : ℝ)*(L*(2*(k : ℝ))/((2*(k : ℝ)-1)*(2*(k : ℝ)+1))))*
          Real.exp ((s : ℝ)*(L/(2*(s : ℝ)+1))))) := by
      field_simp
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
      congr 2
      unfold endpointExponent
      ring

/-- The positive margin uses the contiguous endpoint, not the separated lower endpoint. -/
theorem endpointExponent_le {k s : ℕ} (hk : 1 ≤ k) (hsep : 8*(k : ℝ)^2 ≤ s) :
    endpointExponent k s ≤ -1/(64*(k : ℝ)^2) := by
  have hh := KaratsubaContiguousExponentGap.contiguous_exponent_gap (by exact_mod_cast hk) hsep
  unfold endpointExponent
  rw [neg_div]
  linarith

/-- Polynomial population losses and the full 4^s cost remain explicit in the finite bound. -/
theorem normalized_endpoint_bound {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D) {k s : ℕ}
    (hk : 1 ≤ k) (hsep : 8*(k : ℝ)^2 ≤ s) :
    ((s.factorial : ℝ)*((s : ℝ)*upperEndpoint L s)*Real.exp L*D*(k.factorial : ℝ))/
      ((lowerEndpoint L k/(4*L))^k*(upperEndpoint L (s+1)/(4*L))^s) ≤
        KorolevBlockCost.cost L k s*D*Real.exp (-L/(64*(k : ℝ)^2)) := by
  have raw := KaratsubaSourceExponential.endpoint_factorization
    (s.factorial : ℝ) (k.factorial : ℝ) (s : ℝ) (upperEndpoint L s) (Real.exp L) D
    (lowerEndpoint L k) (upperEndpoint L (s+1)) (4*L) (4*L) k s
  rw [raw, endpoint_ratio]
  have hcoef := endpointExponent_le hk hsep
  have hex : L*endpointExponent k s ≤ -L/(64*(k : ℝ)^2) := by
    calc
      _ ≤ L*(-1/(64*(k : ℝ)^2)) := mul_le_mul_of_nonneg_left hcoef hL
      _ = _ := by ring
  have hc : 0 ≤ KorolevBlockCost.cost L k s*D := by unfold KorolevBlockCost.cost; positivity
  calc
    _ = (KorolevBlockCost.cost L k s*D/4)*Real.exp (L*endpointExponent k s) := by
      unfold KorolevBlockCost.cost
      rw [pow_add]
      ring
    _ ≤ (KorolevBlockCost.cost L k s*D)*Real.exp (L*endpointExponent k s) := by
      gcongr
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) hc

end NField.Alignment.KaratsubaBlockEndpointBound
