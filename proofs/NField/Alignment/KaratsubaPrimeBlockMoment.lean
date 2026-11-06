/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaBlockEndpointBound
import NField.Alignment.KaratsubaSubsetBilinear
import NField.Alignment.KaratsubaSourceCancellation

/-! # Bilinear moment saving normalized by the actual prime-block populations -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaPrimeBlockMoment
open KaratsubaSourceWindows KorolevPrimeWindows
open scoped Topology

/-- The normalizer consists of the full block populations even when canonical cutoffs shrink the summands. -/
theorem normalized_subset_endpoint_bound {m k s : ℕ} [NeZero m]
    {P₀ Q₀ P Q : Finset ℕ} (hPsub : P₀ ⊆ P) (hQsub : Q₀ ⊆ Q)
    (hPsource : P ⊆ pPrimes m k) (hQsource : Q ⊆ qPrimes m s)
    (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hK : 36*(k : ℝ)^2 ≤ Real.log m) (hS : 36*(s : ℝ)^2 ≤ Real.log m)
    (hPpop : lowerEndpoint (Real.log m) k/(4*Real.log m) ≤ (P.card : ℝ))
    (hQpop : upperEndpoint (Real.log m) (s+1)/(4*Real.log m) ≤ (Q.card : ℝ))
    (a b : ZMod m) :
    (‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
      ((P.card : ℝ)*(Q.card : ℝ)))^(2*s*k) ≤
      ((s.factorial : ℝ)*((s : ℝ)*upperEndpoint (Real.log m) s)*(m : ℝ)*
        (a.val.gcd m : ℝ)*(k.factorial : ℝ)) /
        ((lowerEndpoint (Real.log m) k/(4*Real.log m))^k*
          (upperEndpoint (Real.log m) (s+1)/(4*Real.log m))^s) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : 0 < Real.log (m : ℝ) := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hpPos : 0 < lowerEndpoint (Real.log m) k/(4*Real.log m) := div_pos (lowerEndpoint_pos _ _) (by positivity)
  have hqPos : 0 < upperEndpoint (Real.log m) (s+1)/(4*Real.log m) := div_pos (upperEndpoint_pos _ _) (by positivity)
  have hpCard : 0 < P.card := by exact_mod_cast hpPos.trans_le hPpop
  have hqCard : 0 < Q.card := by exact_mod_cast hqPos.trans_le hQpop
  have hpData := fun (p : ℕ) (hp : p ∈ P) => pPrimes_data hk hK (hPsource hp)
  have hqData := fun (q : ℕ) (hq : q ∈ Q) => qPrimes_data hs hS (hQsource hq)
  have raw := KaratsubaSubsetBilinear.normalized_subset_power_bound
    (L := 0) (U := ⌊upperEndpoint (Real.log m) s⌋₊) hPsub hQsub hs hk
    (Finset.card_pos.mp hpCard) (Finset.card_pos.mp hqCard)
    (fun q hq => (hqData q hq).1.pos) (fun q hq => Nat.le_floor (hqData q hq).2.2.2)
    (upper_ge_one hk hK) (fun p hp => (hpData p hp).1) (fun p hp => (hpData p hp).2.1)
    (fun p hp => (hpData p hp).2.2.1) (fun p hp => (hpData p hp).2.2.2)
    (KaratsubaWindowMomentRange.upperEndpoint_short_moment hmR hk)
    (upper_ge_one hs hS) (fun q hq => (hqData q hq).1) (fun q hq => (hqData q hq).2.1)
    (fun q hq => (hqData q hq).2.2.1) (fun q hq => (hqData q hq).2.2.2)
    (KaratsubaWindowMomentRange.upperEndpoint_short_moment hmR hs) a b
  have hwidth : ((s*(⌊upperEndpoint (Real.log m) s⌋₊-0) : ℕ) : ℝ) ≤
      (s : ℝ)*upperEndpoint (Real.log m) s := by
    simp only [Nat.sub_zero, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (upperEndpoint_pos _ _).le) (Nat.cast_nonneg s)
  have hden := mul_le_mul (pow_le_pow_left₀ hpPos.le hPpop k)
    (pow_le_pow_left₀ hqPos.le hQpop s) (pow_nonneg hqPos.le s) (by positivity)
  have hUp := upperEndpoint_pos (Real.log (m : ℝ)) s
  apply raw.trans
  apply div_le_div₀ (by positivity) ?_ (by positivity) hden
  gcongr

/-- Every factorial, polynomial-population and frequency gcd cost is retained in the block estimate. -/
theorem normalized_subset_exponential_bound {m k s : ℕ} [NeZero m]
    {P₀ Q₀ P Q : Finset ℕ} (hPsub : P₀ ⊆ P) (hQsub : Q₀ ⊆ Q)
    (hPsource : P ⊆ pPrimes m k) (hQsource : Q ⊆ qPrimes m s)
    (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hK : 36*(k : ℝ)^2 ≤ Real.log m) (hS : 36*(s : ℝ)^2 ≤ Real.log m)
    (hPpop : lowerEndpoint (Real.log m) k/(4*Real.log m) ≤ (P.card : ℝ))
    (hQpop : upperEndpoint (Real.log m) (s+1)/(4*Real.log m) ≤ (Q.card : ℝ))
    (hsep : 8*(k : ℝ)^2 ≤ s) (a b : ZMod m) :
    (‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
      ((P.card : ℝ)*(Q.card : ℝ)))^(2*s*k) ≤
        KorolevBlockCost.cost (Real.log m) k s*(a.val.gcd m : ℝ)*
          Real.exp (-Real.log m/(64*(k : ℝ)^2)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : 0 ≤ Real.log (m : ℝ) := (by positivity : 0 ≤ 36*(k : ℝ)^2).trans hK
  have hex := KaratsubaBlockEndpointBound.normalized_endpoint_bound hL (Nat.cast_nonneg (a.val.gcd m)) hk hsep
  rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m) : (0 : ℝ) < m)] at hex
  exact (normalized_subset_endpoint_bound hPsub hQsub hPsource hQsource hk hs hK hS hPpop hQpop a b).trans hex

/-- The checked block cost uses half the proved contiguous-edge margin. -/
theorem absorb_cost {L D : ℝ} {k s : ℕ} (hD : 0 ≤ D)
    (hc : KorolevBlockCost.cost L k s ≤ Real.exp (L/(128*(k : ℝ)^2))) :
    KorolevBlockCost.cost L k s*D*Real.exp (-L/(64*(k : ℝ)^2)) ≤
      D*Real.exp (-L/(128*(k : ℝ)^2)) := by
  calc
    _ ≤ Real.exp (L/(128*(k : ℝ)^2))*D*Real.exp (-L/(64*(k : ℝ)^2)) := by gcongr
    _ = D*Real.exp (L/(128*(k : ℝ)^2)+(-L/(64*(k : ℝ)^2))) := by rw [Real.exp_add]; ring
    _ = _ := by congr 2; ring

/-- Uniform power saving for prime blocks with their own proved endpoint-population criterion. -/
theorem eventual_envelope_subset_bound : ∀ᶠ v : ℝ in Filter.atTop,
    ∀ (m : ℕ) [NeZero m], Real.log m = Real.exp v → ∀ k s : ℕ,
      1 ≤ k → 1 ≤ s → (s : ℝ) ≤ KorolevSourceEnvelope.envelope v → 8*(k : ℝ)^2 ≤ s →
      ∀ P₀ Q₀ P Q : Finset ℕ, P₀ ⊆ P → Q₀ ⊆ Q → P ⊆ pPrimes m k → Q ⊆ qPrimes m s →
      lowerEndpoint (Real.log m) k/(4*Real.log m) ≤ (P.card : ℝ) →
      upperEndpoint (Real.log m) (s+1)/(4*Real.log m) ≤ (Q.card : ℝ) → ∀ a b : ZMod m,
      (‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
        ((P.card : ℝ)*(Q.card : ℝ)))^(2*s*k) ≤
          (a.val.gcd m : ℝ)*Real.exp (-Real.log m/(128*(k : ℝ)^2)) := by
  filter_upwards [KorolevBlockCost.eventual_cost_absorbed,
    KaratsubaSourceCancellation.eventual_quadratic_conditions]
    with v hc hq m inst hcoord k s hk hs hse hsep P₀ Q₀ P Q hPsub hQsub hPsrc hQsrc hPpop hQpop a b
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hks : (k : ℝ) ≤ s := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hK := (hq k (hks.trans hse)).2.2
  have hS := (hq s hse).2.2
  have hcost := hc k s hk hs hsep hse
  rw [← hcoord] at hK hS hcost
  exact (normalized_subset_exponential_bound hPsub hQsub hPsrc hQsrc hk hs hK hS hPpop hQpop hsep a b).trans
    (absorb_cost (Nat.cast_nonneg _) hcost)

end NField.Alignment.KaratsubaPrimeBlockMoment
