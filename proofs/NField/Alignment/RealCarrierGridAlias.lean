/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryRealStraightening
import NField.Alignment.RealBernoulliJumpData
import NField.Alignment.EndpointReciprocityBridge

/-! # Carrier-grid aliasing for the actual real function and its one-sided jumps -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealCarrierGridAlias
open scoped BigOperators Topology Classical
open CollisionDedekindPairing RealBernoulliBoundaryLimits RealBernoulliJumpData
  RealBernoulliCapacityIntegral SecondaryRealStraightening CollisionBernoulliStraightening
  EndpointReservoirAlias BernoulliCurvature CarrierJumpData

def bernoulliTwo (x : ℝ) : ℝ := Int.fract x^2-Int.fract x+1/6
def squareValueJump (N : ℕ) (x : ℝ) : ℝ :=
  (realBoundary N x-(halfJump N x:ℝ))^2-(realBoundary N x+(halfJump N x:ℝ))^2
def squareSlopeJump (N : ℕ) (x : ℝ) : ℝ :=
  2*realSlope N*(realBoundary N x-(halfJump N x:ℝ))-
    2*realSlope N*(realBoundary N x+(halfJump N x:ℝ))

theorem bernoulliTwo_rational {a k : ℕ} (_hk : 0<k) :
    bernoulliTwo ((a:ℝ)/k)=(rationalBernoulliTwo (a%k) k:ℝ) := by
  unfold bernoulliTwo rationalBernoulliTwo
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  ring

theorem squareValueJump_rational {N a k : ℕ} (hk : 0<k) (ha : a.Coprime k) :
    squareValueJump N ((a:ℝ)/k)= -4*(N/k:ℕ)*(cyclicPrefixResponse a k (N%k):ℝ) := by
  rw [squareValueJump,boundary_rational hk ha,halfJump_rational hk ha]
  ring

theorem squareSlopeJump_rational {N a k : ℕ} (hk : 0<k) (ha : a.Coprime k) :
    squareSlopeJump N ((a:ℝ)/k)= -4*realSlope N*(N/k:ℕ) := by
  rw [squareSlopeJump,halfJump_rational hk ha]
  ring

theorem realSlope_prime_window {p : ℕ} (hp : p.Prime) :
    realSlope (p-1)=(boundarySlope p:ℝ) := by
  have hn : p-1+1=p := by have := hp.two_le; omega
  unfold realSlope boundarySlope
  push_cast
  have hnR : ((p-1:ℕ):ℝ)+1=(p:ℝ) := by exact_mod_cast hn
  rw [hnR]
  ring

def actualValueJumpSum (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (p-1), ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
    squareValueJump (p-1) ((a:ℝ)/k)*periodicSawtooth ((p:ℝ)^2*((a:ℝ)/k))
def actualSlopeJumpSum (p : ℕ) : ℝ :=
  squareSlopeJump (p-1) 0*bernoulliTwo 0+
    ∑ k ∈ Finset.Icc 2 (p-1), ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
      squareSlopeJump (p-1) ((a:ℝ)/k)*bernoulliTwo ((p:ℝ)^2*((a:ℝ)/k))

theorem actual_value_jump_sum (p : ℕ) : actualValueJumpSum p=(rawValueJumpSum p:ℝ) := by
  unfold actualValueJumpSum rawValueJumpSum
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0<k := by have := (Finset.mem_Icc.mp hk).1; omega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [squareValueJump_rational hk0 (Finset.mem_filter.mp ha).2]
  have ht : (p:ℝ)^2*((a:ℝ)/k)=((p^2*a:ℕ):ℝ)/k := by push_cast; ring
  rw [ht,sawtooth_rational (p^2*a) k hk0]
  ring

theorem actual_slope_jump_sum {p : ℕ} (hp : p.Prime) :
    actualSlopeJumpSum p=(rawSlopeJumpSum p:ℝ) := by
  unfold actualSlopeJumpSum rawSlopeJumpSum
  push_cast
  congr 1
  · simp only [squareSlopeJump,halfJump,mul_zero,Int.fract_zero,Finset.filter_true,
      Finset.card_range,bernoulliTwo,sub_zero]
    rw [realSlope_prime_window hp]
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).1
    have hk0 : 0<k := by omega
    rw [multipliedReducedBernoulliTwoSum,reducedResidues_eq_Ico hk2]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [squareSlopeJump_rational hk0 (Finset.mem_filter.mp ha).2,realSlope_prime_window hp]
    congr 1
    have ht : (p:ℝ)^2*((a:ℝ)/k)=((p^2*a:ℕ):ℝ)/k := by push_cast; ring
    rw [ht,bernoulliTwo_rational hk0]

/-- Title: `Periodic aliasing of the actual square with its actual jump data`. -/
theorem actual_periodic_jump_aliasing {p : ℕ} (hp : p.Prime) (hpodd : p≠2) :
    (∑ A ∈ Finset.range (p^2),realBoundary (p-1) ((A:ℝ)/(p:ℝ)^2)^2)/(p:ℝ)^2-
      (∫ x in (0:ℝ)..1,realBoundary (p-1) x^2)=
      -((p-1:ℕ):ℝ)^2/(p:ℝ)^2+actualValueJumpSum p/(p:ℝ)^2-
        actualSlopeJumpSum p/(2*(p:ℝ)^4) := by
  rw [← real_sampled_energy hp,integral_capacity_eq_continuous_capacity,
    collision_energy_eq_bernoulli_energy,actual_value_jump_sum,actual_slope_jump_sum hp]
  simpa only [PeriodicJumpFourierAbelIdentity,neg_div] using
    EndpointReciprocityBridge.periodicJumpFourierAbelIdentity_odd hp hpodd

/-- Title: `Endpoint reservoir formula for the actual integral and carrier samples`. -/
theorem actual_endpoint_reservoir_alias {p : ℕ} (hp : p.Prime) (hpodd : p≠2) :
    (∫ x in (0:ℝ)..1,realBoundary (p-1) x^2)-
      (∑ A ∈ Finset.range (p^2),realBoundary (p-1) ((A:ℝ)/(p:ℝ)^2)^2)/(p:ℝ)^2=
      ((p-1:ℕ):ℝ)^2/(p:ℝ)^2+4*(jumpPhaseReservoir p:ℝ)/(p:ℝ)^2-
        2*(boundarySlope p:ℝ)*(carrierBernoulliCurvature p:ℝ)/(p:ℝ)^4 := by
  rw [← real_sampled_energy hp,integral_capacity_eq_continuous_capacity]
  exact EndpointReciprocityBridge.exact_endpoint_reservoir_alias_formula hp hpodd

end NField.Alignment.RealCarrierGridAlias
