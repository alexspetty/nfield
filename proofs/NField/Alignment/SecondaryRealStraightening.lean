/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerInverseSeriesLiteral
import NField.Alignment.RealBernoulliCapacityIntegral
import NField.Alignment.CollisionBernoulliStraightening

/-! # Integer straightening into the actual real Bernoulli response -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SecondaryRealStraightening
open scoped BigOperators Topology Classical
open CollisionDedekindPairing IntegerInverseSeriesLiteral
  RealBernoulliBoundaryLimits CollisionBernoulliStraightening
  PrimeCarryTableColumnLaw RealBernoulliCapacityIntegral

theorem bernoulli_boundary_integer {p : ℕ} (hp : p.Prime) (A : ℤ) :
    bernoulliBoundary hp (A:ZMod (p^2))=
      (realBoundary (p-1) ((A:ℝ)/(p:ℝ)^2):ℂ) := by
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp2 : 0<p^2 := pow_pos hp.pos 2
  unfold bernoulliBoundary realBoundary
  push_cast only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_sum]
  congr 1
  symm
  apply Finset.sum_bij (fun i hi => i+1)
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  · intro i hi j hj he
    omega
  · intro r hr
    have := Finset.mem_Ico.mp hr
    exact ⟨r-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro i hi
    have h := centered_sawtooth_int hp2 (((i+1:ℕ):ℤ)*A)
    push_cast at h
    simp only [Nat.cast_add, Nat.cast_one]
    rw [h]
    congr 2
    ring

def realCollisionResponse (p a : ℕ) : ℝ := (carryThresholdCount p a:ℝ)-(a:ℝ)/(p:ℝ)

theorem collision_response_real {p : ℕ} (hp : p.Prime) (a : ZMod (p^2)) :
    collisionResponse p a=(realCollisionResponse p a.val:ℂ) := by
  unfold collisionResponse realCollisionResponse
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  push_cast
  field_simp

/-- Title: `Collision straightening at every integer address`. -/
theorem real_collision_straightening {p : ℕ} (hp : p.Prime) (A : ℤ) :
    realCollisionResponse p ((((1-(p:ℤ))*A:ℤ):ZMod (p^2))).val=
      realBoundary (p-1) ((A:ℝ)/(p:ℝ)^2) := by
  apply Complex.ofReal_injective
  rw [← collision_response_real hp]
  have he : ((((1-(p:ℤ))*A:ℤ):ZMod (p^2)))=(straighteningUnit p).val*(A:ZMod (p^2)) := by
    simp [straighteningUnit]
  rw [he,collision_to_bernoulli_straightening hp,bernoulli_boundary_integer hp]

/-- Title: `Actual Bernoulli samples equal the collision energy`. -/
theorem real_sampled_energy {p : ℕ} (hp : p.Prime) :
    collisionEnergy hp=∑ A ∈ Finset.range (p^2), (realBoundary (p-1) ((A:ℝ)/(p:ℝ)^2))^2 := by
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [collision_energy_eq_bernoulli_energy]
  unfold bernoulliEnergy
  have hpoint (A : ZMod (p^2)) : ‖bernoulliBoundary hp A‖^2=
      (realBoundary (p-1) ((A.val:ℝ)/(p:ℝ)^2))^2 := by
    have hA : A=((A.val:ℤ):ZMod (p^2)) := by simp
    conv_lhs => rw [hA,bernoulli_boundary_integer hp]
    simp only [Int.cast_natCast,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [Finset.sum_congr rfl (fun A hA => hpoint A)]
  exact ProfiniteRemainderMeasure.sum_zmod_val (p^2)
    (fun A : ℕ => (realBoundary (p-1) ((A:ℝ)/(p:ℝ)^2))^2)

end NField.Alignment.SecondaryRealStraightening
