/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionBernoulliStraightening
import NField.Alignment.CollisionRampEnergy

/-!
# The literal real floor-response and midpoint straightening

The inherited collision theorem is stated in complex residue coordinates.
Here both sides are identified with the real floor and midpoint expressions
printed in this manuscript, including the canonical transformed address.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionStraighteningDisplay

open scoped BigOperators Classical
open CollisionBernoulliStraightening CollisionRampEnergy
open CarryBoundarySpectra PrimeCarryTableColumnLaw CollisionFluctuationSum

def floorResponse (p a : ℕ) : ℝ :=
  (∑ d ∈ Finset.range p,
    (((⌊((((d*(p+1)+1)*a : ℕ) : ℝ)/((p^2 : ℕ) : ℝ))⌋ : ℤ) : ℝ)-
    ((⌊(((d*(p+1)*a : ℕ) : ℝ)/((p^2 : ℕ) : ℝ))⌋ : ℤ) : ℝ)))-
  (a : ℝ)/(p : ℝ)

theorem literal_midpoint_convention (t : ℝ) :
    midpointRow 1 t=if t ∈ Set.range (Int.cast : ℤ → ℝ) then 0 else Int.fract t-1/2 := by
  simpa using midpointRow_formula 1 t

theorem floor_nat_ratio (n m : ℕ) : ⌊(n : ℝ)/(m : ℝ)⌋=((n/m : ℕ) : ℤ) := by
  rw [Int.floor_div_natCast,Int.floor_natCast]
  norm_cast

theorem collisionResponse_eq_floorResponse {p : ℕ} (hp : p.Prime)
    (a : ZMod (p^2)) : collisionResponse p a=(floorResponse p a.val : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold collisionResponse floorResponse carryThresholdCount floorJump
  simp only [floor_nat_ratio]
  push_cast
  congr 1
  · apply Finset.sum_congr rfl
    intro d _
    simp only [mul_comm ((p : ℤ)+1) (d : ℤ)]
  · field_simp

theorem residueSawtooth_eq_midpoint {m : ℕ} (hm : 0 < m) (n : ℕ) :
    centeredSawtooth (n : ZMod m)=(midpointRow 1 ((n : ℝ)/(m : ℝ)) : ℂ) := by
  letI : NeZero m := ⟨hm.ne'⟩
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hz : (n : ZMod m)=0 ↔ n%m=0 := by
    rw [← ZMod.val_eq_zero,ZMod.val_natCast]
  have hzR : ((n%m : ℕ) : ℝ)/(m : ℝ)=0 ↔ n%m=0 := by
    rw [div_eq_zero_iff]
    simp [hmR]
  simp only [midpointRow,affineRow,Nat.cast_one,one_mul,Int.fract_div_natCast_eq_div_natCast_mod]
  by_cases hn : n%m=0
  · simp [centeredSawtooth,hz.mpr hn,hn]
  · rw [centeredSawtooth,if_neg (mt hz.mp hn),if_neg (mt hzR.mp hn),ZMod.val_natCast]
    push_cast
    rfl

theorem literal_boundary_straightening {p : ℕ} (hp : p.Prime) (A : ZMod (p^2)) :
    floorResponse p (((1-(p : ZMod (p^2)))*A).val)=
      2*∑ r ∈ Finset.Ico 1 p, midpointRow 1 ((r : ℝ)*(A.val : ℝ)/((p^2 : ℕ) : ℝ)) := by
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have h := collision_to_bernoulli_straightening hp A
  rw [collisionResponse_eq_floorResponse hp] at h
  change (floorResponse p (((1-(p : ZMod (p^2)))*A).val) : ℂ)=_ at h
  unfold bernoulliBoundary at h
  have he (r : ℕ) : centeredSawtooth ((r : ZMod (p^2))*A)=
      (midpointRow 1 ((r : ℝ)*(A.val : ℝ)/((p^2 : ℕ) : ℝ)) : ℂ) := by
    have hr := residueSawtooth_eq_midpoint (pow_pos hp.pos 2) (r*A.val)
    simpa only [Nat.cast_mul,ZMod.natCast_zmod_val] using hr
  simp_rw [he] at h
  have hre := congrArg Complex.re h
  simpa using hre

end NField.Alignment.CollisionStraighteningDisplay
