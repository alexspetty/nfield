/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.RootMeasures
/-! # The literal loaded source and carrier on every clock -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.BranchTransport

open scoped BigOperators
open NField.Alignment CollisionRampEnergy Core CenteredPhase CarryWork LoadedWords

def branchSourceWord (p k : ℕ) : ℕ := foldedWord (p - 1) k
def branchField (p k : ℕ) (x : ℝ) : ℝ := boundaryResponse (branchSourceWord p k) x
def sourceCarrier (p s : ℕ) : ℕ := p + s * (s + 1)
def branchCarrier (p k : ℕ) : ℕ := sourceCarrier p (branchSourceWord p k)
def branchPhase (p k : ℕ) (x : ℝ) : ℝ := midpointRow (branchCarrier p k) x
def branchPotential (p k : ℕ) (x : ℝ) : ℝ :=
  periodicPotential ((p : ℝ) * x + branchField p k x) - periodicPotential ((p : ℝ) * x)
def branchCorrection (p k : ℕ) (x : ℝ) : ℝ :=
  if Int.fract (Int.fract ((p : ℝ) * x) + branchField p k x) = 0
    then branchField p k x / 2 else 0

theorem branch_field_own_root (p : ℕ) {k : ℕ} (hk : 2 ≤ k) (a : ℕ) :
    boundaryResponse (p - 1) ((a : ℝ) / (k : ℝ)) =
      branchField p k ((a : ℝ) / (k : ℝ)) := reflected_source_word hk (p - 1) a

theorem branch_carrier_mod {p k : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k) :
    branchCarrier p k % k = p ^ 2 % k := by
  have h := common_sampling_phase (N := p - 1) hk
  simpa only [branchCarrier, sourceCarrier, branchSourceWord, Nat.sub_add_cancel hp] using h

theorem frequency_fract_congr {k K Q : ℕ} (h : K % k = Q % k) (a : ℕ) :
    Int.fract ((K : ℝ) * ((a : ℝ) / (k : ℝ))) =
      Int.fract ((Q : ℝ) * ((a : ℝ) / (k : ℝ))) := by
  conv_lhs => rw [← mul_div_assoc, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod]
  conv_rhs => rw [← mul_div_assoc, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod]
  rw [Nat.mul_mod K a k, Nat.mul_mod Q a k, h]

theorem branch_phase_own_root {p k : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k) (a : ℕ) :
    branchPhase p k ((a : ℝ) / (k : ℝ)) = midpointRow (p ^ 2) ((a : ℝ) / (k : ℝ)) := by
  have h := frequency_fract_congr (branch_carrier_mod hp hk) a
  unfold branchPhase midpointRow affineRow
  rw [h]

theorem clock_reading_root {p k m : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k)
    (hm : packetLoad p k = m) :
    clockReading (p - 1) (p ^ 2) k =
      rootIntegral m k (fun x => branchField p k x * branchPhase p k x) := by
  unfold clockReading rootIntegral unitAddresses
  change ((packetLoad p k : ℕ) : ℝ) * _ = _
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [branch_field_own_root p hk a, branch_phase_own_root hp hk a]

theorem lower_branch_word_formula {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (hb : lowerBranch p k) :
    branchSourceWord p k = centeredPhase p k - 1 ∧
      p - 1 = k * packetLoad p k + branchSourceWord p k := by
  obtain ⟨hr, _⟩ := predecessor_remainder (by omega : 0 < k) (prime_remainder_pos hp hk hkp)
  have hrl := Nat.mod_lt p (by omega : 0 < k)
  have hc : centeredPhase p k = p % k := min_eq_left hb
  have hf : branchSourceWord p k = (p - 1) % k := by
    unfold branchSourceWord foldedWord
    rw [hr]
    exact min_eq_left (by unfold lowerBranch at hb; omega)
  refine ⟨by rw [hf, hr, hc], ?_⟩
  rw [hf]
  exact (Nat.div_add_mod (p - 1) k).symm

theorem upper_branch_word_formula {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (hb : ¬lowerBranch p k) :
    branchSourceWord p k = centeredPhase p k ∧
      p + branchSourceWord p k = k * (packetLoad p k + 1) := by
  obtain ⟨hr, hd⟩ := predecessor_remainder (by omega : 0 < k) (prime_remainder_pos hp hk hkp)
  have hrl := Nat.mod_lt p (by omega : 0 < k)
  have hbranch : k - p % k < p % k := Nat.lt_of_not_ge hb
  have hc : centeredPhase p k = k - p % k := min_eq_right hbranch.le
  have hf : branchSourceWord p k = k - p % k := by
    unfold branchSourceWord foldedWord
    rw [hr]
    have he : k - 1 - (p % k - 1) = k - p % k := by omega
    rw [he]
    exact min_eq_right (by omega)
  refine ⟨by rw [hf, hc], ?_⟩
  have hdecomp := Nat.div_add_mod p k
  unfold packetLoad
  rw [hd, hf]
  nlinarith [Nat.sub_add_cancel hrl.le]

theorem lower_branch_word_step {p k m : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m)
    (hb : lowerBranch p k) (hbn : lowerBranch p (k + 1)) :
    branchSourceWord p (k + 1) + m = branchSourceWord p k := by
  have h := (lower_branch_word_formula hp hk (by omega : k < p) hb).2
  have hn := (lower_branch_word_formula hp (by omega : 2 ≤ k + 1) hkp hbn).2
  rw [hload] at h
  rw [hnext] at hn
  nlinarith

theorem upper_branch_word_step {p k m : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m)
    (hb : ¬lowerBranch p k) (hbn : ¬lowerBranch p (k + 1)) :
    branchSourceWord p (k + 1) = branchSourceWord p k + (m + 1) := by
  have h := (upper_branch_word_formula hp hk (by omega : k < p) hb).2
  have hn := (upper_branch_word_formula hp (by omega : 2 ≤ k + 1) hkp hbn).2
  rw [hload] at h
  rw [hnext] at hn
  nlinarith

theorem source_phase_fract (p s : ℕ) (x : ℝ) :
    Int.fract ((sourceCarrier p s : ℝ) * x) =
      Int.fract ((p : ℝ) * x + boundaryResponse s x) := by
  have hl := integer_phase_lift s x
  apply Int.fract_eq_fract.mpr
  refine ⟨∑ j ∈ Finset.Icc 1 s,
    (1 + 2 * ⌊(j : ℝ) * x⌋ - (if Int.fract ((j : ℝ) * x) = 0 then 1 else 0)), ?_⟩
  unfold sourceCarrier
  push_cast at hl ⊢
  linear_combination hl

theorem fract_reduced_add (u v : ℝ) : Int.fract (Int.fract u + v) = Int.fract (u + v) := by
  apply Int.fract_eq_fract.mpr
  refine ⟨-⌊u⌋, ?_⟩
  rw [Int.fract]
  push_cast
  ring

theorem branch_reduced_phase_fract (p k : ℕ) (x : ℝ) :
    Int.fract (Int.fract ((p : ℝ) * x) + branchField p k x) =
      Int.fract ((branchCarrier p k : ℝ) * x) := by
  rw [fract_reduced_add]
  exact (source_phase_fract p (branchSourceWord p k) x).symm

end NField.ResetForests.BranchTransport
