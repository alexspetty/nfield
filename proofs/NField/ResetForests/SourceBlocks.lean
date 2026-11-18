/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.BranchFields
import NField.Alignment.RealSawtoothLimits
/-! # The actual harmonic blocks and their carrier slopes -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.BranchTransport

open scoped BigOperators
open NField.Alignment CollisionRampEnergy RealSawtoothLimits Core FibreTraces LoadedWords

theorem boundary_source_block {s t : ℕ} (hst : s ≤ t) (x : ℝ) :
    boundaryResponse t x - boundaryResponse s x =
      2 * ∑ j ∈ Finset.Ioc s t, midpointRow j x := by
  have hsub : Finset.Icc 1 s ⊆ Finset.Icc 1 t := by
    intro j hj
    obtain ⟨h1, hs⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨h1, hs.trans hst⟩
  have he : Finset.Icc 1 t \ Finset.Icc 1 s = Finset.Ioc s t := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := fun j => midpointRow j x) hsub
  rw [he] at h
  unfold boundaryResponse
  linarith

theorem boundary_source_derivative (s : ℕ) (u : ℝ) (hu : regularAt s u) :
    HasDerivAt (boundaryResponse s) ((s : ℝ) * ((s : ℝ) + 1)) u := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 s) :
      HasDerivAt (fun x => midpointRow j x) (j : ℝ) u := by
    have h := (sawtooth_deriv (hu j hj)).comp u ((hasDerivAt_id u).const_mul (j : ℝ))
    convert! h using 1
    ring
  have h := (HasDerivAt.fun_sum hterm).const_mul 2
  convert! h using 1
  rw [source_index_sum]
  ring

theorem branch_source_increment_derivative (p k l : ℕ) (u : ℝ)
    (hk : regularAt (branchSourceWord p k) u) (hl : regularAt (branchSourceWord p l) u) :
    HasDerivAt (fun x => branchField p l x - branchField p k x)
      ((branchCarrier p l : ℝ) - (branchCarrier p k : ℝ)) u := by
  have h := (boundary_source_derivative (branchSourceWord p l) u hl).sub
    (boundary_source_derivative (branchSourceWord p k) u hk)
  convert! h using 1
  simp only [branchCarrier, sourceCarrier, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

theorem lower_harmonic_block {p k m : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m)
    (hb : lowerBranch p k) (hbn : lowerBranch p (k + 1)) :
    (Finset.Ioc (branchSourceWord p (k + 1)) (branchSourceWord p k)).card = m ∧
      ∀ x : ℝ, branchField p (k + 1) x - branchField p k x =
        -(2 * ∑ j ∈ Finset.Ioc (branchSourceWord p (k + 1)) (branchSourceWord p k),
          midpointRow j x) := by
  have hs := lower_branch_word_step hp hk hkp hload hnext hb hbn
  have hle : branchSourceWord p (k + 1) ≤ branchSourceWord p k := by omega
  constructor
  · simp only [Nat.card_Ioc]
    omega
  · intro x
    have h := boundary_source_block hle x
    unfold branchField
    linarith

theorem upper_harmonic_block {p k m : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m)
    (hb : ¬lowerBranch p k) (hbn : ¬lowerBranch p (k + 1)) :
    (Finset.Ioc (branchSourceWord p k) (branchSourceWord p (k + 1))).card = m + 1 ∧
      ∀ x : ℝ, branchField p (k + 1) x - branchField p k x =
        2 * ∑ j ∈ Finset.Ioc (branchSourceWord p k) (branchSourceWord p (k + 1)),
          midpointRow j x := by
  have hs := upper_branch_word_step hp hk hkp hload hnext hb hbn
  have hle : branchSourceWord p k ≤ branchSourceWord p (k + 1) := by omega
  constructor
  · simp only [Nat.card_Ioc]
    omega
  · intro x
    exact boundary_source_block hle x

theorem lower_carrier_increment {p k m : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m)
    (hb : lowerBranch p k) (hbn : lowerBranch p (k + 1)) :
    (branchCarrier p (k + 1) : ℤ) - (branchCarrier p k : ℤ) =
      -(m : ℤ) * (2 * (branchSourceWord p (k + 1) : ℤ) + m + 1) := by
  have hs := lower_branch_word_step hp hk hkp hload hnext hb hbn
  unfold branchCarrier sourceCarrier
  rw [← hs]
  push_cast
  ring

theorem upper_carrier_increment {p k m : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m)
    (hb : ¬lowerBranch p k) (hbn : ¬lowerBranch p (k + 1)) :
    (branchCarrier p (k + 1) : ℤ) - (branchCarrier p k : ℤ) =
      ((m : ℤ) + 1) * (2 * (branchSourceWord p k : ℤ) + m + 2) := by
  have hs := upper_branch_word_step hp hk hkp hload hnext hb hbn
  unfold branchCarrier sourceCarrier
  rw [hs]
  push_cast
  ring

end NField.ResetForests.BranchTransport
