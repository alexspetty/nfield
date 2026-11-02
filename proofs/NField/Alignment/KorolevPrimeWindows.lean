/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevPrimeIntervals

/-!
# The literal selected prime windows in Korolev's decomposition

Work in the logarithmic modulus coordinate L=log m. Source correspondence,
endpoint order and separation are proved before any union is summed.
No source choice of index bounds or asymptotic parameter range is assumed
to have been discharged by these finite algebraic statements.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevPrimeWindows
open scoped BigOperators Classical
open KorolevPrimeIntervals CollisionMertensInput

def upperEndpoint (L : ℝ) (k : ℕ) : ℝ := Real.exp (L / (2 * (k : ℝ) - 1)) / 4
def lowerEndpoint (L : ℝ) (k : ℕ) : ℝ :=
  Real.exp (L * (2 * (k : ℝ)) / ((2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1)))
def windowPrimes (L : ℝ) (k : ℕ) : Finset ℕ :=
  intervalPrimes (lowerEndpoint L k) (upperEndpoint L k)
def selectedPrimes (L : ℝ) (a b : ℕ) : Finset ℕ :=
  (Finset.Icc a b).biUnion (windowPrimes L)

theorem upperEndpoint_pos (L : ℝ) (k : ℕ) : 0 < upperEndpoint L k := by
  unfold upperEndpoint
  positivity
theorem lowerEndpoint_pos (L : ℝ) (k : ℕ) : 0 < lowerEndpoint L k := Real.exp_pos _

theorem upperEndpoint_source {m : ℝ} (hm : 0 < m) (k : ℕ) :
    upperEndpoint (Real.log m) k = m ^ (1 / (2 * (k : ℝ) - 1)) / 4 := by
  rw [upperEndpoint, Real.rpow_def_of_pos hm]
  congr 2
  ring

theorem lowerEndpoint_source {m : ℝ} (hm : 0 < m) {k : ℕ} (hk : 1 ≤ k) :
    lowerEndpoint (Real.log m) k =
      m ^ (1 / (2 * (k : ℝ) - 1) - 1 / (4 * (k : ℝ)^2 - 1)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
  have h2 : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
  have h3 : 4 * (k : ℝ)^2 - 1 ≠ 0 := by nlinarith
  rw [lowerEndpoint, Real.rpow_def_of_pos hm]
  congr 1
  rw [show 4 * (k : ℝ)^2 - 1 = (2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1) by ring]
  field_simp
  ring

theorem log_upper (L : ℝ) (k : ℕ) :
    Real.log (upperEndpoint L k) = L / (2 * (k : ℝ) - 1) - Real.log 4 := by
  rw [upperEndpoint, Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp]

theorem log_lower (L : ℝ) (k : ℕ) :
    Real.log (lowerEndpoint L k) = L * (2 * (k : ℝ)) / ((2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1)) :=
  Real.log_exp _

theorem log_gap (L : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Real.log (upperEndpoint L k) - Real.log (lowerEndpoint L k) =
      L / (4 * (k : ℝ)^2 - 1) - Real.log 4 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
  have h2 : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
  have h3 : 4 * (k : ℝ)^2 - 1 ≠ 0 := by nlinarith
  rw [log_upper, log_lower]
  rw [show 4 * (k : ℝ)^2 - 1 = (2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1) by ring]
  field_simp
  ring

theorem log_lower_ge {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    L / (2 * (k : ℝ) + 1) ≤ Real.log (lowerEndpoint L k) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hminus : 0 < 2 * (k : ℝ) - 1 := by linarith
  rw [log_lower]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (k : ℝ) + 1)
    (by positivity : 0 < (2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1))).mpr
  nlinarith

theorem endpoint_order {L : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hL : (4 * (k : ℝ)^2 - 1) * Real.log 4 ≤ L) :
    lowerEndpoint L k ≤ upperEndpoint L k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 4 * (k : ℝ)^2 - 1 := by nlinarith
  have he := log_gap L hk
  have hr : Real.log 4 ≤ L / (4 * (k : ℝ)^2 - 1) :=
    (le_div_iff₀ hd).mpr (by nlinarith)
  have h := Real.exp_le_exp.mpr (show Real.log (lowerEndpoint L k) ≤
      Real.log (upperEndpoint L k) by linarith)
  simpa only [Real.exp_log (lowerEndpoint_pos L k), Real.exp_log (upperEndpoint_pos L k)] using h

theorem lowerEndpoint_ge_two {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 1 ≤ k)
    (hsize : (2 * (k : ℝ) + 1) * Real.log 2 ≤ L) : 2 ≤ lowerEndpoint L k := by
  have hlog := log_lower_ge hL hk
  have hden : 0 < 2 * (k : ℝ) + 1 := by positivity
  have hb : Real.log 2 ≤ L / (2 * (k : ℝ) + 1) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have h := Real.exp_le_exp.mpr (hb.trans hlog)
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log (lowerEndpoint_pos L k)] using h

theorem upper_antitone {L : ℝ} (hL : 0 ≤ L) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    upperEndpoint L j ≤ upperEndpoint L i := by
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold upperEndpoint
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left hL (by linarith) (by linarith)

theorem successor_separation {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    upperEndpoint L (k+1) < lowerEndpoint L k := by
  have h := log_lower_ge hL hk
  have hu : Real.log (upperEndpoint L (k+1)) = L / (2 * (k : ℝ) + 1) - Real.log 4 := by
    rw [log_upper, Nat.cast_add, Nat.cast_one]
    congr 2; ring
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have he := Real.exp_lt_exp.mpr (show Real.log (upperEndpoint L (k+1)) <
      Real.log (lowerEndpoint L k) by linarith)
  simpa only [Real.exp_log (upperEndpoint_pos L (k+1)), Real.exp_log (lowerEndpoint_pos L k)] using he

theorem window_disjoint {L : ℝ} (hL : 0 ≤ L) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    Disjoint (windowPrimes L i) (windowPrimes L j) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hi' := (intervalPrimes_mem.mp hpi).2.1
  have hj' := (intervalPrimes_mem.mp hpj).2.2
  have hu := upper_antitone hL (by omega : 1 ≤ i+1) (by omega : i+1 ≤ j)
  exact (not_lt_of_ge (hj'.trans (hu.trans (successor_separation hL hi).le))) hi'

theorem selectedPrimes_mem (L : ℝ) (a b p : ℕ) :
    p ∈ selectedPrimes L a b ↔ ∃ k, a ≤ k ∧ k ≤ b ∧
      p.Prime ∧ lowerEndpoint L k < (p : ℝ) ∧ (p : ℝ) ≤ upperEndpoint L k := by
  simp only [selectedPrimes, Finset.mem_biUnion, Finset.mem_Icc, windowPrimes, intervalPrimes_mem]
  aesop

theorem selected_subset {L Q : ℝ} (hL : 0 ≤ L) {a b : ℕ} (ha : 1 ≤ a)
    (hQ : upperEndpoint L a ≤ Q) : selectedPrimes L a b ⊆ primesUpTo Q := by
  intro p hp
  obtain ⟨k, hak, _, hpp, _, hpU⟩ := (selectedPrimes_mem L a b p).mp hp
  exact primesUpTo_mem.mpr ⟨hpp, hpU.trans ((upper_antitone hL ha hak).trans hQ)⟩

theorem selected_reciprocal_sum {L : ℝ} (hL : 0 ≤ L) {a b : ℕ} (ha : 1 ≤ a) :
    (∑ p ∈ selectedPrimes L a b, (1 : ℝ) / p) =
      ∑ k ∈ Finset.Icc a b, ∑ p ∈ windowPrimes L k, (1 : ℝ) / p := by
  unfold selectedPrimes
  apply Finset.sum_biUnion
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact window_disjoint hL (ha.trans (Finset.mem_Icc.mp hi).1) h
  · exact (window_disjoint hL (ha.trans (Finset.mem_Icc.mp hj).1) h).symm

end NField.Alignment.KorolevPrimeWindows
