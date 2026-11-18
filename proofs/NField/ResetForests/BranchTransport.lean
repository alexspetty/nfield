/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.SourceBlocks
/-! # Complete source, phase and root-measure transport

The old and next grids are the actual primitive-root measures. Potential
and midpoint-correction changes retain their complete signed transport.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.BranchTransport

open scoped BigOperators
open NField.Alignment CollisionRampEnergy Core CarryWork LoadedWords MeasureTheory

def branchCarry (p k : ℕ) (x : ℝ) : ℝ :=
  carryMoment (Int.fract ((p : ℝ) * x))
    ⌊Int.fract ((p : ℝ) * x) + branchField p k x⌋
def liftedAngle (Q : ℕ) (A : ℝ) (k : ℕ) : ℝ := (Q : ℝ) * A / (k : ℝ)

theorem actual_branch_connection {p k m : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m) :
    let U := fun x => branchField p (k + 1) x - branchField p k x
    let Δ := fun x => branchPhase p (k + 1) x - branchPhase p k x
    4 * clockReading (p - 1) (p ^ 2) (k + 1) - 4 * clockReading (p - 1) (p ^ 2) k =
      4 * rootIntegral m k (fun x => U x * branchPhase p k x + branchField p k x * Δ x + U x * Δ x) +
      4 * rootDifferenceIntegral m k (k + 1) (fun x => branchField p (k + 1) x * branchPhase p (k + 1) x) := by
  dsimp only
  rw [clock_reading_root hp (by omega : 2 ≤ k + 1) hnext, clock_reading_root hp hk hload]
  have h := measured_root_connection m k (k + 1) (branchField p k) (branchField p (k + 1))
    (branchPhase p k) (branchPhase p (k + 1))
  linear_combination 4 * h

theorem actual_measure_branch_connection {p k m : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k)
    (hload : packetLoad p k = m) (hnext : packetLoad p (k + 1) = m) :
    let U := fun x => branchField p (k + 1) x - branchField p k x
    let Δ := fun x => branchPhase p (k + 1) x - branchPhase p k x
    4 * clockReading (p - 1) (p ^ 2) (k + 1) - 4 * clockReading (p - 1) (p ^ 2) k =
      4 * (∫ x, U x * branchPhase p k x + branchField p k x * Δ x + U x * Δ x ∂rootMeasure m k) +
      4 * ((∫ x, branchField p (k + 1) x * branchPhase p (k + 1) x ∂rootMeasure m (k + 1)) -
        ∫ x, branchField p (k + 1) x * branchPhase p (k + 1) x ∂rootMeasure m k) := by
  simpa only [integral_root_measure, rootDifferenceIntegral] using
    actual_branch_connection hp hk hload hnext

theorem branch_carry_point (p k : ℕ) (x : ℝ) :
    branchField p k x * branchPhase p k x =
      branchPotential p k x + (branchField p k x) ^ 2 / 2 - branchCarry p k x + branchCorrection p k x := by
  have h := carry_potential_identity (Int.fract_nonneg ((p : ℝ) * x))
    (Int.fract_lt_one ((p : ℝ) * x)) (branchField p k x)
  have hphase := branch_reduced_phase_fract p k x
  have hrow : midpointRow 1 (Int.fract ((p : ℝ) * x) + branchField p k x) = branchPhase p k x := by
    unfold branchPhase midpointRow affineRow
    simp only [Nat.cast_one, one_mul]
    rw [hphase]
  have hpot : periodicPotential (Int.fract ((p : ℝ) * x) + branchField p k x) =
      periodicPotential ((p : ℝ) * x + branchField p k x) := by
    unfold periodicPotential
    rw [fract_reduced_add]
  have hbase : periodicPotential (Int.fract ((p : ℝ) * x)) = periodicPotential ((p : ℝ) * x) := by
    simp only [periodicPotential, Int.fract_fract]
  rw [hrow, hpot, hbase] at h
  exact h

theorem branch_potential_own_point {p k : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k) (a : ℕ) :
    branchPotential p k ((a : ℝ) / (k : ℝ)) =
      periodicPotential (((p ^ 2 : ℕ) : ℝ) * ((a : ℝ) / (k : ℝ))) -
        periodicPotential ((p : ℝ) * ((a : ℝ) / (k : ℝ))) := by
  have hl := source_phase_fract p (branchSourceWord p k) ((a : ℝ) / (k : ℝ))
  have hf := frequency_fract_congr (branch_carrier_mod hp hk) a
  have he : Int.fract ((p : ℝ) * ((a : ℝ) / (k : ℝ)) + branchField p k ((a : ℝ) / (k : ℝ))) =
      Int.fract (((p ^ 2 : ℕ) : ℝ) * ((a : ℝ) / (k : ℝ))) := hl.symm.trans hf
  unfold branchPotential periodicPotential
  rw [he]

theorem branch_potential_own_integral {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) (m : ℕ) :
    rootIntegral m k (branchPotential p k) = 0 := by
  have hpc : p.Coprime k := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkp)
  have hsum : (∑ a ∈ unitAddresses k, branchPotential p k ((a : ℝ) / (k : ℝ))) =
      (∑ a ∈ unitAddresses k, periodicPotential (((p ^ 2 : ℕ) : ℝ) * ((a : ℝ) / (k : ℝ)))) -
      ∑ a ∈ unitAddresses k, periodicPotential ((p : ℝ) * ((a : ℝ) / (k : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => branch_potential_own_point hp.one_le hk a)
  unfold rootIntegral
  rw [hsum]
  unfold unitAddresses
  rw [potential_unit_permutation hk (hpc.pow_left 2), potential_unit_permutation hk hpc]
  ring

theorem branch_correction_own_point {p k a : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (ha : a ∈ unitAddresses k) : branchCorrection p k ((a : ℝ) / (k : ℝ)) = 0 := by
  have hpc : p.Coprime k := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkp)
  have hac := (Finset.mem_filter.mp ha).2
  have hn := coprime_grid_nonintegral hk (hpc.pow_left 2) hac
  have hphase := branch_reduced_phase_fract p k ((a : ℝ) / (k : ℝ))
  have hf := frequency_fract_congr (branch_carrier_mod hp.one_le hk) a
  have hnot : Int.fract (Int.fract ((p : ℝ) * ((a : ℝ) / (k : ℝ))) +
      branchField p k ((a : ℝ) / (k : ℝ))) ≠ 0 := by
    rw [hphase, hf]
    exact hn
  unfold branchCorrection
  rw [if_neg hnot]

theorem branch_correction_own_integral {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) (m : ℕ) :
    rootIntegral m k (branchCorrection p k) = 0 := by
  unfold rootIntegral
  have hsum : (∑ a ∈ unitAddresses k, branchCorrection p k ((a : ℝ) / (k : ℝ))) = 0 :=
    Finset.sum_eq_zero (fun a ha => branch_correction_own_point hp hk hkp ha)
  rw [hsum, mul_zero]

theorem complete_branch_potential_transport {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p) (m : ℕ) :
    rootIntegral m k (fun x => branchPotential p (k + 1) x - branchPotential p k x) +
      rootDifferenceIntegral m k (k + 1) (branchPotential p (k + 1)) = 0 := by
  rw [complete_root_transport,
    branch_potential_own_integral hp (by omega : 2 ≤ k + 1) hkp m,
    branch_potential_own_integral hp hk (by omega : k < p) m, sub_self]

theorem complete_branch_midpoint_transport {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p) (m : ℕ) :
    rootIntegral m k (fun x => branchCorrection p (k + 1) x - branchCorrection p k x) +
      rootDifferenceIntegral m k (k + 1) (branchCorrection p (k + 1)) = 0 := by
  rw [complete_root_transport,
    branch_correction_own_integral hp (by omega : 2 ≤ k + 1) hkp m,
    branch_correction_own_integral hp hk (by omega : k < p) m, sub_self]

theorem actual_measure_potential_transport {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p) (m : ℕ) :
    (∫ x, branchPotential p (k + 1) x - branchPotential p k x ∂rootMeasure m k) +
      ((∫ x, branchPotential p (k + 1) x ∂rootMeasure m (k + 1)) -
        ∫ x, branchPotential p (k + 1) x ∂rootMeasure m k) = 0 := by
  simpa only [integral_root_measure, rootDifferenceIntegral] using
    complete_branch_potential_transport hp hk hkp m

theorem actual_measure_midpoint_transport {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k + 1 < p) (m : ℕ) :
    (∫ x, branchCorrection p (k + 1) x - branchCorrection p k x ∂rootMeasure m k) +
      ((∫ x, branchCorrection p (k + 1) x ∂rootMeasure m (k + 1)) -
        ∫ x, branchCorrection p (k + 1) x ∂rootMeasure m k) = 0 := by
  simpa only [integral_root_measure, rootDifferenceIntegral] using
    complete_branch_midpoint_transport hp hk hkp m

theorem branch_carry_clock_identity {p k m : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (hload : packetLoad p k = m) :
    4 * clockReading (p - 1) (p ^ 2) k =
      2 * rootIntegral m k (fun x => (branchField p k x) ^ 2) - 4 * rootIntegral m k (branchCarry p k) := by
  rw [clock_reading_root hp.one_le hk hload]
  have he : (fun x => branchField p k x * branchPhase p k x) =
      (fun x => (branchPotential p k x + (1 / 2 : ℝ) * (branchField p k x) ^ 2) -
        branchCarry p k x + branchCorrection p k x) := by
    funext x
    rw [branch_carry_point]
    ring
  rw [he, root_integral_add, root_integral_sub, root_integral_add, root_integral_const_mul,
    branch_potential_own_integral hp hk hkp m, branch_correction_own_integral hp hk hkp m]
  ring

theorem lifted_angle_root_phase {p k : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k) (a : ℕ) :
    branchPhase p k ((a : ℝ) / (k : ℝ)) = midpointRow 1 (liftedAngle (p ^ 2) (a : ℝ) k) := by
  rw [branch_phase_own_root hp hk a]
  unfold liftedAngle midpointRow affineRow
  simp only [Nat.cast_one, one_mul]
  rw [mul_div_assoc]

theorem actual_lifted_angle_curvature {k : ℕ} (hk : 0 < k) (Q : ℕ) (A : ℝ) :
    liftedAngle Q A (k + 2) - 2 * liftedAngle Q A (k + 1) + liftedAngle Q A k =
      2 * (Q : ℝ) * A / ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have h := reciprocal_angle_curvature (show (0 : ℝ) < k by exact_mod_cast hk) (Q : ℝ) A
  simpa only [liftedAngle, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h

end NField.ResetForests.BranchTransport
