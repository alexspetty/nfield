/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorExtremaTheorem
import NField.Alignment.CollisionAmplitudeEnclosure

/-!
# Certified finite enclosures for the full conductor cutoff

Signed interval arithmetic propagates the proved full-amplitude enclosure.
The universal positive regrouping bound tightens the lower beta endpoint.
All endpoints use finite rational sums; the enclosed objects retain their
full infinite amplitudes. This supplies the software correspondence.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionConductorEnclosure

open scoped BigOperators Classical
open CollisionAmplitudeEnclosure CollisionRemainderDynamics CollisionJordanVariance
open CollisionFiniteRegrouping CollisionPositiveRegrouping CollisionConductorExtrema
open CollisionConductorOne CollisionRestrictedGap CollisionPotentialConvergence
open CollisionCylinderMeans

def scalarLower (c l u : ℝ) : ℝ := if 0 ≤ c then c*l else c*u
def scalarUpper (c l u : ℝ) : ℝ := if 0 ≤ c then c*u else c*l

theorem scalar_mem_enclosure {c l u x : ℝ} (hx : x ∈ Set.Icc l u) :
    c*x ∈ Set.Icc (scalarLower c l u) (scalarUpper c l u) := by
  unfold scalarLower scalarUpper
  split_ifs with hc
  · exact ⟨mul_le_mul_of_nonneg_left hx.1 hc,mul_le_mul_of_nonneg_left hx.2 hc⟩
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hc',mul_le_mul_of_nonpos_left hx.1 hc'⟩

def betaRawLower (d Q M : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (Q/d), scalarLower (ArithmeticFunction.moebius j : ℝ)
    (finiteAmplitude collisionWeight (d*j) M) (amplitudeUpper (d*j) M)

def betaLower (d Q M : ℕ) : ℝ := max (collisionWeight d/2) (betaRawLower d Q M)

def betaUpper (d Q M : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (Q/d), scalarUpper (ArithmeticFunction.moebius j : ℝ)
    (finiteAmplitude collisionWeight (d*j) M) (amplitudeUpper (d*j) M)

theorem beta_raw_enclosure (d Q M : ℕ) :
    beta d Q ∈ Set.Icc (betaRawLower d Q M) (betaUpper d Q M) := by
  constructor
  · apply Finset.sum_le_sum
    intro j _
    exact (scalar_mem_enclosure (amplitude_mem_enclosure (d*j) M)).1
  · apply Finset.sum_le_sum
    intro j _
    exact (scalar_mem_enclosure (amplitude_mem_enclosure (d*j) M)).2

theorem beta_mem_enclosure {d Q : ℕ} (hd : 2 ≤ d) (hdQ : d ≤ Q) (M : ℕ) :
    beta d Q ∈ Set.Icc (betaLower d Q M) (betaUpper d Q M) := by
  have hb := beta_raw_enclosure d Q M
  exact ⟨max_le (beta_strict_half hd hdQ).le hb.1,hb.2⟩

theorem betaLower_pos {d Q : ℕ} (hd : 2 ≤ d) (M : ℕ) : 0 < betaLower d Q M :=
  (div_pos (collisionWeight_pos hd) (by norm_num)).trans_le (le_max_left _ _)

def conductorLower (Q a M : ℕ) : ℝ :=
  (2/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, scalarLower (primitiveValue q a)
    (finiteAmplitude collisionWeight q M) (amplitudeUpper q M)

def conductorUpper (Q a M : ℕ) : ℝ :=
  (2/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, scalarUpper (primitiveValue q a)
    (finiteAmplitude collisionWeight q M) (amplitudeUpper q M)

theorem fixedConductor_mem_enclosure (Q a M : ℕ) :
    fixedConductorValue Q a ∈ Set.Icc (conductorLower Q a M) (conductorUpper Q a M) := by
  have hterm : ∀ q, amplitude q*primitiveValue q a ∈
      Set.Icc (scalarLower (primitiveValue q a) (finiteAmplitude collisionWeight q M) (amplitudeUpper q M))
        (scalarUpper (primitiveValue q a) (finiteAmplitude collisionWeight q M) (amplitudeUpper q M)) := by
    intro q
    simpa only [mul_comm (amplitude q)] using
      (scalar_mem_enclosure (c := primitiveValue q a) (amplitude_mem_enclosure q M))
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2/3)
    exact Finset.sum_le_sum (fun q _ => (hterm q).1)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2/3)
    exact Finset.sum_le_sum (fun q _ => (hterm q).2)

def endpointLower (Q M : ℕ) : ℝ :=
  (1/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, (q.totient : ℝ)*finiteAmplitude collisionWeight q M

def endpointUpper (Q M : ℕ) : ℝ :=
  (1/3 : ℝ)*∑ q ∈ Finset.Icc 2 Q, (q.totient : ℝ)*amplitudeUpper q M

theorem conductorEndpoint_mem_enclosure (Q M : ℕ) :
    conductorEndpoint Q ∈ Set.Icc (endpointLower Q M) (endpointUpper Q M) := by
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/3)
    exact Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left
      (amplitude_mem_enclosure q M).1 (Nat.cast_nonneg _))
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/3)
    exact Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left
      (amplitude_mem_enclosure q M).2 (Nat.cast_nonneg _))

def gapLower (Q a M : ℕ) : ℝ :=
  (2/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q, betaLower d Q M*((a%d : ℕ) : ℝ)

def gapUpper (Q a M : ℕ) : ℝ :=
  (2/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q, betaUpper d Q M*((a%d : ℕ) : ℝ)

theorem conductorGap_mem_enclosure (Q a M : ℕ) :
    conductorGap Q a ∈ Set.Icc (gapLower Q a M) (gapUpper Q a M) := by
  rw [conductorGap_formula]
  have hb : ∀ d ∈ Finset.Icc 2 Q,
      beta d Q ∈ Set.Icc (betaLower d Q M) (betaUpper d Q M) := by
    intro d hd
    exact beta_mem_enclosure (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2 M
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2/3)
    exact Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_right (hb d hd).1 (Nat.cast_nonneg _))
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2/3)
    exact Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_right (hb d hd).2 (Nat.cast_nonneg _))

def restrictedLower (Q M : ℕ) : ℝ :=
  if h : (interiorResidues Q).Nonempty then (interiorResidues Q).inf' h (gapLower Q · M) else 0

def restrictedUpper (Q M : ℕ) : ℝ :=
  if h : (interiorResidues Q).Nonempty then (interiorResidues Q).inf' h (gapUpper Q · M) else 0

theorem restrictedGap_mem_enclosure {Q : ℕ} (hQ : 3 ≤ Q) (M : ℕ) :
    restrictedGap Q ∈ Set.Icc (restrictedLower Q M) (restrictedUpper Q M) := by
  have hne := interiorResidues_nonempty hQ
  rw [restrictedLower,restrictedUpper,dif_pos hne,dif_pos hne]
  constructor
  · obtain ⟨a,ha,hmin⟩ := restrictedGap_attained hQ
    exact (Finset.inf'_le (gapLower Q · M) ha).trans
      ((conductorGap_mem_enclosure Q a M).1.trans_eq hmin)
  · apply Finset.le_inf' _ _
    intro a ha
    exact (restrictedGap_le hQ ha).trans (conductorGap_mem_enclosure Q a M).2

theorem minimizer_in_enclosure_candidates {Q a M : ℕ} (hQ : 3 ≤ Q)
    (hmin : conductorGap Q a=restrictedGap Q) : gapLower Q a M ≤ restrictedUpper Q M := by
  exact (conductorGap_mem_enclosure Q a M).1.trans
    (hmin.trans_le (restrictedGap_mem_enclosure hQ M).2)

end NField.Alignment.CollisionConductorEnclosure
