/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Coordinates
import NField.ResetForests.DivisorBudget
import NField.ResetForests.Sampling
import NField.ResetForests.OrderedWork
import NField.ResetForests.Words
import NField.ResetForests.Carry
import NField.ResetForests.Readout
import NField.ResetForests.CoherentWork
import NField.ResetForests.Targets
import NField.ResetForests.GridWork
import NField.ResetForests.Centered
import NField.ResetForests.CarryClock
import NField.ResetForests.ClockBinary
import NField.ResetForests.PhaseFringe
import NField.ResetForests.LoadTail
import NField.ResetForests.ForestRates
import NField.ResetForests.Opening
import NField.ResetForests.Complement
import NField.ResetForests.WindowExample
import NField.ResetForests.EnergyMatrices
import NField.ResetForests.FibreDirections
import NField.ResetForests.FibreBasisTrace
import NField.ResetForests.GramSectors
import NField.ResetForests.TorusIncidence
import NField.ResetForests.CompleteReset
import NField.ResetForests.OrderedMasks
import NField.ResetForests.PacketPopulation
import NField.ResetForests.PacketReading
import NField.ResetForests.PacketPeriod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-! # The actual finite root measures and their signed transport

The integral against the difference of two finite root measures is written
as the difference of their integrals. Both complete root grids remain.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.BranchTransport

open scoped BigOperators
open MeasureTheory

def unitAddresses (k : ℕ) : Finset ℕ :=
  (Finset.Ico 1 k).filter (fun a => a.Coprime k)
def rootMeasure (m k : ℕ) : Measure ℝ :=
  (m : ENNReal) • ∑ a ∈ unitAddresses k, Measure.dirac ((a : ℝ) / (k : ℝ))
def rootIntegral (m k : ℕ) (f : ℝ → ℝ) : ℝ :=
  (m : ℝ) * ∑ a ∈ unitAddresses k, f ((a : ℝ) / (k : ℝ))
def rootDifferenceIntegral (m k l : ℕ) (f : ℝ → ℝ) : ℝ :=
  rootIntegral m l f - rootIntegral m k f

theorem root_integrable (m k : ℕ) (f : ℝ → ℝ) : Integrable f (rootMeasure m k) := by
  apply Integrable.smul_measure (c := (m : ENNReal)) _ (by simp)
  exact integrable_finsetSum_measure.mpr (fun a _ => integrable_dirac (by simp))

theorem integral_root_measure (m k : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂rootMeasure m k) = rootIntegral m k f := by
  unfold rootMeasure rootIntegral
  rw [integral_smul_measure, integral_finsetSum_measure
    (fun (a : ℕ) _ => integrable_dirac (f := f) (a := ((a : ℝ) / (k : ℝ))) (by simp))]
  simp only [integral_dirac, ENNReal.toReal_natCast, smul_eq_mul]

theorem root_difference_integral (m k l : ℕ) (f : ℝ → ℝ) :
    rootDifferenceIntegral m k l f =
      (∫ x, f x ∂rootMeasure m l) - (∫ x, f x ∂rootMeasure m k) := by
  simp only [integral_root_measure, rootDifferenceIntegral]

theorem root_integral_congr {m k : ℕ} {f g : ℝ → ℝ}
    (h : ∀ a ∈ unitAddresses k, f ((a : ℝ) / (k : ℝ)) = g ((a : ℝ) / (k : ℝ))) :
    rootIntegral m k f = rootIntegral m k g := by
  unfold rootIntegral
  congr 1
  exact Finset.sum_congr rfl h

theorem root_integral_add (m k : ℕ) (f g : ℝ → ℝ) :
    rootIntegral m k (fun x => f x + g x) = rootIntegral m k f + rootIntegral m k g := by
  simp only [rootIntegral, Finset.sum_add_distrib, mul_add]

theorem root_integral_sub (m k : ℕ) (f g : ℝ → ℝ) :
    rootIntegral m k (fun x => f x - g x) = rootIntegral m k f - rootIntegral m k g := by
  simp only [rootIntegral, Finset.sum_sub_distrib, mul_sub]

theorem root_integral_const_mul (m k : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    rootIntegral m k (fun x => c * f x) = c * rootIntegral m k f := by
  simp only [rootIntegral, ← Finset.mul_sum]
  ring

theorem root_integral_zero (m k : ℕ) : rootIntegral m k (fun _ => 0) = 0 := by
  simp [rootIntegral]

theorem measured_root_connection (m k l : ℕ) (v w φ χ : ℝ → ℝ) :
    rootIntegral m l (fun x => w x * χ x) - rootIntegral m k (fun x => v x * φ x) =
      rootIntegral m k (fun x => (w x - v x) * φ x + v x * (χ x - φ x) +
        (w x - v x) * (χ x - φ x)) +
      rootDifferenceIntegral m k l (fun x => w x * χ x) := by
  have he : (fun x => (w x - v x) * φ x + v x * (χ x - φ x) +
      (w x - v x) * (χ x - φ x)) = (fun x => w x * χ x - v x * φ x) := by
    funext x
    ring
  rw [he, root_integral_sub]
  unfold rootDifferenceIntegral
  ring

theorem complete_root_transport (m k l : ℕ) (f g : ℝ → ℝ) :
    rootIntegral m k (fun x => g x - f x) + rootDifferenceIntegral m k l g =
      rootIntegral m l g - rootIntegral m k f := by
  rw [root_integral_sub]
  unfold rootDifferenceIntegral
  ring

end NField.ResetForests.BranchTransport
