/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SignedDivisorWindow
import NField.Alignment.SquareLockResidueArc

/-! # The exact injection from square locks to signed divisors -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SquareLockDivisorInjection
open scoped BigOperators Classical
open SquareLockCarrierMass SignedDivisorWindow

/-- Title: `The exact signed divisor lock`. -/
theorem centered_residue_divisor_lock (n k : ℕ) :
    (k : ℤ) ∣ (n : ℤ) - centeredNaturalResidue n k := by
  have hdiv : ((n % k : ℕ) : ℤ) + k * ((n / k : ℕ) : ℤ) = n := by
    exact_mod_cast Nat.mod_add_div n k
  unfold centeredNaturalResidue
  dsimp only
  split_ifs
  · refine ⟨(n / k : ℕ), ?_⟩
    linarith
  · refine ⟨((n / k : ℕ) : ℤ) + 1, ?_⟩
    nlinarith

theorem centered_residue_toNat_dvd (n k : ℕ) :
    k ∣ ((n : ℤ) - centeredNaturalResidue n k).toNat := by
  by_cases hz : 0 ≤ (n : ℤ) - centeredNaturalResidue n k
  · have ht : (k : ℤ) ∣ (((n : ℤ) - centeredNaturalResidue n k).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hz]
      exact centered_residue_divisor_lock n k
    exact_mod_cast ht
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    exact dvd_zero k

/-- Title: `Square-lock carriers inject into the signed divisor window`. -/
theorem carrier_count_le_signed_divisor_count {p C : ℕ} (hp : p.Prime)
    (hhalf : 2 * C ≤ p) :
    ((smallDisplacementCarriers p C).card : ℝ) ≤ signedDivisorCount p C := by
  let s := smallDisplacementCarriers p C
  let t := (signedDisplacements C).sigma
    (fun c => (((p : ℤ)^2 - c).toNat).divisors)
  let f : ℕ → Σ _ : ℤ, ℕ := fun k => ⟨centeredNaturalResidue (p^2) k, k⟩
  have hCsq : C < p^2 := by have := hp.two_le; nlinarith
  have hmap : Set.MapsTo f s t := by
    intro k hk
    have hks := Finset.mem_filter.mp hk
    have hc : centeredNaturalResidue (p^2) k ∈ signedDisplacements C :=
      signed_displacement_mem.mpr ⟨hks.2.1,hks.2.2⟩
    apply Finset.mem_sigma.mpr
    refine ⟨hc, Nat.mem_divisors.mpr ⟨?_, ?_⟩⟩
    · change k ∣ ((p : ℤ)^2 - centeredNaturalResidue (p^2) k).toNat
      have he : ((p^2 : ℕ) : ℤ) = (p : ℤ)^2 := by norm_cast
      rw [← he]
      exact centered_residue_toNat_dvd (p^2) k
    · have hci := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hc)
      have hcast : (p : ℤ)^2 = (p^2 : ℕ) := by norm_cast
      change ((p : ℤ)^2 - centeredNaturalResidue (p^2) k).toNat ≠ 0
      omega
  have hinj : Set.InjOn f s := by
    intro a ha b hb h
    exact congrArg Sigma.snd h
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  have hreal : (s.card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast hcard
  simpa only [s,t,Finset.card_sigma,Nat.cast_sum,signedDivisorCount] using hreal

end NField.Alignment.SquareLockDivisorInjection
