/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalPrimeSlices
import NField.Alignment.KaratsubaProductCutoffCost
import NField.Alignment.PrimePowerGcdBound

/-! # The canonical represented-integer phase as a completed prime-product phase -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalPhaseSlices
open KorolevCanonicalPrimeSlices KorolevCanonicalPrimeFactors
  KaratsubaProductCutoffCompletion KaratsubaProductCutoffCost
open scoped BigOperators Classical

def integerPhase {m : ℕ} [NeZero m] (α β : ZMod m) (n : ℕ) : ℂ :=
  ZMod.stdAddChar (α*(n : ZMod m)⁻¹+β*(n : ZMod m))

def canonicalDomain (P P₀ : Finset ℕ) (h m : ℕ) : Finset ℕ :=
  P₀.filter (fun p => p.Coprime m ∧ Cutoff P h p)

/-- Multiplicativity of the residue inverse is used only for coprime factors. -/
theorem inverse_product {m n p q : ℕ} (hn : n.Coprime m) (hp : p.Coprime m) (hq : q.Coprime m) :
    ((n*p*q : ℕ) : ZMod m)⁻¹ = (n : ZMod m)⁻¹*(p : ZMod m)⁻¹*(q : ZMod m)⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  push_cast
  calc
    _ = ((n : ZMod m)*(n : ZMod m)⁻¹)*((p : ZMod m)*(p : ZMod m)⁻¹)*
        ((q : ZMod m)*(q : ZMod m)⁻¹) := by ring
    _ = 1 := by rw [ZMod.coe_mul_inv_eq_one n hn, ZMod.coe_mul_inv_eq_one p hp,
      ZMod.coe_mul_inv_eq_one q hq]; ring

/-- Fixed square/residual factors scale the inverse and ordinary frequencies separately. -/
theorem integerPhase_product {m l h p q : ℕ} [NeZero m] (α β : ZMod m)
    (hl : l.Coprime m) (hh : h.Coprime m) (hp : p.Coprime m) (hq : q.Coprime m) :
    integerPhase α β (l^2*p*q*h) =
      phase (α*((l^2*h : ℕ) : ZMod m)⁻¹) (β*((l^2*h : ℕ) : ZMod m)) p q := by
  have hn : (l^2*h).Coprime m := (hl.pow_left 2).mul_left hh
  unfold integerPhase phase
  rw [show l^2*p*q*h = (l^2*h)*p*q by ring, inverse_product hn hp hq]
  push_cast
  congr 1
  ring

/-- Canonical and unit cutoffs form separate domains; the product cap remains coupled. -/
theorem primeSliceOn_eq_productCutoffSum {m : ℕ} [NeZero m]
    (P Q P₀ Q₀ : Finset ℕ) (l h X : ℕ) (α β : ZMod m)
    (hl : l.Coprime m) (hh : h.Coprime m) :
    primeSliceOn P Q P₀ Q₀ l h X m (integerPhase α β) =
      productCutoffSum (canonicalDomain P P₀ h m) (canonicalDomain Q Q₀ h m) l h X
        (α*((l^2*h : ℕ) : ZMod m)⁻¹) (β*((l^2*h : ℕ) : ZMod m)) := by
  unfold primeSliceOn productCutoffSum canonicalDomain
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpk : p.Coprime m ∧ Cutoff P h p
  · rw [if_pos hpk]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqk : q.Coprime m ∧ Cutoff Q h q
    · rw [if_pos hqk]
      by_cases hc : l^2*p*q*h ≤ X
      · rw [if_pos ⟨hpk.1,hpk.2,hqk.1,hqk.2,hc⟩, if_pos hc]
        exact integerPhase_product α β hl hh hpk.1 hqk.1
      · have hn : ¬(p.Coprime m ∧ Cutoff P h p ∧ q.Coprime m ∧ Cutoff Q h q ∧ l^2*p*q*h ≤ X) := by tauto
        rw [if_neg hn, if_neg hc]
    · rw [if_neg hqk]
      have hn : ¬(p.Coprime m ∧ Cutoff P h p ∧ q.Coprime m ∧ Cutoff Q h q ∧ l^2*p*q*h ≤ X) := by tauto
      rw [if_neg hn]
  · rw [if_neg hpk]
    apply Finset.sum_eq_zero
    intro q hq
    have hn : ¬(p.Coprime m ∧ Cutoff P h p ∧ q.Coprime m ∧ Cutoff Q h q ∧ l^2*p*q*h ≤ X) := by tauto
    rw [if_neg hn]

/-- The actual canonical represented-integer phase inherits harmonic-cost completion. -/
theorem norm_primeSliceOn_le {m : ℕ} [NeZero m]
    (P Q P₀ Q₀ : Finset ℕ) (l h X : ℕ) (α β : ZMod m)
    (hlpos : 0 < l) (hhpos : 0 < h) (hl : l.Coprime m) (hh : h.Coprime m)
    (hrect : ∀ p ∈ P₀, ∀ q ∈ Q₀, p*q < m) {B : ℝ}
    (hbound : ∀ c : ZMod m,
      ‖KaratsubaBilinearReduction.bilinearPrimeSum (canonicalDomain P P₀ h m) (canonicalDomain Q Q₀ h m)
        (α*((l^2*h : ℕ) : ZMod m)⁻¹) (β*((l^2*h : ℕ) : ZMod m)+c)‖ ≤ B) :
    ‖primeSliceOn P Q P₀ Q₀ l h X m (integerPhase α β)‖ ≤ (1+(harmonic m : ℝ))*B := by
  rw [primeSliceOn_eq_productCutoffSum P Q P₀ Q₀ l h X α β hl hh]
  apply norm_productCutoffSum_le_harmonic _ _ l h X hlpos hhpos _ _ _ hbound
  intro p hp q hq
  exact hrect p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1

/-- Unit square/residual factors do not turn the inverse-frequency gcd into a coprime hypothesis. -/
theorem scaled_frequency_gcd {m l h : ℕ} [NeZero m] (a : ZMod m)
    (hl : l.Coprime m) (hh : h.Coprime m) :
    ((a*((l^2*h : ℕ) : ZMod m)⁻¹).val).gcd m = a.val.gcd m := by
  have hn : (l^2*h).Coprime m := (hl.pow_left 2).mul_left hh
  have he : (((ZMod.unitOfCoprime (l^2*h) hn)⁻¹ : (ZMod m)ˣ) : ZMod m) =
      ((l^2*h : ℕ) : ZMod m)⁻¹ := by rw [← ZMod.inv_coe_unit]; rfl
  rw [← he]
  exact PrimePowerGcdBound.gcd_val_mul_unit m a _ (Units.isUnit _)

end NField.Alignment.KorolevCanonicalPhaseSlices
