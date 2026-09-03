/-
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthDilation
import Mathlib.Data.Nat.MaxPowDiv

/-!
# Intrinsic conductor-depth weight

The weight is defined directly on a prime-power residue class through its
canonical representative. The main theorem proves, for every residue at once,
that this intrinsic weight is exactly the response of the induced primitive
character to the centered sawtooth.
-/

namespace NField.Alignment.ConductorDepthWeight

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.ConductorDepthDilation

/-- The exact prime-power conductor-depth weight, defined on residue classes. -/
noncomputable def conductorDepthWeight
    (p t s : ℕ) [NeZero (p ^ t * p ^ s)]
    (ψ : Character (p ^ t)) (k : ZMod (p ^ t * p ^ s)) : ℂ :=
  if k = 0 then 0
  else
    let v := padicValNat p k.val
    if v ≤ s then
      (p ^ v : ℂ) * ψ⁻¹ (k.val.divMaxPow p : ZMod (p ^ t))
    else 0

@[simp]
theorem conductorDepthWeight_zero
    {p t s : ℕ} [NeZero (p ^ t * p ^ s)]
    (ψ : Character (p ^ t)) :
    conductorDepthWeight p t s ψ 0 = 0 := by
  simp [conductorDepthWeight]

/--
The conductor-depth weight is the exact twisted-sawtooth response on every
residue class. This single statement contains the within-budget multiplicity
law, the primitive unit twist, the zero residue, and higher-depth invisibility.
-/
theorem conductorDepthWeight_exact_response
    {p t s : ℕ} [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    ∀ k : ZMod (p ^ t * p ^ s),
      twistedTransform centeredSawtooth
          (DirichletCharacter.changeLevel
            (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ) k =
        twistedTransform (m := p ^ t) centeredSawtooth ψ 1 *
          conductorDepthWeight p t s ψ k := by
  intro k
  by_cases hk : k = 0
  · subst k
    simp [twistedTransform, centeredSawtooth]
  · have hkval : k.val ≠ 0 := (ZMod.val_ne_zero k).2 hk
    let v := padicValNat p k.val
    let u := k.val.divMaxPow p
    have hu : ¬p ∣ u := by
      exact Nat.not_dvd_divMaxPow hp.one_lt hkval
    have hdecomp : p ^ v * u = k.val := by
      exact Nat.pow_padicValNat_mul_divMaxPow p k.val
    have hcast :
        ((p ^ v * u : ℕ) : ZMod (p ^ t * p ^ s)) = k := by
      rw [hdecomp, ZMod.natCast_zmod_val]
    by_cases hv : v ≤ s
    · rw [← hcast]
      rw [conductorDepth_twist_within_budget hp ht hv hu ψ]
      simp only [conductorDepthWeight, hcast, hk, if_false, v, u, hv, if_true]
      ring
    · have hsv : s < v := Nat.lt_of_not_ge hv
      let r := v - s - 1
      have hexp : s + (r + 1) = v := by
        dsimp [r]
        omega
      have hlag : p ^ s * p ^ (r + 1) * u = p ^ v * u := by
        rw [← pow_add, hexp]
      rw [← hcast]
      have hzero :=
        conductorDepth_twist_vanishes_of_overdepth_decomposition
          (p := p) (t := t) (s := s) (r := r) (u := u)
          hp ht hu hψ
      rw [hlag] at hzero
      rw [hzero]
      simp only [conductorDepthWeight, hcast, hk, if_false, v, u, hv, if_false,
        mul_zero]

end NField.Alignment.ConductorDepthWeight
