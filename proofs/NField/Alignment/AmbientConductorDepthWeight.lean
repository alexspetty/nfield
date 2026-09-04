/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthDilation
import Mathlib.Data.Nat.MaxPowDiv

/-!
# Ambient prime-power conductor-depth weight

This is the paper's intrinsic depth weight at the fixed ambient modulus p^N.
Unlike a factorized presentation of the modulus, its type is uniform across
all source conductor levels, which permits the complete energy decomposition.
-/

namespace NField.Alignment.AmbientConductorDepthWeight

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.ConductorDepthDilation

/-- Exact conductor-depth weight at ambient level p^N and source level p^t. -/
noncomputable def ambientConductorDepthWeight
    (p N t : ℕ) [NeZero (p ^ N)]
    (ψ : Character (p ^ t)) (k : ZMod (p ^ N)) : ℂ :=
  if k = 0 then 0
  else
    let v := padicValNat p k.val
    if v ≤ N - t then
      (p ^ v : ℂ) * ψ⁻¹ (k.val.divMaxPow p : ZMod (p ^ t))
    else 0

/--
At a fixed ambient prime power, every residue has exactly the response
prescribed by its canonical p-adic depth and primitive unit part.
-/
theorem ambientConductorDepthWeight_exact_response
    {p N t : ℕ} [NeZero (p ^ N)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t) (htN : t ≤ N)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    ∀ k : ZMod (p ^ N),
      twistedTransform centeredSawtooth
          (DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ) k =
        twistedTransform (m := p ^ t) centeredSawtooth ψ 1 *
          ambientConductorDepthWeight p N t ψ k := by
  intro k
  by_cases hk : k = 0
  · subst k
    simp [twistedTransform, centeredSawtooth, ambientConductorDepthWeight]
  · have hkval : k.val ≠ 0 := (ZMod.val_ne_zero k).2 hk
    let v := padicValNat p k.val
    let u := k.val.divMaxPow p
    have hu : ¬p ∣ u := Nat.not_dvd_divMaxPow hp.one_lt hkval
    have hdecomp : p ^ v * u = k.val :=
      Nat.pow_padicValNat_mul_divMaxPow p k.val
    have hcast : ((p ^ v * u : ℕ) : ZMod (p ^ N)) = k := by
      rw [hdecomp, ZMod.natCast_zmod_val]
    by_cases hv : v ≤ N - t
    · rw [← hcast]
      have htop :
          p ^ N = (p ^ t * p ^ (N - t - v)) * p ^ v := by
        calc
          p ^ N = p ^ ((t + (N - t - v)) + v) := by
            congr 1
            omega
          _ = (p ^ t * p ^ (N - t - v)) * p ^ v := by
            rw [pow_add, pow_add]
      have hresponse :=
        conductorDepth_twist_of_factored_modulus
          (top := p ^ N) (p := p) (t := t) (r := N - t - v)
          (v := v) (u := u) hp ht hu ψ htop (pow_dvd_pow p htN)
      rw [hresponse]
      simp only [ambientConductorDepthWeight, hcast, hk, if_false,
        v, u, hv, if_true]
      ring
    · let s := N - t
      let r := v - s - 1
      have hexp : s + (r + 1) = v := by
        dsimp [s, r]
        omega
      have hlag : p ^ s * p ^ (r + 1) * u = p ^ v * u := by
        rw [← pow_add, hexp]
      have htop : p ^ N = p ^ t * p ^ s := by
        dsimp [s]
        rw [← pow_add]
        congr 1
        omega
      rw [← hcast]
      have hzero :=
        conductorDepth_twist_vanishes_of_factored_modulus
          (top := p ^ N) (p := p) (t := t) (s := s) (r := r) (u := u)
          hp ht hu hψ htop (pow_dvd_pow p htN)
      rw [hlag] at hzero
      rw [hzero]
      simp only [ambientConductorDepthWeight, hcast, hk, if_false,
        v, u, hv, if_false, mul_zero]

end NField.Alignment.AmbientConductorDepthWeight
