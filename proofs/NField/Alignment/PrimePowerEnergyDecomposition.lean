/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimePowerCharacterSources
import NField.Alignment.AmbientConductorDepthWeight

/-!
# Prime-power carry energy decomposition

Parseval first removes every even channel. An explicit finite equivalence then
reindexes the remaining characters by their unique positive primitive odd
sources. The final theorem substitutes the exact ambient conductor-depth
factorization into every summand.
-/

namespace NField.Alignment.PrimePowerEnergy

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.ConductorDepthWeight
open NField.Alignment.ConductorDepthFactorization
open NField.Alignment.DepthWeightedBoundaryFactorization
open NField.Alignment.AmbientConductorDepthWeight
open NField.Alignment.PrimePowerCharacterSources

noncomputable def carryEnergy
    {m : ℕ} [NeZero m] (w : ZMod m → ℂ) : ℝ :=
  ∑ u : UnitClass m, ‖unitCarrySignal w u‖ ^ 2

/-- Finite set of odd Dirichlet characters at a fixed level. -/
noncomputable def oddCharacters (m : ℕ) : Finset (Character m) := by
  classical
  exact (Finset.univ : Finset (Character m)).filter
    DirichletCharacter.Odd

theorem carryEnergy_parseval
    {m : ℕ} [NeZero m] (hm : 1 ≤ m) (w : ZMod m → ℂ) :
    carryEnergy w =
      (1 / (m.totient : ℝ)) *
        ∑ χ : Character m, ‖carryTransform w χ‖ ^ 2 := by
  have hphiN : 0 < m.totient := Nat.totient_pos.mpr (by omega)
  have hphi : (m.totient : ℝ) ≠ 0 := by exact_mod_cast hphiN.ne'
  rw [carryTransform_parseval]
  unfold carryEnergy
  field_simp

theorem carryTransform_sum_eq_odd_sum
    {m : ℕ} [NeZero m] (hm : 2 ≤ m) (w : ZMod m → ℂ) :
    (∑ χ : Character m, ‖carryTransform w χ‖ ^ 2) =
      ∑ χ ∈ oddCharacters m,
        ‖carryTransform w χ‖ ^ 2 := by
  classical
  symm
  unfold oddCharacters
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro χ hχuniv hχout
  have hnotodd : ¬χ.Odd := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hχout
  rcases χ.even_or_odd with heven | hodd
  · rw [carryTransform_even_zero hm w χ heven]
    simp
  · exact (hnotodd hodd).elim

theorem carryEnergy_odd_parseval
    {m : ℕ} [NeZero m] (hm : 2 ≤ m) (w : ZMod m → ℂ) :
    carryEnergy w =
      (1 / (m.totient : ℝ)) *
        ∑ χ ∈ oddCharacters m,
          ‖carryTransform w χ‖ ^ 2 := by
  classical
  rw [carryEnergy_parseval (by omega), carryTransform_sum_eq_odd_sum hm]

theorem inverse_isPrimitive
    {m : ℕ} {ψ : Character m} (hψ : ψ.IsPrimitive) :
    ψ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive at hψ ⊢
  rw [DirichletCharacter.conductor_inv, hψ]

theorem inverse_odd
    {m : ℕ} {ψ : Character m} (hψ : ψ.Odd) :
    ψ⁻¹.Odd := by
  unfold DirichletCharacter.Odd at hψ ⊢
  rw [MulChar.inv_apply_eq_inv', hψ]
  simp

theorem primePower_conductor_channel
    {p t s : ℕ} [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t)
    (w : ZMod (p ^ t * p ^ s) → ℂ)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    carryTransform w
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ) =
      -(bernoulliOne ψ⁻¹ *
        depthDifferencePairing w (conductorDepthWeight p t s ψ⁻¹)) := by
  have hpinv : ψ⁻¹.IsPrimitive := inverse_isPrimitive hψ
  have hmod : 2 ≤ p ^ t := hp.two_le.trans (Nat.le_pow ht)
  have hne : ψ⁻¹ ≠ 1 := by
    intro heq
    have hc := hpinv
    rw [heq] at hc
    unfold DirichletCharacter.IsPrimitive at hc
    rw [DirichletCharacter.conductor_one] at hc
    omega
  have hbern :
      twistedTransform (m := p ^ t) centeredSawtooth ψ⁻¹ 1 =
        bernoulliOne ψ⁻¹ :=
    centeredSawtooth_transform_eq_bernoulliOne
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hmod)) hne
  have hfactor :=
    conductorDepth_carry_factorization hp ht w hpinv
  rw [hbern] at hfactor
  rw [← characterCarryTransform_eq_carryTransform_inverse w
    (DirichletCharacter.changeLevel
      (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ)]
  rw [show
    (DirichletCharacter.changeLevel
      (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ)⁻¹ =
      DirichletCharacter.changeLevel
        (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ⁻¹ by
          exact (map_inv
            (DirichletCharacter.changeLevel
              (Nat.dvd_mul_right (p ^ t) (p ^ s))) ψ).symm]
  exact hfactor

noncomputable def sourceBernoulliInverse
    {p N : ℕ} (hp : p.Prime) (source : PrimitiveOddSource p N) : ℂ := by
  letI : NeZero (p ^ source.exponent.val) :=
    ⟨pow_ne_zero _ hp.ne_zero⟩
  exact bernoulliOne source.character⁻¹

theorem oddCharacter_sum_eq_source_sum
    {p N : ℕ} [NeZero (p ^ N)] (hp : p.Prime) (hN : 1 ≤ N)
    (f : Character (p ^ N) → ℝ) :
    (∑ χ ∈ oddCharacters (p ^ N), f χ) =
      ∑ source : PrimitiveOddSource p N,
        f source.lift.val := by
  classical
  calc
    (∑ χ ∈ oddCharacters (p ^ N), f χ) =
        ∑ χ : {χ : Character (p ^ N) // χ.Odd}, f χ.val := by
          apply Finset.sum_subtype
          intro χ
          simp [oddCharacters]
    _ = ∑ source : PrimitiveOddSource p N,
        f ((primitiveOddSourceEquiv hp hN) source).val := by
          symm
          exact Equiv.sum_comp (primitiveOddSourceEquiv hp hN)
            (fun χ => f χ.val)
    _ = ∑ source : PrimitiveOddSource p N, f source.lift.val := by
          rfl

/-- Title: `Conductor channels at a prime power`. -/
theorem ambient_primePower_conductor_channel
    {p N t : ℕ} [NeZero (p ^ N)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t) (htN : t ≤ N)
    (w : ZMod (p ^ N) → ℂ)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    carryTransform w
        (DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ) =
      -(bernoulliOne ψ⁻¹ *
        depthDifferencePairing w
          (ambientConductorDepthWeight p N t ψ⁻¹)) := by
  have hpinv : ψ⁻¹.IsPrimitive := inverse_isPrimitive hψ
  have hmod : 2 ≤ p ^ t := hp.two_le.trans (Nat.le_pow ht)
  have hne : ψ⁻¹ ≠ 1 := by
    intro heq
    have hc := hpinv
    rw [heq] at hc
    unfold DirichletCharacter.IsPrimitive at hc
    rw [DirichletCharacter.conductor_one] at hc
    omega
  have hbern :
      twistedTransform (m := p ^ t) centeredSawtooth ψ⁻¹ 1 =
        bernoulliOne ψ⁻¹ :=
    centeredSawtooth_transform_eq_bernoulliOne
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hmod)) hne
  have hresponse :=
    ambientConductorDepthWeight_exact_response hp ht htN hpinv
  have hfactor :=
    carryTransform_of_exact_response w
      (DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ⁻¹)
      (twistedTransform (m := p ^ t) centeredSawtooth ψ⁻¹ 1)
      (ambientConductorDepthWeight p N t ψ⁻¹) hresponse
  rw [hbern] at hfactor
  rw [← characterCarryTransform_eq_carryTransform_inverse w
    (DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ)]
  rw [show
    (DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ)⁻¹ =
      DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ⁻¹ by
        exact (map_inv
          (DirichletCharacter.changeLevel (pow_dvd_pow p htN)) ψ).symm]
  exact hfactor

/-- Title: `Energy decomposition by primitive conductor`. -/
theorem primePower_energy_decomposition
    {p N : ℕ} [NeZero (p ^ N)]
    (hp : p.Prime) (hN : 1 ≤ N)
    (w : ZMod (p ^ N) → ℂ) :
    carryEnergy w =
      (1 / ((p ^ N).totient : ℝ)) *
        ∑ source : PrimitiveOddSource p N,
          ‖sourceBernoulliInverse hp source *
            depthDifferencePairing w
              (ambientConductorDepthWeight p N source.exponent.val
                source.character⁻¹)‖ ^ 2 := by
  rw [carryEnergy_odd_parseval
    (hp.two_le.trans (Nat.le_pow hN)) w]
  rw [oddCharacter_sum_eq_source_sum hp hN]
  congr 1
  apply Finset.sum_congr rfl
  intro source _
  letI : NeZero (p ^ source.exponent.val) :=
    ⟨pow_ne_zero _ hp.ne_zero⟩
  change ‖carryTransform w source.lift.val‖ ^ 2 =
    ‖bernoulliOne source.character⁻¹ *
      depthDifferencePairing w
        (ambientConductorDepthWeight p N source.exponent.val
          source.character⁻¹)‖ ^ 2
  rw [show source.lift.val =
      DirichletCharacter.changeLevel
        (pow_dvd_pow p (by omega : source.exponent.val ≤ N))
        source.character by rfl]
  rw [ambient_primePower_conductor_channel hp source.positive
    (by omega : source.exponent.val ≤ N) w source.primitive]
  rw [norm_neg]

end NField.Alignment.PrimePowerEnergy
