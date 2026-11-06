/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CharacterPrimeReciprocal
import NField.Alignment.CollisionMertensInput

/-!+# Mertens constants in every fixed reduced residue class

Nonprincipal character sums converge by the proved Dirichlet argument.
The principal character differs from the ordinary prime reciprocal sum
by finitely many primes dividing the modulus. Character orthogonality
then gives an ordinary, unsmoothed residue-class limit.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.ProgressionMertens

open Filter Finset Asymptotics
open scoped BigOperators Topology
open NField.Alignment.CharacterPrimeReciprocal

variable {q : ℕ} [NeZero q]

def characterPrimeSum (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, primeReciprocal χ n

def allPrimeSum (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, if n.Prime then (1 : ℂ) / n else 0

def badPrimeReciprocal (q n : ℕ) : ℂ :=
  if n.Prime ∧ n ∣ q then (1 : ℂ) / n else 0

def badPrimeCorrection (q : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 q, badPrimeReciprocal q n

def progressionPrimeSum (a : ZMod q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, if n.Prime ∧ (n : ZMod q) = a then (1 : ℂ) / n else 0

theorem sum_Ioc_eq_range_succ {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, f n) = ∑ n ∈ Finset.range (N + 1), f n := by
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_range] at hn ⊢
    omega
  · intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_Ioc, Finset.mem_range] at hn hnot
      omega
    simpa [hn0] using hf

theorem nonprincipal_characterPrimeSum_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ L : ℂ, Tendsto (characterPrimeSum χ) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := primeReciprocal_tendsto χ hχ
  refine ⟨L, ?_⟩
  have heq (N : ℕ) : characterPrimeSum χ N =
      ∑ n ∈ Finset.range (N + 1), primeReciprocal χ n :=
    sum_Ioc_eq_range_succ (by simp [primeReciprocal]) N
  change Tendsto (fun N => characterPrimeSum χ N) atTop (𝓝 L)
  simpa only [Function.comp_def, ← heq] using hL.comp (tendsto_add_atTop_nat 1)

theorem allPrimeSum_residual_tendsto :
    Tendsto (fun N : ℕ => allPrimeSum N - (Real.log (Real.log (N : ℝ)) : ℂ))
      atTop (𝓝 (Mertens.M : ℂ)) := by
  have hE : Tendsto Mertens.E₂p atTop (𝓝 (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have hR : Tendsto (fun x : ℝ =>
      (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) -
        Real.log (Real.log x)) atTop (𝓝 Mertens.M) := by
    convert hE.add_const Mertens.M using 1
    · ext x
      simp only [Mertens.E₂p]
      ring
    · simp
  have hN := hR.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hC := (Complex.continuous_ofReal.tendsto Mertens.M).comp hN
  convert hC using 1
  ext N
  simp only [Function.comp_apply, allPrimeSum, Nat.floor_natCast, Finset.sum_filter,
    Complex.ofReal_sub, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem principal_primeReciprocal (n : ℕ) :
    primeReciprocal (1 : DirichletCharacter ℂ q) n =
      (if n.Prime then (1 : ℂ) / n else 0) - badPrimeReciprocal q n := by
  by_cases hp : n.Prime
  · by_cases hd : n ∣ q
    · have hnu : ¬IsUnit (n : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd]
        exact not_not_intro hd
      simp [primeReciprocal, badPrimeReciprocal, hp, hd, MulChar.map_nonunit _ hnu]
    · have hu : IsUnit (n : ZMod q) :=
        (ZMod.isUnit_iff_coprime _ _).mpr (hp.coprime_iff_not_dvd.mpr hd)
      simp [primeReciprocal, badPrimeReciprocal, hp, hd, MulChar.one_apply hu]
  · simp [primeReciprocal, badPrimeReciprocal, hp]

theorem badPrimeCorrection_stable {N : ℕ} (hN : q ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N, badPrimeReciprocal q n) = badPrimeCorrection q := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hN⟩
  · intro n hn hnot
    have hd : ¬n ∣ q := by
      intro hd
      apply hnot
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
        Nat.le_of_dvd (NeZero.pos q) hd⟩
    simp [badPrimeReciprocal, hd]

theorem principal_characterPrimeSum_eventually :
    characterPrimeSum (1 : DirichletCharacter ℂ q) =ᶠ[atTop]
      fun N => allPrimeSum N - badPrimeCorrection q := by
  filter_upwards [eventually_ge_atTop q] with N hN
  simp only [characterPrimeSum, principal_primeReciprocal, Finset.sum_sub_distrib,
    badPrimeCorrection_stable hN, allPrimeSum]

theorem principal_characterPrimeSum_residual_tendsto :
    Tendsto (fun N : ℕ => characterPrimeSum (1 : DirichletCharacter ℂ q) N -
        (Real.log (Real.log (N : ℝ)) : ℂ)) atTop
      (𝓝 ((Mertens.M : ℂ) - badPrimeCorrection q)) := by
  apply (allPrimeSum_residual_tendsto.sub_const (badPrimeCorrection q)).congr'
  filter_upwards [principal_characterPrimeSum_eventually (q := q)] with N hN
  rw [hN]
  ring

theorem characterPrimeSum_residual_tendsto (χ : DirichletCharacter ℂ q) :
    ∃ L : ℂ, Tendsto (fun N : ℕ => characterPrimeSum χ N -
      if χ = 1 then (Real.log (Real.log (N : ℝ)) : ℂ) else 0) atTop (𝓝 L) := by
  by_cases hχ : χ = 1
  · subst χ
    exact ⟨_, by simpa using principal_characterPrimeSum_residual_tendsto (q := q)⟩
  · obtain ⟨L, hL⟩ := nonprincipal_characterPrimeSum_tendsto χ hχ
    exact ⟨L, by simpa only [hχ, ↓reduceIte, sub_zero] using hL⟩

theorem progressionPrimeSum_character_expansion {a : ZMod q} (ha : IsUnit a) (N : ℕ) :
    progressionPrimeSum a N = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * characterPrimeSum χ N := by
  unfold progressionPrimeSum
  simp only [characterPrimeSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.mul_sum]
  by_cases hp : n.Prime
  · simp only [primeReciprocal, hp, ↓reduceIte]
    have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
    rw [show (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (χ (n : ZMod q) / (n : ℂ))) =
        (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (n : ZMod q)) / (n : ℂ) by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro χ _; ring]
    rw [horth]
    have htot : (q.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
    by_cases hna : (n : ZMod q) = a
    · simp only [hna, ↓reduceIte, true_and]
      simp [div_eq_mul_inv, ← mul_assoc, htot]
    · simp [hna, Ne.symm hna]
  · simp [primeReciprocal, hp]

/-- Title: `Mertens limit in a reduced residue class`.
Every fixed positive modulus and reduced residue have an ordinary
reciprocal-prime constant; no prime-distribution assumption is added. -/
theorem progressionPrimeSum_residual_tendsto {a : ZMod q} (ha : IsUnit a) :
    ∃ L : ℂ, Tendsto (fun N : ℕ => progressionPrimeSum a N -
      (q.totient : ℂ)⁻¹ * (Real.log (Real.log (N : ℝ)) : ℂ)) atTop (𝓝 L) := by
  classical
  choose L hL using characterPrimeSum_residual_tendsto (q := q)
  have hone : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := by
    obtain ⟨u, rfl⟩ := ha
    rw [ZMod.inv_coe_unit, MulChar.one_apply_coe]
  have hsum : Tendsto (fun N : ℕ =>
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (characterPrimeSum χ N -
        if χ = 1 then (Real.log (Real.log (N : ℝ)) : ℂ) else 0)) atTop
        (𝓝 (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * L χ)) := by
    apply tendsto_finsetSum
    intro χ _
    exact (hL χ).const_mul (χ a⁻¹)
  refine ⟨(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * L χ, ?_⟩
  convert hsum.const_mul (q.totient : ℂ)⁻¹ using 1
  ext N
  rw [progressionPrimeSum_character_expansion ha]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp [mul_ite, hone, mul_sub]

def realProgressionPrimeSum (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / n else 0

theorem progressionPrimeSum_eq_ofReal (a : ZMod q) (N : ℕ) :
    progressionPrimeSum a N = (realProgressionPrimeSum a N : ℂ) := by
  unfold progressionPrimeSum realProgressionPrimeSum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

/-- The real form, with exactly the usual coefficient `1/φ(q)`. -/
theorem realProgressionPrimeSum_residual_tendsto {a : ZMod q} (ha : IsUnit a) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => realProgressionPrimeSum a N -
      Real.log (Real.log (N : ℝ)) / (q.totient : ℝ)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := progressionPrimeSum_residual_tendsto ha
  refine ⟨L.re, ?_⟩
  have h := (Complex.continuous_re.tendsto L).comp hL
  convert h using 1
  ext N
  simp only [Function.comp_apply, progressionPrimeSum_eq_ofReal, Complex.sub_re,
    Complex.ofReal_re, ← Complex.ofReal_natCast q.totient, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul]
  simp [div_eq_mul_inv, mul_comm]

end NField.Alignment.ProgressionMertens
