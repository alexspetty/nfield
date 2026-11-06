/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ProgressionMertensReal
import NField.External.ProgressionPNT.PNTAP

/-!
# Prime limits of finite periodic signals

The weights are literal values on the unit residue classes. The finite
decomposition below retains the primes dividing the modulus as an explicit
zero extension, so the normalization and the exceptional finite set are
never hidden in an asymptotic hypothesis.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.PrimePeriodicLimits

open Filter Finset
open scoped BigOperators Topology
open NField.Alignment.ProgressionMertens
open NField.External.ProgressionPNT

variable {q : ℕ} [NeZero q]

def unitExtension (f : (ZMod q)ˣ → ℂ) (n : ℕ) : ℂ :=
  if h : IsUnit (n : ZMod q) then f h.unit else 0

def weightedPrimeReciprocalSum (f : (ZMod q)ˣ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if n.Prime then unitExtension f n / (n : ℂ) else 0

def weightedPrimeCountSum (f : (ZMod q)ˣ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if n.Prime then unitExtension f n else 0

theorem unitExtension_eq_sum (f : (ZMod q)ˣ → ℂ) (n : ℕ) :
    unitExtension f n =
      ∑ a : (ZMod q)ˣ, if (n : ZMod q) = a then f a else 0 := by
  classical
  by_cases hn : IsUnit (n : ZMod q)
  · rw [unitExtension, dif_pos hn]
    symm
    rw [Finset.sum_eq_single hn.unit]
    · simp
    · intro a _ hne
      have hna : (n : ZMod q) ≠ a := by
        intro h
        apply hne
        apply Units.ext
        simpa using h.symm
      simp [hna]
    · simp
  · simp only [unitExtension, dif_neg hn]
    symm
    apply Finset.sum_eq_zero
    intro a _
    have hna : (n : ZMod q) ≠ a := fun h => hn (h.symm ▸ a.isUnit)
    simp [hna]

theorem weightedPrimeReciprocalSum_eq_classes (f : (ZMod q)ˣ → ℂ) (x : ℝ) :
    weightedPrimeReciprocalSum f x =
      ∑ a : (ZMod q)ˣ, f a * progressionPrimeSum (a : ZMod q) ⌊x⌋₊ := by
  classical
  unfold weightedPrimeReciprocalSum progressionPrimeSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [unitExtension_eq_sum]
  by_cases hn : n.Prime
  · simp only [hn, ↓reduceIte, true_and, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  · simp [hn]

theorem complex_mertens_progression {a : ZMod q} (ha : IsUnit a) :
    ∃ L : ℂ, Tendsto (fun x : ℝ => progressionPrimeSum a ⌊x⌋₊ -
      (q.totient : ℂ)⁻¹ * (Real.log (Real.log x) : ℂ)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := real_cutoff_mertens_progression ha
  refine ⟨(L : ℂ), ?_⟩
  have h := (Complex.continuous_ofReal.tendsto L).comp hL
  convert h using 1
  ext x
  simp only [Function.comp_apply, progressionPrimeSum_eq_ofReal,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

/-- Every finite periodic unit signal has its exact logarithmic mean and
an ordinary residual constant. -/
theorem periodic_prime_reciprocal_residual_limit (f : (ZMod q)ˣ → ℂ) :
    ∃ L : ℂ, Tendsto (fun x : ℝ => weightedPrimeReciprocalSum f x -
      ((q.totient : ℂ)⁻¹ * ∑ a : (ZMod q)ˣ, f a) * (Real.log (Real.log x) : ℂ))
      atTop (𝓝 L) := by
  classical
  choose K hK using fun a : (ZMod q)ˣ => complex_mertens_progression a.isUnit
  have h : Tendsto (fun x : ℝ =>
      ∑ a : (ZMod q)ˣ, f a * (progressionPrimeSum (a : ZMod q) ⌊x⌋₊ -
        (q.totient : ℂ)⁻¹ * (Real.log (Real.log x) : ℂ))) atTop
      (𝓝 (∑ a : (ZMod q)ˣ, f a * K a)) := by
    apply tendsto_finsetSum
    intro a _
    exact (hK a).const_mul (f a)
  refine ⟨∑ a : (ZMod q)ˣ, f a * K a, ?_⟩
  convert h using 1
  ext x
  rw [weightedPrimeReciprocalSum_eq_classes]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul]
  ring

/-- Title: `Centered periodic prime reciprocal convergence`.
The principal logarithm cancels by the actual finite zero total. -/
theorem centered_periodic_prime_reciprocal_limit (f : (ZMod q)ˣ → ℂ)
    (hzero : ∑ a : (ZMod q)ˣ, f a = 0) :
    ∃ L : ℂ, Tendsto (weightedPrimeReciprocalSum f) atTop (𝓝 L) := by
  simpa only [hzero, mul_zero, zero_mul, sub_zero] using
    periodic_prime_reciprocal_residual_limit f

theorem unit_class_prime_density (a : (ZMod q)ˣ) :
    Tendsto (fun x : ℝ => primeAPCountingReal q (a : ZMod q).val x /
      (x / Real.log x)) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply primeAPCountingReal_normalized_tendsto (NeZero.pos q)
  · apply (ZMod.isUnit_iff_coprime _ _).mp
    simpa only [ZMod.natCast_zmod_val] using a.isUnit
  · exact ZMod.val_lt _

end NField.Alignment.PrimePeriodicLimits
