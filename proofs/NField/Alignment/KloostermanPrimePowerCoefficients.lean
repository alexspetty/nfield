/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanFormalLogDerivative

/-!
# Irreducible prime-power coefficients of the actual quadratic L-series

The coefficient of the formal logarithmic derivative is the sum of
`degree(g) * eta(g)^(n/degree(g))` over actual monic irreducibles whose
degrees divide n. It equals the negative n-th power sum of the actual
quadratic factors. Identification with extension-field trace sums still
requires the irreducible/root correspondence and trace formula.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanPrimePowerCoefficients
open scoped BigOperators Classical
open PowerSeries Polynomial KloostermanPolynomialCharacter
  KloostermanMonicCoefficients KloostermanQuadraticLSeries
  KloostermanSiftedSeries KloostermanFiniteEulerProduct KloostermanFormalLogDerivative

noncomputable def primePowerCoefficient (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) : ℂ :=
  ∑ g ∈ boundedIrreducibles p n,
    if g.natDegree ∣ n then (g.natDegree:ℂ)*polynomialCharacter p a b m g^(n/g.natDegree)
      else 0

theorem constantCoeff_formalLSeries (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) : PowerSeries.constantCoeff (formalLSeries p a b m) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,formalLSeries,
    PowerSeries.coeff_mk,degreeCoefficient_zero]

theorem constantCoeff_eulerFactor (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (g : (ZMod p)[X]) (hi : Irreducible g) :
    PowerSeries.constantCoeff (eulerFactor p a b m g) = 1 := by
  simp [eulerFactor,ne_of_gt hi.natDegree_pos]

theorem constantCoeff_finiteEulerDenominator (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (N : ℕ) :
    PowerSeries.constantCoeff (finiteEulerDenominator p a b m N) = 1 := by
  rw [finiteEulerDenominator,map_prod]
  apply Finset.prod_eq_one
  intro g hg
  exact constantCoeff_eulerFactor p a b m g (boundedIrreducibles_properties p N g hg).2

theorem coeff_logarithmicDerivative_finiteEulerDenominator (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) (hn : 0<n) :
    PowerSeries.coeff n (logarithmicDerivative (finiteEulerDenominator p a b m n)) =
      -primePowerCoefficient p a b m n := by
  rw [finiteEulerDenominator,logarithmicDerivative_prod _ _
    (fun g hg => by rw [constantCoeff_eulerFactor p a b m g
      (boundedIrreducibles_properties p n g hg).2]; exact one_ne_zero),map_sum,
    primePowerCoefficient,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  rw [eulerFactor,coeff_logarithmicDerivative_eulerFactor _ _
    (boundedIrreducibles_properties p n g hg).2.natDegree_pos n hn]
  split_ifs <;> simp

/-- Exact prime-power coefficient identity for the actual L-series. -/
theorem coeff_logarithmicDerivative_LSeries (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) (hn : 0<n) :
    PowerSeries.coeff n (logarithmicDerivative (formalLSeries p a b m)) =
      primePowerCoefficient p a b m n := by
  have h := coeff_logarithmicDerivative_eq_zero
    (finiteEulerDenominator p a b m n * formalLSeries p a b m) n n
    (fun k hk => coeff_finiteEulerDenominator_mul_LSeries p a b m n k hk) le_rfl
  rw [logarithmicDerivative_mul _ _
    (by rw [constantCoeff_finiteEulerDenominator]; exact one_ne_zero)
    (by rw [constantCoeff_formalLSeries]; exact one_ne_zero),map_add,
    coeff_logarithmicDerivative_finiteEulerDenominator p a b m n hn] at h
  exact (neg_add_eq_zero.mp h).symm

/-- The weighted irreducible sum equals the negative root-power sum.
The factorization hypothesis can be discharged by `formalLSeries_factors`. -/
theorem primePowerCoefficient_eq_root_powers (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (α β : ℂ)
    (hf : formalLSeries p a b m =
      (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X))
    (n : ℕ) (hn : 0<n) :
    primePowerCoefficient p a b m n = -(α^n+β^n) := by
  rw [← coeff_logarithmicDerivative_LSeries p a b m n hn,hf,
    logarithmicDerivative_mul _ _ (by simp) (by simp),map_add]
  have ha := coeff_logarithmicDerivative_eulerFactor α 1 (by omega) n hn
  have hb := coeff_logarithmicDerivative_eulerFactor β 1 (by omega) n hn
  simp only [pow_one,one_dvd,if_true,Nat.cast_one,neg_mul,one_mul,Nat.div_one] at ha hb
  rw [ha,hb]
  ring

/-- Actual factors with the complete irreducible prime-power identity at
every positive degree. No extension-field character-sum identity is assumed. -/
theorem exists_factors_primePowerCoefficients (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a≠0) (hb : b≠0) (hm : m≠0) :
    ∃ α β : ℂ, α+β = -KloostermanTraceSum.traceKloostermanSum p a b m ∧
      α*β=p ∧
      formalLSeries p a b m =
        (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X) ∧
      ∀ n : ℕ, 0<n → primePowerCoefficient p a b m n = -(α^n+β^n) := by
  obtain ⟨α,β,hs,hp,hf⟩ := formalLSeries_factors p a b m ha hb hm
  exact ⟨α,β,hs,hp,hf,fun n hn => primePowerCoefficient_eq_root_powers p a b m α β hf n hn⟩

end NField.Alignment.KloostermanPrimePowerCoefficients
