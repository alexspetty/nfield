/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanMinpolyFibers

/-!
# Extension-field Kloosterman sums equal the quadratic root-power sums

Group actual field elements by their actual minimal polynomials. The
proved fiber cardinalities and local trace formula identify the weighted
irreducible coefficients with the extension-field character sum. The same
two reciprocal roots therefore work over every finite extension.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanExtensionTrace
open scoped BigOperators Classical
open Polynomial KloostermanMinpolyFibers KloostermanPolynomialCharacter
  KloostermanFiniteEulerProduct KloostermanPrimePowerCoefficients
  KloostermanQuadraticLSeries KloostermanTraceSum

/-- The exact finite-field trace interpretation of the irreducible
prime-power coefficient, with the zero element and factor X retained. -/
theorem traceKloostermanSum_eq_primePowerCoefficient {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] (a b m : ZMod p) :
    traceKloostermanSum p (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) m =
      primePowerCoefficient p a b m (Module.finrank (ZMod p) K) := by
  let n := Module.finrank (ZMod p) K
  have hmaps : ∀ t ∈ (Finset.univ : Finset K),
      minpoly (ZMod p) t ∈ boundedIrreducibles p n :=
    fun t _ => minpoly_mem_boundedIrreducibles p t
  rw [traceKloostermanSum]
  trans ∑ t : K, polynomialCharacter p a b m (minpoly (ZMod p) t) ^
    (Module.finrank (ZMod p) K / (minpoly (ZMod p) t).natDegree)
  · apply Finset.sum_congr rfl
    intro t _
    exact element_character_eq_minpoly_weight p a b m t
  · rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    unfold primePowerCoefficient
    apply Finset.sum_congr rfl
    intro g hg
    have hgi := boundedIrreducibles_properties p n g hg
    have hfiber := card_minpoly_fiber (K := K) g hgi.1 hgi.2
    rw [Fintype.card_subtype] at hfiber
    calc
      (∑ t ∈ Finset.univ.filter (fun t : K => minpoly (ZMod p) t=g),
        polynomialCharacter p a b m (minpoly (ZMod p) t) ^
          (Module.finrank (ZMod p) K / (minpoly (ZMod p) t).natDegree)) =
        ∑ _t ∈ Finset.univ.filter (fun t : K => minpoly (ZMod p) t=g),
          polynomialCharacter p a b m g ^ (n/g.natDegree) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [(Finset.mem_filter.mp ht).2]
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,hfiber]
        split_ifs <;> simp [n]

/-- Any factorization of the actual quadratic L-series supplies the
root-power formula over every finite extension. -/
theorem traceKloostermanSum_eq_root_powers {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] (a b m : ZMod p) (α β : ℂ)
    (hf : formalLSeries p a b m =
      (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X)) :
    traceKloostermanSum p (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) m =
      -(α^(Module.finrank (ZMod p) K)+β^(Module.finrank (ZMod p) K)) := by
  rw [traceKloostermanSum_eq_primePowerCoefficient]
  exact primePowerCoefficient_eq_root_powers p a b m α β hf _ Module.finrank_pos

/-- Roots are chosen once over the prime field and satisfy the trace
identity in every finite extension, not chosen separately for each field. -/
theorem exists_factors_all_extensions (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a≠0) (hb : b≠0) (hm : m≠0) :
    ∃ α β : ℂ, α+β = -traceKloostermanSum p a b m ∧ α*β=p ∧
      formalLSeries p a b m =
        (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X) ∧
      ∀ (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod p) K],
        traceKloostermanSum p (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) m =
          -(α^(Module.finrank (ZMod p) K)+β^(Module.finrank (ZMod p) K)) := by
  obtain ⟨α,β,hs,hp,hf⟩ := formalLSeries_factors p a b m ha hb hm
  refine ⟨α,β,hs,hp,hf,?_⟩
  intro K _ _ _ _
  exact traceKloostermanSum_eq_root_powers p a b m α β hf

end NField.Alignment.KloostermanExtensionTrace
