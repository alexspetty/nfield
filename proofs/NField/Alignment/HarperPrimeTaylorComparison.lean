/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTaylorComparison
import NField.Alignment.CollisionMertensInput

/-!
# Taylor comparison for the actual prime-and-prime-square arguments

The prime set is the literal cutoff set, and it may grow with the modulus.
The two coefficient families and the factors sqrt(p), p are retained in
both models. This is exact polynomial comparison, not the smooth-function
comparison whose averaged remainder errors still have to be bounded.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators
open Filter MeasureTheory MvPolynomial

namespace NField.Alignment.HarperPrimeTaylorComparison

open CollisionMertensInput HarperTaylorExpansion HarperTaylorComparison
open HarperTaylorBudget HarperRoundedCutoff MagnitudeShortComparison
open SteinhausMoment CollisionCharacterStructure

abbrev Atom (P : ℝ) := {p : ℕ // p ∈ primesUpTo P} × Bool

def atomIndex (P : ℝ) (a : Atom P) : ℕ := if a.2 then a.1.val^2 else a.1.val

def atomCoefficient (P : ℝ) (c1 c2 : ℕ → ℂ) (a : Atom P) : ℂ :=
  if a.2 then c2 a.1.val / (a.1.val : ℂ)
  else c1 a.1.val / (Real.sqrt (a.1.val : ℝ) : ℂ)

def primeArgument (P : ℝ) (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) : ℝ :=
  (∑ p ∈ primesUpTo P,
    (c1 p*z p/(Real.sqrt (p : ℝ) : ℂ) + c2 p*z (p^2)/(p : ℂ))).re

theorem primeArgument_eq (P : ℝ) (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) :
    realArgument (atomCoefficient P c1 c2) (fun a => z (atomIndex P a)) =
      primeArgument P c1 c2 z := by
  classical
  unfold realArgument primeArgument
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, atomCoefficient, atomIndex, Bool.false_eq_true,
    ↓reduceIte]
  rw [← Finset.sum_coe_sort (primesUpTo P)
    (fun p : ℕ => c1 p*z p/(Real.sqrt (p : ℝ) : ℂ) + c2 p*z (p^2)/(p : ℂ))]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem atomIndex_bounds (P : ℝ) (a : Atom P) :
    0 < atomIndex P a ∧ (atomIndex P a : ℝ) ≤ P^2 := by
  have hp := (primesUpTo_mem.mp a.1.property).1
  have hpP := (primesUpTo_mem.mp a.1.property).2
  have hpR : (2 : ℝ) ≤ a.1.val := by exact_mod_cast hp.two_le
  unfold atomIndex
  split_ifs
  · constructor
    · exact pow_pos hp.pos 2
    · push_cast
      exact pow_le_pow_left₀ (by positivity) hpP 2
  · exact ⟨hp.pos, by nlinarith⟩

def primeProduct (delta : ℝ) (J N A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2*J+2)) (c1 c2 : Fin A → ℕ → ℂ) :
    MvPolynomial (Bool × Atom P) ℂ :=
  product delta J N A labels (fun j => atomCoefficient P (c1 j) (c2 j))

def taylorValue (delta : ℝ) (J N A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2*J+2)) (c1 c2 : Fin A → ℕ → ℂ) (z : ℕ → ℂ) : ℝ :=
  ∏ j, Polynomial.eval (primeArgument P (c1 j) (c2 j) z)
    (HarperPartitionTaylor.polynomial delta J (labels j) N)

theorem primeProduct_eval (delta : ℝ) (J N A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2*J+2)) (c1 c2 : Fin A → ℕ → ℂ) (z : ℕ → ℂ) :
    eval (values (fun a => z (atomIndex P a))) (primeProduct delta J N A P labels c1 c2) =
      (taylorValue delta J N A P labels c1 c2 z : ℂ) := by
  simp only [primeProduct, product_eval, primeArgument_eq, taylorValue]

theorem primeProduct_degree (delta : ℝ) (J N A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2*J+2)) (c1 c2 : Fin A → ℕ → ℂ) :
    (primeProduct delta J N A P labels c1 c2).totalDegree ≤ A*(N-1) :=
  product_degree delta J N A labels _

theorem weighted_taylor_integrable (delta : ℝ) (J N A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2*J+2)) (c1 c2 : Fin A → ℕ → ℂ)
    (s : Finset ℕ) (w : ℕ → ℂ) :
    Integrable (fun omega => taylorValue delta J N A P labels c1 c2
      (fun n => steinhaus n omega) * ‖∑ n ∈ s, w n*steinhaus n omega‖^2) phaseMeasure := by
  have h := (weighted_integrable (primeProduct delta J N A P labels c1 c2)
    (atomIndex P) s w).re
  apply h.congr
  filter_upwards with omega
  rw [primeProduct_eval delta J N A P labels c1 c2 (fun n => steinhaus n omega),
    shortSquare_eq_norm_sq]
  change ((taylorValue delta J N A P labels c1 c2 (fun n => steinhaus n omega) : ℂ) *
    ((‖∑ n ∈ s, w n*steinhaus n omega‖^2 : ℝ) : ℂ)).re = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

theorem primeProduct_occurrences (delta : ℝ) (J N A : ℕ) (P : ℝ)
    (labels : Fin A → Fin (2*J+2)) (c1 c2 : Fin A → ℕ → ℂ)
    {d : (Bool × Atom P) →₀ ℕ} (hd : d ∈ (primeProduct delta J N A P labels c1 c2).support)
    (b : Bool) : sideCount d b ≤ A*(N-1) :=
  (sideCount_le hd b).trans (primeProduct_degree delta J N A P labels c1 c2)

theorem eventual_prime_product_size : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ)-1
    let P := primeCutoff x
    ∀ (delta : ℝ) (J : ℕ) (labels : Fin (factorCount x) → Fin (2*J+2))
      (c1 c2 : Fin (factorCount x) → ℕ → ℂ) (d : (Bool × Atom P) →₀ ℕ),
      d ∈ (primeProduct delta J (2*taylorOrder x) (factorCount x) P labels c1 c2).support →
    ∀ (b : Bool) (n : ℕ), (n : ℝ) ≤ x →
      (n*sideIndex (atomIndex P) d b : ℕ) ≤
        x*P^((2*factorCount x*(2*taylorOrder x-1) : ℕ) : ℝ) ∧
      x*P^((2*factorCount x*(2*taylorOrder x-1) : ℕ) : ℝ) <
        x*P^(4*(taylorOrder x : ℝ)*(factorCount x : ℝ)) := by
  filter_upwards [eventual_product_size,
    base_minus_one_tendsto.eventually eventual_taylor_size] with p hs ht
  dsimp only
  intro delta J labels c1 c2 d hd b n hn
  exact ⟨hs (Atom (primeCutoff ((p : ℝ)-1))) delta J labels _ d hd b n
    (atomIndex _) hn (fun a => (atomIndex_bounds _ a).2), ht.1⟩

theorem eventual_prime_product_support : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ)-1
    let P := primeCutoff x
    p.Prime → ∀ (delta : ℝ) (J : ℕ) (labels : Fin (factorCount x) → Fin (2*J+2))
      (c1 c2 : Fin (factorCount x) → ℕ → ℂ) (d : (Bool × Atom P) →₀ ℕ),
      d ∈ (primeProduct delta J (2*taylorOrder x) (factorCount x) P labels c1 c2).support →
    ∀ (b : Bool) (n : ℕ), 0 < n → (n : ℝ) ≤ x →
      0 < n*sideIndex (atomIndex P) d b ∧ n*sideIndex (atomIndex P) d b < p^2 ∧
        (n*sideIndex (atomIndex P) d b).Coprime (p^2) := by
  filter_upwards [eventual_product_support] with p hs
  dsimp only
  intro hp delta J labels c1 c2 d hd b n hn hnx
  exact hs (Atom (primeCutoff ((p : ℝ)-1))) hp delta J labels _ d hd b n
    (atomIndex _) hn hnx (atomIndex_bounds _)

/-- Exact comparison of the actual Taylor products and short-sum square.
The cutoff set, prime squares, coefficients and real-part operation agree
literally in both models. No coefficient-size or comparison hypothesis is assumed. -/
theorem eventual_prime_taylor_comparison : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ)-1
    let P := primeCutoff x
    ∀ [NeZero (p^2)], p.Prime →
    ∀ (delta : ℝ) (J : ℕ) (labels : Fin (factorCount x) → Fin (2*J+2))
      (c1 c2 : Fin (factorCount x) → ℕ → ℂ) (s : Finset ℕ) (w : ℕ → ℂ),
      (∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ x) →
    SpectralRepulsion.uniformAverage (fun chi : Character (p^2) =>
      taylorValue delta J (2*taylorOrder x) (factorCount x) P labels c1 c2
        (fun n => chi (n : ZMod (p^2))) * ‖∑ n ∈ s, w n*chi (n : ZMod (p^2))‖^2) =
      ∫ omega, taylorValue delta J (2*taylorOrder x) (factorCount x) P labels c1 c2
        (fun n => steinhaus n omega) * ‖∑ n ∈ s, w n*steinhaus n omega‖^2 ∂phaseMeasure := by
  filter_upwards [eventual_taylor_product_comparison] with p h
  dsimp only
  intro _ hp delta J labels c1 c2 s w hs
  let P := primeCutoff ((p : ℝ)-1)
  let A := factorCount ((p : ℝ)-1)
  let N := 2*taylorOrder ((p : ℝ)-1)
  have hh := h (Atom P) hp delta J labels
    (fun j => atomCoefficient P (c1 j) (c2 j)) (atomIndex P) s w (atomIndex_bounds P) hs
  change fullCharacterAverage (fun chi : Character (p^2) =>
    eval (values (fun a => chi (atomIndex P a : ZMod (p^2))))
      (primeProduct delta J N A P labels c1 c2) * shortSquare (characterNat chi) s w) =
    ∫ omega, eval (values (fun a => steinhaus (atomIndex P a) omega))
      (primeProduct delta J N A P labels c1 c2) *
      shortSquare (steinhausHom omega).toMonoidHom s w ∂phaseMeasure at hh
  have hchar (chi : Character (p^2)) :
      eval (values (fun a => chi (atomIndex P a : ZMod (p^2))))
        (primeProduct delta J N A P labels c1 c2) =
        (taylorValue delta J N A P labels c1 c2 (fun n => chi (n : ZMod (p^2))) : ℂ) :=
    primeProduct_eval delta J N A P labels c1 c2 (fun n => chi (n : ZMod (p^2)))
  have hrandom (omega : PhaseSpace) :
      eval (values (fun a => steinhaus (atomIndex P a) omega))
        (primeProduct delta J N A P labels c1 c2) =
        (taylorValue delta J N A P labels c1 c2 (fun n => steinhaus n omega) : ℂ) :=
    primeProduct_eval delta J N A P labels c1 c2 (fun n => steinhaus n omega)
  simp_rw [hchar, hrandom, shortSquare_eq_norm_sq] at hh
  simp only [← Complex.ofReal_mul] at hh
  rw [full_character_average_real, integral_complex_ofReal] at hh
  exact Complex.ofReal_injective hh

theorem eventual_short_prime_taylor_comparison : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ)-1
    let P := primeCutoff x
    ∀ [NeZero (p^2)], p.Prime →
    ∀ (delta : ℝ) (J : ℕ) (labels : Fin (factorCount x) → Fin (2*J+2))
      (c1 c2 : Fin (factorCount x) → ℕ → ℂ) (w : ℕ → ℂ),
    SpectralRepulsion.uniformAverage (fun chi : Character (p^2) =>
      taylorValue delta J (2*taylorOrder x) (factorCount x) P labels c1 c2
        (fun n => chi (n : ZMod (p^2))) *
          ‖∑ n ∈ Finset.Icc 1 (p-1), w n*chi (n : ZMod (p^2))‖^2) =
      ∫ omega, taylorValue delta J (2*taylorOrder x) (factorCount x) P labels c1 c2
        (fun n => steinhaus n omega) *
          ‖∑ n ∈ Finset.Icc 1 (p-1), w n*steinhaus n omega‖^2 ∂phaseMeasure := by
  filter_upwards [eventual_prime_taylor_comparison] with p h
  dsimp only at h ⊢
  intro _ hp delta J labels c1 c2 w
  apply h hp delta J labels c1 c2 (Finset.Icc 1 (p-1)) w
  intro n hn
  have hns := Finset.mem_Icc.mp hn
  refine ⟨hns.1, ?_⟩
  have hR := (Nat.cast_le (α := ℝ)).mpr hns.2
  rw [Nat.cast_sub hp.one_le, Nat.cast_one] at hR
  exact hR

end NField.Alignment.HarperPrimeTaylorComparison
