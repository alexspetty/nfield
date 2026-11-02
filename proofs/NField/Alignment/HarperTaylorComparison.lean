/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTaylorExpansion
import NField.Alignment.HarperPrimeSquareComparison

/-!
# Complete support and exact comparison for the actual Taylor product

Occurrence lists are generated from the constructed multivariable polynomial.
The earlier size theorem is applied only after that degree/count correspondence
is proved. Coefficients are identical in the character and random models.
-/

noncomputable section
set_option autoImplicit false
universe u

open scoped BigOperators
open Filter MeasureTheory MvPolynomial

namespace NField.Alignment.HarperTaylorComparison

open HarperTaylorExpansion HarperTaylorBudget HarperRoundedCutoff
open HarperPrimeSquareComparison MagnitudeShortComparison SteinhausMoment
open CollisionCharacterStructure

variable {ι : Type u} [Fintype ι]

theorem product_index_bound (delta : ℝ) (J N A : ℕ)
    (labels : Fin A → Fin (2*J+2)) (c : Fin A → ι → ℂ)
    {d : (Bool × ι) →₀ ℕ} (hd : d ∈ (product delta J N A labels c).support)
    (b : Bool) (n : ℕ) (a : ι → ℕ) {x P : ℝ} (hn : (n : ℝ) ≤ x) (hP : 1 ≤ P)
    (ha : ∀ i, (a i : ℝ) ≤ P^2) :
    (n*sideIndex a d b : ℕ) ≤ x*P^((2*A*(N-1) : ℕ) : ℝ) := by
  have hc : (occurrences d b).card ≤ A*(N-1) := by
    rw [occurrences_card]
    exact product_occurrences delta J N A labels c hd b
  have h := completeMonomial_bound n (occurrences d b) (fun v => a v.1) hn hP
    (fun v _ => ha v.1) hc
  simpa only [completeMonomial, occurrences_product, Nat.mul_assoc] using h

theorem eventual_product_size : ∀ᶠ p : ℕ in atTop,
    ∀ (κ : Type u) [Fintype κ] (delta : ℝ) (J : ℕ)
      (labels : Fin (factorCount ((p : ℝ)-1)) → Fin (2*J+2))
      (c : Fin (factorCount ((p : ℝ)-1)) → κ → ℂ)
      (d : (Bool × κ) →₀ ℕ),
      d ∈ (product delta J (2*taylorOrder ((p : ℝ)-1))
        (factorCount ((p : ℝ)-1)) labels c).support →
    ∀ (b : Bool) (n : ℕ) (a : κ → ℕ), (n : ℝ) ≤ (p : ℝ)-1 →
      (∀ i, (a i : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      (n*sideIndex a d b : ℕ) ≤
        ((p : ℝ)-1)*(primeCutoff ((p : ℝ)-1))^
          ((2*factorCount ((p : ℝ)-1)*(2*taylorOrder ((p : ℝ)-1)-1) : ℕ) : ℝ) := by
  filter_upwards [base_minus_one_tendsto.eventually eventual_taylor_data] with p hp
  intro κ _ delta J labels c d hd b n a hn ha
  exact product_index_bound delta J _ _ labels c hd b n a hn hp.2.1.le ha

theorem eventual_product_support : ∀ᶠ p : ℕ in atTop,
    ∀ (κ : Type u) [Fintype κ] (_hp : p.Prime) (delta : ℝ) (J : ℕ)
      (labels : Fin (factorCount ((p : ℝ)-1)) → Fin (2*J+2))
      (c : Fin (factorCount ((p : ℝ)-1)) → κ → ℂ)
      (d : (Bool × κ) →₀ ℕ),
      d ∈ (product delta J (2*taylorOrder ((p : ℝ)-1))
        (factorCount ((p : ℝ)-1)) labels c).support →
    ∀ (b : Bool) (n : ℕ) (a : κ → ℕ), 0 < n → (n : ℝ) ≤ (p : ℝ)-1 →
      (∀ i, 0 < a i ∧ (a i : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      0 < n*sideIndex a d b ∧ n*sideIndex a d b < p^2 ∧
        (n*sideIndex a d b).Coprime (p^2) := by
  filter_upwards [eventual_product_size,
    base_minus_one_tendsto.eventually eventual_taylor_size,
    base_minus_one_tendsto.eventually eventual_cutoff_square_lt,
    eventually_ge_atTop (2 : ℕ)] with p hs ht hsmall hp2
  intro κ _ hp delta J labels c d hd b n a hn hnx ha
  have hnp : n < p := by exact_mod_cast (by linarith : (n : ℝ) < p)
  have hap (i : κ) : a i < p := by
    exact_mod_cast (show (a i : ℝ) < p by linarith [(ha i).2])
  have hpos : 0 < n*sideIndex a d b :=
    Nat.mul_pos hn (Finset.prod_pos fun i _ => pow_pos (ha i).1 _)
  have hbound := hs κ delta J labels c d hd b n a hnx (fun i => (ha i).2)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hsize : (n*sideIndex a d b : ℕ) < (p : ℝ)^2 :=
    ((hbound.trans_lt ht.1).trans ht.2).trans (by nlinarith)
  refine ⟨hpos, by exact_mod_cast hsize, ?_⟩
  exact (small_factor_unit hp hn hnp).mul_left
    (powered_product_unit hp Finset.univ a (fun i => d (b,i)) (fun i _ => ⟨(ha i).1, hap i⟩))

def shortSquare (z : ℕ →* ℂ) (s : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  (∑ n ∈ s, c n*z n)*star (∑ n ∈ s, c n*z n)

theorem shortSquare_eq_norm_sq (z : ℕ →* ℂ) (s : Finset ℕ) (c : ℕ → ℂ) :
    shortSquare z s c = (‖∑ n ∈ s, c n*z n‖^2 : ℝ) := by
  exact self_pair_eq_norm_sq _

theorem weighted_expansion (Q : MvPolynomial (Bool × ι) ℂ)
    (a : ι → ℕ) (z : ℕ →* ℂ) (s : Finset ℕ) (c : ℕ → ℂ) :
    eval (values (fun i => z (a i))) Q * shortSquare z s c =
      ∑ d ∈ Q.support, ∑ n ∈ s, ∑ m ∈ s,
        (Q.coeff d*c n*star (c m)) *
          (z (n*sideIndex a d true)*star (z (m*sideIndex a d false))) := by
  classical
  rw [evaluation_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  simp only [shortSquare, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  simp only [map_mul, star_mul]
  ring

def characterNat {q : ℕ} (chi : Character q) : ℕ →* ℂ :=
  chi.toMonoidHom.comp (Nat.castRingHom (ZMod q)).toMonoidHom

@[simp] theorem characterNat_apply {q : ℕ} (chi : Character q) (n : ℕ) :
    characterNat chi n = chi (n : ZMod q) := rfl

theorem weighted_integrable (Q : MvPolynomial (Bool × ι) ℂ)
    (a : ι → ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (fun omega => eval (values (fun i => steinhaus (a i) omega)) Q *
      shortSquare (steinhausHom omega).toMonoidHom s c) phaseMeasure := by
  have he : (fun omega => eval (values (fun i => steinhaus (a i) omega)) Q *
      shortSquare (steinhausHom omega).toMonoidHom s c) =
      (fun omega => ∑ d ∈ Q.support, ∑ n ∈ s, ∑ m ∈ s,
        (Q.coeff d*c n*star (c m)) *
          (steinhaus (n*sideIndex a d true) omega *
            star (steinhaus (m*sideIndex a d false) omega))) := by
    funext omega
    exact weighted_expansion Q a (steinhausHom omega).toMonoidHom s c
  rw [he]
  exact integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun n _ =>
    integrable_finsetSum _ (fun m _ =>
      (steinhaus_pair_integrable (n*sideIndex a d true) (m*sideIndex a d false)).const_mul _)))

theorem weighted_comparison {q : ℕ} [NeZero q]
    (Q : MvPolynomial (Bool × ι) ℂ) (a : ι → ℕ) (s : Finset ℕ) (c : ℕ → ℂ)
    (hindices : ∀ d ∈ Q.support, ∀ n ∈ s, ∀ b : Bool,
      0 < n*sideIndex a d b ∧ n*sideIndex a d b < q ∧ (n*sideIndex a d b).Coprime q) :
    fullCharacterAverage (fun chi : Character q =>
      eval (values (fun i => chi (a i : ZMod q))) Q * shortSquare (characterNat chi) s c) =
      ∫ omega, eval (values (fun i => steinhaus (a i) omega)) Q *
        shortSquare (steinhausHom omega).toMonoidHom s c ∂phaseMeasure := by
  classical
  change fullCharacterAverage (fun chi : Character q =>
    eval (values (fun i => characterNat chi (a i))) Q * shortSquare (characterNat chi) s c) =
    ∫ omega, eval (values (fun i => (steinhausHom omega).toMonoidHom (a i))) Q *
      shortSquare (steinhausHom omega).toMonoidHom s c ∂phaseMeasure
  simp_rw [weighted_expansion]
  change fullCharacterAverage (fun chi : Character q =>
    ∑ d ∈ Q.support, ∑ n ∈ s, ∑ m ∈ s,
      (Q.coeff d*c n*star (c m)) *
        (chi ((n*sideIndex a d true : ℕ) : ZMod q)*
          star (chi ((m*sideIndex a d false : ℕ) : ZMod q)))) =
    ∫ omega, ∑ d ∈ Q.support, ∑ n ∈ s, ∑ m ∈ s,
      (Q.coeff d*c n*star (c m)) *
        (steinhaus (n*sideIndex a d true) omega *
          star (steinhaus (m*sideIndex a d false) omega)) ∂phaseMeasure
  have hI (d : (Bool × ι) →₀ ℕ) (n m : ℕ) : Integrable
      (fun omega => (Q.coeff d*c n*star (c m)) *
        (steinhaus (n*sideIndex a d true) omega * star (steinhaus (m*sideIndex a d false) omega)))
      phaseMeasure := (steinhaus_pair_integrable _ _).const_mul _
  rw [fullCharacterAverage_sum,
    integral_finsetSum Q.support (fun d _ => integrable_finsetSum s (fun n _ =>
      integrable_finsetSum s (fun m _ => hI d n m)))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [fullCharacterAverage_sum,
    integral_finsetSum s (fun n _ => integrable_finsetSum s (fun m _ => hI d n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fullCharacterAverage_sum, integral_finsetSum s (fun m _ => hI d n m)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [fullCharacterAverage_const_mul, integral_const_mul]
  apply congrArg
  have hu := hindices d hd n hn true
  have hv := hindices d hd m hm false
  exact character_random_pair_comparison hu.1 hv.1 hu.2.1 hv.2.1 hu.2.2 hv.2.2

theorem eventual_taylor_product_comparison : ∀ᶠ p : ℕ in atTop,
    ∀ (κ : Type u) [Fintype κ] [NeZero (p^2)], p.Prime →
    ∀ (delta : ℝ) (J : ℕ)
      (labels : Fin (factorCount ((p : ℝ)-1)) → Fin (2*J+2))
      (c : Fin (factorCount ((p : ℝ)-1)) → κ → ℂ)
      (a : κ → ℕ) (s : Finset ℕ) (w : ℕ → ℂ),
      (∀ i, 0 < a i ∧ (a i : ℝ) ≤ (primeCutoff ((p : ℝ)-1))^2) →
      (∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ (p : ℝ)-1) →
    let Q := product delta J (2*taylorOrder ((p : ℝ)-1)) (factorCount ((p : ℝ)-1)) labels c
    fullCharacterAverage (fun chi : Character (p^2) =>
      eval (values (fun i => chi (a i : ZMod (p^2)))) Q * shortSquare (characterNat chi) s w) =
      ∫ omega, eval (values (fun i => steinhaus (a i) omega)) Q *
        shortSquare (steinhausHom omega).toMonoidHom s w ∂phaseMeasure := by
  filter_upwards [eventual_product_support] with p hs
  intro κ _ _ hp delta J labels c a s w ha hn
  apply weighted_comparison
  intro d hd n hns b
  exact hs κ hp delta J labels c d hd b n a (hn n hns).1 (hn n hns).2 ha

end NField.Alignment.HarperTaylorComparison
