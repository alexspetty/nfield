/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTupleMultiplicity

/-!
# Prime-and-prime-square even-moment estimates

The moment is bounded from its actual finite coefficients, the proved
smooth-divisor convolution inequality and the proved ordered-tuple count.
The factorial, prime-square weight six and both coefficient denominators
are retained. The weighted random inequality has constant one; exact
comparison supplies the character inequality at every required remainder
order. The unweighted estimate has no factor two outside the prime sum,
and a stronger form with square weight two is proved as well.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperEvenMomentBound

open scoped BigOperators
open MeasureTheory Filter SteinhausMoment HarperMomentExpansion HarperMomentReduction
  HarperSmoothDivisor HarperSmoothConvolution HarperPrimeTaylorComparison
  HarperPrimeEvenMoment HarperTuplePolynomial HarperTupleMultiplicity
  CollisionMertensInput MagnitudeShortComparison CollisionCharacterStructure SpectralRepulsion
  HarperTaylorBudget HarperRoundedCutoff

theorem tuple_energy_bound (P : ℝ) (k : ℕ) (b : Atom P → ℂ) :
    (∑ t : Fin k → Atom P,
      (tupleMultiplicity k (atomIndex P) (tupleIndex k (atomIndex P) t) : ℝ) *
        ∏ j, (smoothDivisorCount P (atomIndex P (t j)) : ℝ) * ‖b (t j)‖ ^ 2) ≤
      (k.factorial : ℝ) *
        (∑ a : Atom P, (if a.2 then (4 : ℝ) else 1) *
          ((smoothDivisorCount P (atomIndex P a) : ℝ) * ‖b a‖ ^ 2)) ^ k := by
  classical
  rw [Fintype.sum_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have ht : (tupleMultiplicity k (atomIndex P) (tupleIndex k (atomIndex P) t) : ℝ) ≤
      (k.factorial : ℝ) * 4 ^ squareCount k t := by
    exact_mod_cast tupleMultiplicity_le_factorial_four P k t
  calc
    _ ≤ ((k.factorial : ℝ) * 4 ^ squareCount k t) *
        ∏ j, (smoothDivisorCount P (atomIndex P (t j)) : ℝ) * ‖b (t j)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right ht
        (Finset.prod_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    _ = _ := by simp only [Finset.prod_mul_distrib, square_weight_product]; ring

/-- The literal weighted random moment, with an absolute constant of one. -/
theorem random_weighted_even_moment_bound (P : ℝ) (k : ℕ) (s : Finset ℕ)
    (c1 c2 w : ℕ → ℂ) (hs : ∀ n ∈ s, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) ∂phaseMeasure) ≤
      (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2) * (k.factorial : ℝ) *
        (2 * ∑ p ∈ primesUpTo P,
          (‖c1 p‖ ^ 2 / (p : ℝ) + 6 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2)) ^ k := by
  have he (ω : PhaseSpace) := primePolynomial_eq P c1 c2 (fun n => steinhaus n ω)
  have h := weighted_even_moment_tuple_bound k s (atomIndex P) (atomCoefficient P c1 c2) w hs
    (atom_smooth P)
  simp only [he] at h
  calc
    _ ≤ _ := h
    _ ≤ (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2) *
        ((k.factorial : ℝ) * (∑ a : Atom P, (if a.2 then (4 : ℝ) else 1) *
          ((smoothDivisorCount P (atomIndex P a) : ℝ) * ‖atomCoefficient P c1 c2 a‖ ^ 2)) ^ k) :=
      mul_le_mul_of_nonneg_left (tuple_energy_bound P k (atomCoefficient P c1 c2))
        (Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    _ = _ := by rw [corrected_atom_energy_sum]; ring

/-- Exact finite comparison transfers the same bound to the complete character family. -/
theorem character_weighted_even_moment_bound {q : ℕ} [NeZero q] (P x : ℝ) (k : ℕ)
    (s : Finset ℕ) (c1 c2 w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ x ∧ n.Coprime q)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : x * (P ^ 2) ^ k < q) :
    uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
      ‖primePolynomial P c1 c2 (fun n => χ (n : ZMod q))‖ ^ (2 * k)) ≤
      (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2) * (k.factorial : ℝ) *
        (2 * ∑ p ∈ primesUpTo P,
          (‖c1 p‖ ^ 2 / (p : ℝ) + 6 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2)) ^ k := by
  rw [prime_even_moment_comparison P x k s c1 c2 w hs ha hsize]
  exact random_weighted_even_moment_bound P k s c1 c2 w (fun n hn => (hs n hn).1.ne')

/-- The actual rounded remainder orders, with no supplied unit, size, or moment estimate. -/
theorem eventual_remainder_moment_bound : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    let P := primeCutoff x
    ∀ [NeZero (p ^ 2)], p.Prime → ∀ j : ℕ, j ≤ factorCount x → ∀ c1 c2 w : ℕ → ℂ,
    uniformAverage (fun χ : Character (p ^ 2) =>
      ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * χ (n : ZMod (p ^ 2))‖ ^ 2 *
        ‖primePolynomial P c1 c2 (fun n => χ (n : ZMod (p ^ 2)))‖ ^ (2 * (taylorOrder x * j))) ≤
      (∑ n ∈ Finset.Icc 1 (p - 1), (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2) *
        ((taylorOrder x * j).factorial : ℝ) *
          (2 * ∑ r ∈ primesUpTo P,
            (‖c1 r‖ ^ 2 / (r : ℝ) + 6 * ‖c2 r‖ ^ 2 / (r : ℝ) ^ 2)) ^ (taylorOrder x * j) := by
  filter_upwards [eventual_remainder_moment_comparison] with p h
  dsimp only at h ⊢
  intro _ hp j hj c1 c2 w
  rw [h hp j hj c1 c2 w]
  apply random_weighted_even_moment_bound
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  omega

theorem power_energy_tuple_bound {ι : Type*} [Fintype ι] (k : ℕ)
    (a : ι → ℕ) (b : ι → ℂ) :
    (∑ m ∈ Finset.univ.image (tupleIndex k a), ‖powerCoefficient k a b m‖ ^ 2) ≤
      ∑ t : Fin k → ι, (tupleMultiplicity k a (tupleIndex k a t) : ℝ) * ∏ j, ‖b (t j)‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ m ∈ Finset.univ.image (tupleIndex k a), (tupleMultiplicity k a m : ℝ) *
        ∑ t : Fin k → ι with tupleIndex k a t = m, ∏ j, ‖b (t j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      have h := norm_sum_sq_le
        (Finset.univ.filter (fun t : Fin k → ι => tupleIndex k a t = m)) (tupleCoefficient k b)
      simpa only [powerCoefficient, groupedCoefficient, tupleMultiplicity,
        tupleCoefficient, norm_prod, ← Finset.prod_pow] using h
    _ = ∑ m ∈ Finset.univ.image (tupleIndex k a),
        ∑ t : Fin k → ι with tupleIndex k a t = m,
          (tupleMultiplicity k a (tupleIndex k a t) : ℝ) * ∏ j, ‖b (t j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.mp ht).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun t ht => Finset.mem_image_of_mem (tupleIndex k a) ht) _

theorem plain_power_energy_bound (P : ℝ) (k : ℕ) (b : Atom P → ℂ) :
    (∑ m ∈ Finset.univ.image (tupleIndex k (atomIndex P)),
      ‖powerCoefficient k (atomIndex P) b m‖ ^ 2) ≤
      (k.factorial : ℝ) * (∑ a : Atom P, (if a.2 then (2 : ℝ) else 1) * ‖b a‖ ^ 2) ^ k := by
  classical
  refine (power_energy_tuple_bound k (atomIndex P) b).trans ?_
  rw [Fintype.sum_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have ht : (tupleMultiplicity k (atomIndex P) (tupleIndex k (atomIndex P) t) : ℝ) ≤
      (k.factorial : ℝ) * 2 ^ squareCount k t := by
    exact_mod_cast tupleMultiplicity_le_factorial_two P k t
  calc
    _ ≤ ((k.factorial : ℝ) * 2 ^ squareCount k t) * ∏ j, ‖b (t j)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right ht (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by rw [Finset.prod_mul_distrib, square_weight_product]; ring

theorem atom_norm_energy (P : ℝ) (c1 c2 : ℕ → ℂ) (a : Atom P) :
    ‖atomCoefficient P c1 c2 a‖ ^ 2 =
      if a.2 then ‖c2 a.1.val‖ ^ 2 / (a.1.val : ℝ) ^ 2
      else ‖c1 a.1.val‖ ^ 2 / (a.1.val : ℝ) := by
  unfold atomCoefficient
  split_ifs
  · simp only [norm_div, Complex.norm_natCast, div_pow]
  · simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem plain_atom_energy_sum (P : ℝ) (c1 c2 : ℕ → ℂ) (v : ℝ) :
    (∑ a : Atom P, (if a.2 then v else 1) * ‖atomCoefficient P c1 c2 a‖ ^ 2) =
      ∑ p ∈ primesUpTo P, (‖c1 p‖ ^ 2 / (p : ℝ) + v * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2) := by
  classical
  simp_rw [atom_norm_energy]
  rw [Fintype.sum_prod_type,
    ← Finset.sum_coe_sort (primesUpTo P)
      (fun p : ℕ => ‖c1 p‖ ^ 2 / (p : ℝ) + v * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  ring

theorem random_even_moment_integrable (P : ℝ) (k : ℕ) (c1 c2 : ℕ → ℂ) :
    Integrable (fun ω => ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k))
      phaseMeasure := by
  simpa using prime_even_moment_integrable P k {1} c1 c2 (fun _ => 1)

/-- A stronger random estimate with square weight two follows from the derivative recurrence. -/
theorem random_even_moment_bound_two (P : ℝ) (k : ℕ) (c1 c2 : ℕ → ℂ) :
    (∫ ω, ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) ∂phaseMeasure) ≤
      (k.factorial : ℝ) *
        (∑ p ∈ primesUpTo P, (‖c1 p‖ ^ 2 / (p : ℝ) + 2 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2)) ^ k := by
  classical
  have hp (ω : PhaseSpace) := primePolynomial_eq P c1 c2 (fun n => steinhaus n ω)
  have he (ω : PhaseSpace) := power_coefficient_expansion k (atomIndex P)
    (atomCoefficient P c1 c2) (steinhausHom ω).toMonoidHom
  change ∀ ω, (∑ a : Atom P, atomCoefficient P c1 c2 a * steinhaus (atomIndex P a) ω) ^ k =
    ∑ m ∈ Finset.univ.image (tupleIndex k (atomIndex P)),
      powerCoefficient k (atomIndex P) (atomCoefficient P c1 c2) m * steinhaus m ω at he
  have hn (ω : PhaseSpace) :
      ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) =
        ‖∑ m ∈ Finset.univ.image (tupleIndex k (atomIndex P)),
          powerCoefficient k (atomIndex P) (atomCoefficient P c1 c2) m * steinhaus m ω‖ ^ 2 := by
    rw [← he, norm_pow, ← pow_mul, Nat.mul_comm k 2, hp]
  simp_rw [hn]
  rw [polynomial_second_moment _ _ (by
    intro m hm
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.prod_pos (fun j _ => (atomIndex_bounds P (t j)).1)).ne')]
  simpa only [plain_atom_energy_sum] using plain_power_energy_bound P k (atomCoefficient P c1 c2)

/-- The sharper unweighted form of the printed estimate, with no factor two outside the sum. -/
theorem random_even_moment_bound (P : ℝ) (k : ℕ) (c1 c2 : ℕ → ℂ) :
    (∫ ω, ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) ∂phaseMeasure) ≤
      (k.factorial : ℝ) *
        (∑ p ∈ primesUpTo P, (‖c1 p‖ ^ 2 / (p : ℝ) + 6 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2)) ^ k := by
  refine (random_even_moment_bound_two P k c1 c2).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀
  · exact Finset.sum_nonneg fun p _ => add_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
  · apply Finset.sum_le_sum
    intro p _
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 6)
      (sq_nonneg _)) (sq_nonneg _)

theorem character_even_moment_bound {q : ℕ} [NeZero q] (P : ℝ) (k : ℕ)
    (c1 c2 : ℕ → ℂ) (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : (P ^ 2) ^ k < q) :
    uniformAverage (fun χ : Character q =>
      ‖primePolynomial P c1 c2 (fun n => χ (n : ZMod q))‖ ^ (2 * k)) ≤
      (k.factorial : ℝ) *
        (∑ p ∈ primesUpTo P, (‖c1 p‖ ^ 2 / (p : ℝ) + 6 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2)) ^ k := by
  have h := prime_even_moment_comparison (q := q) P 1 k {1} c1 c2 (fun _ => 1)
    (by simp) ha (by simpa using hsize)
  have he : uniformAverage (fun χ : Character q =>
      ‖primePolynomial P c1 c2 (fun n => χ (n : ZMod q))‖ ^ (2 * k)) =
      ∫ ω, ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) ∂phaseMeasure := by
    simpa using h
  rw [he]
  exact random_even_moment_bound P k c1 c2

end NField.Alignment.HarperEvenMomentBound
