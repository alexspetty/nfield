/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothConvolution
import NField.Alignment.HarperPrimeTaylorComparison

/-!
# Reducing the weighted even moment to tuple multiplicities

The random expectation, the smooth-divisor weights and the coefficient
fibers are all constructed here. The final bound retains the actual number
of ordered tuples with each integer product. Bounding that number by the
factorial and the prime-square weight is a separate arithmetic task.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperMomentReduction

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperMomentExpansion HarperSmoothDivisor
  HarperSmoothConvolution HarperPrimeTaylorComparison

theorem convolution_expansion (s t : Finset ℕ) (c b : ℕ → ℂ) (z : ℕ →* ℂ) :
    (∑ n ∈ s, c n * z n) * (∑ m ∈ t, b m * z m) =
      ∑ u ∈ (s ×ˢ t).image (fun v => v.1 * v.2), convolutionCoefficient s t c b u * z u := by
  calc
    _ = ∑ v ∈ s ×ˢ t, (c v.1 * b v.2) * z (v.1 * v.2) := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [map_mul]
      ring
    _ = _ := grouped_expansion _ _ _ _

/-- The analytic expectation reduces to the smooth weighted coefficient energy. -/
theorem random_product_moment_bound {P : ℝ} (s t : Finset ℕ) (c b : ℕ → ℂ)
    (hs : ∀ n ∈ s, n ≠ 0) (ht : ∀ m ∈ t, m ∈ smoothIntegers P) :
    (∫ ω, ‖∑ n ∈ s, c n * steinhaus n ω‖ ^ 2 *
      ‖∑ m ∈ t, b m * steinhaus m ω‖ ^ 2 ∂phaseMeasure) ≤
      (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖c n‖ ^ 2) *
        (∑ m ∈ t, (smoothDivisorCount P m : ℝ) * ‖b m‖ ^ 2) := by
  have he (ω : PhaseSpace) := convolution_expansion s t c b (steinhausHom ω).toMonoidHom
  change ∀ ω, (∑ n ∈ s, c n * steinhaus n ω) * (∑ m ∈ t, b m * steinhaus m ω) =
    ∑ u ∈ (s ×ˢ t).image (fun v => v.1 * v.2),
      convolutionCoefficient s t c b u * steinhaus u ω at he
  have hn (ω : PhaseSpace) :
      ‖∑ n ∈ s, c n * steinhaus n ω‖ ^ 2 * ‖∑ m ∈ t, b m * steinhaus m ω‖ ^ 2 =
        ‖∑ u ∈ (s ×ˢ t).image (fun v => v.1 * v.2),
          convolutionCoefficient s t c b u * steinhaus u ω‖ ^ 2 := by
    rw [← he, norm_mul, mul_pow]
  simp_rw [hn]
  rw [polynomial_second_moment _ _ (by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hn, hm⟩ := Finset.mem_product.mp hv
    exact mul_ne_zero (hs v.1 hn) (smoothIntegers_mem.mp (ht v.2 hm)).1)]
  exact convolution_energy_bound s t c b hs ht

variable {ι : Type*} [Fintype ι]

/-- The multiplicity counts ordered tuples, including repetitions. -/
def tupleMultiplicity (k : ℕ) (a : ι → ℕ) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin k → ι => tupleIndex k a t = m)).card

theorem weighted_even_moment_coefficient_bound {P : ℝ} (k : ℕ) (s : Finset ℕ)
    (a : ι → ℕ) (b : ι → ℂ) (w : ℕ → ℂ) (hs : ∀ n ∈ s, n ≠ 0)
    (ha : ∀ i, a i ∈ smoothIntegers P) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) ∂phaseMeasure) ≤
      (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2) *
        ∑ m ∈ Finset.univ.image (tupleIndex k a),
          (smoothDivisorCount P m : ℝ) * ‖powerCoefficient k a b m‖ ^ 2 := by
  classical
  have he (ω : PhaseSpace) := power_coefficient_expansion k a b (steinhausHom ω).toMonoidHom
  change ∀ ω, (∑ i, b i * steinhaus (a i) ω) ^ k =
    ∑ m ∈ Finset.univ.image (tupleIndex k a), powerCoefficient k a b m * steinhaus m ω at he
  have hn (ω : PhaseSpace) : ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) =
      ‖∑ m ∈ Finset.univ.image (tupleIndex k a), powerCoefficient k a b m * steinhaus m ω‖ ^ 2 := by
    rw [← he, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  simp_rw [hn]
  apply random_product_moment_bound _ _ _ _ hs
  intro m hm
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hm
  exact smooth_prod Finset.univ (fun j => a (t j)) (fun j _ => ha (t j))

theorem power_coefficient_bound (P : ℝ) (k : ℕ) (a : ι → ℕ) (b : ι → ℂ) (m : ℕ) :
    (smoothDivisorCount P m : ℝ) * ‖powerCoefficient k a b m‖ ^ 2 ≤
      (tupleMultiplicity k a m : ℝ) *
        ∑ t : Fin k → ι with tupleIndex k a t = m,
          ∏ j, (smoothDivisorCount P (a (t j)) : ℝ) * ‖b (t j)‖ ^ 2 := by
  classical
  let F := Finset.univ.filter (fun t : Fin k → ι => tupleIndex k a t = m)
  calc
    _ ≤ (smoothDivisorCount P m : ℝ) *
        ((F.card : ℝ) * ∑ t ∈ F, ‖tupleCoefficient k b t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_sum_sq_le _ _) (Nat.cast_nonneg _)
    _ = (F.card : ℝ) * ∑ t ∈ F,
        (smoothDivisorCount P m : ℝ) * ‖tupleCoefficient k b t‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro t ht
      have hd : (smoothDivisorCount P m : ℝ) ≤
          ∏ j, (smoothDivisorCount P (a (t j)) : ℝ) := by
        rw [← (Finset.mem_filter.mp ht).2]
        exact_mod_cast smoothDivisorCount_prod_le P Finset.univ (fun j => a (t j))
      calc
        _ ≤ (∏ j, (smoothDivisorCount P (a (t j)) : ℝ)) * ‖tupleCoefficient k b t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hd (sq_nonneg _)
        _ = _ := by
          simp only [tupleCoefficient, norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]

theorem power_energy_bound (P : ℝ) (k : ℕ) (a : ι → ℕ) (b : ι → ℂ) :
    (∑ m ∈ Finset.univ.image (tupleIndex k a),
      (smoothDivisorCount P m : ℝ) * ‖powerCoefficient k a b m‖ ^ 2) ≤
      ∑ t : Fin k → ι, (tupleMultiplicity k a (tupleIndex k a t) : ℝ) *
        ∏ j, (smoothDivisorCount P (a (t j)) : ℝ) * ‖b (t j)‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ m ∈ Finset.univ.image (tupleIndex k a),
        (tupleMultiplicity k a m : ℝ) *
          ∑ t : Fin k → ι with tupleIndex k a t = m,
            ∏ j, (smoothDivisorCount P (a (t j)) : ℝ) * ‖b (t j)‖ ^ 2 :=
      Finset.sum_le_sum (fun m _ => power_coefficient_bound P k a b m)
    _ = ∑ m ∈ Finset.univ.image (tupleIndex k a),
        ∑ t : Fin k → ι with tupleIndex k a t = m,
          (tupleMultiplicity k a (tupleIndex k a t) : ℝ) *
            ∏ j, (smoothDivisorCount P (a (t j)) : ℝ) * ‖b (t j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.mp ht).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun t ht => Finset.mem_image_of_mem (tupleIndex k a) ht) _

/-- An unconditional arithmetic reduction, with the actual tuple counts still visible. -/
theorem weighted_even_moment_tuple_bound {P : ℝ} (k : ℕ) (s : Finset ℕ)
    (a : ι → ℕ) (b : ι → ℂ) (w : ℕ → ℂ) (hs : ∀ n ∈ s, n ≠ 0)
    (ha : ∀ i, a i ∈ smoothIntegers P) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) ∂phaseMeasure) ≤
      (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2) *
        ∑ t : Fin k → ι, (tupleMultiplicity k a (tupleIndex k a t) : ℝ) *
          ∏ j, (smoothDivisorCount P (a (t j)) : ℝ) * ‖b (t j)‖ ^ 2 :=
  (weighted_even_moment_coefficient_bound k s a b w hs ha).trans
    (mul_le_mul_of_nonneg_left (power_energy_bound P k a b)
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))))

end NField.Alignment.HarperMomentReduction
