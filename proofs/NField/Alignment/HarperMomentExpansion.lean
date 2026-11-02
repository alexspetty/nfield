/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SteinhausMoment
import NField.Alignment.MagnitudeShortComparison
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact coefficients for the weighted even moments

The terms of a power are indexed by ordered tuples, so repeated atoms and
coincidences between prime and prime-square products are retained. Grouping
by the complete natural-number index gives the exact random second moment.
Each side has `k` atoms, rather than a bound of `2*k` on a combined degree.
This module supplies identities and support bounds, not the factorial bound.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperMomentExpansion

open scoped BigOperators
open MeasureTheory SteinhausMoment MagnitudeShortComparison SpectralRepulsion

variable {ι : Type*}

/-- Coefficients obtained by collecting all terms with the same index. -/
def groupedCoefficient (s : Finset ι) (a : ι → ℕ) (b : ι → ℂ) (m : ℕ) : ℂ :=
  ∑ i ∈ s with a i = m, b i

theorem grouped_expansion (s : Finset ι) (a : ι → ℕ) (b : ι → ℂ)
    (z : ℕ → ℂ) :
    (∑ i ∈ s, b i * z (a i)) =
      ∑ m ∈ s.image a, groupedCoefficient s a b m * z m := by
  classical
  symm
  calc
    _ = ∑ m ∈ s.image a, ∑ i ∈ s with a i = m, b i * z (a i) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [groupedCoefficient, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem a hi) _

theorem grouped_norm_sq_integrable (s : Finset ι) (a : ι → ℕ) (b : ι → ℂ) :
    Integrable (fun ω => ‖∑ i ∈ s, b i * steinhaus (a i) ω‖ ^ 2) phaseMeasure := by
  classical
  have he (ω : PhaseSpace) := grouped_expansion s a b (fun n => steinhaus n ω)
  simp_rw [he]
  have h := (polynomial_pair_integrable (s.image a) (s.image a)
    (groupedCoefficient s a b) (groupedCoefficient s a b)).re
  simpa only [self_pair_eq_norm_sq, RCLike.re_to_complex, Complex.ofReal_re] using h

/-- Coincident integer products are collected before applying orthogonality. -/
theorem grouped_second_moment (s : Finset ι) (a : ι → ℕ) (b : ι → ℂ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    (∫ ω, ‖∑ i ∈ s, b i * steinhaus (a i) ω‖ ^ 2 ∂phaseMeasure) =
      ∑ m ∈ s.image a, ‖groupedCoefficient s a b m‖ ^ 2 := by
  classical
  have he (ω : PhaseSpace) := grouped_expansion s a b (fun n => steinhaus n ω)
  simp_rw [he]
  apply polynomial_second_moment
  intro m hm
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
  exact ha i hi

variable [Fintype ι]

def tupleIndex (k : ℕ) (a : ι → ℕ) (t : Fin k → ι) : ℕ := ∏ j, a (t j)

def tupleCoefficient (k : ℕ) (b : ι → ℂ) (t : Fin k → ι) : ℂ := ∏ j, b (t j)

/-- The actual coefficient of the `k`th power at the natural index `m`. -/
def powerCoefficient (k : ℕ) (a : ι → ℕ) (b : ι → ℂ) (m : ℕ) : ℂ :=
  groupedCoefficient Finset.univ (tupleIndex k a) (tupleCoefficient k b) m

theorem power_tuple_expansion (k : ℕ) (a : ι → ℕ) (b : ι → ℂ) (z : ℕ →* ℂ) :
    (∑ i, b i * z (a i)) ^ k =
      ∑ t : Fin k → ι, tupleCoefficient k b t * z (tupleIndex k a t) := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro t _
  simp only [tupleCoefficient, tupleIndex, map_prod, Finset.prod_mul_distrib]

theorem power_coefficient_expansion (k : ℕ) (a : ι → ℕ) (b : ι → ℂ) (z : ℕ →* ℂ) :
    (∑ i, b i * z (a i)) ^ k =
      ∑ m ∈ Finset.univ.image (tupleIndex k a), powerCoefficient k a b m * z m := by
  rw [power_tuple_expansion, grouped_expansion]
  rfl

def completeIndex (k : ℕ) (a : ι → ℕ) (t : ℕ × (Fin k → ι)) : ℕ :=
  t.1 * tupleIndex k a t.2

def completeCoefficient (k : ℕ) (b : ι → ℂ) (w : ℕ → ℂ)
    (t : ℕ × (Fin k → ι)) : ℂ := w t.1 * tupleCoefficient k b t.2

/-- The product coefficient includes the short Dirichlet-polynomial index. -/
def weightedCoefficient (k : ℕ) (s : Finset ℕ) (a : ι → ℕ)
    (b : ι → ℂ) (w : ℕ → ℂ) (m : ℕ) : ℂ :=
  groupedCoefficient (s ×ˢ Finset.univ) (completeIndex k a) (completeCoefficient k b w) m

theorem weighted_tuple_expansion (k : ℕ) (s : Finset ℕ) (a : ι → ℕ)
    (b : ι → ℂ) (w : ℕ → ℂ) (z : ℕ →* ℂ) :
    (∑ n ∈ s, w n * z n) * (∑ i, b i * z (a i)) ^ k =
      ∑ t ∈ s ×ˢ Finset.univ, completeCoefficient k b w t * z (completeIndex k a t) := by
  rw [power_tuple_expansion, Finset.sum_mul, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [completeCoefficient, completeIndex, map_mul]
  ring

theorem weighted_coefficient_expansion (k : ℕ) (s : Finset ℕ) (a : ι → ℕ)
    (b : ι → ℂ) (w : ℕ → ℂ) (z : ℕ →* ℂ) :
    (∑ n ∈ s, w n * z n) * (∑ i, b i * z (a i)) ^ k =
      ∑ m ∈ (s ×ˢ Finset.univ).image (completeIndex k a),
        weightedCoefficient k s a b w m * z m := by
  rw [weighted_tuple_expansion, grouped_expansion]
  rfl

theorem weighted_norm_expansion (k : ℕ) (s : Finset ℕ) (a : ι → ℕ)
    (b : ι → ℂ) (w : ℕ → ℂ) (z : ℕ →* ℂ) :
    ‖∑ n ∈ s, w n * z n‖ ^ 2 * ‖∑ i, b i * z (a i)‖ ^ (2 * k) =
      ‖∑ t ∈ s ×ˢ Finset.univ,
        completeCoefficient k b w t * z (completeIndex k a t)‖ ^ 2 := by
  rw [← weighted_tuple_expansion, norm_mul, norm_pow, mul_pow, ← pow_mul]
  rw [Nat.mul_comm k 2]

omit [Fintype ι] in
theorem completeIndex_pos (k : ℕ) (a : ι → ℕ) (t : ℕ × (Fin k → ι))
    (hn : 0 < t.1) (ha : ∀ i, 0 < a i) : 0 < completeIndex k a t :=
  Nat.mul_pos hn (Finset.prod_pos (fun j _ => ha (t.2 j)))

omit [Fintype ι] in
/-- The complete index has exactly `k` atom factors on this side. -/
theorem completeIndex_le (k : ℕ) (a : ι → ℕ) (t : ℕ × (Fin k → ι))
    {x U : ℝ} (hn : (t.1 : ℝ) ≤ x)
    (ha : ∀ i, (a i : ℝ) ≤ U) : (completeIndex k a t : ℝ) ≤ x * U ^ k := by
  have ht : (tupleIndex k a t.2 : ℝ) ≤ U ^ k := by
    simp only [tupleIndex, Nat.cast_prod]
    calc
      _ ≤ ∏ _j : Fin k, U := Finset.prod_le_prod
        (fun j _ => Nat.cast_nonneg _) (fun j _ => ha (t.2 j))
      _ = _ := by simp
  simp only [completeIndex, Nat.cast_mul]
  exact mul_le_mul hn ht (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hn)

theorem weighted_even_moment_integrable (k : ℕ) (s : Finset ℕ) (a : ι → ℕ)
    (b : ι → ℂ) (w : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k)) phaseMeasure := by
  have he (ω : PhaseSpace) := weighted_norm_expansion k s a b w (steinhausHom ω).toMonoidHom
  change ∀ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
    ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) =
      ‖∑ t ∈ s ×ˢ Finset.univ,
        completeCoefficient k b w t * steinhaus (completeIndex k a t) ω‖ ^ 2 at he
  simp_rw [he]
  exact grouped_norm_sq_integrable _ _ _

/-- The random weighted even moment is the squared norm of the actual coefficients. -/
theorem weighted_even_moment_exact (k : ℕ) (s : Finset ℕ) (a : ι → ℕ)
    (b : ι → ℂ) (w : ℕ → ℂ) (hs : ∀ n ∈ s, 0 < n) (ha : ∀ i, 0 < a i) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) ∂phaseMeasure) =
      ∑ m ∈ (s ×ˢ Finset.univ).image (completeIndex k a),
        ‖weightedCoefficient k s a b w m‖ ^ 2 := by
  have he (ω : PhaseSpace) := weighted_norm_expansion k s a b w (steinhausHom ω).toMonoidHom
  change ∀ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
    ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) =
      ‖∑ t ∈ s ×ˢ Finset.univ,
        completeCoefficient k b w t * steinhaus (completeIndex k a t) ω‖ ^ 2 at he
  simp_rw [he]
  apply grouped_second_moment
  intro t ht
  exact (completeIndex_pos k a t (hs t.1 (Finset.mem_product.mp ht).1) ha).ne'

end NField.Alignment.HarperMomentExpansion
