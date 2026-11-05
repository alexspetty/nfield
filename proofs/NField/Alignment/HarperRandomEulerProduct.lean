/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSmoothIntervals
import NField.Alignment.SteinhausMoment
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The actual finite-prime random Euler product

Complete multiplicativity and absolute convergence for Re(s)>0 identify
the finite-prime product with the Dirichlet series of the actual smooth
Steinhaus coefficients. The norm majorant is the existing positive Euler
product. Rankin bounds prove the required partial-sum growth, giving the
integral representation with the actual smooth partial sums.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperRandomEulerProduct

open scoped BigOperators Topology
open MeasureTheory Filter Asymptotics SteinhausMoment HarperSmoothDivisor
  HarperSmoothCount HarperSmoothIntervals CollisionMertensInput

def eulerProduct (P : ℝ) (s : ℂ) (ω : PhaseSpace) : ℂ :=
  ∏ q ∈ primesUpTo P, (1-steinhaus q ω/(q : ℂ)^s)⁻¹

def smoothCoefficient (P : ℝ) (ω : PhaseSpace) (n : ℕ) : ℂ :=
  if n ∈ smoothIntegers P then steinhaus n ω else 0

def termHom (s : ℂ) (ω : PhaseSpace) : ℕ →* ℂ where
  toFun n := steinhaus n ω * (n : ℂ)^(-s)
  map_one' := by simp
  map_mul' m n := by
    simp only [steinhaus_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring

theorem termHom_norm {n : ℕ} (hn : n ≠ 0) (s : ℂ) (ω : PhaseSpace) :
    ‖termHom s ω n‖ = (n : ℝ)^(-s.re) := by
  change ‖steinhaus n ω * (n : ℂ)^(-s)‖ = _
  rw [norm_mul, steinhaus_norm hn, one_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.neg_re]

theorem smooth_hasSum (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    HasSum (fun n : smoothIntegers P => steinhaus n ω/(n : ℕ)^s) (eulerProduct P s ω) := by
  have hp {q : ℕ} (hq : q.Prime) : ‖termHom s ω q‖ < 1 := by
    rw [termHom_norm hq.ne_zero]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq.one_lt) (by linarith)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := termHom s ω) (fun {_} hq => hp hq) (primesUpTo P)).2
  have hf : (primesUpTo P).filter Nat.Prime = primesUpTo P :=
    Finset.filter_true_of_mem (fun _ hq => (primesUpTo_mem.mp hq).1)
  simpa only [hf, termHom, MonoidHom.coe_mk, OneHom.coe_mk, Complex.cpow_neg,
    ← div_eq_mul_inv, smoothIntegers, eulerProduct] using h

theorem smooth_norm_hasSum (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    HasSum (fun n : smoothIntegers P => ‖steinhaus n ω/(n : ℕ)^s‖)
      (shiftedProduct P s.re) := by
  have he (n : smoothIntegers P) : ‖steinhaus n ω/(n : ℕ)^s‖ = ((n : ℕ) : ℝ)^(-s.re) := by
    simpa only [termHom, MonoidHom.coe_mk, OneHom.coe_mk, Complex.cpow_neg,
      ← div_eq_mul_inv] using termHom_norm (smoothIntegers_mem.mp n.property).1 s ω
  simp_rw [he]
  exact smooth_power_hasSum P hs

theorem smoothCoefficient_zero (P : ℝ) (ω : PhaseSpace) : smoothCoefficient P ω 0 = 0 := by
  simp [smoothCoefficient]

theorem smoothCoefficient_partial_sum (P x : ℝ) (ω : PhaseSpace) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, smoothCoefficient P ω n) =
      smoothSum x P (fun n => steinhaus n ω) := by
  simp only [smoothCoefficient, smoothSum, smoothSet, Finset.sum_filter]
  rfl

theorem smoothCoefficient_term (P : ℝ) (s : ℂ) (ω : PhaseSpace) (n : ℕ) :
    LSeries.term (smoothCoefficient P ω) s n =
      (smoothIntegers P).indicator (fun n : ℕ => steinhaus n ω/(n : ℂ)^s) n := by
  rw [LSeries.term_def₀ (smoothCoefficient_zero P ω)]
  simp only [smoothCoefficient, Set.indicator_apply,
    Complex.cpow_neg, ← div_eq_mul_inv, ite_div, zero_div]

theorem smooth_LSeries_hasSum (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    LSeriesHasSum (smoothCoefficient P ω) s (eulerProduct P s ω) := by
  have h : HasSum ((fun n : ℕ => steinhaus n ω/(n : ℂ)^s) ∘
      (Subtype.val : smoothIntegers P → ℕ)) (eulerProduct P s ω) := smooth_hasSum P hs ω
  rw [hasSum_subtype_iff_indicator] at h
  change HasSum (LSeries.term (smoothCoefficient P ω) s) _
  rw [funext (smoothCoefficient_term P s ω)]
  exact h

theorem smooth_LSeries_eq (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    LSeries (smoothCoefficient P ω) s = eulerProduct P s ω :=
  (smooth_LSeries_hasSum P hs ω).tsum_eq

theorem eulerProduct_norm_le (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    ‖eulerProduct P s ω‖ ≤ shiftedProduct P s.re := by
  rw [← (smooth_hasSum P hs ω).tsum_eq, ← (smooth_norm_hasSum P hs ω).tsum_eq]
  exact norm_tsum_le_tsum_norm (smooth_norm_hasSum P hs ω).summable

theorem eulerProduct_measurable (P : ℝ) (s : ℂ) : Measurable (eulerProduct P s) := by
  apply Finset.measurable_prod
  intro q hq
  exact (measurable_const.sub ((steinhaus_measurable q).div_const _)).inv

theorem eulerProduct_integrable (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (eulerProduct P s) phaseMeasure :=
  Integrable.of_bound (eulerProduct_measurable P s).aestronglyMeasurable
    (shiftedProduct P s.re) (Filter.Eventually.of_forall (eulerProduct_norm_le P hs))

theorem smoothCoefficient_norm_sum (P : ℝ) (ω : PhaseSpace) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖smoothCoefficient P ω n‖) = smoothCount (N : ℝ) P := by
  simp only [smoothCount, smoothSet, Nat.floor_natCast, Finset.card_eq_sum_ones,
    Finset.sum_filter, smoothCoefficient]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hs
  · exact steinhaus_norm (smoothIntegers_mem.mp hs).1 ω
  · exact norm_zero

theorem smoothCoefficient_norm_sum_isBigO (P : ℝ) {r : ℝ} (hr : 0 < r) (ω : PhaseSpace) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖smoothCoefficient P ω n‖) =O[atTop]
      (fun N : ℕ => (N : ℝ)^r) := by
  apply IsBigO.of_bound (shiftedProduct P r)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  rw [smoothCoefficient_norm_sum, Real.norm_of_nonneg (by unfold smoothCount; positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) r)]
  simpa only [mul_comm] using rankin_bound hN0 P hr

theorem eulerProduct_integral (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    eulerProduct P s ω = s * ∫ t in Set.Ioi (1 : ℝ),
      smoothSum t P (fun n => steinhaus n ω) * (t : ℂ)^(-(s+1)) := by
  have hr : 0 < s.re/2 := by linarith
  rw [← smooth_LSeries_eq P hs ω, LSeries_eq_mul_integral' _ hr.le (by linarith)
    (smoothCoefficient_norm_sum_isBigO P hr ω)]
  simp_rw [smoothCoefficient_partial_sum]

theorem smoothSum_norm_le_count (x P : ℝ) (ω : PhaseSpace) :
    ‖smoothSum x P (fun n => steinhaus n ω)‖ ≤ smoothCount x P := by
  calc
    _ ≤ ∑ n ∈ smoothSet x P, ‖steinhaus n ω‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ smoothSet x P, (1 : ℝ) := Finset.sum_le_sum (fun n _ => steinhaus_norm_le n ω)
    _ = _ := by simp [smoothCount]

theorem smoothSum_rankin_bound {x : ℝ} (hx : 0 < x) (P : ℝ) {r : ℝ} (hr : 0 < r)
    (ω : PhaseSpace) :
    ‖smoothSum x P (fun n => steinhaus n ω)‖ ≤ x^r * shiftedProduct P r :=
  (smoothSum_norm_le_count x P ω).trans (rankin_bound hx P hr)

end NField.Alignment.HarperRandomEulerProduct
