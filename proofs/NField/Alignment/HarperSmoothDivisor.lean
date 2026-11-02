/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionMertensInput
import NField.Alignment.HarperRoundedCutoff
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The literal smooth-divisor bound in the Harper transfer

The cutoff uses every prime at most the real number `P`, with the endpoint
included. `smoothDivisorCount` counts positive smooth divisors, including one.
Dirichlet convolution gives the exact finite rearrangement with `N / d`.
The convergent sum of reciprocal smooth integers is the finite Euler product;
global summability of the harmonic series is neither assumed nor needed.

The canonical proved Mertens theorem supplies the logarithmic bound. The
last theorem is the entire two-link inequality of manuscript display 070,
at the actual rounded cutoff and `x = p - 1`. It proves no smooth-number
count, Taylor remainder, conditioning error or fractional-moment estimate.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperSmoothDivisor

open scoped BigOperators Topology
open Filter Asymptotics
open CollisionMertensInput HarperRoundedCutoff

/-- Positive integers whose prime divisors are at most `P`. -/
def smoothIntegers (P : ℝ) : Set ℕ := Nat.factoredNumbers (primesUpTo P)

instance (P : ℝ) : DecidablePred (· ∈ smoothIntegers P) :=
  inferInstanceAs (DecidablePred (· ∈ Nat.factoredNumbers (primesUpTo P)))

/-- The actual number of positive `P`-smooth divisors; zero has count zero. -/
def smoothDivisorCount (P : ℝ) (n : ℕ) : ℕ :=
  (n.divisors.filter (· ∈ smoothIntegers P)).card

/-- The positive-integer sum through a real cutoff, with the natural floor. -/
def smoothDivisorSum (P x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (smoothDivisorCount P n : ℝ)

theorem smoothIntegers_mem {P : ℝ} {n : ℕ} :
    n ∈ smoothIntegers P ↔
      n ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ n → (q : ℝ) ≤ P := by
  rw [smoothIntegers, Nat.mem_factoredNumbers_iff_primeFactors_subset]
  constructor
  · rintro ⟨hn, hs⟩
    exact ⟨hn, fun q hq hqn => (primesUpTo_mem.mp (hs (Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩))).2⟩
  · rintro ⟨hn, hs⟩
    exact ⟨hn, fun q hq => primesUpTo_mem.mpr
      ⟨(Nat.mem_primeFactors.mp hq).1, hs q (Nat.mem_primeFactors.mp hq).1
        (Nat.mem_primeFactors.mp hq).2.1⟩⟩

def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_comm]

/-- A finite prime set gives a convergent reciprocal sum over all smooth integers. -/
theorem smooth_reciprocal_hasSum (P : ℝ) :
    HasSum (fun n : smoothIntegers P => ((n : ℕ) : ℝ)⁻¹) (inversePrimeProduct P) := by
  have hprime {p : ℕ} (hp : p.Prime) : ‖reciprocalHom p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun {_} hp => hprime hp) (primesUpTo P)).2
  have hf : (primesUpTo P).filter Nat.Prime = primesUpTo P :=
    Finset.filter_true_of_mem fun _ hp => (primesUpTo_mem.mp hp).1
  simpa only [hf, reciprocalHom, MonoidHom.coe_mk, OneHom.coe_mk,
    inversePrimeProduct, smoothIntegers] using h

private def smoothIndicator (P : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∈ smoothIntegers P then 1 else 0,
    by simp [smoothIntegers, Nat.mem_factoredNumbers]⟩

private theorem smoothIndicator_convolution (P : ℝ) (n : ℕ) :
    (smoothIndicator P * ArithmeticFunction.zeta) n = (smoothDivisorCount P n : ℝ) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp [smoothIndicator, smoothDivisorCount, Finset.sum_boole]

/-- Exact finite counting by smooth divisors, retaining the integer quotient. -/
theorem smooth_divisor_sum_exact (P : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (smoothDivisorCount P n : ℝ)) =
      ∑ d ∈ (Finset.Ioc 0 N).filter (· ∈ smoothIntegers P), ((N / d : ℕ) : ℝ) := by
  simp_rw [← smoothIndicator_convolution]
  rw [ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
  simp [smoothIndicator, Finset.sum_filter]

theorem smooth_partial_reciprocal_bound (P : ℝ) (s : Finset ℕ) :
    (∑ d ∈ s.filter (· ∈ smoothIntegers P), (d : ℝ)⁻¹) ≤ inversePrimeProduct P := by
  have h := smooth_reciprocal_hasSum P
  have hs : Summable ((smoothIntegers P).indicator (fun n : ℕ => (n : ℝ)⁻¹)) :=
    (summable_subtype_iff_indicator (s := smoothIntegers P)
      (f := fun n : ℕ => (n : ℝ)⁻¹)).mp h.summable
  have he : (∑' n : ℕ, (smoothIntegers P).indicator (fun d : ℕ => (d : ℝ)⁻¹) n) =
      inversePrimeProduct P :=
    (tsum_subtype (smoothIntegers P) (fun n : ℕ => (n : ℝ)⁻¹)).symm.trans h.tsum_eq
  rw [← he]
  simpa only [Finset.sum_filter, Set.indicator_apply] using
    hs.sum_le_tsum s (fun n _ => by simp only [Set.indicator_apply]; split_ifs <;> positivity)

theorem smooth_divisor_sum_bound (P : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (smoothDivisorCount P n : ℝ)) ≤
      (N : ℝ) * inversePrimeProduct P := by
  rw [smooth_divisor_sum_exact]
  calc
    _ ≤ ∑ d ∈ (Finset.Ioc 0 N).filter (· ∈ smoothIntegers P),
        (N : ℝ) * (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← div_eq_mul_inv]
      exact Nat.cast_div_le
    _ = (N : ℝ) * ∑ d ∈ (Finset.Ioc 0 N).filter (· ∈ smoothIntegers P), (d : ℝ)⁻¹ :=
      (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ) * inversePrimeProduct P :=
      mul_le_mul_of_nonneg_left (smooth_partial_reciprocal_bound P _) (Nat.cast_nonneg N)

theorem smooth_divisor_sum_real_bound (P : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    smoothDivisorSum P x ≤ x * inversePrimeProduct P :=
  (smooth_divisor_sum_bound P ⌊x⌋₊).trans
    (mul_le_mul_of_nonneg_right (Nat.floor_le hx) (inversePrimeProduct_pos P).le)

theorem inversePrimeProduct_isBigO_log :
    inversePrimeProduct =O[atTop] Real.log :=
  mertens_inverse_product.isBigO.trans
    ((isBigO_refl Real.log atTop).const_mul_left (Real.exp Real.eulerMascheroniConstant))

/-- One positive constant works for every nonnegative `x` once `P` is large. -/
theorem uniform_smooth_divisor_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop, ∀ x : ℝ, 0 ≤ x →
      smoothDivisorSum P x ≤ x * inversePrimeProduct P ∧
      x * inversePrimeProduct P ≤ C * x * Real.log P := by
  obtain ⟨C, hC, hbound⟩ := inversePrimeProduct_isBigO_log.exists_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℝ)] with P hP hP1
  have hb : inversePrimeProduct P ≤ C * Real.log P := by
    simpa only [Real.norm_eq_abs, abs_of_pos (inversePrimeProduct_pos P),
      abs_of_nonneg (Real.log_nonneg hP1)] using hP
  intro x hx
  refine ⟨smooth_divisor_sum_real_bound P hx, ?_⟩
  simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hb hx

theorem primeCutoff_tendsto : Tendsto primeCutoff atTop atTop :=
  Real.tendsto_exp_atTop.comp cutoffLog_tendsto

theorem harper_smooth_divisor_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      smoothDivisorSum (primeCutoff x) x ≤ x * inversePrimeProduct (primeCutoff x) ∧
      x * inversePrimeProduct (primeCutoff x) ≤ C * x * cutoffLog x := by
  obtain ⟨C, hC, hbound⟩ := uniform_smooth_divisor_estimate
  refine ⟨C, hC, ?_⟩
  filter_upwards [primeCutoff_tendsto.eventually hbound, eventually_ge_atTop (0 : ℝ)]
    with x hx hx0
  simpa only [log_primeCutoff] using hx x hx0

/-- The full printed smooth-divisor chain at `x = p - 1`; primality is unnecessary. -/
theorem prime_square_smooth_divisor_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop,
      let x := (p : ℝ) - 1
      smoothDivisorSum (primeCutoff x) x ≤ x * inversePrimeProduct (primeCutoff x) ∧
      x * inversePrimeProduct (primeCutoff x) ≤ C * x * cutoffLog x := by
  obtain ⟨C, hC, hbound⟩ := harper_smooth_divisor_estimate
  exact ⟨C, hC, base_minus_one_tendsto.eventually hbound⟩

end NField.Alignment.HarperSmoothDivisor
