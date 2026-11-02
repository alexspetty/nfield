/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperMomentReduction

/-!
# The literal prime-and-prime-square even moment

These declarations apply the finite coefficient and divisor arguments to
the actual atom family and its two denominators. The complete product size
is `x * (P^2)^k`, separately on each side of the norm square. The arithmetic
tuple-count bound, hence the final factorial estimate, is not asserted here.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.HarperPrimeEvenMoment

open scoped BigOperators
open MeasureTheory SteinhausMoment HarperMomentExpansion HarperMomentReduction
  HarperSmoothDivisor HarperSmoothConvolution HarperPrimeTaylorComparison
  CollisionMertensInput MagnitudeShortComparison CollisionCharacterStructure SpectralRepulsion
open Filter HarperTaylorBudget HarperRoundedCutoff

def primePolynomial (P : ℝ) (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) : ℂ :=
  ∑ p ∈ primesUpTo P,
    (c1 p * z p / (Real.sqrt (p : ℝ) : ℂ) + c2 p * z (p ^ 2) / (p : ℂ))

theorem primePolynomial_eq (P : ℝ) (c1 c2 : ℕ → ℂ) (z : ℕ → ℂ) :
    (∑ a : Atom P, atomCoefficient P c1 c2 a * z (atomIndex P a)) =
      primePolynomial P c1 c2 z := by
  classical
  unfold primePolynomial
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, atomCoefficient, atomIndex, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_coe_sort (primesUpTo P)
    (fun p : ℕ => c1 p * z p / (Real.sqrt (p : ℝ) : ℂ) + c2 p * z (p ^ 2) / (p : ℂ))]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem atom_smooth (P : ℝ) (a : Atom P) : atomIndex P a ∈ smoothIntegers P := by
  have hp := primesUpTo_mem.mp a.1.property
  unfold atomIndex
  split_ifs
  · exact smooth_pow (prime_smooth hp.1 hp.2) 2
  · exact prime_smooth hp.1 hp.2

theorem atom_divisor_count (P : ℝ) (a : Atom P) :
    smoothDivisorCount P (atomIndex P a) = if a.2 then 3 else 2 := by
  have hp := primesUpTo_mem.mp a.1.property
  unfold atomIndex
  split_ifs
  · exact smoothDivisorCount_prime_pow hp.1 hp.2 2
  · simpa only [pow_one] using smoothDivisorCount_prime_pow hp.1 hp.2 1

/-- The two and three here come from the actual smooth-divisor count. -/
theorem atom_coefficient_energy (P : ℝ) (c1 c2 : ℕ → ℂ) (a : Atom P) :
    (smoothDivisorCount P (atomIndex P a) : ℝ) * ‖atomCoefficient P c1 c2 a‖ ^ 2 =
      if a.2 then 3 * ‖c2 a.1.val‖ ^ 2 / (a.1.val : ℝ) ^ 2
      else 2 * ‖c1 a.1.val‖ ^ 2 / (a.1.val : ℝ) := by
  rw [atom_divisor_count]
  unfold atomCoefficient
  split_ifs
  · simp only [Nat.cast_ofNat, norm_div, Complex.norm_natCast, div_pow]
    ring
  · simp only [Nat.cast_ofNat, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
    ring

/-- The factor four per square is exactly what turns the divisor weights into Harper's weights. -/
theorem corrected_atom_energy_sum (P : ℝ) (c1 c2 : ℕ → ℂ) :
    (∑ a : Atom P, (if a.2 then (4 : ℝ) else 1) *
      ((smoothDivisorCount P (atomIndex P a) : ℝ) * ‖atomCoefficient P c1 c2 a‖ ^ 2)) =
      2 * ∑ p ∈ primesUpTo P,
        (‖c1 p‖ ^ 2 / (p : ℝ) + 6 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2) := by
  classical
  simp_rw [atom_coefficient_energy]
  rw [Fintype.sum_prod_type, Finset.mul_sum,
    ← Finset.sum_coe_sort (primesUpTo P)
      (fun p : ℕ => 2 * (‖c1 p‖ ^ 2 / (p : ℝ) + 6 * ‖c2 p‖ ^ 2 / (p : ℝ) ^ 2))]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  ring

theorem prime_even_moment_integrable (P : ℝ) (k : ℕ) (s : Finset ℕ)
    (c1 c2 w : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k)) phaseMeasure := by
  have he (ω : PhaseSpace) := primePolynomial_eq P c1 c2 (fun n => steinhaus n ω)
  simpa only [he] using
    weighted_even_moment_integrable k s (atomIndex P) (atomCoefficient P c1 c2) w

theorem prime_even_moment_exact (P : ℝ) (k : ℕ) (s : Finset ℕ)
    (c1 c2 w : ℕ → ℂ) (hs : ∀ n ∈ s, 0 < n) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) ∂phaseMeasure) =
      ∑ m ∈ (s ×ˢ Finset.univ).image (completeIndex k (atomIndex P)),
        ‖weightedCoefficient k s (atomIndex P) (atomCoefficient P c1 c2) w m‖ ^ 2 := by
  have he (ω : PhaseSpace) := primePolynomial_eq P c1 c2 (fun n => steinhaus n ω)
  simpa only [he] using weighted_even_moment_exact k s
    (atomIndex P) (atomCoefficient P c1 c2) w hs (fun a => (atomIndex_bounds P a).1)

/-- No tuple-count estimate is assumed: the true finite multiplicity remains on the right. -/
theorem prime_even_moment_tuple_bound (P : ℝ) (k : ℕ) (s : Finset ℕ)
    (c1 c2 w : ℕ → ℂ) (hs : ∀ n ∈ s, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
      ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) ∂phaseMeasure) ≤
      (∑ n ∈ s, (smoothDivisorCount P n : ℝ) * ‖w n‖ ^ 2) *
        ∑ t : Fin k → Atom P,
          (tupleMultiplicity k (atomIndex P) (tupleIndex k (atomIndex P) t) : ℝ) *
            ∏ j, (if (t j).2 then 3 * ‖c2 (t j).1.val‖ ^ 2 / ((t j).1.val : ℝ) ^ 2
              else 2 * ‖c1 (t j).1.val‖ ^ 2 / ((t j).1.val : ℝ)) := by
  have he (ω : PhaseSpace) := primePolynomial_eq P c1 c2 (fun n => steinhaus n ω)
  simpa only [he, atom_coefficient_energy] using
    weighted_even_moment_tuple_bound k s (atomIndex P) (atomCoefficient P c1 c2) w hs (atom_smooth P)

theorem weighted_even_moment_comparison {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]
    (k : ℕ) (s : Finset ℕ) (a : ι → ℕ) (b : ι → ℂ) (w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ n.Coprime q) (ha : ∀ i, 0 < a i ∧ (a i).Coprime q)
    (hsize : ∀ t ∈ s ×ˢ Finset.univ, completeIndex k a t < q) :
    uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
      ‖∑ i, b i * χ (a i : ZMod q)‖ ^ (2 * k)) =
      ∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
        ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) ∂phaseMeasure := by
  classical
  have he (z : ℕ →* ℂ) :
      ‖∑ n ∈ s, w n * z n‖ ^ 2 * ‖∑ i, b i * z (a i)‖ ^ (2 * k) =
        ‖∑ m ∈ (s ×ˢ Finset.univ).image (completeIndex k a),
          weightedCoefficient k s a b w m * z m‖ ^ 2 := by
    rw [← weighted_coefficient_expansion, norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm k 2]
  have hc (χ : Character q) := he (HarperTaylorComparison.characterNat χ)
  have hr (ω : PhaseSpace) := he (steinhausHom ω).toMonoidHom
  change ∀ χ : Character q,
    ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 * ‖∑ i, b i * χ (a i : ZMod q)‖ ^ (2 * k) =
      ‖∑ m ∈ (s ×ˢ Finset.univ).image (completeIndex k a),
        weightedCoefficient k s a b w m * χ (m : ZMod q)‖ ^ 2 at hc
  change ∀ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
    ‖∑ i, b i * steinhaus (a i) ω‖ ^ (2 * k) =
      ‖∑ m ∈ (s ×ˢ Finset.univ).image (completeIndex k a),
        weightedCoefficient k s a b w m * steinhaus m ω‖ ^ 2 at hr
  simp_rw [hc, hr]
  apply polynomial_second_moment_comparison
  intro m hm
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
  have hn := hs t.1 (Finset.mem_product.mp ht).1
  exact ⟨completeIndex_pos k a t hn.1 (fun i => (ha i).1), hsize t ht,
    hn.2.mul_left (Nat.Coprime.prod_left (fun j _ => (ha (t.2 j)).2))⟩

/-- The printed complete size, with one `k`-fold product on each side. -/
theorem prime_even_moment_comparison {q : ℕ} [NeZero q] (P x : ℝ) (k : ℕ)
    (s : Finset ℕ) (c1 c2 w : ℕ → ℂ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ x ∧ n.Coprime q)
    (ha : ∀ p ∈ primesUpTo P, p.Coprime q) (hsize : x * (P ^ 2) ^ k < q) :
    uniformAverage (fun χ : Character q => ‖∑ n ∈ s, w n * χ (n : ZMod q)‖ ^ 2 *
      ‖primePolynomial P c1 c2 (fun n => χ (n : ZMod q))‖ ^ (2 * k)) =
      ∫ ω, ‖∑ n ∈ s, w n * steinhaus n ω‖ ^ 2 *
        ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * k) ∂phaseMeasure := by
  have hu (a : Atom P) : (atomIndex P a).Coprime q := by
    unfold atomIndex
    split_ifs
    · exact (ha a.1.val a.1.property).pow_left 2
    · exact ha a.1.val a.1.property
  have hb : ∀ t ∈ s ×ˢ Finset.univ, completeIndex k (atomIndex P) t < q := by
    intro t ht
    have hn := hs t.1 (Finset.mem_product.mp ht).1
    have h := (completeIndex_le k (atomIndex P) t hn.2.1
      (fun a => (atomIndex_bounds P a).2)).trans_lt hsize
    exact_mod_cast h
  have hc (χ : Character q) := primePolynomial_eq P c1 c2 (fun n => χ (n : ZMod q))
  have hr (ω : PhaseSpace) := primePolynomial_eq P c1 c2 (fun n => steinhaus n ω)
  simpa only [hc, hr] using weighted_even_moment_comparison k s
    (atomIndex P) (atomCoefficient P c1 c2) w (fun n hn => ⟨(hs n hn).1, (hs n hn).2.2⟩)
    (fun a => ⟨(atomIndex_bounds P a).1, hu a⟩) hb

/-- Exact comparison for every even moment used by a product of actual Taylor remainders. -/
theorem eventual_remainder_moment_comparison : ∀ᶠ p : ℕ in atTop,
    let x := (p : ℝ) - 1
    let P := primeCutoff x
    ∀ [NeZero (p ^ 2)], p.Prime → ∀ j : ℕ, j ≤ factorCount x → ∀ c1 c2 w : ℕ → ℂ,
    uniformAverage (fun χ : Character (p ^ 2) =>
      ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * χ (n : ZMod (p ^ 2))‖ ^ 2 *
        ‖primePolynomial P c1 c2 (fun n => χ (n : ZMod (p ^ 2)))‖ ^ (2 * (taylorOrder x * j))) =
      ∫ ω, ‖∑ n ∈ Finset.Icc 1 (p - 1), w n * steinhaus n ω‖ ^ 2 *
        ‖primePolynomial P c1 c2 (fun n => steinhaus n ω)‖ ^ (2 * (taylorOrder x * j))
          ∂phaseMeasure := by
  filter_upwards [eventual_prime_square_remainder_size,
    base_minus_one_tendsto.eventually eventual_cutoff_square_lt] with p hb hsmall
  dsimp only at hb ⊢
  intro _ hp j hj c1 c2 w
  apply prime_even_moment_comparison (primeCutoff ((p : ℝ) - 1)) ((p : ℝ) - 1)
    (taylorOrder ((p : ℝ) - 1) * j) (Finset.Icc 1 (p - 1)) c1 c2 w
  · intro n hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    have hnxR : (n : ℝ) ≤ (p : ℝ) - 1 := by
      have h := (Nat.cast_le (α := ℝ)).mpr hnx
      rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at h
    exact ⟨hn1, hnxR, small_factor_unit hp hn1
      (by exact_mod_cast (show (n : ℝ) < p by linarith))⟩
  · intro r hr
    have hprime := (primesUpTo_mem.mp hr).1
    have hbound := (atomIndex_bounds (primeCutoff ((p : ℝ) - 1)) (⟨r, hr⟩, false)).2
    change (r : ℝ) ≤ (primeCutoff ((p : ℝ) - 1)) ^ 2 at hbound
    exact small_factor_unit hp hprime.pos
      (by exact_mod_cast (show (r : ℝ) < p by linarith))
  · have h := hb j hj
    simpa only [Real.rpow_natCast, Nat.cast_pow] using h.1.trans_lt (h.2.1.trans h.2.2)

end NField.Alignment.HarperPrimeEvenMoment
