/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetFourier
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! # Exact additive-order kernels and divisor inversion -/

noncomputable section

namespace NField.Alignment.CommonResetConductor

open scoped BigOperators ArithmeticFunction.Moebius
open CommonResetFourier DedekindReciprocity BernoulliCurvature

def conductorKernel (t h : ℕ) : ℝ :=
  (1/4 : ℝ) * ∑ a ∈ (Finset.range t).filter (fun a => a.Coprime t),
    cotangentTerm t a * cotangentTerm t (h*a)

theorem cotangentTerm_scale {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (a : ℕ) :
    cotangentTerm (g*d) (g*a) = cotangentTerm d a := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  unfold cotangentTerm
  simp only [Nat.mul_dvd_mul_iff_left hg]
  split_ifs
  · rfl
  · congr 1
    push_cast
    field_simp

theorem cotangent_reduceGridPoint {h m a : ℕ} (hm : 0 < m) :
    cotangentTerm m a * cotangentTerm m (h*a) =
      cotangentTerm (reduceGridPoint m a).1 (reduceGridPoint m a).2 *
        cotangentTerm (reduceGridPoint m a).1 (h*(reduceGridPoint m a).2) := by
  let g := a.gcd m
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hm
  have hga : g ∣ a := Nat.gcd_dvd_left a m
  have hgm : g ∣ m := Nat.gcd_dvd_right a m
  have ha : g*(a/g)=a := Nat.mul_div_cancel' hga
  have hmm : g*(m/g)=m := Nat.mul_div_cancel' hgm
  have hd : 0 < m/g := Nat.div_pos (Nat.le_of_dvd hm hgm) hg
  unfold reduceGridPoint
  dsimp only
  change cotangentTerm m a*cotangentTerm m (h*a) =
    cotangentTerm (m/g) (a/g)*cotangentTerm (m/g) (h*(a/g))
  calc
    _ = cotangentTerm (g*(m/g)) (g*(a/g))*
        cotangentTerm (g*(m/g)) (g*(h*(a/g))) := by rw [hmm]; congr 1; rw [ha]; congr 1; nlinarith [ha]
    _ = _ := by rw [cotangentTerm_scale hg hd, cotangentTerm_scale hg hd]

/-- Title: `Every additive frequency belongs to its exact reduced denominator`. -/
theorem cotangent_divisor_partition {m : ℕ} (hm : 0 < m) (h : ℕ) :
    (1/4 : ℝ)*∑ a ∈ Finset.range m, cotangentTerm m a*cotangentTerm m (h*a) =
      ∑ d ∈ m.divisors, conductorKernel d h := by
  have hsum : (∑ a ∈ Finset.range m, cotangentTerm m a*cotangentTerm m (h*a)) =
      ∑ da ∈ reducedFractionPairs m,
        cotangentTerm da.1 da.2*cotangentTerm da.1 (h*da.2) := by
    apply Finset.sum_bij (fun a _ => reduceGridPoint m a)
    · exact fun a ha => reduceGridPoint_mem hm ha
    · intro a ha b hb
      exact reduceGridPoint_injective hm ha hb
    · exact reduceGridPoint_surjective hm
    · intro a _
      exact cotangent_reduceGridPoint hm
  rw [hsum]
  unfold reducedFractionPairs conductorKernel
  rw [Finset.sum_filter]
  rw [show (∑ da ∈ m.divisors.product (Finset.range m),
      if da.2 < da.1 ∧ da.2.Coprime da.1 then
        cotangentTerm da.1 da.2*cotangentTerm da.1 (h*da.2) else 0) =
      ∑ d ∈ m.divisors, ∑ a ∈ Finset.range m,
        if a < d ∧ a.Coprime d then cotangentTerm d a*cotangentTerm d (h*a) else 0 from
      Finset.sum_product _ _ _]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdle : d ≤ m := Nat.divisor_le hd
  congr 1
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro a _
    rfl

/-- Title: `The order-one conductor kernel vanishes`. -/
theorem conductorKernel_one (h : ℕ) : conductorKernel 1 h = 0 := by
  simp [conductorKernel, cotangentTerm]

/-- Title: `Dedekind sums are the complete sum of exact-order kernels`. -/
theorem conductor_inversion {t : ℕ} (ht : 0 < t) (h : ℕ) :
    (t : ℝ)*(arithmeticDedekindSum h t : ℝ) = ∑ d ∈ t.divisors, conductorKernel d h := by
  by_cases ht1 : t = 1
  · subst t
    simp [conductorKernel_one, arithmeticDedekindSum, rationalSawtooth]
  · rw [arithmeticDedekind_cotangent (by omega), cotangent_divisor_partition ht]

/-- Title: `Möbius inversion recovers the printed exact-order kernel`. -/
theorem conductor_moebius {t : ℕ} (ht : 0 < t) (h : ℕ) :
    conductorKernel t h = ∑ d ∈ t.divisors,
      (ArithmeticFunction.moebius (t/d) : ℝ)*(d : ℝ)*(arithmeticDedekindSum h d : ℝ) := by
  have hi : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, conductorKernel d h) =
      (n : ℝ)*(arithmeticDedekindSum h n : ℝ) :=
    fun n hn => (conductor_inversion hn h).symm
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hi) t ht
  have hs : (∑ x ∈ t.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℝ)*((x.2 : ℝ)*(arithmeticDedekindSum h x.2 : ℝ))) =
      ∑ d ∈ t.divisors,
        (ArithmeticFunction.moebius (t/d) : ℝ)*((d : ℝ)*(arithmeticDedekindSum h d : ℝ)) :=
    Nat.sum_divisorsAntidiagonal' (fun x y =>
      (ArithmeticFunction.moebius x : ℝ)*((y : ℝ)*(arithmeticDedekindSum h y : ℝ)))
  rw [hs] at hm
  rw [← hm]
  apply Finset.sum_congr rfl
  intro d _
  ring

end NField.Alignment.CommonResetConductor
