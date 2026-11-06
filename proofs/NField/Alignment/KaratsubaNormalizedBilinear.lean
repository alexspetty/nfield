/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaJointPopulation

/-! # Normalization of the finite bilinear power bound by both prime populations -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaNormalizedBilinear

/-- The exact population exponents cancel without replacing either population by an estimate. -/
theorem population_normalizing_identity (A B F G W M D : ℝ) {s k : ℕ}
    (hs : 1 ≤ s) (hk : 1 ≤ k) :
    (((A^(s-1))^k * (B^s)^(k-1))^2 *
      ((F*B^s)*(W*(M*(D*(G*A^k)))))) * (A^k*B^s) =
        (A*B)^(2*s*k) * (F*W*M*D*G) := by
  have hA : ((A^(s-1))^k * A^k)^2 = A^(2*s*k) := by
    rw [← mul_pow, ← pow_succ, Nat.sub_add_cancel hs]
    simp only [← pow_mul]
    congr 1
    ring
  have hB : ((B^s)^(k-1) * B^s)^2 = B^(2*s*k) := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
    simp only [← pow_mul]
    congr 1
    ring
  calc
    _ = (((A^(s-1))^k * A^k)^2 * ((B^s)^(k-1) * B^s)^2) * (F*W*M*D*G) := by ring
    _ = _ := by rw [hA, hB, mul_pow]

/-- The raw checked moment bound gives a relative bound with the precise inverse population powers. -/
theorem normalized_bound_of_power_bound {A B F G W M D z : ℝ} {s k : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (h : z^(2*s*k) ≤ ((A^(s-1))^k * (B^s)^(k-1))^2 *
      ((F*B^s)*(W*(M*(D*(G*A^k)))))) :
    (z/(A*B))^(2*s*k) ≤ (F*W*M*D*G)/(A^k*B^s) := by
  rw [div_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < (A*B)^(2*s*k))
    (by positivity : 0 < A^k*B^s)).mpr
  have hm := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ A^k*B^s)
  rw [population_normalizing_identity A B F G W M D hs hk] at hm
  simpa only [mul_comm] using hm

/-- The actual finite bilinear sum has the normalized bound with inverse kth and sth prime populations. -/
theorem normalized_bilinear_power_bound {P Q : Finset ℕ} {m s k L U : ℕ}
    [NeZero m] {X Y : ℝ} (hs : 1 ≤ s) (hk : 1 ≤ k) (hPn : P.Nonempty) (hQn : Q.Nonempty)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime) (hPc : ∀ p ∈ P, p.Coprime m)
    (hPl : ∀ p ∈ P, k < p) (hPu : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hPs : (k : ℝ)*X^(2*k-1) < m)
    (hY : 1 ≤ Y) (hQ : ∀ q ∈ Q, q.Prime) (hQc : ∀ q ∈ Q, q.Coprime m)
    (hQl : ∀ q ∈ Q, s < q) (hQu : ∀ q ∈ Q, (q : ℝ) ≤ Y)
    (hQs : (s : ℝ)*Y^(2*s-1) < m) (a b : ZMod m) :
    (‖KaratsubaBilinearReduction.bilinearPrimeSum P Q a b‖ /
      ((P.card : ℝ)*(Q.card : ℝ)))^(2*s*k) ≤
        ((s.factorial : ℝ)*((s*(U-L) : ℕ) : ℝ)*(m : ℝ)*
          (a.val.gcd m : ℝ)*(k.factorial : ℝ)) /
            ((P.card : ℝ)^k*(Q.card : ℝ)^s) := by
  have raw := KaratsubaJointPopulation.bilinear_power_bound hs hk hL hU
    hX hP hPc hPl hPu hPs hY hQ hQc hQl hQu hQs a b
  have hA : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hPn
  have hB : (0 : ℝ) < Q.card := by exact_mod_cast Finset.card_pos.mpr hQn
  apply normalized_bound_of_power_bound hA hB hs hk
  simpa only [Nat.cast_mul, Nat.cast_pow] using raw

end NField.Alignment.KaratsubaNormalizedBilinear
