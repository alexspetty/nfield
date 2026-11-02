/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.StepanovAuxiliary
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# The nonsquare obstruction in Stepanov's nonvanishing argument

Low-degree cancellation modulo X^q forces a polynomial square identity.
Over the algebraic closure that identity contradicts the nonsquare
hypothesis. All degree and constant-term conditions are explicit.
-/

set_option autoImplicit false
namespace NField.Alignment.StepanovNonvanishing

open scoped BigOperators
open Polynomial StepanovAuxiliary

/-- A rational square root of a polynomial over an algebraically closed
field is already polynomial. Here it is expressed without a fraction field. -/
theorem isSquare_of_square_identity {K : Type*} [Field K] [IsAlgClosed K]
    (f r s : K[X]) (c : K) (hr : r ≠ 0)
    (h : r^2 * f = C c * s^2) : IsSquare f := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 2)
  have hid : r^2 * f = (C b * s)^2 := by
    rw [mul_pow, ← C_pow, hb]
    exact h
  have hd : r^2 ∣ (C b * s)^2 := ⟨f, hid.symm⟩
  obtain ⟨t, ht⟩ := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
    (by decide : (2 : ℕ) ≠ 0)).mp hd
  have hf : f = t^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hr)
    rw [hid, ht, mul_pow]
  exact ⟨t, by simpa only [pow_two] using hf⟩

/-- Frobenius expansion is constant modulo X^q. -/
theorem X_pow_card_dvd_frobenius_sub_constant {K : Type*} [Field K] [Fintype K]
    (f : K[X]) :
    X ^ Fintype.card K ∣ f ^ Fintype.card K - C (f.eval 0) := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [coeff_sub, ← FiniteField.expand_card,
    coeff_expand (Fintype.card_pos : 0 < Fintype.card K)]
  by_cases hk0 : k = 0
  · subst k
    simp [coeff_zero_eq_eval_zero]
  · rw [if_neg (fun hd => (Nat.le_of_dvd (by omega) hd).not_gt hk)]
    simp [coeff_C, hk0]

/-- The low-degree congruence in the source's least-index argument becomes
an exact square identity. The cardinality equation records that q is odd. -/
theorem square_identity_of_block_dvd {K : Type*} [Field K] [Fintype K]
    (f r s : K[X]) (d : ℕ) (hd : 2*d+1 = Fintype.card K)
    (hr : 2*r.natDegree + f.natDegree < Fintype.card K)
    (hs : 2*s.natDegree < Fintype.card K)
    (hblock : X ^ Fintype.card K ∣ r + s * f^d) :
    r^2 * f = C (f.eval 0) * s^2 := by
  have hfirst : X ^ Fintype.card K ∣ r^2*f - s^2*f^(Fintype.card K) := by
    convert hblock.mul_right ((r - s*f^d)*f) using 1
    rw [← hd]
    ring
  have hsecond := (X_pow_card_dvd_frobenius_sub_constant f).mul_left (s^2)
  have hdiv : X ^ Fintype.card K ∣ r^2*f - C (f.eval 0)*s^2 := by
    convert dvd_add hfirst hsecond using 1
    ring
  have hdegree : (r^2*f - C (f.eval 0)*s^2).natDegree < Fintype.card K := by
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt
    · have h := natDegree_mul_le (p := r^2) (q := f)
      simp only [natDegree_pow] at h
      exact h.trans_lt hr
    · exact (natDegree_C_mul_le _ _).trans_lt (by simpa only [natDegree_pow] using hs)
  have hz := eq_zero_of_dvd_of_natDegree_lt hdiv
    (by simpa only [natDegree_X_pow] using hdegree)
  exact sub_eq_zero.mp hz

/-- A bounded coefficient block cannot be divisible by X^q unless both
coefficients vanish. The nonsquare condition is over the algebraic closure,
as in the point-count theorem, rather than only over the base field. -/
theorem block_coefficients_eq_zero {K : Type*} [Field K] [Fintype K]
    (f r s : K[X]) (d : ℕ) (hd : 2*d+1 = Fintype.card K)
    (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (hr : 2*r.natDegree + f.natDegree < Fintype.card K)
    (hs : 2*s.natDegree < Fintype.card K)
    (hblock : X ^ Fintype.card K ∣ r + s * f^d) : r = 0 ∧ s = 0 := by
  have hid := square_identity_of_block_dvd f r s d hd hr hs hblock
  have hr0 : r = 0 := by
    by_contra hr0
    apply hns
    apply isSquare_of_square_identity
      (f.map (algebraMap K (AlgebraicClosure K)))
      (r.map (algebraMap K (AlgebraicClosure K)))
      (s.map (algebraMap K (AlgebraicClosure K)))
      (algebraMap K (AlgebraicClosure K) (f.eval 0))
      ((Polynomial.map_ne_zero_iff (algebraMap K (AlgebraicClosure K)).injective).mpr hr0)
    simpa only [Polynomial.map_mul, Polynomial.map_pow, map_C] using
      congrArg (Polynomial.map (algebraMap K (AlgebraicClosure K))) hid
  refine ⟨hr0, ?_⟩
  rw [hr0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] at hid
  have hs2 : s^2 = 0 := (mul_eq_zero.mp hid.symm).resolve_left (by simpa using hf0)
  simpa using hs2

/-- A block expansion is unique when a coefficient divisible by the block
modulus must vanish. This avoids an implicit least-nonzero-index choice. -/
theorem block_sum_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (P : ℕ → R[X]) (q J : ℕ)
    (hP : ∀ j < J, X^q ∣ P j → P j = 0) :
    (∑ j ∈ Finset.range J, P j * X^(j*q)) = 0 ↔ ∀ j < J, P j = 0 := by
  constructor
  · intro h
    induction J generalizing P with
    | zero => simp
    | succ J ih =>
      have hsplit : (∑ j ∈ Finset.range (J+1), P j * X^(j*q)) =
          (∑ j ∈ Finset.range J, P (j+1) * X^(j*q)) * X^q + P 0 := by
        rw [Finset.sum_range_succ']
        simp only [zero_mul, pow_zero, mul_one]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.add_mul, one_mul, pow_add]
        ring
      rw [hsplit] at h
      have hdiv : X^q ∣ P 0 := by
        refine ⟨-(∑ j ∈ Finset.range J, P (j+1) * X^(j*q)), ?_⟩
        linear_combination h
      have hzero := hP 0 (by omega) hdiv
      rw [hzero, add_zero] at h
      have htail := (mul_eq_zero.mp h).resolve_right (pow_ne_zero q X_ne_zero)
      have hrest := ih (fun j => P (j+1)) (fun j hj => hP (j+1) (by omega)) htail
      intro j hj
      cases j with
      | zero => exact hzero
      | succ j => exact hrest j (by omega)
  · intro h
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj), zero_mul]

/-- Exact common-factor form of the already defined auxiliary polynomial. -/
theorem auxiliary_factor {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (r s : ℕ → K[X]) (ell d J : ℕ) :
    auxiliary f r s ell d J = f^ell *
      ∑ j ∈ Finset.range J, (r j + s j * f^d) * X^(j*Fintype.card K) := by
  unfold auxiliary
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- Under the source's degree and nonsquare conditions, the auxiliary
polynomial vanishes exactly when every coefficient polynomial vanishes. -/
theorem auxiliary_eq_zero_iff {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (r s : ℕ → K[X]) (ell d J : ℕ)
    (hd : 2*d+1 = Fintype.card K) (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (hr : ∀ j < J, 2*(r j).natDegree + f.natDegree < Fintype.card K)
    (hs : ∀ j < J, 2*(s j).natDegree + f.natDegree < Fintype.card K) :
    auxiliary f r s ell d J = 0 ↔ ∀ j < J, r j = 0 ∧ s j = 0 := by
  have hf : f ≠ 0 := by intro h; simp [h] at hf0
  have hblock (j : ℕ) (hj : j < J)
      (hdiv : X ^ Fintype.card K ∣ r j + s j * f^d) : r j = 0 ∧ s j = 0 :=
    block_coefficients_eq_zero f (r j) (s j) d hd hf0 hns (hr j hj)
      (by have := hs j hj; omega) hdiv
  rw [auxiliary_factor, mul_eq_zero, or_iff_right (pow_ne_zero ell hf)]
  rw [block_sum_eq_zero_iff _ _ _ (by
    intro j hj hdvd
    obtain ⟨hr0, hs0⟩ := hblock j hj hdvd
    simp [hr0, hs0])]
  constructor
  · intro h j hj
    apply hblock j hj
    rw [h j hj]
    exact dvd_zero _
  · intro h j hj
    obtain ⟨hr0, hs0⟩ := h j hj
    simp [hr0, hs0]

/-- A nonzero bounded coefficient family now supplies nonvanishing as a
proved conclusion, not as an additional auxiliary-polynomial hypothesis. -/
theorem auxiliary_ne_zero {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (r s : ℕ → K[X]) (ell d J : ℕ)
    (hd : 2*d+1 = Fintype.card K) (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (hr : ∀ j < J, 2*(r j).natDegree + f.natDegree < Fintype.card K)
    (hs : ∀ j < J, 2*(s j).natDegree + f.natDegree < Fintype.card K)
    (hne : ∃ j < J, r j ≠ 0 ∨ s j ≠ 0) : auxiliary f r s ell d J ≠ 0 := by
  intro hz
  obtain ⟨j, hj, hnonzero⟩ := hne
  have h := (auxiliary_eq_zero_iff f r s ell d J hd hf0 hns hr hs).mp hz j hj
  exact hnonzero.elim (fun hn => hn h.1) (fun hn => hn h.2)

end NField.Alignment.StepanovNonvanishing
