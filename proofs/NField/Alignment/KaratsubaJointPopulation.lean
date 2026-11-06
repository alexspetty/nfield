/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaPopulationCauchy

/-! # The actual joint reciprocal and ordinary coordinate population -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaJointPopulation
open scoped BigOperators
open KaratsubaPrimeMoment KaratsubaTupleSumRange KaratsubaBilinearReduction
  KaratsubaFiberEnergy KaratsubaPopulationCauchy KaratsubaWeightedMoment KaratsubaPhaseAlignment

abbrev Reading (Q : Finset ℕ) (m s : ℕ) := ZMod m × {j // j ∈ ordinaryTupleSums Q s}

def jointReading (Q : Finset ℕ) (m s : ℕ) (u : PrimeTuple Q s) : Reading Q m s :=
  ⟨reciprocalSum m (fun i => (u i).val),
    ⟨ordinarySum u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩⟩

theorem joint_energy_le_reciprocal (Q : Finset ℕ) (m s : ℕ) [NeZero m] :
    (∑ y : Reading Q m s, fiberCount (jointReading Q m s) y ^ 2) ≤
      ∑ t : ZMod m, fiberCount (fun u : PrimeTuple Q s =>
        reciprocalSum m (fun i => (u i).val)) t ^ 2 := by
  have h := refinement_energy_le (jointReading Q m s) Prod.fst
  exact h

def readingResponse (P Q : Finset ℕ) {m s : ℕ} [NeZero m]
    (a b : ZMod m) (y : Reading Q m s) : ℂ :=
  ∑ p : {p // p ∈ P}, phaseAlign (primeRow Q a b p.val) ^ s *
    ZMod.stdAddChar ((a * y.1) * (p.val : ZMod m)⁻¹ +
      (b * (y.2.val : ZMod m)) * (p.val : ZMod m))

theorem response_at_joint (P Q : Finset ℕ) {m s : ℕ} [NeZero m]
    (a b : ZMod m) (u : PrimeTuple Q s) :
    readingResponse P Q a b (jointReading Q m s u) = tupleResponse P Q a b u := rfl

theorem tuple_response_cauchy (P Q : Finset ℕ) {m s k : ℕ} [NeZero m] (a b : ZMod m) :
    (∑ u : PrimeTuple Q s, ‖tupleResponse P Q a b u‖ ^ k) ^ 2 ≤
      (∑ y : Reading Q m s, (fiberCount (jointReading Q m s) y : ℝ) ^ 2) *
        ∑ y : Reading Q m s, ‖readingResponse P Q a b y‖ ^ (2*k) := by
  have h := population_cauchy (jointReading Q m s) (fun y => ‖readingResponse P Q a b y‖ ^ k)
  simpa only [response_at_joint, ← pow_mul, Nat.mul_comm k 2] using h

theorem readingResponse_eq_weighted (P Q : Finset ℕ) {m s : ℕ} [NeZero m]
    (a b : ZMod m) (t : ZMod m) (j : {j // j ∈ ordinaryTupleSums Q s}) :
    readingResponse P Q a b (t,j) = weightedPrimeSum P
      (fun p => phaseAlign (primeRow Q a b p.val) ^ s *
        ZMod.stdAddChar ((b * (j.val : ZMod m)) * (p.val : ZMod m))) (t*a) := by
  simp only [readingResponse, weightedPrimeSum, AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_comm t a]
  ring

theorem reading_response_moment_le {P Q : Finset ℕ} {m s k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2*k-1) < m) (a b : ZMod m) :
    (∑ y : Reading Q m s, ‖readingResponse P Q a b y‖ ^ (2*k)) ≤
      ((ordinaryTupleSums Q s).card : ℝ) *
        ((m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k))) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ ≤ ∑ _j : {j // j ∈ ordinaryTupleSums Q s},
        (m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k)) := by
      apply Finset.sum_le_sum
      intro j _
      simp_rw [readingResponse_eq_weighted]
      apply weighted_prime_norm_moment_le hX hprime hcop hlower hupper hsize
      intro p
      simpa only [norm_mul, AddChar.norm_apply, mul_one] using
        norm_phaseAlign_power_le (primeRow Q a b p.val) s
    _ = _ := by simp

theorem tuple_response_moment_bound {P Q : Finset ℕ} {m s k L U : ℕ}
    [NeZero m] {X Y : ℝ} (hs : 0 < s)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime) (hPc : ∀ p ∈ P, p.Coprime m)
    (hPl : ∀ p ∈ P, k < p) (hPu : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hPs : (k : ℝ)*X^(2*k-1) < m)
    (hY : 1 ≤ Y) (hQ : ∀ q ∈ Q, q.Prime) (hQc : ∀ q ∈ Q, q.Coprime m)
    (hQl : ∀ q ∈ Q, s < q) (hQu : ∀ q ∈ Q, (q : ℝ) ≤ Y)
    (hQs : (s : ℝ)*Y^(2*s-1) < m) (a b : ZMod m) :
    (∑ u : PrimeTuple Q s, ‖tupleResponse P Q a b u‖ ^ k) ^ 2 ≤
      ((s.factorial * Q.card ^ s : ℕ) : ℝ) *
        (((s*(U-L) : ℕ) : ℝ) *
          ((m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k)))) := by
  have hj : (∑ y : Reading Q m s, (fiberCount (jointReading Q m s) y : ℝ) ^ 2) ≤
      ((s.factorial * Q.card ^ s : ℕ) : ℝ) := by
    exact_mod_cast (joint_energy_le_reciprocal Q m s).trans
      (reciprocal_energy_le hY hQ hQc hQl hQu hQs)
  have hr := reading_response_moment_le (Q := Q) (s := s) hX hP hPc hPl hPu hPs a b
  have hb : ((ordinaryTupleSums Q s).card : ℝ) ≤ ((s*(U-L) : ℕ) : ℝ) := by
    exact_mod_cast ordinaryTupleSums_card_le hs hL hU
  have hr' := hr.trans (mul_le_mul_of_nonneg_right hb (by positivity))
  exact (tuple_response_cauchy P Q a b).trans
    (mul_le_mul hj hr' (Finset.sum_nonneg fun y _ => pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))

/-- Finite bilinear power bound with both actual prime populations and the frequency gcd. -/
theorem bilinear_power_bound {P Q : Finset ℕ} {m s k L U : ℕ}
    [NeZero m] {X Y : ℝ} (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime) (hPc : ∀ p ∈ P, p.Coprime m)
    (hPl : ∀ p ∈ P, k < p) (hPu : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hPs : (k : ℝ)*X^(2*k-1) < m)
    (hY : 1 ≤ Y) (hQ : ∀ q ∈ Q, q.Prime) (hQc : ∀ q ∈ Q, q.Coprime m)
    (hQl : ∀ q ∈ Q, s < q) (hQu : ∀ q ∈ Q, (q : ℝ) ≤ Y)
    (hQs : (s : ℝ)*Y^(2*s-1) < m) (a b : ZMod m) :
    ‖bilinearPrimeSum P Q a b‖ ^ (2*s*k) ≤
      (((P.card : ℝ) ^ (s-1)) ^ k * ((Q.card : ℝ) ^ s) ^ (k-1)) ^ 2 *
        (((s.factorial * Q.card ^ s : ℕ) : ℝ) *
          (((s*(U-L) : ℕ) : ℝ) *
            ((m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k))))) := by
  have h := pow_le_pow_left₀ (by positivity) (two_holder_steps P Q a b hs hk) 2
  rw [← pow_mul, mul_pow] at h
  have ht := tuple_response_moment_bound (by omega : 0 < s) hL hU
    hX hP hPc hPl hPu hPs hY hQ hQc hQl hQu hQs a b
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ (((P.card : ℝ) ^ (s-1)) ^ k * ((Q.card : ℝ) ^ s) ^ (k-1)) ^ 2 by positivity)
  have he : s*k*2 = 2*s*k := by ring
  rw [he] at h
  exact h.trans hm

end NField.Alignment.KaratsubaJointPopulation
