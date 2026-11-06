/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KaratsubaNormalizedBilinear

/-! # Bilinear bounds for prime cutoffs relative to their full populations -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KaratsubaSubsetBilinear
open scoped BigOperators

/-- Restricting either prime family retains the full-family power bound. -/
theorem subset_power_bound {P₀ Q₀ P Q : Finset ℕ} {m s k L U : ℕ}
    [NeZero m] {X Y : ℝ} (hPsub : P₀ ⊆ P) (hQsub : Q₀ ⊆ Q) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime) (hPc : ∀ p ∈ P, p.Coprime m)
    (hPl : ∀ p ∈ P, k < p) (hPu : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hPs : (k : ℝ)*X^(2*k-1) < m)
    (hY : 1 ≤ Y) (hQ : ∀ q ∈ Q, q.Prime) (hQc : ∀ q ∈ Q, q.Coprime m)
    (hQl : ∀ q ∈ Q, s < q) (hQu : ∀ q ∈ Q, (q : ℝ) ≤ Y)
    (hQs : (s : ℝ)*Y^(2*s-1) < m) (a b : ZMod m) :
    ‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ ^ (2*s*k) ≤
      (((P.card : ℝ) ^ (s-1)) ^ k * ((Q.card : ℝ) ^ s) ^ (k-1)) ^ 2 *
        (((s.factorial * Q.card ^ s : ℕ) : ℝ) *
          (((s*(U-L) : ℕ) : ℝ) *
            ((m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k))))) := by
  have h := KaratsubaJointPopulation.bilinear_power_bound (P := P₀) (Q := Q₀) hs hk
    (fun q hq => hL q (hQsub hq)) (fun q hq => hU q (hQsub hq))
    hX (fun p hp => hP p (hPsub hp)) (fun p hp => hPc p (hPsub hp))
    (fun p hp => hPl p (hPsub hp)) (fun p hp => hPu p (hPsub hp)) hPs
    hY (fun q hq => hQ q (hQsub hq)) (fun q hq => hQc q (hQsub hq))
    (fun q hq => hQl q (hQsub hq)) (fun q hq => hQu q (hQsub hq)) hQs a b
  apply h.trans
  have hpN := Finset.card_le_card hPsub
  have hqN := Finset.card_le_card hQsub
  have hp : (P₀.card : ℝ) ≤ P.card := by exact_mod_cast hpN
  have hq : (Q₀.card : ℝ) ≤ Q.card := by exact_mod_cast hqN
  simp only [Nat.cast_mul, Nat.cast_pow]
  gcongr

/-- Prime cutoffs are normalized by the full populations; the cutoffs may be empty. -/
theorem normalized_subset_power_bound {P₀ Q₀ P Q : Finset ℕ} {m s k L U : ℕ}
    [NeZero m] {X Y : ℝ} (hPsub : P₀ ⊆ P) (hQsub : Q₀ ⊆ Q) (hs : 1 ≤ s) (hk : 1 ≤ k) (hPn : P.Nonempty) (hQn : Q.Nonempty)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime) (hPc : ∀ p ∈ P, p.Coprime m)
    (hPl : ∀ p ∈ P, k < p) (hPu : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hPs : (k : ℝ)*X^(2*k-1) < m)
    (hY : 1 ≤ Y) (hQ : ∀ q ∈ Q, q.Prime) (hQc : ∀ q ∈ Q, q.Coprime m)
    (hQl : ∀ q ∈ Q, s < q) (hQu : ∀ q ∈ Q, (q : ℝ) ≤ Y)
    (hQs : (s : ℝ)*Y^(2*s-1) < m) (a b : ZMod m) :
    (‖KaratsubaBilinearReduction.bilinearPrimeSum P₀ Q₀ a b‖ /
      ((P.card : ℝ)*(Q.card : ℝ)))^(2*s*k) ≤
        ((s.factorial : ℝ)*((s*(U-L) : ℕ) : ℝ)*(m : ℝ)*
          (a.val.gcd m : ℝ)*(k.factorial : ℝ)) /
            ((P.card : ℝ)^k*(Q.card : ℝ)^s) := by
  have raw := subset_power_bound hPsub hQsub hs hk hL hU
    hX hP hPc hPl hPu hPs hY hQ hQc hQl hQu hQs a b
  have hA : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hPn
  have hB : (0 : ℝ) < Q.card := by exact_mod_cast Finset.card_pos.mpr hQn
  apply KaratsubaNormalizedBilinear.normalized_bound_of_power_bound hA hB hs hk
  simpa only [Nat.cast_mul, Nat.cast_pow] using raw

def weightedBilinearSum (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (A B : ℕ → ℂ) (a b : ZMod m) : ℂ :=
  ∑ p ∈ P, ∑ q ∈ Q, A p*B q*
    ZMod.stdAddChar (a*(p : ZMod m)⁻¹*(q : ZMod m)⁻¹+b*(p : ZMod m)*(q : ZMod m))

/-- Separable indicator weights exactly encode the two independent prime cutoffs. -/
theorem filtered_eq_indicator (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (pKeep qKeep : ℕ → Prop) [DecidablePred pKeep] [DecidablePred qKeep]
    (a b : ZMod m) :
    KaratsubaBilinearReduction.bilinearPrimeSum (P.filter pKeep) (Q.filter qKeep) a b =
      weightedBilinearSum P Q (fun p => if pKeep p then 1 else 0)
        (fun q => if qKeep q then 1 else 0) a b := by
  unfold KaratsubaBilinearReduction.bilinearPrimeSum KaratsubaBilinearReduction.primeRow
    KaratsubaWeightedMoment.mixedPrimeSum weightedBilinearSum
  have hsum (S : Finset ℕ) (f : ℕ → ℂ) :
      (∑ x : {x // x ∈ S}, f x.val) = ∑ x ∈ S, f x :=
    (Finset.sum_subtype S (fun _ => Iff.rfl) f).symm
  let phase : ℕ → ℕ → ℂ := fun p q =>
    ZMod.stdAddChar (a*(p : ZMod m)⁻¹*(q : ZMod m)⁻¹+b*(p : ZMod m)*(q : ZMod m))
  change (∑ p : {p // p ∈ P.filter pKeep}, ∑ q : {q // q ∈ Q.filter qKeep}, phase p.val q.val) =
    ∑ p ∈ P, ∑ q ∈ Q, ((if pKeep p then 1 else 0)*(if qKeep q then 1 else 0))*phase p q
  have hout : (∑ p : {p // p ∈ P.filter pKeep}, ∑ q : {q // q ∈ Q.filter qKeep}, phase p.val q.val) =
      ∑ p ∈ P.filter pKeep, ∑ q ∈ Q.filter qKeep, phase p q := by
    calc
      _ = ∑ p ∈ P.filter pKeep, ∑ q : {q // q ∈ Q.filter qKeep}, phase p q.val :=
        hsum (P.filter pKeep) (fun p => ∑ q : {q // q ∈ Q.filter qKeep}, phase p q.val)
      _ = _ := Finset.sum_congr rfl (fun p _ => hsum (Q.filter qKeep) (phase p))
  rw [hout]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpk : pKeep p
  · simp only [hpk, ite_true, one_mul]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqk : qKeep q <;> simp [hqk]
  · simp [hpk]

/-- Independent prime-membership cutoffs retain the full-population normalized bound with no extra factor. -/
theorem indicator_normalized_power_bound {P Q : Finset ℕ} {m s k L U : ℕ}
    [NeZero m] {X Y : ℝ} (pKeep qKeep : ℕ → Prop) [DecidablePred pKeep] [DecidablePred qKeep] (hs : 1 ≤ s) (hk : 1 ≤ k) (hPn : P.Nonempty) (hQn : Q.Nonempty)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime) (hPc : ∀ p ∈ P, p.Coprime m)
    (hPl : ∀ p ∈ P, k < p) (hPu : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hPs : (k : ℝ)*X^(2*k-1) < m)
    (hY : 1 ≤ Y) (hQ : ∀ q ∈ Q, q.Prime) (hQc : ∀ q ∈ Q, q.Coprime m)
    (hQl : ∀ q ∈ Q, s < q) (hQu : ∀ q ∈ Q, (q : ℝ) ≤ Y)
    (hQs : (s : ℝ)*Y^(2*s-1) < m) (a b : ZMod m) :
    (‖weightedBilinearSum P Q (fun p => if pKeep p then 1 else 0)
        (fun q => if qKeep q then 1 else 0) a b‖ /
      ((P.card : ℝ)*(Q.card : ℝ)))^(2*s*k) ≤
        ((s.factorial : ℝ)*((s*(U-L) : ℕ) : ℝ)*(m : ℝ)*
          (a.val.gcd m : ℝ)*(k.factorial : ℝ)) /
            ((P.card : ℝ)^k*(Q.card : ℝ)^s) := by
  rw [← filtered_eq_indicator P Q pKeep qKeep a b]
  exact normalized_subset_power_bound (Finset.filter_subset pKeep P) (Finset.filter_subset qKeep Q)
    hs hk hPn hQn hL hU hX hP hPc hPl hPu hPs hY hQ hQc hQl hQu hQs a b

end NField.Alignment.KaratsubaSubsetBilinear
