/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Targets
/-! # The actual incoming and surviving factors of each forest denominator

The split uses the manuscript's prime-power product. Mathlib's product,
prime-divisor and coprime divisor-count identities retain every exponent.
-/

noncomputable section

namespace NField.ResetForests.AbsoluteForestWork

open scoped BigOperators

def incomingPart (N k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors.filter (fun p => p ∣ N), p^(k.factorization p)

theorem incoming_rough_product (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    incomingPart N k*Core.roughPart N k=k := by
  unfold incomingPart Core.roughPart
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization hk).symm

theorem incoming_rough_positive (N : ℕ) {k : ℕ} (hk : 0 < k) :
    0 < incomingPart N k ∧ 0 < Core.roughPart N k := by
  have he := incoming_rough_product N hk.ne'
  exact ⟨Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega),
    Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)⟩

theorem incoming_part_dvd (N : ℕ) {k : ℕ} (hk : k ≠ 0) : incomingPart N k ∣ k :=
  ⟨Core.roughPart N k, (incoming_rough_product N hk).symm⟩

theorem rough_part_dvd (N : ℕ) {k : ℕ} (hk : k ≠ 0) : Core.roughPart N k ∣ k :=
  ⟨incomingPart N k, (incoming_rough_product N hk).symm.trans (mul_comm _ _)⟩

theorem prime_dvd_filtered_factor_product {q k : ℕ} (hq : q.Prime)
    (P : ℕ → Prop) [DecidablePred P]
    (hdiv : q ∣ ∏ p ∈ k.primeFactors.filter P, p^(k.factorization p)) : P q := by
  obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff _).mp hdiv
  have hp' := Finset.mem_filter.mp hp
  have he : q=p := (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hp'.1)).mp
    (hq.dvd_of_dvd_pow hqp)
  simpa only [he] using hp'.2

theorem incoming_prime_dvd_base {q N k : ℕ} (hq : q.Prime)
    (hdiv : q ∣ incomingPart N k) : q ∣ N :=
  prime_dvd_filtered_factor_product hq (fun p => p ∣ N) hdiv

theorem rough_prime_not_dvd_base {q N k : ℕ} (hq : q.Prime)
    (hdiv : q ∣ Core.roughPart N k) : ¬q ∣ N :=
  prime_dvd_filtered_factor_product hq (fun p => ¬p ∣ N) hdiv

theorem incoming_rough_coprime (N k : ℕ) :
    (incomingPart N k).Coprime (Core.roughPart N k) := by
  by_contra hc
  obtain ⟨q, hq, hi, hr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  exact rough_prime_not_dvd_base hq hr (incoming_prime_dvd_base hq hi)

theorem rough_part_coprime_base (N k : ℕ) : (Core.roughPart N k).Coprime N := by
  by_contra hc
  obtain ⟨q, hq, hr, hN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  exact rough_prime_not_dvd_base hq hr hN

theorem incoming_part_supported_cutoff {N k : ℕ} (hN : N ≠ 0)
    (hk : 0 < k) (hkN : k ≤ N) : incomingPart N k ∈ Core.supportedCutoff N := by
  apply (Core.supported_cutoff_mem hN).mpr
  refine ⟨(incoming_rough_positive N hk).1,
    (Nat.le_of_dvd hk (incoming_part_dvd N hk.ne')).trans hkN, ?_⟩
  intro q hq hdiv
  exact incoming_prime_dvd_base hq hdiv

theorem forest_divisor_count_factor (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    k.divisors.card=(incomingPart N k).divisors.card*(Core.roughPart N k).divisors.card := by
  nth_rw 1 [← incoming_rough_product N hk]
  exact (incoming_rough_coprime N k).card_divisors_mul

theorem forest_factor_pair_injective (N : ℕ) :
    Set.InjOn (fun k => (incomingPart N k, Core.roughPart N k)) {k : ℕ | k ≠ 0} := by
  intro a ha b hb he
  have hfirst := congrArg Prod.fst he
  have hsecond := congrArg Prod.snd he
  change incomingPart N a=incomingPart N b at hfirst
  change Core.roughPart N a=Core.roughPart N b at hsecond
  calc
    a=incomingPart N a*Core.roughPart N a := (incoming_rough_product N ha).symm
    _=incomingPart N b*Core.roughPart N b := by rw [hfirst, hsecond]
    _=b := incoming_rough_product N hb

def forestClocks (N D : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter (fun k => Core.roughPart N k ∣ D)

theorem forest_factor_pair_mem {N D k : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hk : k ∈ forestClocks N D) :
    (incomingPart N k, Core.roughPart N k) ∈ (Core.supportedCutoff N) ×ˢ D.divisors := by
  obtain ⟨hkI, hd⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hkI
  exact Finset.mem_product.mpr ⟨incoming_part_supported_cutoff hN (by omega) hkN,
    Nat.mem_divisors.mpr ⟨hd, hD⟩⟩

theorem forest_divisor_budget {N D : ℕ} (hN : 0 < N) (hD : 0 < D) :
    (∑ k ∈ forestClocks N D, (k.divisors.card : ℝ)) ≤
      Core.incomingDivisorBudget N*(Core.tripleDivisorCount D : ℝ) := by
  classical
  let φ := fun k => (incomingPart N k, Core.roughPart N k)
  let f := fun z : ℕ × ℕ => (z.1.divisors.card : ℝ)*(z.2.divisors.card : ℝ)
  have hinj : Set.InjOn φ (forestClocks N D) := by
    intro a ha b hb he
    have ha0 : a ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1; omega
    have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1; omega
    exact forest_factor_pair_injective N ha0 hb0 he
  have hsub : (forestClocks N D).image φ ⊆ (Core.supportedCutoff N) ×ˢ D.divisors := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact forest_factor_pair_mem hN.ne' hD.ne' hk
  calc
    _ = ∑ z ∈ (forestClocks N D).image φ, f z := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1; omega
      change (k.divisors.card : ℝ)=(incomingPart N k).divisors.card*(Core.roughPart N k).divisors.card
      exact_mod_cast forest_divisor_count_factor N hk0
    _ ≤ ∑ z ∈ (Core.supportedCutoff N) ×ˢ D.divisors, f z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by dsimp [f]; positivity)
    _ = _ := by
      unfold Core.incomingDivisorBudget Core.tripleDivisorCount f
      push_cast
      rw [Finset.sum_product]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

end NField.ResetForests.AbsoluteForestWork
