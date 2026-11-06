/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalTuples
import NField.Alignment.KorolevLemmaA

/-! # Canonical tuple sums for the actual selected representations and their failure bound -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalSelectedSum
open Filter KorolevCanonicalTuples KorolevSquarefreeRepresentation
  KorolevSourceWindowCount KorolevPrimeSeparation
open scoped Topology BigOperators Classical

/-- The generic represented set is exactly the paper's selected representation predicate. -/
theorem represented_eq_selected {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q) {x : ℝ} (hx : 0 ≤ Real.log x) :
    represented P Q ⌊Real.log x⌋₊ ⌊x⌋₊ =
      (Finset.Icc 1 ⌊x⌋₊).filter (HasSelectedRepresentation x P Q) := by
  classical
  ext n
  simp only [represented, Finset.mem_filter, HasSelectedRepresentation]
  constructor
  · rintro ⟨hnrange,l,p,q,h,hl,hL,hp,hq,hh,hsq,hform⟩
    have hlR : (l : ℝ) ≤ Real.log x :=
      (by exact_mod_cast hL : (l : ℝ) ≤ (⌊Real.log x⌋₊ : ℝ)).trans (Nat.floor_le hx)
    have hne : p ≠ q := by
      intro he
      apply Finset.disjoint_left.mp hdis hp
      simpa only [he] using hq
    exact ⟨hnrange,l,p,q,h,by omega,hlR,hh,hP p hp,hQ q hq,hne,hp,hq,hform,hsq⟩
  · rintro ⟨hnrange,l,p,q,h,hl,hL,hh,_,_,_,hp,hq,hform,hsq⟩
    exact ⟨hnrange,l,p,q,h,by omega,Nat.le_floor hL,hp,hq,hh,hsq,hform⟩

/-- The literal selected-representation sum equals the multiplicity-free canonical tuple sum. -/
theorem sum_selected {G : Type*} [AddCommMonoid G] {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    {x : ℝ} (hx : 0 ≤ Real.log x) (f : ℕ → G) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (HasSelectedRepresentation x P Q), f n) =
      ∑ t ∈ tuples P Q ⌊Real.log x⌋₊ ⌊x⌋₊, f (value t) := by
  classical
  rw [← represented_eq_selected hP hQ hdis hx]
  exact sum_represented hP hQ hdis _ _ f

/-- The selected-representation sum on units has the same exact canonical form. -/
theorem sum_coprime_selected {G : Type*} [AddCommMonoid G] {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    {x : ℝ} (hx : 0 ≤ Real.log x) (m : ℕ) (f : ℕ → G) :
    (∑ n ∈ ((Finset.Icc 1 ⌊x⌋₊).filter (HasSelectedRepresentation x P Q)).filter
      (fun n => n.Coprime m), f n) =
        ∑ t ∈ (tuples P Q ⌊Real.log x⌋₊ ⌊x⌋₊).filter (fun t => (value t).Coprime m), f (value t) := by
  classical
  rw [← represented_eq_selected hP hQ hdis hx]
  exact sum_coprime_represented hP hQ hdis _ _ m f

def failure (x : ℝ) (P Q : Finset ℕ) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Coprime m ∧ ¬HasSelectedRepresentation x P Q n)

/-- Only the actual failure set is bounded by the exception union; no exception predicate enters the tuple sum. -/
theorem failure_subset_exception {x : ℝ} (hx : 0 ≤ x) {P Q : Finset ℕ}
    (hprimes : ∀ p ∈ P, ∀ q ∈ Q, p.Prime ∧ q.Prime ∧ Real.log x < (q : ℝ) ∧ q < p)
    (m : ℕ) : failure x P Q m ⊆ (exceptionSet x P Q).filter (fun n => n.Coprime m) := by
  classical
  intro n hn
  obtain ⟨hnrange, hcop, hnot⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnpos, hnupper⟩ := Finset.mem_Icc.mp hnrange
  have hnR : (n : ℝ) ≤ x :=
    (by exact_mod_cast hnupper : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx)
  refine Finset.mem_filter.mpr ⟨?_, hcop⟩
  by_contra hout
  exact hnot (representation_outside_exception hx hprimes (by omega) hnR hout)

/-- The actual omitted selected representations have the already-proved source gamma decay. -/
theorem eventual_failure_count (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ M : ℝ in atTop, ∀ x : ℝ,
      Real.exp ((Real.log M)^(4/5 : ℝ)*(Real.log (Real.log M))^5) ≤ x →
      x ≤ M^(4/7 : ℝ) → ∀ m : ℕ,
        ((failure x (sourcePPrimes C M x) (sourceQPrimes C M x) m).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-sourceGamma C M x) := by
  obtain ⟨K,hK,hbound⟩ := KorolevLemmaA.eventual_source_representation C hC
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound, eventual_source_prime_properties C hC] with M hb hp x hlo hhi m
  have hx : 0 ≤ x := (Real.exp_pos _).le.trans hlo
  have hsub := failure_subset_exception hx (hp x hlo hhi) m
  have hc : ((failure x (sourcePPrimes C M x) (sourceQPrimes C M x) m).card : ℝ) ≤
      (((exceptionSet x (sourcePPrimes C M x) (sourceQPrimes C M x)).filter
        (fun n => n.Coprime m)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (hb x hlo hhi m).1

/-- Exact prefix split into the canonical tuple sum and the actual omitted integers. -/
theorem sum_all_eq_canonical_add_failure {G : Type*} [AddCommMonoid G] {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    {x : ℝ} (hx : 0 ≤ Real.log x) (m : ℕ) (f : ℕ → G) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Coprime m), f n) =
      (∑ t ∈ (tuples P Q ⌊Real.log x⌋₊ ⌊x⌋₊).filter (fun t => (value t).Coprime m), f (value t)) +
        ∑ n ∈ failure x P Q m, f n := by
  classical
  have hg : ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Coprime m)).filter (HasSelectedRepresentation x P Q) =
      ((Finset.Icc 1 ⌊x⌋₊).filter (HasSelectedRepresentation x P Q)).filter (fun n => n.Coprime m) := by
    ext n
    simp only [Finset.mem_filter, and_assoc, and_comm]
  have hb : ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Coprime m)).filter
      (fun n => ¬HasSelectedRepresentation x P Q n) = failure x P Q m := by
    ext n
    simp only [failure, Finset.mem_filter, and_assoc]
  have h := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n.Coprime m))
    (HasSelectedRepresentation x P Q) f
  rw [hg, hb, sum_coprime_selected hP hQ hdis hx m f] at h
  exact h.symm

/-- The omitted part costs at most its actual population times a pointwise norm bound. -/
theorem norm_failure_sum_le {G : Type*} [SeminormedAddCommGroup G]
    (x : ℝ) (P Q : Finset ℕ) (m : ℕ) (f : ℕ → G) (B : ℝ)
    (hf : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖ ≤ B) :
    ‖∑ n ∈ failure x P Q m, f n‖ ≤ ((failure x P Q m).card : ℝ)*B := by
  classical
  calc
    _ ≤ ∑ n ∈ failure x P Q m, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ failure x P Q m, B :=
      Finset.sum_le_sum (fun n hn => hf n (Finset.mem_filter.mp hn).1)
    _ = _ := by simp

end NField.Alignment.KorolevCanonicalSelectedSum
