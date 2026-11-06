/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevCanonicalPrimeFactors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact finite sums over canonical selected-factor tuples -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalTuples
open KorolevCanonicalPrimeFactors
open scoped BigOperators

/-- The canonical prime cutoff excludes the distinguished prime from the residual factor. -/
theorem cutoff_not_dvd {P : Finset ℕ} {h p : ℕ} (hp : p ∈ P) (hc : Cutoff P h p) : ¬p ∣ h :=
  fun hd => (Nat.lt_irrefl p) (hc p hp hd)

/-- Squarefreeness of the residual factor is sufficient under the two separate canonical cutoffs. -/
theorem squarefree_product {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    {p q h : ℕ} (hp : p ∈ P) (hq : q ∈ Q) (hh : Squarefree h)
    (hcutP : Cutoff P h p) (hcutQ : Cutoff Q h q) : Squarefree (p*q*h) := by
  have hpp := hP p hp
  have hqp := hQ q hq
  have hne : p ≠ q := by
    intro he
    apply Finset.disjoint_left.mp hdis hp
    simpa only [he] using hq
  have hpq := (Nat.coprime_primes hpp hqp).mpr hne
  have hph := hpp.coprime_iff_not_dvd.mpr (cutoff_not_dvd hp hcutP)
  have hqh := hqp.coprime_iff_not_dvd.mpr (cutoff_not_dvd hq hcutQ)
  exact (Nat.squarefree_mul (hph.mul_left hqh)).mpr
    ⟨(Nat.squarefree_mul hpq).mpr ⟨hpp.squarefree, hqp.squarefree⟩, hh⟩

abbrev Tuple := ℕ × ℕ × ℕ × ℕ

def value (t : Tuple) : ℕ := t.1^2*t.2.1*t.2.2.1*t.2.2.2

def tuples (P Q : Finset ℕ) (L X : ℕ) : Finset Tuple := by
  classical
  exact ((Finset.Icc 1 L).product (P.product (Q.product (Finset.Icc 1 X)))).filter
    (fun t => Squarefree t.2.2.2 ∧ Cutoff P t.2.2.2 t.2.1 ∧
      Cutoff Q t.2.2.2 t.2.2.1 ∧ value t ≤ X)

def represented (P Q : Finset ℕ) (L X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (fun n => ∃ l p q h : ℕ,
    1 ≤ l ∧ l ≤ L ∧ p ∈ P ∧ q ∈ Q ∧ 0 < h ∧ Squarefree (p*q*h) ∧ n = l^2*p*q*h)

theorem mem_tuples (P Q : Finset ℕ) (L X l p q h : ℕ) :
    (l,p,q,h) ∈ tuples P Q L X ↔
      1 ≤ l ∧ l ≤ L ∧ p ∈ P ∧ q ∈ Q ∧ 1 ≤ h ∧ h ≤ X ∧ Squarefree h ∧
        Cutoff P h p ∧ Cutoff Q h q ∧ l^2*p*q*h ≤ X := by
  classical
  simp [tuples, value, and_assoc]

/-- Unit restrictions split into separate restrictions on the four positive factors. -/
theorem value_coprime_iff (t : Tuple) (m : ℕ) :
    (value t).Coprime m ↔ t.1.Coprime m ∧ t.2.1.Coprime m ∧
      t.2.2.1.Coprime m ∧ t.2.2.2.Coprime m := by
  simp only [value, Nat.coprime_mul_iff_left,
    Nat.coprime_pow_left_iff (by norm_num : 0 < 2), and_assoc]

/-- Canonical tuples represent each integer at most once. -/
theorem value_injOn {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q) (L X : ℕ) :
    Set.InjOn value (tuples P Q L X : Set Tuple) := by
  rintro ⟨l,p,q,h⟩ ht ⟨l',p',q',h'⟩ hu he
  obtain ⟨hl, _, hp, hq, _, _, hh, hcP, hcQ, _⟩ := (mem_tuples P Q L X l p q h).mp ht
  obtain ⟨hl', _, hp', hq', _, _, hh', hcP', hcQ', _⟩ := (mem_tuples P Q L X l' p' q' h').mp hu
  change l^2*p*q*h = l'^2*p'*q'*h' at he
  obtain ⟨hlEq, hpEq, hqEq, hhEq⟩ := canonical_representation_unique hP hQ hdis
    (by omega : 0 < l) (by omega : 0 < l') hp hq hp' hq'
    (squarefree_product hP hQ hdis hp hq hh hcP hcQ)
    (squarefree_product hP hQ hdis hp' hq' hh' hcP' hcQ') rfl he hcP hcQ hcP' hcQ'
  exact Prod.ext hlEq (Prod.ext hpEq (Prod.ext hqEq hhEq))

/-- The canonical tuples have exactly the actually represented integers as their image. -/
theorem image_tuples {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q) (L X : ℕ) :
    (tuples P Q L X).image value = represented P Q L X := by
  classical
  ext n
  constructor
  · rintro hn
    obtain ⟨⟨l,p,q,h⟩, ht, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hl, hL, hp, hq, hh, _, hsq, hcP, hcQ, hcap⟩ := (mem_tuples P Q L X l p q h).mp ht
    have hpos : 0 < l^2*p*q*h := Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (pow_pos (by omega : 0 < l) 2) (hP p hp).pos) (hQ q hq).pos)
      (by omega : 0 < h)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by exact hpos, hcap⟩, ?_⟩
    exact ⟨l,p,q,h,hl,hL,hp,hq,by omega,squarefree_product hP hQ hdis hp hq hsq hcP hcQ,rfl⟩
  · intro hn
    obtain ⟨hnrange, l,p,q,h,hl,hL,hp,hq,hh,hsq,hform⟩ := Finset.mem_filter.mp hn
    have hPn : (P.filter (fun r => r ∣ p*q*h)).Nonempty :=
      ⟨p, Finset.mem_filter.mpr ⟨hp, ⟨q*h, by ring⟩⟩⟩
    have hQn : (Q.filter (fun r => r ∣ p*q*h)).Nonempty :=
      ⟨q, Finset.mem_filter.mpr ⟨hq, ⟨p*h, by ring⟩⟩⟩
    have ha : 0 < p*q*h := Nat.mul_pos (Nat.mul_pos (hP p hp).pos (hQ q hq).pos) hh
    obtain ⟨p',q',h',hp',hq',hh',hsqh',hcore,hcP,hcQ⟩ :=
      exists_canonical_factors hP hQ hdis ha hsq hPn hQn
    have hval : value (l,p',q',h') = n := by
      change l^2*p'*q'*h' = n
      calc
        _ = l^2*(p'*q'*h') := by ring
        _ = l^2*(p*q*h) := by rw [hcore]
        _ = n := by rw [hform]; ring
    have hA : 0 < l^2*p'*q' :=
      Nat.mul_pos (Nat.mul_pos (pow_pos (by omega : 0 < l) 2) (hP p' hp').pos) (hQ q' hq').pos
    have hhle : h' ≤ value (l,p',q',h') := by
      exact (by simpa [value] using Nat.mul_le_mul_right h' (Nat.succ_le_of_lt hA))
    have hhX : h' ≤ X := by rw [hval] at hhle; exact hhle.trans (Finset.mem_Icc.mp hnrange).2
    apply Finset.mem_image.mpr
    refine ⟨(l,p',q',h'), (mem_tuples P Q L X l p' q' h').mpr ?_, hval⟩
    exact ⟨hl,hL,hp',hq',by omega,hhX,hsqh',hcP,hcQ,by rw [← hval] at hnrange; exact (Finset.mem_Icc.mp hnrange).2⟩

/-- The exact finite canonical sum has no representation multiplicity. -/
theorem sum_represented {G : Type*} [AddCommMonoid G] {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    (L X : ℕ) (f : ℕ → G) :
    (∑ n ∈ represented P Q L X, f n) = ∑ t ∈ tuples P Q L X, f (value t) := by
  classical
  rw [← image_tuples hP hQ hdis L X, Finset.sum_image]
  exact fun t ht u hu he => value_injOn hP hQ hdis L X ht hu he

/-- Restricting to units of the modulus preserves the exact canonical sum identity. -/
theorem sum_coprime_represented {G : Type*} [AddCommMonoid G] {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    (L X m : ℕ) (f : ℕ → G) :
    (∑ n ∈ (represented P Q L X).filter (fun n => n.Coprime m), f n) =
      ∑ t ∈ (tuples P Q L X).filter (fun t => (value t).Coprime m), f (value t) := by
  classical
  simpa only [Finset.sum_filter] using
    sum_represented hP hQ hdis L X (fun n => if n.Coprime m then f n else 0)

end NField.Alignment.KorolevCanonicalTuples
