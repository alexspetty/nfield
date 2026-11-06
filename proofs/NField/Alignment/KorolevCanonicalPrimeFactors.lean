/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Max

/-! # Canonical selected prime factors of a fixed squarefree integer -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevCanonicalPrimeFactors

/-- For fixed residual h, the canonical largest-factor condition is a separate prime cutoff. -/
def Cutoff (P : Finset ℕ) (h p : ℕ) : Prop := ∀ r ∈ P, r ∣ h → r < p

/-- A prime selected from the first family is at most its canonical representative. -/
theorem selected_factor_le {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    {n p q h r : ℕ} (hp : p ∈ P) (hq : q ∈ Q)
    (hform : n = p*q*h) (hcut : Cutoff P h p) (hr : r ∈ P) (hrn : r ∣ n) : r ≤ p := by
  have hrPrime := hP r hr
  rw [hform] at hrn
  rcases hrPrime.dvd_mul.mp hrn with hrpq | hrh
  · rcases hrPrime.dvd_mul.mp hrpq with hrp | hrq
    · have he := ((hP p hp).dvd_iff_eq hrPrime.ne_one).mp hrp
      omega
    · have he := ((hQ q hq).dvd_iff_eq hrPrime.ne_one).mp hrq
      have hrQ : r ∈ Q := by simpa only [he] using hq
      exact False.elim (Finset.disjoint_left.mp hdis hr hrQ)
  · exact (hcut r hr hrh).le

/-- Two canonical prime/residual triples for the same integer coincide. -/
theorem canonical_factors_unique {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    {n p q h p' q' h' : ℕ} (hp : p ∈ P) (hq : q ∈ Q) (hp' : p' ∈ P) (hq' : q' ∈ Q)
    (hform : n = p*q*h) (hform' : n = p'*q'*h')
    (hcutP : Cutoff P h p) (hcutQ : Cutoff Q h q)
    (hcutP' : Cutoff P h' p') (hcutQ' : Cutoff Q h' q') : p = p' ∧ q = q' ∧ h = h' := by
  have hpd : p ∣ n := ⟨q*h, by rw [hform]; ring⟩
  have hp'd : p' ∣ n := ⟨q'*h', by rw [hform']; ring⟩
  have hpEq := le_antisymm
    (selected_factor_le hP hQ hdis hp' hq' hform' hcutP' hp hpd)
    (selected_factor_le hP hQ hdis hp hq hform hcutP hp' hp'd)
  have hqd : q ∣ n := ⟨p*h, by rw [hform]; ring⟩
  have hq'd : q' ∣ n := ⟨p'*h', by rw [hform']; ring⟩
  have hswap : n = q*p*h := by rw [hform]; ring
  have hswap' : n = q'*p'*h' := by rw [hform']; ring
  have hqEq := le_antisymm
    (selected_factor_le hQ hP hdis.symm hq' hp' hswap' hcutQ' hq hqd)
    (selected_factor_le hQ hP hdis.symm hq hp hswap hcutQ hq' hq'd)
  refine ⟨hpEq, hqEq, ?_⟩
  rw [hpEq, hqEq] at hform
  have hh : p'*q'*h = p'*q'*h' := hform.symm.trans hform'
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (hP p' hp').pos (hQ q' hq').pos) hh

/-- Every squarefree integer with selected factors in both disjoint families has a canonical triple. -/
theorem exists_canonical_factors {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree n) (hPn : (P.filter (fun p => p ∣ n)).Nonempty)
    (hQn : (Q.filter (fun q => q ∣ n)).Nonempty) :
    ∃ p q h : ℕ, p ∈ P ∧ q ∈ Q ∧ 0 < h ∧ Squarefree h ∧ n = p*q*h ∧
      Cutoff P h p ∧ Cutoff Q h q := by
  classical
  let p := (P.filter (fun p => p ∣ n)).max' hPn
  let q := (Q.filter (fun q => q ∣ n)).max' hQn
  have hp := Finset.mem_filter.mp (Finset.max'_mem (P.filter (fun p => p ∣ n)) hPn)
  have hq := Finset.mem_filter.mp (Finset.max'_mem (Q.filter (fun q => q ∣ n)) hQn)
  change p ∈ P ∧ p ∣ n at hp
  change q ∈ Q ∧ q ∣ n at hq
  have hpp := hP p hp.1
  have hqp := hQ q hq.1
  have hne : p ≠ q := by
    intro he
    apply Finset.disjoint_left.mp hdis hp.1
    simpa only [he] using hq.1
  have hcop := (Nat.coprime_primes hpp hqp).mpr hne
  obtain ⟨h, hform⟩ := hcop.mul_dvd_of_dvd_of_dvd hp.2 hq.2
  have hh : 0 < h := by
    by_contra hle
    have he : h = 0 := by omega
    simp [he] at hform
    omega
  have hd : h ∣ n := ⟨p*q, by rw [hform]; ring⟩
  have hnotP : ¬p ∣ h := by
    rintro ⟨t, ht⟩
    apply Nat.squarefree_iff_prime_squarefree.mp hsq p hpp
    exact ⟨q*t, by rw [hform, ht]; ring⟩
  have hnotQ : ¬q ∣ h := by
    rintro ⟨t, ht⟩
    apply Nat.squarefree_iff_prime_squarefree.mp hsq q hqp
    exact ⟨p*t, by rw [hform, ht]; ring⟩
  refine ⟨p, q, h, hp.1, hq.1, hh, Squarefree.squarefree_of_dvd hd hsq, hform, ?_, ?_⟩
  · intro r hr hrh
    have hrf : r ∈ P.filter (fun p => p ∣ n) := Finset.mem_filter.mpr ⟨hr, hrh.trans hd⟩
    have hle : r ≤ p := Finset.le_max' (P.filter (fun p => p ∣ n)) r hrf
    have hneq : r ≠ p := by intro he; apply hnotP; simpa only [he] using hrh
    omega
  · intro r hr hrh
    have hrf : r ∈ Q.filter (fun q => q ∣ n) := Finset.mem_filter.mpr ⟨hr, hrh.trans hd⟩
    have hle : r ≤ q := Finset.le_max' (Q.filter (fun q => q ∣ n)) r hrf
    have hneq : r ≠ q := by intro he; apply hnotQ; simpa only [he] using hrh
    omega

/-- Positive square-times-squarefree representations have the same square part and remainder. -/
theorem square_part_unique {l l' a a' : ℕ} (hl : 0 < l) (hl' : 0 < l')
    (ha : Squarefree a) (ha' : Squarefree a') (he : l^2*a = l'^2*a') : l = l' ∧ a = a' := by
  let d := l.gcd l'
  let u := l/d
  let v := l'/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left l' hl
  have hdu : d*u = l := Nat.mul_div_cancel' (Nat.gcd_dvd_left l l')
  have hdv : d*v = l' := Nat.mul_div_cancel' (Nat.gcd_dvd_right l l')
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hd
  have hred : u^2*a = v^2*a' := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hd 2)
    calc
      d^2*(u^2*a) = (d*u)^2*a := by ring
      _ = l^2*a := by rw [hdu]
      _ = l'^2*a' := he
      _ = (d*v)^2*a' := by rw [hdv]
      _ = d^2*(v^2*a') := by ring
  have huD : u^2 ∣ a' := (hcop.pow 2 2).dvd_of_dvd_mul_left ⟨a, hred.symm⟩
  have hvD : v^2 ∣ a := (hcop.symm.pow 2 2).dvd_of_dvd_mul_left ⟨a', hred⟩
  have hu : u = 1 := Nat.isUnit_iff.mp (ha' u (by simpa only [pow_two] using huD))
  have hv : v = 1 := Nat.isUnit_iff.mp (ha v (by simpa only [pow_two] using hvD))
  have hlEq : l = l' := by
    calc
      l = d*u := hdu.symm
      _ = d := by rw [hu, mul_one]
      _ = d*v := by rw [hv, mul_one]
      _ = l' := hdv
  refine ⟨hlEq, ?_⟩
  rw [hlEq] at he
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hl' 2) he

/-- The full canonical square-part/prime-factor representation is injective. -/
theorem canonical_representation_unique {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hdis : Disjoint P Q)
    {n l p q h l' p' q' h' : ℕ} (hl : 0 < l) (hl' : 0 < l')
    (hp : p ∈ P) (hq : q ∈ Q) (hp' : p' ∈ P) (hq' : q' ∈ Q)
    (hsq : Squarefree (p*q*h)) (hsq' : Squarefree (p'*q'*h'))
    (hform : n = l^2*p*q*h) (hform' : n = l'^2*p'*q'*h')
    (hcutP : Cutoff P h p) (hcutQ : Cutoff Q h q)
    (hcutP' : Cutoff P h' p') (hcutQ' : Cutoff Q h' q') :
    l = l' ∧ p = p' ∧ q = q' ∧ h = h' := by
  have he : l^2*(p*q*h) = l'^2*(p'*q'*h') := by
    calc
      _ = n := by rw [hform]; ring
      _ = _ := by rw [hform']; ring
  have hparts := square_part_unique hl hl' hsq hsq' he
  exact ⟨hparts.1, canonical_factors_unique hP hQ hdis hp hq hp' hq' rfl hparts.2
    hcutP hcutQ hcutP' hcutQ'⟩

end NField.Alignment.KorolevCanonicalPrimeFactors
