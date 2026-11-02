/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanMonicFactorization
import NField.Alignment.KloostermanQuadraticLSeries

/-!
# Removing an irreducible Euler factor from the actual monic sums

Multiplication by a monic polynomial parametrizes its monic multiples at
exactly the shifted degree. For a new monic irreducible, the remaining
sieving conditions pass unchanged to the quotient. No character value is
inverted, so the zero-weight factor X is retained.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanSiftedSeries
open scoped BigOperators Classical
open Polynomial KloostermanMonicCoefficients KloostermanPolynomialCharacter

/-- Multiplication gives the actual monic multiples, with the degree shift. -/
noncomputable def monicMultipleEquiv {K : Type*} [Field K]
    (g : K[X]) (hg : g.Monic) (n : ℕ) :
    MonicDegree K n ≃ {f : MonicDegree K (g.natDegree+n) // g ∣ f.val} :=
  Equiv.ofBijective
    (fun h => ⟨⟨g*h.val, hg.mul h.property.1,
      by rw [natDegree_mul hg.ne_zero h.property.1.ne_zero, h.property.2]⟩,
      dvd_mul_right g h.val⟩) (by
    constructor
    · intro h k heq
      apply Subtype.ext
      exact mul_left_cancel₀ hg.ne_zero (congrArg (fun f => f.val.val) heq)
    · intro f
      obtain ⟨h,hh⟩ := f.property
      have hm : h.Monic := hg.of_mul_monic_left (hh ▸ f.val.property.1)
      have hd : h.natDegree=n := by
        have he := f.val.property.2
        rw [hh,natDegree_mul hg.ne_zero hm.ne_zero] at he
        omega
      exact ⟨⟨h,hm,hd⟩,Subtype.ext (Subtype.ext hh.symm)⟩)

@[simp] theorem monicMultipleEquiv_val {K : Type*} [Field K]
    (g : K[X]) (hg : g.Monic) (n : ℕ) (h : MonicDegree K n) :
    (monicMultipleEquiv g hg n h).val.val = g*h.val := rfl

def Avoids {K : Type*} [Field K] (s : Finset K[X]) (f : K[X]) : Prop :=
  ∀ k ∈ s, ¬ k ∣ f

/-- A distinct monic irreducible cannot divide the newly removed factor. -/
theorem irreducible_not_dvd_of_ne {K : Type*} [Field K]
    (k g : K[X]) (hk : k.Monic) (hi : Irreducible k)
    (hg : g.Monic) (hgi : Irreducible g) (hne : k ≠ g) : ¬ k ∣ g := by
  intro hd
  exact hne (Polynomial.eq_of_monic_of_associated hk hg (hi.associated_of_dvd hgi hd))

theorem avoids_mul_new_irreducible {K : Type*} [Field K]
    (s : Finset K[X]) (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k)
    (g : K[X]) (hg : g.Monic) (hi : Irreducible g) (hgs : g ∉ s)
    (h : K[X]) : Avoids s (g*h) ↔ Avoids s h := by
  unfold Avoids
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  have hkg : ¬ k ∣ g := irreducible_not_dvd_of_ne k g (hs k hk).1
    (hs k hk).2 hg hi (by intro he; exact hgs (he ▸ hk))
  rw [(hs k hk).2.prime.dvd_mul, or_iff_right hkg]

noncomputable def siftedCoefficient (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X]) (n : ℕ) : ℂ := by
  classical
  exact ∑ f : MonicDegree (ZMod p) n,
    if Avoids s f.val then polynomialCharacter p a b m f.val else 0

@[simp] theorem siftedCoefficient_empty (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) :
    siftedCoefficient p a b m ∅ n = degreeCoefficient p a b m n := by
  classical
  simp [siftedCoefficient,Avoids,degreeCoefficient]

/-- The contribution of multiples of a new irreducible factors as its
character times the actual sifted sum in the complementary degree. -/
theorem sifted_multiples_sum (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X])
    (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k)
    (g : (ZMod p)[X]) (hg : g.Monic) (hi : Irreducible g) (hgs : g ∉ s)
    (n : ℕ) :
    (∑ f : {f : MonicDegree (ZMod p) (g.natDegree+n) // g ∣ f.val},
      if Avoids s f.val.val then polynomialCharacter p a b m f.val.val else 0) =
      polynomialCharacter p a b m g * siftedCoefficient p a b m s n := by
  classical
  rw [siftedCoefficient,Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (monicMultipleEquiv g hg n)
  intro f
  rw [monicMultipleEquiv_val, polynomialCharacter_mul,
    avoids_mul_new_irreducible s hs g hg hi hgs]
  split_ifs <;> simp

/-- Finite subtype sums are the corresponding zero-extended sums. -/
theorem sum_subtype_eq_ite {ι : Type*} [Fintype ι]
    (P : ι → Prop) (F : ι → ℂ) :
    (∑ x : {x // P x}, F x.val) = ∑ x, if P x then F x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) F).symm

/-- Removing one irreducible subtracts exactly its weighted multiples. -/
theorem siftedCoefficient_insert_shift (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X])
    (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k)
    (g : (ZMod p)[X]) (hg : g.Monic) (hi : Irreducible g) (hgs : g ∉ s)
    (n : ℕ) :
    siftedCoefficient p a b m (insert g s) (g.natDegree+n) =
      siftedCoefficient p a b m s (g.natDegree+n) -
        polynomialCharacter p a b m g * siftedCoefficient p a b m s n := by
  rw [← sifted_multiples_sum p a b m s hs g hg hi hgs n,
    sum_subtype_eq_ite (fun f : MonicDegree (ZMod p) (g.natDegree+n) => g ∣ f.val)
      (fun f => if Avoids s f.val then polynomialCharacter p a b m f.val else 0)]
  unfold siftedCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  have h : Avoids (insert g s) f.val ↔ ¬ g ∣ f.val ∧ Avoids s f.val := by
    simp [Avoids]
  simp only [h]
  by_cases hd : g ∣ f.val <;> by_cases hs' : Avoids s f.val <;> simp [hd,hs']

/-- Below the new factor's degree there are no multiples to remove. -/
theorem siftedCoefficient_insert_of_lt (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X]) (g : (ZMod p)[X])
    (n : ℕ) (hn : n < g.natDegree) :
    siftedCoefficient p a b m (insert g s) n = siftedCoefficient p a b m s n := by
  unfold siftedCoefficient
  apply Finset.sum_congr rfl
  intro f _
  have hd : ¬ g ∣ f.val := by
    intro h
    have := Polynomial.natDegree_le_of_dvd h f.property.1.ne_zero
    rw [f.property.2] at this
    omega
  simp [Avoids, hd]

noncomputable def siftedSeries (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X]) : PowerSeries ℂ :=
  PowerSeries.mk (siftedCoefficient p a b m s)

noncomputable def eulerFactor (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (g : (ZMod p)[X]) : PowerSeries ℂ :=
  1-PowerSeries.C (polynomialCharacter p a b m g)*PowerSeries.X^g.natDegree

/-- Exact removal of one actual irreducible Euler factor. -/
theorem siftedSeries_insert (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X])
    (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k)
    (g : (ZMod p)[X]) (hg : g.Monic) (hi : Irreducible g) (hgs : g ∉ s) :
    siftedSeries p a b m (insert g s) =
      eulerFactor p a b m g * siftedSeries p a b m s := by
  ext n
  simp only [siftedSeries, eulerFactor, sub_mul, one_mul, map_sub,
    mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk]
  by_cases hn : g.natDegree ≤ n
  · rw [if_pos hn]
    convert siftedCoefficient_insert_shift p a b m s hs g hg hi hgs
      (n-g.natDegree) using 1 <;> rw [Nat.add_sub_of_le hn]
  · rw [if_neg hn,mul_zero,sub_zero]
    exact siftedCoefficient_insert_of_lt p a b m s g n (by omega)

/-- Finite Euler-factor removal for the actual formal L-series. -/
theorem siftedSeries_eq_finite_product (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (ZMod p)[X])
    (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k) :
    siftedSeries p a b m s =
      (∏ g ∈ s, eulerFactor p a b m g) *
        KloostermanQuadraticLSeries.formalLSeries p a b m := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,one_mul]
    ext n
    simp [siftedSeries,KloostermanQuadraticLSeries.formalLSeries]
  | @insert g s hgs ih =>
    have hg := hs g (Finset.mem_insert_self _ _)
    have hs' : ∀ k ∈ s, k.Monic ∧ Irreducible k :=
      fun k hk => hs k (Finset.mem_insert_of_mem hk)
    rw [siftedSeries_insert p a b m s hs' g hg.1 hg.2 hgs,
      ih hs',Finset.prod_insert hgs,mul_assoc]

end NField.Alignment.KloostermanSiftedSeries
