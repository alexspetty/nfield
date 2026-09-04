/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The coprime Euler mass

The reduced ratios in the cubic collision term form the positive
Calkin--Wilf tree below `1`.  The local potential identity in this file is a
telescoping proof of the constant one; it avoids importing the classical
Euler harmonic-sum evaluation as a black box.
-/

namespace NField.Alignment.CoprimeEulerMass

open scoped BigOperators

/-- The summand attached to a reduced ratio `k / a` with `0 < k < a`. -/
noncomputable def eulerPairWeight (k a : ℕ) : ℝ :=
  1 / ((k : ℝ) * (a : ℝ) ^ 2)

/-- A telescoping potential on the positive Calkin--Wilf tree. -/
noncomputable def eulerPairPotential (k a : ℕ) : ℝ :=
  2 / ((k : ℝ) * (a : ℝ) ^ 2) +
    1 / ((k : ℝ) ^ 2 * (a : ℝ))

/-- The two children of `k / a` after identifying a fraction with its
reciprocal so that the smaller coordinate remains first. -/
def leftChild (ka : ℕ × ℕ) : ℕ × ℕ :=
  (ka.1, ka.1 + ka.2)

def rightChild (ka : ℕ × ℕ) : ℕ × ℕ :=
  (ka.2, ka.1 + ka.2)

/-- The exact local conservation law.  Every node loses precisely its Euler
weight to its two children. -/
theorem eulerPairPotential_children
    {k a : ℕ} (hk : 0 < k) (ha : 0 < a) :
    eulerPairPotential k a -
        eulerPairPotential k (k + a) -
        eulerPairPotential a (k + a) =
      eulerPairWeight k a := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hkaR : ((k + a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.add_pos_left hk a).ne'
  unfold eulerPairPotential eulerPairWeight
  push_cast
  field_simp [hkR, haR, hkaR]
  ring

theorem eulerPairPotential_root : eulerPairPotential 1 2 = 1 := by
  norm_num [eulerPairPotential]

/-- Reduced strict positive pairs whose denominator does not exceed `N`. -/
def reducedEulerPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter fun ka =>
    0 < ka.1 ∧ ka.1 < ka.2 ∧ ka.1.Coprime ka.2

theorem mem_reducedEulerPairs_iff
    {N k a : ℕ} :
    (k, a) ∈ reducedEulerPairs N ↔
      0 < k ∧ k < a ∧ k.Coprime a ∧ a ≤ N := by
  simp [reducedEulerPairs]
  omega

theorem root_mem_reducedEulerPairs {N : ℕ} (hN : 2 ≤ N) :
    (1, 2) ∈ reducedEulerPairs N := by
  rw [mem_reducedEulerPairs_iff]
  exact ⟨by omega, by omega, by decide, hN⟩

theorem leftChild_preserves_reduced
    {k a : ℕ} (hk : 0 < k) (hka : k < a) (hcop : k.Coprime a) :
    0 < (leftChild (k, a)).1 ∧
      (leftChild (k, a)).1 < (leftChild (k, a)).2 ∧
      (leftChild (k, a)).1.Coprime (leftChild (k, a)).2 := by
  change 0 < k ∧ k < k + a ∧ k.Coprime (k + a)
  exact ⟨hk, by omega, Nat.coprime_self_add_right.mpr hcop⟩

theorem rightChild_preserves_reduced
    {k a : ℕ} (hk : 0 < k) (ha : 0 < a) (hcop : k.Coprime a) :
    0 < (rightChild (k, a)).1 ∧
      (rightChild (k, a)).1 < (rightChild (k, a)).2 ∧
      (rightChild (k, a)).1.Coprime (rightChild (k, a)).2 := by
  change 0 < a ∧ a < k + a ∧ a.Coprime (k + a)
  exact ⟨ha, by omega, Nat.coprime_add_self_right.mpr hcop.symm⟩

theorem leftChild_injective : Function.Injective leftChild := by
  rintro ⟨k, a⟩ ⟨u, v⟩ h
  simp only [leftChild, Prod.mk.injEq] at h ⊢
  omega

theorem rightChild_injective : Function.Injective rightChild := by
  rintro ⟨k, a⟩ ⟨u, v⟩ h
  simp only [rightChild, Prod.mk.injEq] at h ⊢
  omega

theorem leftChild_ne_rightChild_of_strict
    {ka uv : ℕ × ℕ} (hka : ka.1 < ka.2) (huv : uv.1 < uv.2) :
    leftChild ka ≠ rightChild uv := by
  intro h
  have hfirst : ka.1 = uv.2 := congrArg Prod.fst h
  have hsecond : ka.1 + ka.2 = uv.1 + uv.2 := congrArg Prod.snd h
  omega

/-- Parents whose two children are still inside the denominator cutoff. -/
def interiorEulerParents (N : ℕ) : Finset (ℕ × ℕ) :=
  (reducedEulerPairs N).filter fun ka => ka.1 + ka.2 ≤ N

/-- The children generated before reaching the cutoff frontier. -/
def interiorEulerChildren (N : ℕ) : Finset (ℕ × ℕ) :=
  (interiorEulerParents N).image leftChild ∪
    (interiorEulerParents N).image rightChild

/-- Every reduced strict pair except `1 / 2` has a unique Euclidean parent.
Consequently the interior children are exactly the cutoff tree with its root
removed. -/
theorem interiorEulerChildren_eq_erase_root
    (N : ℕ) :
    interiorEulerChildren N = (reducedEulerPairs N).erase (1, 2) := by
  ext ka
  constructor
  · intro hka
    rw [interiorEulerChildren, Finset.mem_union] at hka
    rcases hka with hleft | hright
    · rcases Finset.mem_image.mp hleft with ⟨uv, huv, rfl⟩
      have huv' := (Finset.mem_filter.mp huv)
      have huvReduced := (mem_reducedEulerPairs_iff.mp huv'.1)
      have hpres := leftChild_preserves_reduced
        huvReduced.1 huvReduced.2.1 huvReduced.2.2.1
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hstrict := huvReduced.2.1
        simp only [leftChild, Prod.mk.injEq] at heq
        omega
      · rw [mem_reducedEulerPairs_iff]
        change 0 < uv.1 ∧ uv.1 < uv.1 + uv.2 ∧
          uv.1.Coprime (uv.1 + uv.2) ∧ uv.1 + uv.2 ≤ N
        exact ⟨hpres.1, hpres.2.1, hpres.2.2, huv'.2⟩
    · rcases Finset.mem_image.mp hright with ⟨uv, huv, rfl⟩
      have huv' := (Finset.mem_filter.mp huv)
      have huvReduced := (mem_reducedEulerPairs_iff.mp huv'.1)
      have hpres := rightChild_preserves_reduced
        huvReduced.1 (lt_trans huvReduced.1 huvReduced.2.1)
          huvReduced.2.2.1
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hstrict := huvReduced.2.1
        simp only [rightChild, Prod.mk.injEq] at heq
        omega
      · rw [mem_reducedEulerPairs_iff]
        change 0 < uv.2 ∧ uv.2 < uv.1 + uv.2 ∧
          uv.2.Coprime (uv.1 + uv.2) ∧ uv.1 + uv.2 ≤ N
        exact ⟨hpres.1, hpres.2.1, hpres.2.2, huv'.2⟩
  · intro hka
    have hka' := Finset.mem_erase.mp hka
    rcases ka with ⟨k, a⟩
    have hred := mem_reducedEulerPairs_iff.mp hka'.2
    have hkpos : 0 < k := hred.1
    have hkaLt : k < a := hred.2.1
    have hcop : k.Coprime a := hred.2.2.1
    have haN : a ≤ N := hred.2.2.2
    by_cases htwice : 2 * k < a
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(k, a - k), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · rw [mem_reducedEulerPairs_iff]
          refine ⟨hkpos, by omega, ?_, by omega⟩
          exact (Nat.coprime_sub_self_right (le_of_lt hkaLt)).mpr hcop
        · omega
      · simp [leftChild]
        omega
    · have halt : a < 2 * k := by
        have hle : a ≤ 2 * k := by omega
        exact lt_of_le_of_ne hle <| by
          intro heq
          have hkdvd : k ∣ a := by
            use 2
            omega
          have hkone := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hkdvd
          apply hka'.1
          simp only [Prod.mk.injEq]
          omega
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(a - k, k), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · rw [mem_reducedEulerPairs_iff]
          refine ⟨by omega, by omega, ?_, by omega⟩
          exact (Nat.coprime_sub_self_left (le_of_lt hkaLt)).mpr hcop.symm
        · omega
      · simp [rightChild]
        omega

/-- The unexpanded potential attached to a pair. -/
noncomputable def pairPotential (ka : ℕ × ℕ) : ℝ :=
  eulerPairPotential ka.1 ka.2

/-- The Euler summand attached to a pair. -/
noncomputable def pairWeight (ka : ℕ × ℕ) : ℝ :=
  eulerPairWeight ka.1 ka.2

/-- Parents whose children cross the denominator cutoff. -/
def frontierEulerParents (N : ℕ) : Finset (ℕ × ℕ) :=
  (reducedEulerPairs N).filter fun ka => ¬(ka.1 + ka.2 ≤ N)

/-- Potential left on the outer frontier after telescoping all pairs with
denominator at most `N`. -/
noncomputable def eulerFrontierPotential (N : ℕ) : ℝ :=
  ∑ ka ∈ frontierEulerParents N,
    (pairPotential (leftChild ka) + pairPotential (rightChild ka))

theorem interiorEulerChildPotential_sum (N : ℕ) :
    (∑ ka ∈ interiorEulerParents N, pairPotential (leftChild ka)) +
        (∑ ka ∈ interiorEulerParents N, pairPotential (rightChild ka)) =
      ∑ ka ∈ (reducedEulerPairs N).erase (1, 2), pairPotential ka := by
  classical
  have hdisjoint :
      Disjoint ((interiorEulerParents N).image leftChild)
        ((interiorEulerParents N).image rightChild) := by
    rw [Finset.disjoint_left]
    intro x hxleft hxright
    rcases Finset.mem_image.mp hxleft with ⟨ka, hka, hleft⟩
    rcases Finset.mem_image.mp hxright with ⟨uv, huv, hright⟩
    have hkaRed := mem_reducedEulerPairs_iff.mp
      (Finset.mem_filter.mp hka).1
    have huvRed := mem_reducedEulerPairs_iff.mp
      (Finset.mem_filter.mp huv).1
    exact leftChild_ne_rightChild_of_strict hkaRed.2.1 huvRed.2.1
      (hleft.trans hright.symm)
  calc
    (∑ ka ∈ interiorEulerParents N, pairPotential (leftChild ka)) +
          (∑ ka ∈ interiorEulerParents N, pairPotential (rightChild ka)) =
        (∑ x ∈ (interiorEulerParents N).image leftChild, pairPotential x) +
          ∑ x ∈ (interiorEulerParents N).image rightChild, pairPotential x := by
            rw [Finset.sum_image (leftChild_injective.injOn),
              Finset.sum_image (rightChild_injective.injOn)]
    _ = ∑ x ∈ interiorEulerChildren N, pairPotential x := by
          rw [interiorEulerChildren, Finset.sum_union hdisjoint]
    _ = _ := by rw [interiorEulerChildren_eq_erase_root]

/-- Exact finite telescoping formula. -/
theorem reducedEulerPairs_weight_sum_eq_one_sub_frontier
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ ka ∈ reducedEulerPairs N, pairWeight ka) =
      1 - eulerFrontierPotential N := by
  classical
  let S := reducedEulerPairs N
  let childMass := fun ka : ℕ × ℕ =>
    pairPotential (leftChild ka) + pairPotential (rightChild ka)
  have hlocal (ka : ℕ × ℕ) (hka : ka ∈ S) :
      pairPotential ka - childMass ka = pairWeight ka := by
    have hred := mem_reducedEulerPairs_iff.mp hka
    simpa [pairPotential, pairWeight, childMass, leftChild, rightChild,
      sub_sub] using
      eulerPairPotential_children hred.1 (lt_trans hred.1 hred.2.1)
  have hsplit :
      (∑ ka ∈ S, childMass ka) =
        (∑ ka ∈ interiorEulerParents N, childMass ka) +
          ∑ ka ∈ frontierEulerParents N, childMass ka := by
    simpa [S, interiorEulerParents, frontierEulerParents] using
      (Finset.sum_filter_add_sum_filter_not
        (reducedEulerPairs N) (fun ka => ka.1 + ka.2 ≤ N) childMass).symm
  have hinterior :
      (∑ ka ∈ interiorEulerParents N, childMass ka) =
        (∑ ka ∈ S, pairPotential ka) - 1 := by
    rw [show (∑ ka ∈ interiorEulerParents N, childMass ka) =
        (∑ ka ∈ interiorEulerParents N,
            pairPotential (leftChild ka)) +
          ∑ ka ∈ interiorEulerParents N,
            pairPotential (rightChild ka) by
      unfold childMass
      rw [← Finset.sum_add_distrib]]
    rw [interiorEulerChildPotential_sum]
    have hroot := root_mem_reducedEulerPairs hN
    have hsum := Finset.sum_erase_add (reducedEulerPairs N)
      pairPotential hroot
    simp [pairPotential, eulerPairPotential_root, S] at hsum ⊢
    linarith
  calc
    (∑ ka ∈ reducedEulerPairs N, pairWeight ka) =
        ∑ ka ∈ S, (pairPotential ka - childMass ka) := by
          apply Finset.sum_congr rfl
          intro ka hka
          exact (hlocal ka hka).symm
    _ = (∑ ka ∈ S, pairPotential ka) -
          ∑ ka ∈ S, childMass ka := by
            rw [Finset.sum_sub_distrib]
    _ = 1 - eulerFrontierPotential N := by
      rw [hsplit, hinterior]
      unfold eulerFrontierPotential childMass
      ring

/-! ## Vanishing of the Calkin--Wilf frontier -/

/-- After the local conservation law is expanded, a frontier parent leaves
exactly these two positive rational terms on its children. -/
theorem childPotentialSum_eq
    {k a : ℕ} (hk : 0 < k) (ha : 0 < a) :
    pairPotential (leftChild (k, a)) +
        pairPotential (rightChild (k, a)) =
      1 / ((k : ℝ) * (a : ℝ) ^ 2) +
        1 / ((k : ℝ) ^ 2 * (a : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hkaR : ((k + a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.add_pos_left hk a).ne'
  simp only [pairPotential, leftChild, rightChild, eulerPairPotential]
  push_cast
  field_simp [hkR, haR, hkaR]
  ring

/-- Denominators that occur above a fixed numerator on the cutoff frontier. -/
def frontierDenominators (N k : ℕ) : Finset ℕ :=
  (Finset.Icc (k + 1) N).filter fun a =>
    N < k + a ∧ k.Coprime a

theorem mem_frontierDenominators_iff {N k a : ℕ} :
    a ∈ frontierDenominators N k ↔
      k < a ∧ a ≤ N ∧ N < k + a ∧ k.Coprime a := by
  simp [frontierDenominators]
  omega

/-- There are at most `k` possible denominators above numerator `k` on the
frontier, because they all lie in the final interval of length `k`. -/
theorem card_frontierDenominators_le (N k : ℕ) :
    (frontierDenominators N k).card ≤ k := by
  calc
    (frontierDenominators N k).card ≤ (Finset.Ioc (N - k) N).card := by
      apply Finset.card_le_card
      intro a ha
      have h := mem_frontierDenominators_iff.mp ha
      simp only [Finset.mem_Ioc]
      omega
    _ = N - (N - k) := by simp
    _ ≤ k := by omega

/-- The frontier parents split into their numerator slices. -/
theorem frontierEulerParents_eq_biUnion (N : ℕ) :
    frontierEulerParents N =
      (Finset.Icc 1 N).biUnion fun k =>
        (frontierDenominators N k).image fun a => (k, a) := by
  classical
  ext ka
  rcases ka with ⟨k, a⟩
  simp only [frontierEulerParents, Finset.mem_filter,
    mem_reducedEulerPairs_iff, not_le, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hk, hka, hcop, haN⟩, hfront⟩
    refine ⟨k, ⟨hk, le_trans (Nat.le_of_lt hka) haN⟩, a, ?_, rfl⟩
    exact mem_frontierDenominators_iff.mpr ⟨hka, haN, hfront, hcop⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    simp only [Prod.mk.injEq] at huv
    rcases huv with ⟨rfl, rfl⟩
    have hv' := mem_frontierDenominators_iff.mp hv
    exact ⟨⟨hu.1, hv'.1, hv'.2.2.2, hv'.2.1⟩, hv'.2.2.1⟩

/-- Pointwise estimate used on every frontier child pair. -/
theorem frontier_childPotential_le
    {N k a : ℕ} (hN : 2 ≤ N) (hk : 0 < k) (hka : k < a)
    (_haN : a ≤ N) (hfront : N < k + a) :
    pairPotential (leftChild (k, a)) +
        pairPotential (rightChild (k, a)) ≤
      4 / ((N : ℝ) ^ 2 * (k : ℝ)) +
        2 / ((N : ℝ) * (k : ℝ) ^ 2) := by
  rw [childPotentialSum_eq hk (lt_trans hk hka)]
  have hNR : (0 : ℝ) < N := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have haR : (0 : ℝ) < a := by exact_mod_cast (lt_trans hk hka)
  have htwice : (N : ℝ) < 2 * (a : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hfront (by omega : k + a ≤ 2 * a))
  have hsquare : (N : ℝ) ^ 2 ≤ 4 * (a : ℝ) ^ 2 := by nlinarith
  have hlinear : (N : ℝ) ≤ 2 * (a : ℝ) := le_of_lt htwice
  have hfirst :
      1 / ((k : ℝ) * (a : ℝ) ^ 2) ≤
        4 / ((N : ℝ) ^ 2 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (mul_pos hkR (sq_pos_of_pos haR))
      (mul_pos (sq_pos_of_pos hNR) hkR)]
    nlinarith
  have hsecond :
      1 / ((k : ℝ) ^ 2 * (a : ℝ)) ≤
        2 / ((N : ℝ) * (k : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (mul_pos (sq_pos_of_pos hkR) haR)
      (mul_pos hNR (sq_pos_of_pos hkR))]
    nlinarith
  linarith

/-- A quantitative outer-frontier estimate. -/
theorem eulerFrontierPotential_le
    {N : ℕ} (hN : 2 ≤ N) :
    eulerFrontierPotential N ≤
      4 / (N : ℝ) + 2 * (harmonic N : ℝ) / (N : ℝ) := by
  classical
  rw [eulerFrontierPotential, frontierEulerParents_eq_biUnion]
  rw [Finset.sum_biUnion]
  · calc
      (∑ k ∈ Finset.Icc 1 N,
          ∑ ka ∈ (frontierDenominators N k).image (fun a => (k, a)),
            (pairPotential (leftChild ka) + pairPotential (rightChild ka))) ≤
          ∑ k ∈ Finset.Icc 1 N,
            (k : ℝ) *
              (4 / ((N : ℝ) ^ 2 * (k : ℝ)) +
                2 / ((N : ℝ) * (k : ℝ) ^ 2)) := by
            apply Finset.sum_le_sum
            intro k hkN
            rw [Finset.sum_image]
            · calc
                (∑ a ∈ frontierDenominators N k,
                    (pairPotential (leftChild (k, a)) +
                      pairPotential (rightChild (k, a)))) ≤
                    (frontierDenominators N k).card *
                      (4 / ((N : ℝ) ^ 2 * (k : ℝ)) +
                        2 / ((N : ℝ) * (k : ℝ) ^ 2)) := by
                      simpa [nsmul_eq_mul] using
                        (Finset.sum_le_card_nsmul
                          (frontierDenominators N k)
                          (fun a => pairPotential (leftChild (k, a)) +
                            pairPotential (rightChild (k, a)))
                          (4 / ((N : ℝ) ^ 2 * (k : ℝ)) +
                            2 / ((N : ℝ) * (k : ℝ) ^ 2))
                          (by
                            intro a ha
                            have ha' := mem_frontierDenominators_iff.mp ha
                            exact frontier_childPotential_le hN
                              (Finset.mem_Icc.mp hkN).1 ha'.1
                              ha'.2.1 ha'.2.2.1))
                _ ≤ (k : ℝ) *
                      (4 / ((N : ℝ) ^ 2 * (k : ℝ)) +
                        2 / ((N : ℝ) * (k : ℝ) ^ 2)) := by
                      gcongr
                      exact_mod_cast card_frontierDenominators_le N k
            · intro a ha b hb hab
              simp only [Prod.mk.injEq] at hab
              exact hab.2
      _ = ∑ k ∈ Finset.Icc 1 N,
            (4 / (N : ℝ) ^ 2 + 2 / ((N : ℝ) * (k : ℝ))) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
              have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
              field_simp [hkR]
      _ = (N : ℝ) * (4 / (N : ℝ) ^ 2) +
            2 / (N : ℝ) * (harmonic N : ℝ) := by
              rw [Finset.sum_add_distrib]
              have hcard : (Finset.Icc 1 N).card = N := by simp
              rw [Finset.sum_const, nsmul_eq_mul, hcard]
              rw [harmonic_eq_sum_Icc]
              simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro k _hk
              ring
      _ = 4 / (N : ℝ) + 2 * (harmonic N : ℝ) / (N : ℝ) := by
            have hNR : (N : ℝ) ≠ 0 := by positivity
            field_simp [hNR]
  · intro k hk l hl hkl
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro ka ⟨a, ha, hka⟩ ⟨c, hc, hkc⟩
    have hfirst := congrArg Prod.fst (hka.trans hkc.symm)
    exact hkl hfirst

/-- Every frontier potential is nonnegative. -/
theorem eulerFrontierPotential_nonneg (N : ℕ) :
    0 ≤ eulerFrontierPotential N := by
  classical
  unfold eulerFrontierPotential pairPotential eulerPairPotential
  positivity

/-- The Calkin--Wilf frontier disappears at infinity. -/
theorem tendsto_eulerFrontierPotential_zero :
    Filter.Tendsto eulerFrontierPotential Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (λ N : ℕ => 1 / (N : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_nhds_zero_nat :
        Filter.Tendsto (λ N : ℕ => (N : ℝ)⁻¹) Filter.atTop (nhds 0))
  have hlog : Filter.Tendsto
      (λ N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
    exact (Real.isLittleO_log_id_atTop.comp_tendsto
      tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
  have hharmonic : Filter.Tendsto
      (λ N : ℕ => (harmonic N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
      have hharmonicQ : (0 : ℚ) ≤ harmonic N := by
        unfold harmonic
        positivity
      exact div_nonneg (by exact_mod_cast hharmonicQ) (by positivity)
    · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
      have hNR : (0 : ℝ) < N := by positivity
      apply div_le_div_of_nonneg_right (harmonic_le_one_add_log N) hNR.le
    · simpa [add_div] using hinv.add hlog
  have hupper : Filter.Tendsto
      (λ N : ℕ => 4 / (N : ℝ) + 2 * (harmonic N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (hinv.const_mul 4).add (hharmonic.const_mul 2)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall eulerFrontierPotential_nonneg
  · filter_upwards [Filter.eventually_atTop.2 ⟨2, fun N hN => hN⟩] with N hN
    exact eulerFrontierPotential_le hN
  · exact hupper

/-- The finite reduced Euler masses converge to the exact constant one. -/
theorem tendsto_reducedEulerPairs_weight_sum_one :
    Filter.Tendsto
      (λ N => ∑ ka ∈ reducedEulerPairs N, pairWeight ka)
      Filter.atTop (nhds 1) := by
  have ht : Filter.Tendsto (λ N => 1 - eulerFrontierPotential N)
      Filter.atTop (nhds 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      tendsto_eulerFrontierPotential_zero)
  have heq : (λ N => 1 - eulerFrontierPotential N) =ᶠ[Filter.atTop]
      (λ N => ∑ ka ∈ reducedEulerPairs N, pairWeight ka) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨2, fun N hN => hN⟩] with N hN
    exact (reducedEulerPairs_weight_sum_eq_one_sub_frontier hN).symm
  exact ht.congr' heq

end NField.Alignment.CoprimeEulerMass
