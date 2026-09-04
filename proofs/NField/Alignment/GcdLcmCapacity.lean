/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareReducedRatio
import NField.Alignment.SecondaryCapacityLedger

/-!
# GCD and LCM capacity

The literal GCD/LCM sums in the continuous corollary, their reduction to
primitive ratios, and the exact square-to-triangle identity.
-/

namespace NField.Alignment.GcdLcmCapacity

open scoped BigOperators
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareReducedRatio
open NField.Alignment.SecondaryCapacityLedger

/-- The paper's GCD/LCM kernel, written in the equivalent squared-GCD form.
The positive indices used below avoid the zero-denominator convention. -/
noncomputable def gcdLcmKernel (r s : ℕ) : ℝ :=
  ((r.gcd s : ℕ) : ℝ) ^ 2 / ((r : ℝ) * (s : ℝ))

/-- The same kernel in the manuscript's literal GCD-over-LCM notation. -/
noncomputable def gcdOverLcmKernel (r s : ℕ) : ℝ :=
  ((r.gcd s : ℕ) : ℝ) / ((r.lcm s : ℕ) : ℝ)

theorem gcdOverLcmKernel_eq_gcdLcmKernel
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    gcdOverLcmKernel r s = gcdLcmKernel r s := by
  unfold gcdOverLcmKernel gcdLcmKernel
  have hlcm : 0 < r.lcm s := Nat.lcm_pos hr hs
  have hlcmℝ : ((r.lcm s : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hlcm.ne'
  have hrℝ : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsℝ : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hproduct := congrArg (fun n : ℕ => (n : ℝ)) (Nat.gcd_mul_lcm r s)
  push_cast at hproduct
  field_simp [hlcmℝ, hrℝ, hsℝ]
  nlinarith

/-- The literal square-box sum over `1 ≤ r,s ≤ N`. -/
noncomputable def gcdLcmSquareSum (N : ℕ) : ℝ :=
  ∑ i : FirstWindowIndex (N + 1), ∑ j : FirstWindowIndex (N + 1),
    gcdLcmKernel (firstWindowNat i) (firstWindowNat j)

/-- The literal one-sided sum `∑_{n≤N} ∑_{k≤n} (k,n)/[k,n]`. -/
noncomputable def gcdLcmTriangularSum (N : ℕ) : ℝ :=
  ∑ i : FirstWindowIndex (N + 1),
    ∑ j : FirstWindowIndex (N + 1),
      if j ≤ i then gcdLcmKernel (firstWindowNat j) (firstWindowNat i) else 0

theorem gcdLcmKernel_comm (r s : ℕ) :
    gcdLcmKernel r s = gcdLcmKernel s r := by
  unfold gcdLcmKernel
  rw [Nat.gcd_comm]
  ring

theorem gcdLcmKernel_self (r : ℕ) (hr : 0 < r) :
    gcdLcmKernel r r = 1 := by
  unfold gcdLcmKernel
  rw [Nat.gcd_self]
  have hrℝ : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrℝ]

theorem gcdLcmKernel_scaled_coprime
    {t a k : ℕ} (ht : 0 < t) (ha : 0 < a) (hk : 0 < k)
    (hcop : k.Coprime a) :
    gcdLcmKernel (t * k) (t * a) =
      (1 : ℝ) / ((k : ℝ) * (a : ℝ)) := by
  unfold gcdLcmKernel
  rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  have htℝ : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have haℝ : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp [htℝ, haℝ, hkℝ]

/-- The strict upper triangle, in literal positive coordinates. -/
noncomputable def gcdLcmUpperTriangle (N : ℕ) : ℝ :=
  ∑ i : FirstWindowIndex (N + 1),
    ∑ j : FirstWindowIndex (N + 1),
      if i < j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0

/-- Dividing an increasing pair by its GCD reindexes the literal upper
triangle by a primitive ratio and its admissible positive scale. -/
theorem gcdLcmUpperTriangle_eq_scaledReducedRatios (N : ℕ) :
    gcdLcmUpperTriangle N =
      ∑ r ∈ scaledReducedRatios (N + 1),
        (1 : ℝ) / ((r.2.1 : ℝ) * (r.1 : ℝ)) := by
  classical
  let sourceTerm := fun ij :
      FirstWindowIndex (N + 1) × FirstWindowIndex (N + 1) =>
    gcdLcmKernel (firstWindowNat ij.1) (firstWindowNat ij.2)
  let targetTerm := fun r : ℕ × (ℕ × ℕ) =>
    (1 : ℝ) / ((r.2.1 : ℝ) * (r.1 : ℝ))
  by_cases hN : N = 0
  · subst N
    have hempty : scaledReducedRatios 1 = ∅ := by
      ext r
      constructor
      · intro hr
        have hpred := (Finset.mem_filter.mp hr).2
        have hprod : 0 < r.2.2 * r.1 :=
          Nat.mul_pos hpred.2.2.2.2.1 hpred.1
        omega
      · intro hr
        simp at hr
    simp [gcdLcmUpperTriangle, FirstWindowIndex, hempty]
  · have hp2 : 2 ≤ N + 1 := by omega
    calc
      gcdLcmUpperTriangle N =
          ∑ ij ∈ upperIndexPairs (N + 1), sourceTerm ij := by
            unfold gcdLcmUpperTriangle upperIndexPairs sourceTerm
            rw [Finset.sum_filter]
            exact (Finset.sum_product Finset.univ Finset.univ
              (fun ij : FirstWindowIndex (N + 1) ×
                  FirstWindowIndex (N + 1) =>
                if ij.1 < ij.2 then
                  gcdLcmKernel (firstWindowNat ij.1) (firstWindowNat ij.2)
                else 0)).symm
      _ = ∑ r ∈ scaledReducedRatios (N + 1), targetTerm r := by
            apply Finset.sum_bij (fun ij _ => reducedTripleOfPair ij)
            · exact reducedTripleOfPair_mem hp2
            · intro ij hij uv huv
              exact reducedTripleOfPair_injective_on hp2 hij huv
            · exact reducedTripleOfPair_surjective_on hp2
            · intro ij hij
              let x := firstWindowNat ij.1
              let y := firstWindowNat ij.2
              let g := x.gcd y
              have hlt : ij.1 < ij.2 := by
                simpa [upperIndexPairs] using hij
              have hxpos : 0 < x := firstWindowNat_pos ij.1
              have hypos : 0 < y := firstWindowNat_pos ij.2
              have hxy : x < y := by
                dsimp [x, y, firstWindowNat]
                exact Nat.add_lt_add_right hlt 1
              have hgpos : 0 < g := Nat.gcd_pos_of_pos_left y hxpos
              have hgx : g ∣ x := Nat.gcd_dvd_left x y
              have hgy : g ∣ y := Nat.gcd_dvd_right x y
              have hkpos : 0 < x / g :=
                Nat.div_pos (Nat.gcd_le_left y hxpos) hgpos
              have hapos : 0 < y / g :=
                Nat.div_pos (Nat.gcd_le_right x hypos) hgpos
              have hcop : (x / g).Coprime (y / g) :=
                Nat.coprime_div_gcd_div_gcd hgpos
              change gcdLcmKernel x y = targetTerm (reducedTripleOfPair ij)
              unfold targetTerm reducedTripleOfPair
              change gcdLcmKernel x y =
                (1 : ℝ) / (((x / g : ℕ) : ℝ) * ((y / g : ℕ) : ℝ))
              calc
                gcdLcmKernel x y =
                    gcdLcmKernel (g * (x / g)) (g * (y / g)) := by
                      rw [Nat.mul_div_cancel' hgx, Nat.mul_div_cancel' hgy]
                _ = _ := gcdLcmKernel_scaled_coprime hgpos hapos hkpos hcop
      _ = ∑ r ∈ scaledReducedRatios (N + 1),
          (1 : ℝ) / ((r.2.1 : ℝ) * (r.1 : ℝ)) := rfl

/-- The scale coordinate has exactly `⌊N/a⌋` choices. -/
theorem gcdLcmScaledRatios_eq_primitiveRatios (N : ℕ) :
    (∑ r ∈ scaledReducedRatios (N + 1),
        (1 : ℝ) / ((r.2.1 : ℝ) * (r.1 : ℝ))) =
      ∑ ak ∈ reducedRatioPairs (N + 1),
        ((N / ak.1 : ℕ) : ℝ) /
          ((ak.2 : ℝ) * (ak.1 : ℝ)) := by
  classical
  let K := fun a k : ℕ => (1 : ℝ) / ((k : ℝ) * (a : ℝ))
  have hinner (a k : ℕ) :
      (∑ t ∈ Finset.range (N + 1),
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < N + 1 then K a k else 0) =
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          ((N / a : ℕ) : ℝ) * K a k else 0 := by
    by_cases hpair : 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a
    · have ha := hpair.1
      rw [if_pos hpair]
      have hpred (t : ℕ) :
          (0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < N + 1) ↔
            (0 < t ∧ t * a < N + 1) := by tauto
      simp_rw [hpred]
      rw [← Finset.sum_filter]
      change (∑ _t ∈ admissibleScales (N + 1) a, K a k) = _
      simp [admissibleScales_card ha]
    · have hfalse (t : ℕ) :
          ¬(0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < N + 1) := by
        intro h
        exact hpair ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      rw [if_neg hpair]
      apply Finset.sum_eq_zero
      intro t _
      rw [if_neg (hfalse t)]
  calc
    (∑ r ∈ scaledReducedRatios (N + 1),
        (1 : ℝ) / ((r.2.1 : ℝ) * (r.1 : ℝ))) =
      ∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∑ t ∈ Finset.range (N + 1),
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < N + 1 then K a k else 0 := by
        unfold scaledReducedRatios K
        rw [Finset.sum_filter]
        calc
          _ = ∑ a ∈ Finset.range (N + 1),
              ∑ kt ∈ (Finset.range (N + 1)).product
                  (Finset.range (N + 1)),
                if 0 < a ∧ 0 < kt.1 ∧ kt.1 < a ∧ kt.1.Coprime a ∧
                    0 < kt.2 ∧ kt.2 * a < N + 1 then
                  (1 : ℝ) / ((kt.1 : ℝ) * (a : ℝ)) else 0 :=
              Finset.sum_product _ _ _
          _ = _ := by
              apply Finset.sum_congr rfl
              intro a _
              exact Finset.sum_product _ _ _
    _ = ∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          ((N / a : ℕ) : ℝ) * K a k else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro k _
        exact hinner a k
    _ = ∑ ak ∈ reducedRatioPairs (N + 1),
        ((N / ak.1 : ℕ) : ℝ) * K ak.1 ak.2 := by
        unfold reducedRatioPairs
        rw [Finset.sum_filter]
        exact (Finset.sum_product (Finset.range (N + 1))
          (Finset.range (N + 1))
          (fun ak : ℕ × ℕ =>
            if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧
                ak.2.Coprime ak.1 then
              ((N / ak.1 : ℕ) : ℝ) * K ak.1 ak.2 else 0)).symm
    _ = ∑ ak ∈ reducedRatioPairs (N + 1),
        ((N / ak.1 : ℕ) : ℝ) /
          ((ak.2 : ℝ) * (ak.1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro ak _
        unfold K
        ring

/-- Summing primitive numerators produces exactly the reduced harmonic sum
in the continuous-capacity ledger. -/
theorem gcdLcmPrimitiveRatios_eq_reducedHarmonic (N : ℕ) :
    (∑ ak ∈ reducedRatioPairs (N + 1),
        ((N / ak.1 : ℕ) : ℝ) /
          ((ak.2 : ℝ) * (ak.1 : ℝ))) =
      ∑ a ∈ Finset.Icc 2 N,
        (((N / a : ℕ) : ℝ) / (a : ℝ)) * reducedHarmonicStar a := by
  classical
  unfold reducedRatioPairs reducedHarmonicStar
  rw [Finset.sum_filter]
  calc
    (∑ ak ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)),
        if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧ ak.2.Coprime ak.1 then
          ((N / ak.1 : ℕ) : ℝ) / ((ak.2 : ℝ) * (ak.1 : ℝ))
        else 0) =
      ∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          ((N / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ))
        else 0 := Finset.sum_product _ _ _
    _ = ∑ a ∈ Finset.Icc 2 N, ∑ k ∈ (Finset.Ico 1 a).filter
          fun k => k.Coprime a,
        ((N / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ)) := by
      have hinner (a : ℕ) (haRange : a ∈ Finset.range (N + 1)) :
          (∑ k ∈ Finset.range (N + 1),
              if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
                ((N / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ))
              else 0) =
            if a ∈ Finset.Icc 2 N then
              ∑ k ∈ (Finset.Ico 1 a).filter fun k => k.Coprime a,
                ((N / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ))
            else 0 := by
        by_cases ha : a ∈ Finset.Icc 2 N
        · rw [if_pos ha, ← Finset.sum_filter]
          have hset :
              (Finset.range (N + 1)).filter
                  (fun k => 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a) =
                (Finset.Ico 1 a).filter fun k => k.Coprime a := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
            have ha2 := (Finset.mem_Icc.mp ha).1
            have haN := (Finset.mem_Icc.mp ha).2
            constructor
            · intro h
              exact ⟨⟨by omega, h.2.2.2.1⟩, h.2.2.2.2⟩
            · intro h
              exact ⟨by omega, by omega, by omega, h.1.2, h.2⟩
          rw [hset]
        · rw [if_neg ha]
          apply Finset.sum_eq_zero
          intro k hk
          rw [if_neg]
          intro hpred
          apply ha
          have haN := Finset.mem_range.mp haRange
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have houter :
          (Finset.range (N + 1)).filter (fun a => a ∈ Finset.Icc 2 N) =
            Finset.Icc 2 N := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact fun h => h.2
        · intro h
          have haN := (Finset.mem_Icc.mp h).2
          exact ⟨by omega, h⟩
      calc
        (∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
            if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
              ((N / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ))
            else 0) =
          ∑ a ∈ Finset.range (N + 1),
            if a ∈ Finset.Icc 2 N then
              ∑ k ∈ (Finset.Ico 1 a).filter fun k => k.Coprime a,
                ((N / a : ℕ) : ℝ) / ((k : ℝ) * (a : ℝ))
            else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              exact hinner a ha
        _ = _ := by
          rw [← Finset.sum_filter, houter]
    _ = ∑ a ∈ Finset.Icc 2 N,
        (((N / a : ℕ) : ℝ) / (a : ℝ)) *
          ∑ k ∈ (Finset.Ico 1 a).filter fun k => k.Coprime a,
            (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have ha0 : (a : ℝ) ≠ 0 := by
        have ha2 := (Finset.mem_Icc.mp ha).1
        exact_mod_cast (by omega : 0 < a).ne'
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast (by
          have hk1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1).1
          omega : 0 < k).ne'
      field_simp [ha0, hk0]
    _ = _ := rfl

theorem gcdLcmUpperTriangle_eq_reducedHarmonic (N : ℕ) :
    gcdLcmUpperTriangle N =
      ∑ a ∈ Finset.Icc 2 N,
        (((N / a : ℕ) : ℝ) / (a : ℝ)) * reducedHarmonicStar a := by
  rw [gcdLcmUpperTriangle_eq_scaledReducedRatios,
    gcdLcmScaledRatios_eq_primitiveRatios,
    gcdLcmPrimitiveRatios_eq_reducedHarmonic]

/-- The strict lower triangle equals the strict upper triangle by symmetry
of the literal GCD/LCM kernel. -/
theorem gcdLcmLowerTriangle_eq_upperTriangle (N : ℕ) :
    (∑ i : FirstWindowIndex (N + 1),
        ∑ j : FirstWindowIndex (N + 1),
          if j < i then gcdLcmKernel (firstWindowNat i) (firstWindowNat j)
          else 0) = gcdLcmUpperTriangle N := by
  classical
  unfold gcdLcmUpperTriangle
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp [hij, gcdLcmKernel_comm]
  · simp [hij]

/-- Exact diagonal-plus-two-triangles decomposition of the square box. -/
theorem gcdLcmSquareSum_eq_diagonal_add_upper (N : ℕ) :
    gcdLcmSquareSum N = (N : ℝ) + 2 * gcdLcmUpperTriangle N := by
  classical
  let I := FirstWindowIndex (N + 1)
  have hsplit (i j : I) :
      gcdLcmKernel (firstWindowNat i) (firstWindowNat j) =
        (if i = j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) +
        (if i < j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) +
        (if j < i then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, ne_of_lt hij, not_lt_of_ge (le_of_lt hij)]
    · subst j
      rw [if_pos (Eq.refl i), if_neg (lt_irrefl i)]
      ring
    · simp [hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]
  unfold gcdLcmSquareSum
  rw [show
      (∑ i : I, ∑ j : I,
        gcdLcmKernel (firstWindowNat i) (firstWindowNat j)) =
      ∑ i : I, ∑ j : I,
        ((if i = j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) +
        (if i < j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) +
        (if j < i then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0)) by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j]
  simp_rw [Finset.sum_add_distrib]
  have hdiagPoint (i : I) :
      (∑ j : I,
        if i = j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) =
        1 := by
    rw [Finset.sum_eq_single i]
    · simp [gcdLcmKernel_self, firstWindowNat_pos]
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hdiag :
      (∑ i : I, ∑ j : I,
        if i = j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) =
        (N : ℝ) := by
    simp_rw [hdiagPoint]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    change ((Fintype.card (Fin N) : ℕ) : ℝ) = (N : ℝ)
    rw [Fintype.card_fin]
  rw [hdiag]
  change (N : ℝ) + gcdLcmUpperTriangle N +
      (∑ i : FirstWindowIndex (N + 1),
        ∑ j : FirstWindowIndex (N + 1),
          if j < i then gcdLcmKernel (firstWindowNat i) (firstWindowNat j)
          else 0) = _
  rw [gcdLcmLowerTriangle_eq_upperTriangle]
  ring

/-- The literal square-box GCD/LCM sum is exactly three times the Bernoulli
continuous capacity. -/
theorem gcdLcmSquareSum_eq_three_continuousCapacity (N : ℕ) :
    gcdLcmSquareSum N = 3 * continuousCapacity N := by
  rw [gcdLcmSquareSum_eq_diagonal_add_upper,
    gcdLcmUpperTriangle_eq_reducedHarmonic,
    reduced_ratio_capacity]

/-- The literal one-sided sum is the diagonal plus one strict triangle. -/
theorem gcdLcmTriangularSum_eq_diagonal_add_upper (N : ℕ) :
    gcdLcmTriangularSum N = (N : ℝ) + gcdLcmUpperTriangle N := by
  classical
  let I := FirstWindowIndex (N + 1)
  have hsplit (i j : I) :
      (if j ≤ i then gcdLcmKernel (firstWindowNat j) (firstWindowNat i) else 0) =
        (if i = j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) +
        (if j < i then gcdLcmKernel (firstWindowNat j) (firstWindowNat i) else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [ne_of_lt hij, not_le_of_gt hij,
        not_lt_of_ge (le_of_lt hij)]
    · subst j
      rw [if_pos (le_refl i), if_pos rfl, if_neg (lt_irrefl i)]
      ring
    · simp [hij, ne_of_gt hij, le_of_lt hij]
  unfold gcdLcmTriangularSum
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hdiagPoint (i : I) :
      (∑ j : I,
        if i = j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) =
        1 := by
    rw [Finset.sum_eq_single i]
    · simp [gcdLcmKernel_self, firstWindowNat_pos]
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hdiag :
      (∑ i : I, ∑ j : I,
        if i = j then gcdLcmKernel (firstWindowNat i) (firstWindowNat j) else 0) =
        (N : ℝ) := by
    simp_rw [hdiagPoint]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    change ((Fintype.card (Fin N) : ℕ) : ℝ) = (N : ℝ)
    rw [Fintype.card_fin]
  rw [hdiag]
  congr 1
  unfold gcdLcmUpperTriangle
  rw [Finset.sum_comm]

/-- Exact square-to-triangle relation from symmetry and the unit diagonal. -/
theorem gcdLcmSquareSum_eq_two_triangular_sub_diagonal (N : ℕ) :
    gcdLcmSquareSum N = 2 * gcdLcmTriangularSum N - (N : ℝ) := by
  rw [gcdLcmSquareSum_eq_diagonal_add_upper,
    gcdLcmTriangularSum_eq_diagonal_add_upper]
  ring

theorem gcdLcmTriangularSum_eq_capacity (N : ℕ) :
    gcdLcmTriangularSum N =
      ((N : ℝ) + 3 * continuousCapacity N) / 2 := by
  have hsquare := gcdLcmSquareSum_eq_two_triangular_sub_diagonal N
  rw [gcdLcmSquareSum_eq_three_continuousCapacity] at hsquare
  linarith

end NField.Alignment.GcdLcmCapacity
