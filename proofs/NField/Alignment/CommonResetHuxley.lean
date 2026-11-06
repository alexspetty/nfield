/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTeeth

/-! # The exact Huxley notation comparison

Huxley, Identities involving Farey fractions (2012), Lemma 3.3, defines
S1 by the reduced-residue discrepancy sum and S2 by the full grid product.
Here both are built from his literal row of teeth. The reduced-grid
bijection proves their coefficient expansions, and the endpoint correction
then gives both identities printed in the Common Reset manuscript.
-/

noncomputable section

namespace NField.Alignment.CommonResetHuxley

open scoped BigOperators
open BernoulliCurvature CommonResetTeeth CommonResetWeightedSources
open CommonResetWeightedSampling CommonResetGram RademacherThreeTerm

def teethRow (j : ℕ) (x : ℝ) : ℝ := 1/2-Int.fract ((j : ℝ)*x)

def huxleyProfile (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, c j*teethRow j x

def firstSum (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, resetWeight N c d*
    ∑ a ∈ (Finset.range d).filter (fun a => a.Coprime d),
      teethRow q ((a : ℝ)/d)*huxleyProfile N c ((a : ℝ)/d)

def secondSum (N q : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range q, huxleyProfile N c ((a : ℝ)/q)^2

theorem teethRow_grid (j a q : ℕ) : teethRow j ((a : ℝ)/q)=rationalTeeth (j*a) q := by
  unfold teethRow rationalTeeth
  rw [← mul_div_assoc, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod]

theorem reduced_grid_ratio {k : ℕ} (hk : 0 < k) (a : ℕ) :
    (a : ℝ)/k=((reduceGridPoint k a).2 : ℝ)/(reduceGridPoint k a).1 := by
  let g := a.gcd k
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hk
  have ha : (a : ℝ)=(g : ℝ)*(a/g : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a k)).symm
  have hkk : (k : ℝ)=(g : ℝ)*(k/g : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a k)).symm
  change (a : ℝ)/k=((a/g : ℕ) : ℝ)/(k/g : ℕ)
  rw [ha, hkk]
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  field_simp

/-- Title: `Every rational grid, including its origin, partitions exactly by reduced reset denominators`. -/
theorem reduced_grid_sum {R : Type*} [AddCommMonoid R] {k : ℕ} (hk : 0 < k) (F : ℝ → R) :
    (∑ a ∈ Finset.range k, F ((a : ℝ)/k))=
      ∑ d ∈ k.divisors, ∑ a ∈ (Finset.range d).filter (fun a => a.Coprime d), F ((a : ℝ)/d) := by
  calc
    _ = ∑ da ∈ reducedFractionPairs k, F ((da.2 : ℝ)/da.1) := by
      apply Finset.sum_bij (fun a _ => reduceGridPoint k a)
      · exact fun a ha => reduceGridPoint_mem hk ha
      · intro a ha b hb
        exact reduceGridPoint_injective hk ha hb
      · exact reduceGridPoint_surjective hk
      · intro a ha
        rw [reduced_grid_ratio hk]
    _ = _ := by
      unfold reducedFractionPairs
      rw [Finset.sum_filter]
      rw [show (∑ da ∈ k.divisors.product (Finset.range k),
          if da.2<da.1 ∧ da.2.Coprime da.1 then F ((da.2 : ℝ)/da.1) else 0)=
        ∑ d ∈ k.divisors, ∑ a ∈ Finset.range k,
          if a<d ∧ a.Coprime d then F ((a : ℝ)/d) else 0 from Finset.sum_product _ _ _]
      apply Finset.sum_congr rfl
      intro d hd
      have hdle := Nat.le_of_dvd hk (Nat.mem_divisors.mp hd).1
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext a
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro a ha
        rfl

theorem firstSum_coefficients (N q : ℕ) (c : ℕ → ℝ) :
    firstSum N q c=∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*teethCoefficient q k j := by
  unfold firstSum
  rw [← weighted_divisor_columns]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← reduced_grid_sum (Finset.mem_Icc.mp hj).1
    (fun x => teethRow q x*huxleyProfile N c x)]
  unfold huxleyProfile
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  unfold teethCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [teethRow_grid, teethRow_grid]
  ring

theorem secondSum_coefficients (N q : ℕ) (c : ℕ → ℝ) :
    secondSum N q c=∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j*c k*teethCoefficient j k q := by
  unfold secondSum huxleyProfile
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  unfold teethCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [teethRow_grid, teethRow_grid]
  ring

/-- Title: `Huxley's actual first reduced-residue sum is exactly half the interior source plus a quarter of the sampled reset mass`. -/
theorem firstSum_exact {q : ℕ} (hq : 0 < q) (N : ℕ) (c : ℕ → ℝ) :
    firstSum N q c=weightedInterior N q c/2+resetMass N q c/4 := by
  rw [firstSum_coefficients, weightedInterior_coefficient_sum, resetMass_gcd_sum hq]
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [teethCoefficient_exact (Finset.mem_Icc.mp hj).1]
  have he : (q.gcd k).gcd j=(j.gcd k).gcd q := by ac_rfl
  rw [he]
  ring

/-- Title: `Huxley's actual second grid sum is the printed quarter square-sum plus the complete endpoint correction`. -/
theorem secondSum_exact {q : ℕ} (hq : 0 < q) (N : ℕ) (c : ℕ → ℝ) :
    secondSum N q c=(1/4 : ℝ)*∑ a ∈ Finset.range q,
      weightedProfile N c ((a : ℝ)/q)^2+resetMass N q c/4 := by
  have he : secondSum N q c=
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j*c k*(arithmeticCoefficientDedekindTerm j k q : ℝ))+resetMass N q c/4 := by
    rw [secondSum_coefficients, resetMass_gcd_sum hq]
    simp only [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [teethCoefficient_exact hq]
    ring
  have hw := weightedSample_coefficient_sum hq N c
  unfold weightedSample at hw
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [he]
  field_simp [hqR] at hw ⊢
  nlinarith [hw]

end NField.Alignment.CommonResetHuxley
