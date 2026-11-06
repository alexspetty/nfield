/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetTailRows
import NField.Alignment.CommonResetDivisorFibers

/-! # Summing the actual linear tail over its nonzero determinant fibers -/

noncomputable section

namespace NField.Alignment.CommonResetLinearTailAssembly

open scoped BigOperators
open CommonResetTailRows CommonResetFrequencies CommonResetHalfFrequencies
open CommonResetDeterminants CommonResetDivisorFibers CommonResetSmallConductors

def naturalLinearTail (N q t u j start length : ℕ) : ℝ :=
  if ht : 0 < t then
    letI : NeZero t := ⟨ht.ne'⟩
    if hu : u.Coprime t then
      linearTail N q (ZMod.unitOfCoprime u hu) (j : ZMod t) start length
    else 0
  else 0

theorem natural_linear_tail_bound {p t u j : ℕ} (hp : p.Prime)
    (ht : 2 ≤ t) (htp : t < p) (hu : 0 < u) (hut : 2*u < t)
    (hj : 0 < j) (hjt : 2*j < t) (hcop : u.Coprime t)
    (start length : ℕ) (hs : 0 < start) :
    |naturalLinearTail (p-1) (p^2) t u j start length| ≤
      ((t : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)))*
        centeredReciprocal (centeredCarrier p j u t) := by
  letI : NeZero t := ⟨by omega⟩
  let U : (ZMod t)ˣ := ZMod.unitOfCoprime u hcop
  have hUval : U.val.val = u := by
    simp only [U, ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega : u < t)]
  have hJval : (j : ZMod t).val = j := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hU : U ∈ lowerUnits t := by simp only [lowerUnits, Finset.mem_filter,
    Finset.mem_univ, true_and, hUval]; exact ⟨hu, hut⟩
  have hJ : (j : ZMod t) ∈ lowerResidues t := by simp only [lowerResidues,
    Finset.mem_filter, Finset.mem_univ, true_and, hJval]; exact ⟨hj, hjt⟩
  have he := linear_phase_center p U (j : ZMod t)
  rw [hUval, hJval] at he
  have hz := centeredCarrier_ne_zero hp (by omega) htp hj (by omega) hcop
  have hx : (j : ZMod t)*((p^2 : ℕ) : ZMod t)*(↑(U⁻¹) : ZMod t) ≠ 0 := by
    intro hzero
    have hh := congrArg ZMod.valMinAbs hzero
    rw [he, ZMod.valMinAbs_zero] at hh
    exact hz hh
  have hb := linear_tail_bound (p-1) (p^2) U (j : ZMod t) hU hJ start length hs hx
  rw [hUval, hJval, he] at hb
  rw [naturalLinearTail, dif_pos (by omega : 0 < t), dif_pos hcop,
    centeredReciprocal, if_neg hz]
  calc
    _ ≤ (t : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)*|(centeredCarrier p j u t : ℝ)|) := hb
    _ = _ := by ring

/-- Title: `Every retained modulus in a linear tail is charged to its actual determinant`. -/
theorem fixed_linear_tail_bound {p u j : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hup : u < p) (hj : 0 < j) (hjp : j < p)
    (S : Finset ℕ) (hS : ∀ t ∈ S, 2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*j < t ∧ u.Coprime t)
    (start : ℕ) (hs : 0 < start) (length : ℕ → ℕ) :
    |∑ t ∈ S, (harmonic ((p-1)/t) : ℝ)*
      naturalLinearTail (p-1) (p^2) t u j start (length t)| ≤
        (p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/
          ((start : ℝ)*(u : ℝ)*(j : ℝ)) := by
  have hterm (t : ℕ) (htS : t ∈ S) :
      |(harmonic ((p-1)/t) : ℝ)*naturalLinearTail (p-1) (p^2) t u j start (length t)| ≤
      ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)))*
        centeredReciprocal (centeredCarrier p j u t) := by
    have htd := hS t htS
    have hb := natural_linear_tail_bound hp htd.1 htd.2.1 hu htd.2.2.1 hj htd.2.2.2.1
      htd.2.2.2.2 start (length t) hs
    have hH : (harmonic ((p-1)/t) : ℝ) ≤ (harmonic p : ℝ) :=
      harmonic_monotone ((Nat.div_le_self (p-1) t).trans (Nat.sub_le p 1))
    have htR : (t : ℝ)^2 ≤ (p : ℝ)^2 := by
      exact_mod_cast Nat.pow_le_pow_left htd.2.1.le 2
    rw [abs_mul, abs_of_nonneg (harmonic_nonneg _)]
    calc
      _ ≤ (harmonic p : ℝ)*(((t : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)))*
          centeredReciprocal (centeredCarrier p j u t)) :=
        mul_le_mul hH hb (abs_nonneg _) (harmonic_nonneg _)
      _ ≤ (harmonic p : ℝ)*(((p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)))*
          centeredReciprocal (centeredCarrier p j u t)) := by
        apply mul_le_mul_of_nonneg_left _ (harmonic_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (centeredReciprocal_nonneg _)
        exact div_le_div_of_nonneg_right htR (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ t ∈ S, |(harmonic ((p-1)/t) : ℝ)*
        naturalLinearTail (p-1) (p^2) t u j start (length t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ S, ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)))*
        centeredReciprocal (centeredCarrier p j u t) := Finset.sum_le_sum hterm
    _ = ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)))*
        ∑ t ∈ S, centeredReciprocal (centeredCarrier p j u t) := by rw [Finset.mul_sum]
    _ ≤ ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(j : ℝ)))*
        (2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact carrier_fiber_bound hp.two_le hj hjp hup S (fun t ht => by
          have hh := hS t ht
          exact ⟨by omega, hh.2.1, hh.2.2.2.2⟩)
      · exact div_nonneg (mul_nonneg (harmonic_nonneg _) (sq_nonneg _)) (by positivity)
    _ = _ := by ring

def selectedLinearTail (p U J start : ℕ) (S : ℕ → ℕ → Finset ℕ)
    (length : ℕ → ℕ → ℕ → ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 U, ∑ j ∈ Finset.Icc 1 J, ∑ t ∈ S u j,
    (harmonic ((p-1)/t) : ℝ)*naturalLinearTail (p-1) (p^2) t u j start (length u j t)

/-- Title: `All retained inverse and endpoint indices have the full linear-tail bound`. -/
theorem selected_linear_tail_bound {p : ℕ} (hp : p.Prime)
    (U J start : ℕ) (hU : U < p) (hJ : J < p) (hs : 0 < start)
    (S : ℕ → ℕ → Finset ℕ) (length : ℕ → ℕ → ℕ → ℕ)
    (hS : ∀ u ∈ Finset.Icc 1 U, ∀ j ∈ Finset.Icc 1 J, ∀ t ∈ S u j,
      2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*j < t ∧ u.Coprime t) :
    |selectedLinearTail p U J start S length| ≤
      (p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^4/(start : ℝ) := by
  have hsum : |selectedLinearTail p U J start S length| ≤
      ∑ u ∈ Finset.Icc 1 U, ∑ j ∈ Finset.Icc 1 J,
        (p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/
          ((start : ℝ)*(u : ℝ)*(j : ℝ)) := by
    unfold selectedLinearTail
    calc
      _ ≤ ∑ u ∈ Finset.Icc 1 U,
          |∑ j ∈ Finset.Icc 1 J, ∑ t ∈ S u j, (harmonic ((p-1)/t) : ℝ)*
            naturalLinearTail (p-1) (p^2) t u j start (length u j t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        exact fixed_linear_tail_bound hp (Finset.mem_Icc.mp hu).1
          (lt_of_le_of_lt (Finset.mem_Icc.mp hu).2 hU) (Finset.mem_Icc.mp hj).1
          (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 hJ) (S u j) (hS u hu j hj)
          start hs (length u j)
  have he : (∑ u ∈ Finset.Icc 1 U, ∑ j ∈ Finset.Icc 1 J,
      (p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/
        ((start : ℝ)*(u : ℝ)*(j : ℝ))) =
      ((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/(start : ℝ))*
        ((harmonic U : ℝ)*(harmonic J : ℝ)) := by
    rw [harmonic_eq_sum_Icc (n := U), harmonic_eq_sum_Icc (n := J)]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hsum
  have hH : (harmonic U : ℝ)*(harmonic J : ℝ) ≤ (harmonic p : ℝ)^2 := by
    simpa only [pow_two] using mul_le_mul (harmonic_monotone hU.le)
      (harmonic_monotone hJ.le) (harmonic_nonneg J) (harmonic_nonneg p)
  calc
    _ ≤ ((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/(start : ℝ))*
        ((harmonic U : ℝ)*(harmonic J : ℝ)) := hsum
    _ ≤ ((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/(start : ℝ))*
        (harmonic p : ℝ)^2 := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = _ := by ring

/-- Title: `The complete linear-frequency tail permits arbitrary retained moduli and initial cutoffs`. -/
theorem linear_frequency_tail_finite_bound {p : ℕ} (hp : p.Prime)
    (U J V : ℕ) (hU : U < p) (hJ : J < p) (hV : 0 < V)
    (S : ℕ → ℕ → Finset ℕ) (length : ℕ → ℕ → ℕ → ℕ)
    (hS : ∀ u ∈ Finset.Icc 1 U, ∀ j ∈ Finset.Icc 1 J, ∀ t ∈ S u j,
      2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*j < t ∧ u.Coprime t) :
    |selectedLinearTail p U J (V+1) S length| ≤
      (p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^4/(V : ℝ) := by
  apply (selected_linear_tail_bound hp U J (V+1) hU hJ (by omega) S length hS).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast hV : (0 : ℝ) < V)
  exact_mod_cast Nat.le_succ V

end NField.Alignment.CommonResetLinearTailAssembly
