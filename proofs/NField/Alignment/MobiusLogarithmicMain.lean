/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondarySeriesConsequences

/-! # The literal logarithmic error in the reciprocal-square Möbius main term -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.MobiusLogarithmicMain
open scoped BigOperators Topology
open Filter Asymptotics MobiusReciprocalSquare

def mobiusLogMain (N : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 N,
  mobiusReciprocalSquare d*Real.log ((N : ℝ)/(d : ℝ))^2
def logarithmicMomentBound : ℝ := 25*∑' d : ℕ,(d : ℝ)^(-3/2 : ℝ)

theorem logarithmic_moment_bound_nonneg : 0 ≤ logarithmicMomentBound := by
  unfold logarithmicMomentBound
  positivity

theorem mobius_log_variation {N : ℕ} (hN : 1 ≤ N) :
    |mobiusLogMain N-Real.log (N : ℝ)^2*
      (∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d)| ≤
      2*Real.log (N : ℝ)*logarithmicMomentBound := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have he : mobiusLogMain N-Real.log (N : ℝ)^2*
      (∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d)=
      ∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d*
        ((Real.log (N : ℝ)-Real.log (d : ℝ))^2-Real.log (N : ℝ)^2) := by
    rw [mobiusLogMain,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0 < d by have := (Finset.mem_Icc.mp hd).1; omega)
    rw [Real.log_div hNR.ne' hdR.ne']
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N,|mobiusReciprocalSquare d*
        ((Real.log (N : ℝ)-Real.log (d : ℝ))^2-Real.log (N : ℝ)^2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,2*Real.log (N : ℝ)*
        (|mobiusReciprocalSquare d| * (1+Real.log (d : ℝ))^2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hl0 : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
      have hlN' : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < d by have := (Finset.mem_Icc.mp hd).1; omega))
          (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
      have hsign : (Real.log (N : ℝ)-Real.log (d : ℝ))^2-Real.log (N : ℝ)^2 ≤ 0 := by
        nlinarith
      have hb : |(Real.log (N : ℝ)-Real.log (d : ℝ))^2-Real.log (N : ℝ)^2| ≤
          2*Real.log (N : ℝ)*(1+Real.log (d : ℝ))^2 := by
        rw [abs_of_nonpos hsign]
        calc
          _ ≤ 2*Real.log (N : ℝ)*Real.log (d : ℝ) := by nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith :
            Real.log (d : ℝ) ≤ (1+Real.log (d : ℝ))^2) (by positivity)
      rw [abs_mul]
      calc
        _ ≤ |mobiusReciprocalSquare d| *
            (2*Real.log (N : ℝ)*(1+Real.log (d : ℝ))^2) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = _ := by ring
    _ = 2*Real.log (N : ℝ)*∑ d ∈ Finset.Icc 1 N,
        |mobiusReciprocalSquare d| * (1+Real.log (d : ℝ))^2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mobiusLogMomentFiniteSum_le N) (by positivity)

/-- Title: `The reciprocal-square Möbius main term has only logarithmic error`. -/
theorem mobius_log_main_bound {N : ℕ} (hN : 1 ≤ N) :
    |mobiusLogMain N-(6/Real.pi^2)*Real.log (N : ℝ)^2| ≤
      (2*logarithmicMomentBound+1)*Real.log (N : ℝ) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have htail := abs_mobiusReciprocalSquare_tail_le hN
  have hlogN : Real.log (N : ℝ) ≤ N := by
    linarith [Real.log_le_sub_one_of_pos hNR]
  have htailterm :
      |Real.log (N : ℝ)^2*(∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d)-
        (6/Real.pi^2)*Real.log (N : ℝ)^2| ≤ Real.log (N : ℝ) := by
    have he : Real.log (N : ℝ)^2*(∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d)-
        (6/Real.pi^2)*Real.log (N : ℝ)^2=
        -(Real.log (N : ℝ)^2*(6/Real.pi^2-
          ∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d)) := by ring
    rw [he,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ Real.log (N : ℝ)^2*(1/(N : ℝ)) :=
        mul_le_mul_of_nonneg_left htail (sq_nonneg _)
      _ = Real.log (N : ℝ)^2/(N : ℝ) := by ring
      _ ≤ _ := (div_le_iff₀ hNR).mpr (by nlinarith)
  calc
    _ ≤ |mobiusLogMain N-Real.log (N : ℝ)^2*
          (∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d)|+
        |Real.log (N : ℝ)^2*(∑ d ∈ Finset.Icc 1 N,mobiusReciprocalSquare d)-
          (6/Real.pi^2)*Real.log (N : ℝ)^2| := abs_sub_le _ _ _
    _ ≤ 2*Real.log (N : ℝ)*logarithmicMomentBound+Real.log (N : ℝ) :=
      add_le_add (mobius_log_variation hN) htailterm
    _ = _ := by ring

theorem mobius_log_main_isBigO :
    (fun N => mobiusLogMain N-(6/Real.pi^2)*Real.log (N : ℝ)^2) =O[atTop]
      (fun N => Real.log (N : ℝ)) := by
  apply IsBigO.of_bound (2*logarithmicMomentBound+1)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.log_natCast_nonneg N)]
  exact mobius_log_main_bound hN

end NField.Alignment.MobiusLogarithmicMain
