/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperSourceBarrierRadii

/-!
# The critical weighted source barrier without comparison-radius inputs

The lower barrier is -a-b*j and the upper barrier a+j+10*log(j), at
positive times. The threshold may depend on the fixed nonnegative slope
b, but not on the amplitude, length, selected blocks or frequencies.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperSourceBarrier
open MeasureTheory ProbabilityTheory Set HarperPathGrid HarperPrimeBlocks HarperPrimeBlockPath
  HarperPathSuffix HarperSourceBarrierRadii HarperLogarithmicSourcePath
  HarperLogarithmicBarrier HarperCenteredPath HarperTiltedMeasure HarperEulerIntegral

def sourceBarrierEvent {n : ℕ} (x : ℝ) (l : Fin n → ℕ) (t : Fin n → ℝ) (a b : ℝ) :=
  blockPathEvent x l t (fun j => -a-b*((j.val : ℝ)+1))
    (fun j => a+((j.val : ℝ)+1)+10*Real.log ((j.val : ℝ)+1))

theorem sourceBarrierEvent_measurable {n : ℕ} (x : ℝ) (l : Fin n → ℕ)
    (t : Fin n → ℝ) (a b : ℝ) : MeasurableSet (sourceBarrierEvent x l t a b) :=
  blockPathEvent_measurable _ _ _ _ _

theorem actual_source_barrier_suffix {b : ℝ} (hb : 0 ≤ b) :
    ∃ X₀ : ℝ, ∀ x : ℝ, 1 < x → ∀ (m n : ℕ) (l : Fin ((m+1)+(n+1)) → ℕ),
      StrictAnti l → X₀ ≤ blockUpper x (l 0) → ∀ t : Fin ((m+1)+(n+1)) → ℝ,
        (∀ i, |t i| ≤ 1/(((i.val : ℝ)+1)^(2/3 : ℝ)*Real.log (blockUpper x (l i)))) →
        ∀ a : ℝ, 1 ≤ a → (m+1 : ℕ) ≤ a → a ≤ (m+1 : ℕ)+1 →
        (tiltedMeasure (sourceCutoff x) (linePoint (1/2) 0)).real (sourceBarrierEvent x l t a b) ≤
          (4*logSurvivalConstant)*min 1
            (((b+13)*a+centeredPathAllowance)/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  obtain ⟨A,hA⟩ := actual_logarithmic_block_barrier
  refine ⟨max A (Real.exp ((160*(b+20))^2)),fun x hx m n l hl hfirst t ht a ha hpa hap => ?_⟩
  have hfirstA : A ≤ blockUpper x (l 0) := (le_max_left _ _).trans hfirst
  have hfirstR : (160*(b+20))^2 ≤ Real.log (blockUpper x (l 0)) := by
    have h := Real.log_le_log (Real.exp_pos ((160*(b+20))^2)) ((le_max_right _ _).trans hfirst)
    simpa only [Real.log_exp] using h
  let ls : Fin (n+1) → ℕ := fun i => l (Fin.natAdd (m+1) i)
  let ts : Fin (n+1) → ℝ := fun i => t (Fin.natAdd (m+1) i)
  let u : Fin ((m+1)+(n+1)) → ℝ := fun j => -a-b*((j.val : ℝ)+1)
  let v : Fin ((m+1)+(n+1)) → ℝ := fun j => a+((j.val : ℝ)+1)+10*Real.log ((j.val : ℝ)+1)
  let us : Fin (n+1) → ℝ := fun j => u (Fin.natAdd (m+1) j)-v (Fin.castAdd (n+1) (Fin.last m))
  let vs : Fin (n+1) → ℝ := fun j => v (Fin.natAdd (m+1) j)-u (Fin.castAdd (n+1) (Fin.last m))
  have hrad (j : Fin (n+1)) : (b+20)*((m+1 : ℕ)+(j.val : ℝ)+1) ≤
      Real.sqrt (Real.log (blockUpper x (ls j)))/80 := by
    simpa only [ls,Fin.val_natAdd,Nat.cast_add] using
      source_radius_linear hx (by linarith : 0 ≤ b+20) hl hfirstR (Fin.natAdd (m+1) j)
  have hu (j : Fin (n+1)) : -Real.sqrt (Real.log (blockUpper x (ls j)))/80 ≤ us j := by
    have h := suffix_lower_radius hb
      (show (1 : ℝ) ≤ (m+1 : ℕ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
      (show (1 : ℝ) ≤ (j.val : ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg _)) hap
    dsimp [us,u,v]
    simp only [Nat.cast_add,Nat.cast_one,← add_assoc] at *
    linarith [hrad j]
  have hv (j : Fin (n+1)) : vs j ≤ Real.sqrt (Real.log (blockUpper x (ls j)))/80 := by
    have h := suffix_upper_radius hb
      (show (1 : ℝ) ≤ (m+1 : ℕ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
      (show (1 : ℝ) ≤ (j.val : ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg _)) hap
    dsimp [vs,u,v]
    simp only [Nat.cast_add,Nat.cast_one,← add_assoc] at *
    linarith [hrad j]
  have hbar (j : Fin (n+1)) : vs j ≤ ((j.val : ℝ)+1)+(b+13)*a+10*Real.log ((j.val : ℝ)+1) := by
    have h := suffix_upper_logarithmic hb (Nat.cast_nonneg (α := ℝ) (m+1))
      (show (1 : ℝ) ≤ (j.val : ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg _)) hpa
    dsimp [vs,u,v]
    simp only [Nat.cast_add,Nat.cast_one,← add_assoc] at *
    exact h
  have hprob := hA x hx n ls (suffix_strictAnti hl)
    (hfirstA.trans (blockUpper_antitone hx.le (hl.antitone (Fin.zero_le (Fin.natAdd (m+1) 0)))))
    ts us vs (suffix_frequency_bound hx l t ht) hu hv ((b+13)*a)
    (by nlinarith) hbar
  letI := tiltedMeasure_probability (sourceCutoff x) (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  have hsub := blockPathEvent_suffix x l t u v
  exact (measureReal_mono hsub (by finiteness)).trans hprob

end NField.Alignment.HarperSourceBarrier
