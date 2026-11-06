/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetEndpointPhases
import NField.Alignment.CommonResetTailRows
import NField.Alignment.CommonResetShiftedFibers

/-! # Actual rows of all three endpoint-frequency tails -/

noncomputable section

namespace NField.Alignment.CommonResetEndpointTailRows

open scoped BigOperators
open CommonResetTailWeights CommonResetEndpointPhases CommonResetShiftedDeterminants
open CommonResetDivisorFibers CommonResetFrequencies CommonResetFourier
open CommonResetHalfFrequencies CommonResetSineEndpoint CommonResetTrigonometric

def phaseCoefficient (t u v : ℕ) (η : ℤ) : ℝ :=
  (if η = 0 then 2 else -1)/(t : ℝ)^2*
    Real.cot (halfAngle t u)*Real.cot (halfAngle t v)

theorem phaseCoefficient_bound {t u v : ℕ} (hu : 0 < u) (hut : 2*u < t)
    (hv : 0 < v) (hvt : 2*v < t) (η : ℤ) :
    |phaseCoefficient t u v η| ≤ 1/(2*(u : ℝ)*(v : ℝ)) := by
  have hu0 : 0 ≤ Real.cot (halfAngle t u) := trigonometricWeight_nonneg true hu hut
  have hv0 : 0 ≤ Real.cot (halfAngle t v) := trigonometricWeight_nonneg true hv hvt
  have hub : Real.cot (halfAngle t u) ≤ (t : ℝ)/(2*(u : ℝ)) := trigonometricWeight_le true hu hut
  have hvb : Real.cot (halfAngle t v) ≤ (t : ℝ)/(2*(v : ℝ)) := trigonometricWeight_le true hv hvt
  have hη : |(if η = 0 then 2 else -1 : ℝ)| ≤ 2 := by split_ifs <;> norm_num
  rw [phaseCoefficient, abs_mul, abs_mul, abs_div, abs_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ t by positivity), abs_of_nonneg hu0, abs_of_nonneg hv0]
  calc
    _ ≤ (2/(t : ℝ)^2)*((t : ℝ)/(2*(u : ℝ)))*((t : ℝ)/(2*(v : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul (div_le_div_of_nonneg_right hη (sq_nonneg _)) hub hu0 (by positivity)
      · exact hvb
      · exact hv0
      · positivity
    _ = _ := by
      have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
      field_simp

def phaseTail (p t u v : ℕ) (η : ℤ) (start length : ℕ) : ℝ :=
  if ht : 0 < t then
    letI : NeZero (2*t) := ⟨by omega⟩
    phaseCoefficient t u v η*
      (∑ a ∈ Finset.range length, (truncatedWeight (η == 0) t start a : ℂ)*
        ZMod.stdAddChar ((twiceEndpointPhase p v u t η : ZMod (2*t))*
          ((start+a : ℕ) : ZMod (2*t)))).im
  else 0

/-- Title: `Every linked endpoint tail is bounded by its actual centered phase`. -/
theorem phase_tail_bound {p t u v : ℕ} (hp : p.Prime) (ht : 2 ≤ t) (htp : t < p)
    (hu : 0 < u) (hut : 2*u < t) (hv : 0 < v) (hvt : 2*v < t) (hcop : u.Coprime t)
    (η : ℤ) (hη : η = 0 ∨ η = 1 ∨ η = -1)
    (start length : ℕ) (hs : 0 < start) :
    |phaseTail p t u v η start length| ≤
      ((t : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(v : ℝ)))*
        centeredReciprocal (centeredEndpointPhase p v u t η) := by
  letI : NeZero (2*t) := ⟨by omega⟩
  have hz := centeredEndpointPhase_ne_zero hp (by omega) htp hv (by omega) hcop η hη
  have hx : (twiceEndpointPhase p v u t η : ZMod (2*t)) ≠ 0 := by
    intro he
    apply hz
    change (twiceEndpointPhase p v u t η : ZMod (2*t)).valMinAbs = 0
    rw [he, ZMod.valMinAbs_zero]
  have hb := trigonometric_tail_bound_period (η == 0) t start length hs
    (twiceEndpointPhase p v u t η : ZMod (2*t)) hx
  have hIm := (Complex.abs_im_le_norm _).trans hb
  rw [phaseTail, dif_pos (by omega : 0 < t), abs_mul,
    centeredReciprocal, if_neg hz]
  calc
    _ ≤ (1/(2*(u : ℝ)*(v : ℝ)))*
        ((t : ℝ)*((2*t : ℕ) : ℝ)/(2*(start : ℝ)*
          |((twiceEndpointPhase p v u t η : ZMod (2*t)).valMinAbs : ℝ)|)) := by
      apply mul_le_mul (phaseCoefficient_bound hu hut hv hvt η) hIm (abs_nonneg _)
      positivity
    _ = _ := by
      dsimp [centeredEndpointPhase]
      push_cast
      ring

def endpointTail {t : ℕ} [NeZero t] (N q : ℕ) (u : (ZMod t)ˣ) (v : ZMod t)
    (start length : ℕ) : ℝ :=
  ∑ a ∈ Finset.range length, if 2*(start+a) < t then
    frequencyTerm N q u v ((start+a : ℕ) : ZMod t) else 0

def phaseTerm (p t u v : ℕ) (η : ℤ) (j : ℕ) : ℝ :=
  if ht : 0 < t then
    letI : NeZero (2*t) := ⟨by omega⟩
    phaseCoefficient t u v η*trigonometricWeight (η == 0) t j*
      characterSine ((twiceEndpointPhase p v u t η : ZMod (2*t))*(j : ZMod (2*t)))
  else 0

theorem phaseTail_eq_sum {p t u v : ℕ} (ht : 0 < t) (η : ℤ) (start length : ℕ) :
    phaseTail p t u v η start length =
      ∑ a ∈ Finset.range length, if 2*(start+a) < t then phaseTerm p t u v η (start+a) else 0 := by
  rw [phaseTail, dif_pos ht, Complex.im_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [phaseTerm, dif_pos ht]
  by_cases ha : 2*(start+a) < t
  · simp only [if_pos ha, truncatedWeight, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, characterSine]
    ring
  · simp only [if_neg ha, truncatedWeight, Complex.ofReal_zero, zero_mul, Complex.zero_im,
      mul_zero]

theorem phaseTerm_literal {p t u v : ℕ} (ht : 0 < t) (η : ℤ) (j : ℕ) :
    phaseTerm p t u v η j = phaseCoefficient t u v η*trigonometricWeight (η == 0) t j*
      Real.sin (2*Real.pi*(j : ℝ)*(p : ℝ)^2*(v : ℝ)*
        (DedekindInverseResidueTransform.inverseResidue u t : ℝ)/(t : ℝ)+
          (η : ℝ)*(2*(p : ℝ)-1)*halfAngle t j) := by
  rw [phaseTerm, dif_pos ht, endpoint_phase_sine ht]

/-- Title: `The endpoint frequency splits into all three literal linked phases`. -/
theorem frequencyTerm_three_phases {p t : ℕ} [NeZero t] (hp : 2 ≤ p)
    (u : (ZMod t)ˣ) (v j : ZMod t) (hj : j ∈ lowerResidues t) :
    frequencyTerm (p-1) (p^2) u v j =
      phaseTerm p t u.val.val v.val 0 j.val+
      phaseTerm p t u.val.val v.val 1 j.val+
      phaseTerm p t u.val.val v.val (-1) j.val := by
  rw [frequencyTerm_literal (p-1) (p^2) u v j hj]
  simp only [phaseTerm_literal (NeZero.pos t), phaseCoefficient, trigonometricWeight,
    beq_self_eq_true, beq_iff_eq, ite_true, Int.reduceNeg, Int.reduceEq, ite_false,
    Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, zero_add, one_mul, neg_one_mul]
  have hp1 : 1 ≤ p := by omega
  rw [Nat.cast_sub hp1, Nat.cast_one, Nat.cast_pow]
  let θ : ℝ := halfAngle t j.val
  let φ : ℝ := 2*Real.pi*(j.val : ℝ)*(p : ℝ)^2*(v.val : ℝ)*
    (DedekindInverseResidueTransform.inverseResidue u.val.val t : ℝ)/(t : ℝ)
  have hA : Real.pi*(j.val : ℝ)*((p : ℝ)-1)/(t : ℝ) = ((p : ℝ)-1)*θ := by dsimp [θ, halfAngle]; ring
  have hB : Real.pi*(j.val : ℝ)*((p : ℝ)-1+1)/(t : ℝ) = (((p : ℝ)-1)+1)*θ := by dsimp [θ, halfAngle]; ring
  rw [hA, hB]
  have he := three_sine_phases ((p : ℝ)-1) θ φ
  have hβ : 2*((p : ℝ)-1)+1 = 2*(p : ℝ)-1 := by ring
  rw [hβ] at he
  have hmul := congrArg (fun z : ℝ =>
    (Real.cot (halfAngle t u.val.val)*Real.cot (halfAngle t v.val)/(t : ℝ)^2)*z) he
  dsimp only [φ, θ, halfAngle] at hmul
  dsimp only [θ, halfAngle]
  convert hmul using 1 <;> ring

/-- Title: `The full endpoint tail is exactly the sum of its three linked phase tails`. -/
theorem endpointTail_three_phases {p t : ℕ} [NeZero t] (hp : 2 ≤ p)
    (u : (ZMod t)ˣ) (v : ZMod t) (start length : ℕ) (hs : 0 < start) :
    endpointTail (p-1) (p^2) u v start length =
      phaseTail p t u.val.val v.val 0 start length+
      phaseTail p t u.val.val v.val 1 start length+
      phaseTail p t u.val.val v.val (-1) start length := by
  rw [phaseTail_eq_sum (NeZero.pos t), phaseTail_eq_sum (NeZero.pos t),
    phaseTail_eq_sum (NeZero.pos t), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 2*(start+a) < t
  · have hval : ((start+a : ℕ) : ZMod t).val = start+a := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hj : ((start+a : ℕ) : ZMod t) ∈ lowerResidues t := by
      simp only [lowerResidues, Finset.mem_filter, Finset.mem_univ, true_and, hval]
      exact ⟨by omega, ha⟩
    simp only [if_pos ha]
    rw [frequencyTerm_three_phases hp u v _ hj, hval]
  · simp only [if_neg ha, add_zero]

end NField.Alignment.CommonResetEndpointTailRows
