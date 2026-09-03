/-
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindReciprocity
import NField.Alignment.DedekindAbelRemainder
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Dedekind additive transform and inverse-residue inputs

This module fixes every object in the inverse-residue part of the manuscript.
The exact finite transforms and the analytic estimates are represented by
propositions about those objects.  This prevents a caller from satisfying a
theorem with unrelated functions or by passing the desired conclusion as an
unnamed hypothesis.
-/

namespace NField.Alignment.DedekindInverseResidueTransform

open scoped BigOperators ZMod ArithmeticFunction.Moebius
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.DedekindReciprocity
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindFourierMoment

/-- The extended finite Dedekind value on every residue. -/
noncomputable def extendedDedekindValue (K : ℕ) [NeZero K]
    (h : ZMod K) : ℂ :=
  (arithmeticDedekindSum h.val K : ℂ)

/-- The extended arithmetic value is the centered-sawtooth correlation on
the complete residue ring, without a unit hypothesis. -/
theorem extendedDedekindValue_eq_sum
    {K : ℕ} [NeZero K] (h : ZMod K) :
    extendedDedekindValue K h =
      ∑ x : ZMod K, centeredSawtooth x * centeredSawtooth (h * x) := by
  unfold extendedDedekindValue arithmeticDedekindSum
  rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  calc
    (∑ x : Fin K,
        ((rationalSawtooth x.val K : ℚ) : ℂ) *
          ((rationalSawtooth (h.val * x.val) K : ℚ) : ℂ)) =
      ∑ x : Fin K,
        centeredSawtooth (x.val : ZMod K) *
          centeredSawtooth (h * (x.val : ZMod K)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [← rationalSawtooth_val_eq_centeredSawtooth
              (x.val : ZMod K)]
            rw [show (x.val : ZMod K).val = x.val by
              rw [ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]]
            rw [← rationalSawtooth_val_eq_centeredSawtooth
              (h * (x.val : ZMod K))]
            congr 2
            unfold rationalSawtooth
            simp [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod,
              Nat.mod_eq_of_lt x.isLt]
    _ = ∑ x : Fin K,
        centeredSawtooth ((ZMod.finEquiv K).toEquiv x) *
          centeredSawtooth (h * (ZMod.finEquiv K).toEquiv x) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [show ((ZMod.finEquiv K).toEquiv x : ZMod K) =
                (x.val : ZMod K) by
              simpa using
                NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast x]
    _ = ∑ x : ZMod K,
        centeredSawtooth x * centeredSawtooth (h * x) :=
          (ZMod.finEquiv K).toEquiv.sum_comp
            (fun x : ZMod K =>
              centeredSawtooth x * centeredSawtooth (h * x))

/-- The unrestricted additive transform `F_K(t)`, indexed by an integer
representative `t`. -/
noncomputable def fullDedekindTransform (K t : ℕ) : ℂ :=
  if hK : K = 0 then 0 else
    letI : NeZero K := ⟨hK⟩
    ∑ h : ZMod K,
      extendedDedekindValue K h * ZMod.stdAddChar (-((t : ZMod K) * h))

/-- The unit-supported additive transform `D_K(t)`. -/
noncomputable def unitDedekindTransform (K t : ℕ) : ℂ :=
  if hK : K = 0 then 0 else
    letI : NeZero K := ⟨hK⟩
    ∑ h : (ZMod K)ˣ,
      (arithmeticDedekindSum h.val.val K : ℂ) *
        ZMod.stdAddChar (-((t : ZMod K) * h.val))

theorem fullDedekindTransform_eq_range
    {K t : ℕ} [NeZero K] (hK : 0 < K) :
    fullDedekindTransform K t =
      ∑ h ∈ Finset.range K,
        (arithmeticDedekindSum h K : ℂ) *
          ZMod.stdAddChar (-((t : ZMod K) * (h : ZMod K))) := by
  unfold fullDedekindTransform
  rw [dif_neg hK.ne']
  calc
    (∑ h : ZMod K,
        extendedDedekindValue K h *
          ZMod.stdAddChar (-((t : ZMod K) * h))) =
      ∑ h : Fin K,
        extendedDedekindValue K ((ZMod.finEquiv K).toEquiv h) *
          ZMod.stdAddChar
            (-((t : ZMod K) * (ZMod.finEquiv K).toEquiv h)) :=
        ((ZMod.finEquiv K).toEquiv.sum_comp fun h : ZMod K =>
          extendedDedekindValue K h *
            ZMod.stdAddChar (-((t : ZMod K) * h))).symm
    _ = ∑ h : Fin K,
        (arithmeticDedekindSum h.val K : ℂ) *
          ZMod.stdAddChar (-((t : ZMod K) * (h.val : ZMod K))) := by
        apply Finset.sum_congr rfl
        intro h _hh
        rw [show ((ZMod.finEquiv K).toEquiv h : ZMod K) =
            (h.val : ZMod K) by
          simpa using
            NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast h]
        simp [extendedDedekindValue, ZMod.val_natCast,
          Nat.mod_eq_of_lt h.isLt]
    _ = _ := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun h : ℕ => (arithmeticDedekindSum h K : ℂ) *
          ZMod.stdAddChar (-((t : ZMod K) * (h : ZMod K)))) K

/-- The centered sawtooth mass on the solution fiber of `n*x=t`. -/
noncomputable def solutionSawSum (K t : ℕ) [NeZero K] (n : ZMod K) : ℂ :=
  ∑ x : ZMod K,
    if n * x = (t : ZMod K) then centeredSawtooth x else 0

theorem sum_stdAddChar_mul_local
    {K : ℕ} [NeZero K] (a : ZMod K) :
    (∑ h : ZMod K, ZMod.stdAddChar (a * h)) =
      if a = 0 then (K : ℂ) else 0 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar K ha)

/-- Expanding the second sawtooth and applying additive-character
orthogonality turns the unrestricted transform into exact solution-fiber
masses. -/
theorem fullDedekindTransform_eq_fourierSolution
    {K t : ℕ} [NeZero K] :
    fullDedekindTransform K t =
      ∑ n : ZMod K,
        ZMod.dft (centeredSawtooth : ZMod K → ℂ) n * solutionSawSum K t n := by
  classical
  have hK : K ≠ 0 := NeZero.ne K
  unfold fullDedekindTransform
  rw [dif_neg hK]
  simp_rw [extendedDedekindValue_eq_sum]
  calc
    (∑ h : ZMod K,
        (∑ x : ZMod K,
          centeredSawtooth x * centeredSawtooth (h * x)) *
            ZMod.stdAddChar (-((t : ZMod K) * h))) =
      ∑ h : ZMod K, ∑ x : ZMod K,
        centeredSawtooth x * centeredSawtooth (h * x) *
          ZMod.stdAddChar (-((t : ZMod K) * h)) := by
            apply Finset.sum_congr rfl
            intro h _hh
            rw [Finset.sum_mul]
    _ = ∑ h : ZMod K, ∑ x : ZMod K,
        centeredSawtooth x *
          ((K : ℂ)⁻¹ * ∑ n : ZMod K,
            ZMod.stdAddChar (n * (h * x)) *
              ZMod.dft (centeredSawtooth : ZMod K → ℂ) n) *
          ZMod.stdAddChar (-((t : ZMod K) * h)) := by
            apply Finset.sum_congr rfl
            intro h _hh
            apply Finset.sum_congr rfl
            intro x _hx
            rw [centeredSawtooth_fourier_inversion (h * x)]
    _ = ∑ h : ZMod K, ∑ x : ZMod K, ∑ n : ZMod K,
        (K : ℂ)⁻¹ *
          ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
          centeredSawtooth x *
          ZMod.stdAddChar ((n * x - (t : ZMod K)) * h) := by
            apply Finset.sum_congr rfl
            intro h _hh
            apply Finset.sum_congr rfl
            intro x _hx
            rw [show centeredSawtooth x *
                ((K : ℂ)⁻¹ * ∑ n : ZMod K,
                  ZMod.stdAddChar (n * (h * x)) *
                    ZMod.dft (centeredSawtooth : ZMod K → ℂ) n) *
                ZMod.stdAddChar (-((t : ZMod K) * h)) =
              ∑ n : ZMod K,
                centeredSawtooth x *
                  ((K : ℂ)⁻¹ *
                    (ZMod.stdAddChar (n * (h * x)) *
                      ZMod.dft (centeredSawtooth : ZMod K → ℂ) n)) *
                  ZMod.stdAddChar (-((t : ZMod K) * h)) by
                simp only [Finset.mul_sum, Finset.sum_mul]]
            apply Finset.sum_congr rfl
            intro n _hn
            have hchar :
                ZMod.stdAddChar (n * (h * x)) *
                    ZMod.stdAddChar (-((t : ZMod K) * h)) =
                  ZMod.stdAddChar ((n * x - (t : ZMod K)) * h) := by
              rw [← AddChar.map_add_eq_mul]
              congr 1
              ring
            calc
              centeredSawtooth x *
                    ((K : ℂ)⁻¹ *
                      (ZMod.stdAddChar (n * (h * x)) *
                        ZMod.dft (centeredSawtooth : ZMod K → ℂ) n)) *
                    ZMod.stdAddChar (-((t : ZMod K) * h)) =
                (K : ℂ)⁻¹ *
                  ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
                  centeredSawtooth x *
                  (ZMod.stdAddChar (n * (h * x)) *
                    ZMod.stdAddChar (-((t : ZMod K) * h))) := by ring
              _ = _ := by rw [hchar]
    _ = ∑ x : ZMod K, ∑ h : ZMod K, ∑ n : ZMod K,
        (K : ℂ)⁻¹ *
          ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
          centeredSawtooth x *
          ZMod.stdAddChar ((n * x - (t : ZMod K)) * h) := by
            rw [Finset.sum_comm]
    _ = ∑ x : ZMod K, ∑ n : ZMod K, ∑ h : ZMod K,
        (K : ℂ)⁻¹ *
          ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
          centeredSawtooth x *
          ZMod.stdAddChar ((n * x - (t : ZMod K)) * h) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [Finset.sum_comm]
    _ = ∑ n : ZMod K, ∑ x : ZMod K, ∑ h : ZMod K,
        (K : ℂ)⁻¹ *
          ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
          centeredSawtooth x *
          ZMod.stdAddChar ((n * x - (t : ZMod K)) * h) := by
            rw [Finset.sum_comm]
    _ = ∑ n : ZMod K, ∑ x : ZMod K,
        ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
          (if n * x = (t : ZMod K) then centeredSawtooth x else 0) := by
            apply Finset.sum_congr rfl
            intro n _hn
            apply Finset.sum_congr rfl
            intro x _hx
            rw [← Finset.mul_sum,
              sum_stdAddChar_mul_local (n * x - (t : ZMod K))]
            by_cases hsol : n * x = (t : ZMod K)
            · rw [if_pos hsol, if_pos (sub_eq_zero.mpr hsol)]
              have hKC : (K : ℂ) ≠ 0 := by exact_mod_cast hK
              field_simp [hKC]
            · rw [if_neg hsol, if_neg (sub_ne_zero.mpr hsol)]
              simp
    _ = ∑ n : ZMod K,
        ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
          solutionSawSum K t n := by
            apply Finset.sum_congr rfl
            intro n _hn
            unfold solutionSawSum
            rw [Finset.mul_sum]

theorem scaled_natCast_eq_iff
    {g q a b : ℕ} (hg : g ≠ 0) :
    ((g * a : ℕ) : ZMod (g * q)) = (g * b : ℕ) ↔
      (a : ZMod q) = (b : ZMod q) := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.mul_left_cancel_iff' hg


theorem unitDedekindTransform_eq_coprimeRange
    {K t : ℕ} [NeZero K] (hK : 0 < K) :
    unitDedekindTransform K t =
      ∑ h ∈ (Finset.range K).filter fun h => h.Coprime K,
        (arithmeticDedekindSum h K : ℂ) *
          ZMod.stdAddChar (-((t : ZMod K) * (h : ZMod K))) := by
  unfold unitDedekindTransform
  rw [dif_neg hK.ne']
  apply Finset.sum_bij (fun u _hu => u.val.val)
  · intro u _hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr u.val.val_lt,
      ZMod.val_coe_unit_coprime u⟩
  · intro u₁ _hu₁ u₂ _hu₂ heq
    apply Units.ext
    apply ZMod.val_injective K
    exact heq
  · intro h hh
    have hrange : h < K := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    have hcop : h.Coprime K := (Finset.mem_filter.mp hh).2
    refine ⟨ZMod.unitOfCoprime h hcop, Finset.mem_univ _, ?_⟩
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hrange]
  · intro u _hu
    rw [ZMod.natCast_zmod_val]

/-- The inverse of `n` modulo `q`, with zero used outside the unit group. -/
noncomputable def inverseResidue (n q : ℕ) : ℕ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    if hn : n.Coprime q then
      (ZMod.unitOfCoprime n hn)⁻¹.val.val
    else 0

theorem rationalSawtooth_scale
    {c x q : ℕ} (hc : 0 < c) (hq : 0 < q) :
    rationalSawtooth (c * x) (c * q) = rationalSawtooth x q := by
  unfold rationalSawtooth
  rw [Nat.mul_mod_mul_left]
  by_cases hx : x % q = 0
  · simp [hx]
  · have hcx : c * (x % q) ≠ 0 := mul_ne_zero hc.ne' hx
    rw [if_neg hcx, if_neg hx]
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    field_simp [hcQ, hqQ]

/-- The first Bernoulli multiplication formula on one complete family of
lifts. -/
theorem sum_rationalSawtooth_lifts
    {d K y : ℕ} (hd : 0 < d) (hK : 0 < K) (hy : y < K) :
    (∑ j ∈ Finset.range d, rationalSawtooth (y + j * K) (d * K)) =
      rationalSawtooth y K := by
  have hsumRange : (∑ j ∈ Finset.range d, (j : ℚ)) =
      (d : ℚ) * ((d - 1 : ℕ) : ℚ) / 2 := by
    have htwiceNat := Finset.sum_range_id_mul_two d
    have htwice := congrArg (fun n : ℕ => (n : ℚ)) htwiceNat
    push_cast at htwice
    linarith
  have hsub : ((d - 1 : ℕ) : ℚ) = (d : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  by_cases hy0 : y = 0
  · subst y
    have hpoint : ∀ j ∈ Finset.range d,
        rationalSawtooth (0 + j * K) (d * K) =
          if j = 0 then 0 else (j : ℚ) / (d : ℚ) - 1 / 2 := by
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      by_cases hj0 : j = 0
      · subst j
        simp [rationalSawtooth_zero]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hxpos : 0 < j * K := Nat.mul_pos hjpos hK
        have hxlt : j * K < d * K := (Nat.mul_lt_mul_right hK).mpr hjd
        rw [if_neg hj0]
        simp only [zero_add]
        rw [rationalSawtooth_of_lt hxpos hxlt]
        push_cast
        have hKQ : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
        field_simp [hKQ]
    rw [Finset.sum_congr rfl hpoint]
    have herase :
        (∑ j ∈ Finset.range d,
          if j = 0 then (0 : ℚ) else (j : ℚ) / (d : ℚ) - 1 / 2) =
        ∑ j ∈ (Finset.range d).erase 0,
          ((j : ℚ) / (d : ℚ) - 1 / 2) := by
      calc
        (∑ j ∈ Finset.range d,
            if j = 0 then (0 : ℚ) else (j : ℚ) / (d : ℚ) - 1 / 2) =
            ∑ j ∈ (Finset.range d).erase 0,
              (if j = 0 then (0 : ℚ) else (j : ℚ) / (d : ℚ) - 1 / 2) := by
                symm
                apply Finset.sum_subset (Finset.erase_subset 0 (Finset.range d))
                intro j hjrange hjnot
                have hj0 : j = 0 := by
                  by_contra hjne
                  exact hjnot (Finset.mem_erase.mpr ⟨hjne, hjrange⟩)
                simp [hj0]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          exact if_neg (Finset.mem_erase.mp hj).1
    rw [herase]
    have hsum : (∑ j ∈ (Finset.range d).erase 0, (j : ℚ)) =
        (d : ℚ) * ((d - 1 : ℕ) : ℚ) / 2 := by
      have heraseSum := Finset.sum_erase_add (Finset.range d)
        (fun j : ℕ => (j : ℚ)) (Finset.mem_range.mpr hd)
      simpa using heraseSum.trans hsumRange
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_div, hsum]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr hd),
      Finset.card_range]
    rw [rationalSawtooth_zero]
    simp only [nsmul_eq_mul]
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp [hdQ]
    rw [hsub]
    ring

  · have hypos : 0 < y := Nat.pos_of_ne_zero hy0
    have hpoint : ∀ j ∈ Finset.range d,
        rationalSawtooth (y + j * K) (d * K) =
          ((y + j * K : ℕ) : ℚ) / ((d * K : ℕ) : ℚ) - 1 / 2 := by
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      have hxpos : 0 < y + j * K := Nat.add_pos_left hypos _
      have hj1 : j + 1 ≤ d := Nat.succ_le_iff.mpr hjd
      have hxlt : y + j * K < d * K := by
        calc
          y + j * K < K + j * K := Nat.add_lt_add_right hy (j * K)
          _ = (j + 1) * K := by ring
          _ ≤ d * K := Nat.mul_le_mul_right K hj1
      exact rationalSawtooth_of_lt hxpos hxlt
    rw [Finset.sum_congr rfl hpoint]
    push_cast
    have hconst : (∑ _x ∈ Finset.range d, (1 / 2 : ℚ)) =
        (d : ℚ) / 2 := by simp [nsmul_eq_mul]; ring
    have hyconst : (∑ _x ∈ Finset.range d, (y : ℚ)) =
        (d : ℚ) * (y : ℚ) := by simp [nsmul_eq_mul]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.sum_mul, hsumRange, hconst, hyconst]
    rw [rationalSawtooth_of_lt hypos hy]
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hKQ : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
    field_simp [hdQ, hKQ]
    rw [hsub]
    ring

/-- A complete interval of length `d*K` decomposes uniquely into `d` lifts
of each residue modulo `K`. -/
theorem sum_range_mul_blocks
    {R : Type*} [AddCommMonoid R] {d K : ℕ} (hK : 0 < K)
    (f : ℕ → R) :
    (∑ x ∈ Finset.range (d * K), f x) =
      ∑ y ∈ Finset.range K, ∑ j ∈ Finset.range d, f (y + j * K) := by
  rw [← Finset.sum_product (Finset.range K) (Finset.range d)
    (fun yj => f (yj.1 + yj.2 * K))]
  apply Finset.sum_bij (fun x _hx => (x % K, x / K))
  · intro x hx
    have hxlt : x < d * K := Finset.mem_range.mp hx
    exact Finset.mem_product.mpr ⟨
      Finset.mem_range.mpr (Nat.mod_lt x hK),
      Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hK).mpr (by
        simpa [Nat.mul_comm] using hxlt))⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    have hmod : x₁ % K = x₂ % K := congrArg Prod.fst heq
    have hdiv : x₁ / K = x₂ / K := congrArg Prod.snd heq
    calc
      x₁ = x₁ % K + K * (x₁ / K) := (Nat.mod_add_div x₁ K).symm
      _ = x₂ % K + K * (x₂ / K) := by rw [hmod, hdiv]
      _ = x₂ := Nat.mod_add_div x₂ K
  · intro yj hyj
    rcases yj with ⟨y, j⟩
    have hy := Finset.mem_range.mp (Finset.mem_product.mp hyj).1
    have hj := Finset.mem_range.mp (Finset.mem_product.mp hyj).2
    refine ⟨y + j * K, Finset.mem_range.mpr ?_, ?_⟩
    · calc
        y + j * K < K + j * K := Nat.add_lt_add_right hy (j * K)
        _ = (j + 1) * K := by ring
        _ ≤ d * K := Nat.mul_le_mul_right K (Nat.succ_le_iff.mpr hj)
    · apply Prod.ext
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hy]
      · change (y + j * K) / K = j
        rw [show y + j * K = y + K * j by ring,
          Nat.add_mul_div_left y j hK, Nat.div_eq_of_lt hy, zero_add]
  · intro x hx
    congr 1
    calc
      x = x % K + K * (x / K) := (Nat.mod_add_div x K).symm
      _ = x % K + x / K * K := by ring

/-- Multiples of a positive divisor in a complete interval reindex by the
quotient interval. -/
theorem sum_range_divisible_reindex
    {R : Type*} [AddCommMonoid R] {K d : ℕ}
    (hd : 0 < d) (hdK : d ∣ K) (f : ℕ → R) :
    (∑ h ∈ Finset.range K, if d ∣ h then f h else 0) =
      ∑ b ∈ Finset.range (K / d), f (d * b) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun h _hh => h / d)
  · intro h hh
    have hrange : h < K := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    have hdh : d ∣ h := (Finset.mem_filter.mp hh).2
    exact Finset.mem_range.mpr
      ((Nat.div_lt_div_right hd.ne' hdh hdK).mpr hrange)
  · intro h₁ hh₁ h₂ hh₂ heq
    have hd₁ : d ∣ h₁ := (Finset.mem_filter.mp hh₁).2
    have hd₂ : d ∣ h₂ := (Finset.mem_filter.mp hh₂).2
    calc
      h₁ = d * (h₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (h₂ / d) := by rw [heq]
      _ = h₂ := Nat.mul_div_cancel' hd₂
  · intro b hb
    have hbq : b < K / d := Finset.mem_range.mp hb
    have hK : K = d * (K / d) := (Nat.mul_div_cancel' hdK).symm
    refine ⟨d * b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, dvd_mul_right d b⟩, ?_⟩
    · rw [hK]
      exact (Nat.mul_lt_mul_left hd).mpr hbq
    · simpa [Nat.mul_comm] using Nat.mul_div_left b hd
  · intro h hh
    exact congrArg f (Nat.mul_div_cancel' (Finset.mem_filter.mp hh).2).symm

/-- Scaling both the numerator and modulus leaves the extended Dedekind value
unchanged. -/
theorem arithmeticDedekindSum_scale
    {d K b : ℕ} (hd : 0 < d) (hK : 0 < K) :
    arithmeticDedekindSum (d * b) (d * K) =
      arithmeticDedekindSum b K := by
  unfold arithmeticDedekindSum
  rw [sum_range_mul_blocks hK]
  apply Finset.sum_congr rfl
  intro y hy
  have hyK : y < K := Finset.mem_range.mp hy
  calc
    (∑ j ∈ Finset.range d,
        rationalSawtooth (y + j * K) (d * K) *
          rationalSawtooth ((d * b) * (y + j * K)) (d * K)) =
      ∑ j ∈ Finset.range d,
        rationalSawtooth (y + j * K) (d * K) *
          rationalSawtooth (b * y) K := by
            apply Finset.sum_congr rfl
            intro j _hj
            congr 1
            calc
              rationalSawtooth ((d * b) * (y + j * K)) (d * K) =
                  rationalSawtooth (d * (b * (y + j * K))) (d * K) := by
                    congr 1
                    ring
              _ = rationalSawtooth (b * (y + j * K)) K :=
                    rationalSawtooth_scale hd hK
              _ = rationalSawtooth (b * y) K := by
                    unfold rationalSawtooth
                    rw [show (b * (y + j * K)) % K = (b * y) % K by
                      rw [show b * (y + j * K) = b * y + K * (b * j) by ring,
                        Nat.add_mul_mod_self_left]]
    _ = (∑ j ∈ Finset.range d,
        rationalSawtooth (y + j * K) (d * K)) *
          rationalSawtooth (b * y) K := by rw [Finset.sum_mul]
    _ = rationalSawtooth y K * rationalSawtooth (b * y) K := by
          rw [sum_rationalSawtooth_lifts hd hK hyK]

/-- Additive characters are compatible with simultaneous scaling of their
argument and modulus. -/
theorem stdAddChar_scale
    {d q t b : ℕ} [NeZero d] [NeZero q] :
    ZMod.stdAddChar
        (-((t : ZMod (d * q)) * (d * b : ZMod (d * q)))) =
      ZMod.stdAddChar (-((t : ZMod q) * (b : ZMod q))) := by
  rw [show -((t : ZMod (d * q)) * (d * b : ZMod (d * q))) =
      ((-((t * d * b : ℕ) : ℤ) : ℤ) : ZMod (d * q)) by
        push_cast
        ring]
  rw [show -((t : ZMod q) * (b : ZMod q)) =
      ((-((t * b : ℕ) : ℤ) : ℤ) : ZMod q) by
        push_cast
        ring]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp [hdC, hqC]

theorem inverseResidue_lt
    {n q : ℕ} (hq : 0 < q) (hn : n.Coprime q) :
    inverseResidue n q < q := by
  letI : NeZero q := ⟨hq.ne'⟩
  unfold inverseResidue
  rw [dif_neg hq.ne', dif_pos hn]
  exact (ZMod.unitOfCoprime n hn)⁻¹.val.val_lt

theorem inverseResidue_coprime
    {n q : ℕ} (hq : 0 < q) (hn : n.Coprime q) :
    (inverseResidue n q).Coprime q := by
  letI : NeZero q := ⟨hq.ne'⟩
  unfold inverseResidue
  rw [dif_neg hq.ne', dif_pos hn]
  exact ZMod.val_coe_unit_coprime (ZMod.unitOfCoprime n hn)⁻¹

theorem inverseResidue_mod_of_dvd
    {Q q n : ℕ} (hQ : 0 < Q) (hq : 0 < q)
    (hQq : Q ∣ q) (hn : n.Coprime q) :
    inverseResidue n q % Q = inverseResidue n Q := by
  have hnQ : n.Coprime Q := hn.coprime_dvd_right hQq
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hmulq :
      (n : ZMod q) * (inverseResidue n q : ZMod q) = 1 := by
    unfold inverseResidue
    rw [dif_neg hq.ne', dif_pos hn]
    simp [ZMod.coe_unitOfCoprime]
  have hmulQ := congrArg (ZMod.castHom hQq (ZMod Q)) hmulq
  simp only [map_mul, map_one, ZMod.castHom_apply] at hmulQ
  have hinvQ :
      ((n : ZMod Q)⁻¹) = (inverseResidue n q : ZMod Q) :=
    ZMod.inv_eq_of_mul_eq_one Q (n : ZMod Q)
      (inverseResidue n q : ZMod Q) (by
        simpa [ZMod.cast_natCast hQq] using hmulQ)
  have hcanonical :
      ((n : ZMod Q)⁻¹) = (inverseResidue n Q : ZMod Q) := by
    unfold inverseResidue
    rw [dif_neg hQ.ne', dif_pos hnQ]
    rw [ZMod.natCast_zmod_val]
    simpa [ZMod.coe_unitOfCoprime] using
      (ZMod.inv_coe_unit (ZMod.unitOfCoprime n hnQ))
  have hz : (inverseResidue n q : ZMod Q) =
      (inverseResidue n Q : ZMod Q) := hinvQ.symm.trans hcanonical
  have hval := congrArg ZMod.val hz
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (inverseResidue_lt hQ hnQ)] using hval

/-- The periodic centered inverse-residue coefficient, extended by zero away
from the unit classes. -/
noncomputable def inverseSawCoefficient (q r n : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    if hn : n.Coprime q then
      centeredSawtooth
        ((r : ZMod q) * (ZMod.unitOfCoprime n hn)⁻¹.val)
    else 0

theorem inverseSawCoefficient_complement
    {q r u : ℕ} (hq : 2 ≤ q) (huq : u ≤ q) :
    inverseSawCoefficient q r (q - u) =
      -inverseSawCoefficient q r u := by
  have hqpos : 0 < q := by omega
  letI : NeZero q := ⟨hqpos.ne'⟩
  by_cases hu : u.Coprime q
  · have hqu : (q - u).Coprime q :=
      (Nat.coprime_self_sub_left huq).mpr hu
    unfold inverseSawCoefficient
    rw [dif_neg hqpos.ne', dif_pos hqu,
      dif_neg hqpos.ne', dif_pos hu]
    have hunit : ZMod.unitOfCoprime (q - u) hqu =
        -(ZMod.unitOfCoprime u hu) := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, Units.val_neg,
        ZMod.coe_unitOfCoprime]
      rw [Nat.cast_sub huq]
      simp
    rw [hunit, inv_neg, Units.val_neg]
    rw [show (r : ZMod q) * -(ZMod.unitOfCoprime u hu)⁻¹.val =
        -((r : ZMod q) * (ZMod.unitOfCoprime u hu)⁻¹.val) by ring]
    exact centeredSawtooth_neg hq _
  · have hqu : ¬(q - u).Coprime q := by
      simpa only [Nat.coprime_self_sub_left huq] using hu
    simp [inverseSawCoefficient, hqpos.ne', hu, hqu]

/-- One term of the centered inverse-residue harmonic series. -/
noncomputable def inverseSawTerm (q r n : ℕ) : ℂ :=
  if 0 < n then
    ((n : ℝ)⁻¹) • inverseSawCoefficient q r n
  else 0

theorem inverseSawCoefficient_add_period (q r n : ℕ) :
    inverseSawCoefficient q r (n + q) =
      inverseSawCoefficient q r n := by
  by_cases hq : q = 0
  · simp [hq]
  · simp only [inverseSawCoefficient, hq, dite_false]
    by_cases hn : n.Coprime q
    · have hn' : (n + q).Coprime q := Nat.coprime_add_self_left.mpr hn
      rw [dif_pos hn', dif_pos hn]
      have hu : ZMod.unitOfCoprime (n + q) hn' =
          ZMod.unitOfCoprime n hn := by
        apply Units.ext
        simp [ZMod.coe_unitOfCoprime]
      rw [hu]
    · have hn' : ¬(n + q).Coprime q := by
        simpa only [Nat.coprime_add_self_left] using hn
      rw [dif_neg hn', dif_neg hn]

/-- The same coefficient written intrinsically on the residue ring. -/
noncomputable def residueInverseSawCoefficient
    (q r : ℕ) [NeZero q] (x : ZMod q) : ℂ :=
  if hx : IsUnit x then
    centeredSawtooth ((r : ZMod q) * hx.unit⁻¹.val)
  else 0

theorem inverseSawCoefficient_eq_residue
    {q r n : ℕ} [NeZero q] :
    inverseSawCoefficient q r n =
      residueInverseSawCoefficient q r (n : ZMod q) := by
  have hq : q ≠ 0 := NeZero.ne q
  unfold inverseSawCoefficient residueInverseSawCoefficient
  rw [dif_neg hq]
  by_cases hn : n.Coprime q
  · rw [dif_pos hn]
    have hx : IsUnit (n : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      simpa using hn
    rw [dif_pos hx]
    have hu : hx.unit = ZMod.unitOfCoprime n hn := by
      apply Units.ext
      rw [hx.unit_spec]
      simp [ZMod.coe_unitOfCoprime]
    rw [hu]
  · rw [dif_neg hn]
    have hx : ¬IsUnit (n : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      simpa using hn
    rw [dif_neg hx]

/-- The intrinsic coefficient is exactly the manuscript's rational
sawtooth of the inverse residue. -/
theorem inverseSawCoefficient_eq_rationalSawtooth
    {q r n : ℕ} (hq : 0 < q) (hn : n.Coprime q) :
    inverseSawCoefficient q r n =
      ((rationalSawtooth (r * inverseResidue n q) q : ℚ) : ℂ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  unfold inverseSawCoefficient inverseResidue
  rw [dif_neg hq.ne', dif_pos hn, dif_neg hq.ne', dif_pos hn]
  rw [← rationalSawtooth_val_eq_centeredSawtooth]
  have hval :
      ((r : ZMod q) * (ZMod.unitOfCoprime n hn)⁻¹.val).val =
        (r * (ZMod.unitOfCoprime n hn)⁻¹.val.val) % q := by
    simp [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod]
  rw [hval]
  simp [rationalSawtooth]

theorem rationalSawtooth_eq_of_mod_eq
    {x y q : ℕ} (hxy : x % q = y % q) :
    rationalSawtooth x q = rationalSawtooth y q := by
  unfold rationalSawtooth
  rw [hxy]

/-- On a congruence fiber with a common factor `g`, Bernoulli
multiplication collapses the `g` lifts to the centered sawtooth on the true
quotient modulus. -/
theorem solutionSawSum_scaled
    {g q u r : ℕ} [NeZero g] [NeZero q]
    (hg : 0 < g) (hq : 0 < q) (huq : u.Coprime q) :
    solutionSawSum (g * q) (g * r) ((g * u : ℕ) : ZMod (g * q)) =
      inverseSawCoefficient q r u := by
  let U : (ZMod q)ˣ := ZMod.unitOfCoprime u huq
  let y₀ : ℕ := (U⁻¹.val * (r : ZMod q)).val
  have hy₀lt : y₀ < q := (U⁻¹.val * (r : ZMod q)).val_lt
  have hcondition : ∀ y ∈ Finset.range q, ∀ j ∈ Finset.range g,
      (((g * u) * (y + j * q) : ℕ) : ZMod (g * q)) =
          ((g * r : ℕ) : ZMod (g * q)) ↔
        ((u * y : ℕ) : ZMod q) = (r : ZMod q) := by
    intro y _hy j _hj
    have hscaled := scaled_natCast_eq_iff
      (g := g) (q := q) (a := u * (y + j * q)) (b := r) hg.ne'
    simpa [mul_assoc, mul_add] using hscaled
  have hunique : ∀ y ∈ Finset.range q,
      (((u * y : ℕ) : ZMod q) = (r : ZMod q) ↔ y = y₀) := by
    intro y hy
    have hylt : y < q := Finset.mem_range.mp hy
    push_cast
    rw [show (u : ZMod q) = U.val by simp [U, ZMod.coe_unitOfCoprime]]
    constructor
    · intro h
      have h' := congrArg (fun z : ZMod q => U⁻¹.val * z) h
      have hyres : (y : ZMod q) = U⁻¹.val * (r : ZMod q) := by
        simpa [mul_assoc] using h'
      have hval := congrArg ZMod.val hyres
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hylt, y₀] using hval
    · intro hy
      subst y
      have hyres : (y₀ : ZMod q) = U⁻¹.val * (r : ZMod q) := by
        unfold y₀
        exact ZMod.natCast_zmod_val (U⁻¹.val * (r : ZMod q))
      rw [hyres, ← mul_assoc, ← Units.val_mul]
      simp
  unfold solutionSawSum
  calc
    (∑ x : ZMod (g * q),
        if ((g * u : ℕ) : ZMod (g * q)) * x =
            ((g * r : ℕ) : ZMod (g * q)) then
          centeredSawtooth x else 0) =
      ∑ x : Fin (g * q),
        if (((g * u) * x.val : ℕ) : ZMod (g * q)) =
            ((g * r : ℕ) : ZMod (g * q)) then
          ((rationalSawtooth x.val (g * q) : ℚ) : ℂ) else 0 := by
            rw [← (ZMod.finEquiv (g * q)).toEquiv.sum_comp]
            apply Finset.sum_congr rfl
            intro x _hx
            rw [show ((ZMod.finEquiv (g * q)).toEquiv x : ZMod (g * q)) =
                (x.val : ZMod (g * q)) by
              simpa using
                NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast x]
            rw [← rationalSawtooth_val_eq_centeredSawtooth
              (x.val : ZMod (g * q))]
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]
            push_cast
            rfl
    _ = ∑ x ∈ Finset.range (g * q),
        if (((g * u) * x : ℕ) : ZMod (g * q)) =
            ((g * r : ℕ) : ZMod (g * q)) then
          ((rationalSawtooth x (g * q) : ℚ) : ℂ) else 0 := by
            simpa using Fin.sum_univ_eq_sum_range
              (fun x : ℕ =>
                if (((g * u) * x : ℕ) : ZMod (g * q)) =
                    ((g * r : ℕ) : ZMod (g * q)) then
                  ((rationalSawtooth x (g * q) : ℚ) : ℂ) else 0) (g * q)
    _ = ∑ y ∈ Finset.range q, ∑ j ∈ Finset.range g,
        if (((g * u) * (y + j * q) : ℕ) : ZMod (g * q)) =
            ((g * r : ℕ) : ZMod (g * q)) then
          ((rationalSawtooth (y + j * q) (g * q) : ℚ) : ℂ) else 0 := by
            simpa using sum_range_mul_blocks hq
              (fun x : ℕ =>
                if (((g * u) * x : ℕ) : ZMod (g * q)) =
                    ((g * r : ℕ) : ZMod (g * q)) then
                  ((rationalSawtooth x (g * q) : ℚ) : ℂ) else 0)
    _ = ∑ y ∈ Finset.range q,
        if ((u * y : ℕ) : ZMod q) = (r : ZMod q) then
          ((rationalSawtooth y q : ℚ) : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hsol : ((u * y : ℕ) : ZMod q) = (r : ZMod q)
            · rw [if_pos hsol]
              have hall : ∀ j ∈ Finset.range g,
                  (((g * u) * (y + j * q) : ℕ) : ZMod (g * q)) =
                    ((g * r : ℕ) : ZMod (g * q)) := by
                intro j hj
                exact (hcondition y hy j hj).mpr hsol
              calc
                (∑ j ∈ Finset.range g,
                    if (((g * u) * (y + j * q) : ℕ) : ZMod (g * q)) =
                        ((g * r : ℕ) : ZMod (g * q)) then
                      ((rationalSawtooth (y + j * q) (g * q) : ℚ) : ℂ)
                    else 0) =
                  ∑ j ∈ Finset.range g,
                    ((rationalSawtooth (y + j * q) (g * q) : ℚ) : ℂ) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      rw [if_pos (hall j hj)]
                _ = ((rationalSawtooth y q : ℚ) : ℂ) := by
                      have hlifts := sum_rationalSawtooth_lifts hg hq
                        (Finset.mem_range.mp hy)
                      exact_mod_cast hlifts
            · rw [if_neg hsol]
              apply Finset.sum_eq_zero
              intro j hj
              rw [if_neg]
              exact fun h => hsol ((hcondition y hy j hj).mp h)
    _ = ((rationalSawtooth y₀ q : ℚ) : ℂ) := by
          rw [Finset.sum_eq_single y₀]
          · rw [if_pos ((hunique y₀ (Finset.mem_range.mpr hy₀lt)).mpr rfl)]
          · intro y hy hyne
            rw [if_neg]
            exact fun h => hyne ((hunique y hy).mp h)
          · exact fun hy => (hy (Finset.mem_range.mpr hy₀lt)).elim
    _ = inverseSawCoefficient q r u := by
          rw [inverseSawCoefficient_eq_rationalSawtooth hq huq]
          norm_cast
          apply rationalSawtooth_eq_of_mod_eq
          unfold y₀ U inverseResidue
          rw [dif_neg hq.ne', dif_pos huq]
          simp [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, mul_comm]

theorem solutionSawSum_scaled_of_eq
    {K t g q u r : ℕ} [NeZero K] [NeZero g] [NeZero q]
    (hK : K = g * q) (ht : t = g * r)
    (hg : 0 < g) (hq : 0 < q) (huq : u.Coprime q) :
    solutionSawSum K t ((g * u : ℕ) : ZMod K) =
      inverseSawCoefficient q r u := by
  subst K
  subst t
  exact solutionSawSum_scaled hg hq huq

/-- Every nonzero residue `n mod K` is uniquely `g*u`, where `g=(n,K)`
and `u` is a unit modulo `K/g`. -/
theorem sum_Ico_gcd_unit_reindex
    {R : Type*} [AddCommMonoid R] {K : ℕ} (hK : 2 ≤ K) (f : ℕ → R) :
    (∑ n ∈ Finset.Ico 1 K, f n) =
      ∑ g ∈ K.divisors.filter fun g => 2 ≤ K / g,
        ∑ u ∈ (Finset.Ico 1 (K / g)).filter fun u => u.Coprime (K / g),
          f (g * u) := by
  have hKpos : 0 < K := by omega
  let G : Finset ℕ := K.divisors.filter fun g => 2 ≤ K / g
  have hmaps : ∀ n ∈ Finset.Ico 1 K, n.gcd K ∈ G := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hgpos : 0 < n.gcd K := Nat.gcd_pos_of_pos_left K hnIco.1
    have hgdvd : n.gcd K ∣ K := Nat.gcd_dvd_right n K
    have hKfactor : K = n.gcd K * (K / n.gcd K) :=
      (Nat.mul_div_cancel' hgdvd).symm
    have hqpos : 0 < K / n.gcd K := Nat.div_pos
      (Nat.gcd_le_right n hKpos) hgpos
    have hg_le_n : n.gcd K ≤ n := Nat.gcd_le_left K hnIco.1
    have hq2 : 2 ≤ K / n.gcd K := by
      by_contra hnot
      have hq1 : K / n.gcd K = 1 := by omega
      rw [hq1, mul_one] at hKfactor
      omega
    exact Finset.mem_filter.mpr ⟨
      Nat.mem_divisors.mpr ⟨hgdvd, hKpos.ne'⟩, hq2⟩
  have hinner : ∀ g ∈ G,
      (∑ n ∈ (Finset.Ico 1 K).filter fun n => n.gcd K = g, f n) =
        ∑ u ∈ (Finset.Ico 1 (K / g)).filter
            (fun u => u.Coprime (K / g)), f (g * u) := by
    intro g hgG
    have hgDiv := (Finset.mem_filter.mp hgG).1
    have hgK : g ∣ K := (Nat.mem_divisors.mp hgDiv).1
    have hgpos : 0 < g := Nat.pos_of_mem_divisors hgDiv
    have hq2 : 2 ≤ K / g := (Finset.mem_filter.mp hgG).2
    have hKfactor : K = g * (K / g) := (Nat.mul_div_cancel' hgK).symm
    apply Finset.sum_bij (fun n _hn => n / g)
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnIco := Finset.mem_Ico.mp hnData.1
      have hgcd : n.gcd K = g := hnData.2
      have hgdn : g ∣ n := by rw [← hgcd]; exact Nat.gcd_dvd_left n K
      have hnfactor : n = g * (n / g) := (Nat.mul_div_cancel' hgdn).symm
      have hupos : 1 ≤ n / g := by
        exact Nat.div_pos (Nat.le_of_dvd hnIco.1 hgdn) hgpos
      have hult : n / g < K / g := by
        rw [hnfactor, hKfactor] at hnIco
        exact (Nat.mul_lt_mul_left hgpos).mp hnIco.2
      have hcop0 := Nat.coprime_div_gcd_div_gcd
        (Nat.gcd_pos_of_pos_left K hnIco.1)
      have hcop : (n / g).Coprime (K / g) := by
        simpa [hgcd] using hcop0
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hupos, hult⟩, hcop⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      have hgd₁ : g ∣ n₁ := by
        rw [← (Finset.mem_filter.mp hn₁).2]
        exact Nat.gcd_dvd_left n₁ K
      have hgd₂ : g ∣ n₂ := by
        rw [← (Finset.mem_filter.mp hn₂).2]
        exact Nat.gcd_dvd_left n₂ K
      calc
        n₁ = g * (n₁ / g) := (Nat.mul_div_cancel' hgd₁).symm
        _ = g * (n₂ / g) := by rw [heq]
        _ = n₂ := Nat.mul_div_cancel' hgd₂
    · intro u hu
      have huData := Finset.mem_filter.mp hu
      have huIco := Finset.mem_Ico.mp huData.1
      have hcop := huData.2
      refine ⟨g * u, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact Nat.mul_pos hgpos huIco.1
      · rw [hKfactor]
        exact (Nat.mul_lt_mul_left hgpos).mpr huIco.2
      · rw [hKfactor, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
      · exact Nat.mul_div_cancel_left u hgpos
    · intro n hn
      have hgdn : g ∣ n := by
        rw [← (Finset.mem_filter.mp hn).2]
        exact Nat.gcd_dvd_left n K
      exact congrArg f (Nat.mul_div_cancel' hgdn).symm
  unfold G at hmaps hinner
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  apply Finset.sum_congr rfl
  intro g hg
  exact hinner g hg

/-- The zero Fourier mode vanishes, leaving a natural sum over the nonzero
frequencies. -/
theorem fullDedekindTransform_eq_naturalFourierSolution
    {K t : ℕ} [NeZero K] (hK : 2 ≤ K) :
    fullDedekindTransform K t =
      ∑ n ∈ Finset.Ico 1 K,
        sawtoothFourier K n * solutionSawSum K t (n : ZMod K) := by
  have hKpos : 0 < K := by omega
  rw [fullDedekindTransform_eq_fourierSolution]
  calc
    (∑ n : ZMod K,
        ZMod.dft (centeredSawtooth : ZMod K → ℂ) n *
          solutionSawSum K t n) =
      ∑ n : Fin K,
        sawtoothFourier K n.val *
          solutionSawSum K t (n.val : ZMod K) := by
            rw [← (ZMod.finEquiv K).toEquiv.sum_comp]
            apply Finset.sum_congr rfl
            intro n _hn
            rw [show ((ZMod.finEquiv K).toEquiv n : ZMod K) =
                (n.val : ZMod K) by
              simpa using
                NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast n]
            rw [sawtoothFourier_eq_dft]
    _ = ∑ n ∈ Finset.range K,
        sawtoothFourier K n * solutionSawSum K t (n : ZMod K) := by
          simpa using Fin.sum_univ_eq_sum_range
            (fun n : ℕ =>
              sawtoothFourier K n * solutionSawSum K t (n : ZMod K)) K
    _ = ∑ n ∈ Finset.Ico 1 K,
        sawtoothFourier K n * solutionSawSum K t (n : ZMod K) := by
          apply sum_range_eq_sum_Ico_one _ hKpos
          rw [sawtoothFourier_zero hKpos, zero_mul]

theorem solutionSawSum_eq_zero_of_not_dvd
    {K t g u : ℕ} [NeZero K] (hgK : g ∣ K) (hgt : ¬g ∣ t) :
    solutionSawSum K t ((g * u : ℕ) : ZMod K) = 0 := by
  unfold solutionSawSum
  apply Finset.sum_eq_zero
  intro x _hx
  rw [if_neg]
  intro hsolution
  have hnat :
      (((g * u) * x.val : ℕ) : ZMod K) = (t : ZMod K) := by
    calc
      (((g * u) * x.val : ℕ) : ZMod K) =
          ((g * u : ℕ) : ZMod K) * (x.val : ZMod K) := by push_cast; rfl
      _ = ((g * u : ℕ) : ZMod K) * x := by rw [ZMod.natCast_zmod_val]
      _ = (t : ZMod K) := hsolution
  have hmod : (g * u) * x.val ≡ t [MOD K] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hnat
  have hdvd := (hmod.dvd_iff hgK).mp (by
    rw [mul_assoc]
    exact dvd_mul_right g (u * x.val))
  exact hgt hdvd

/-- Cancelling a common numerator/modulus factor commutes with the inverse
residue coefficient whenever the summation index is a unit upstairs. -/
theorem inverseSawCoefficient_descend
    {c Q R q r n : ℕ} (hc : 0 < c) (hQ : 0 < Q)
    (hqeq : q = c * Q) (hreq : r = c * R) (hn : n.Coprime q) :
    inverseSawCoefficient q r n = inverseSawCoefficient Q R n := by
  have hq : 0 < q := by rw [hqeq]; positivity
  have hQq : Q ∣ q := by
    rw [hqeq]
    exact dvd_mul_left Q c
  have hnQ : n.Coprime Q := hn.coprime_dvd_right hQq
  rw [inverseSawCoefficient_eq_rationalSawtooth hq hn,
    inverseSawCoefficient_eq_rationalSawtooth hQ hnQ]
  norm_cast
  rw [hqeq, hreq]
  rw [show c * R * inverseResidue n (c * Q) =
      c * (R * inverseResidue n (c * Q)) by ring]
  rw [rationalSawtooth_scale hc hQ]
  apply rationalSawtooth_eq_of_mod_eq
  have hinv := inverseResidue_mod_of_dvd hQ hq hQq hn
  have hinv' : inverseResidue n (c * Q) % Q =
      inverseResidue n Q := by simpa [hqeq] using hinv
  simp [Nat.mul_mod, hinv']

theorem sum_inverseSawCoefficient_period_eq_zero
    {q r : ℕ} (hq : 0 < q) :
    (∑ n ∈ Finset.range q, inverseSawCoefficient q r n) = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  by_cases hq1 : q = 1
  · subst q
    have hr : (r : ZMod 1) = 0 := Subsingleton.elim _ _
    simp [inverseSawCoefficient, centeredSawtooth, hr]
  · have hq2 : 2 ≤ q := by omega
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (ZMod q)) IsUnit
        (residueInverseSawCoefficient q r)
    have hnonunit :
        (∑ x ∈ (Finset.univ : Finset (ZMod q)) with ¬IsUnit x,
          residueInverseSawCoefficient q r x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [residueInverseSawCoefficient, hx]
    have hresidue :
        (∑ x : ZMod q, residueInverseSawCoefficient q r x) =
          ∑ u : (ZMod q)ˣ,
            centeredSawtooth ((r : ZMod q) * u⁻¹.val) := by
      calc
        (∑ x : ZMod q, residueInverseSawCoefficient q r x) =
            ∑ x ∈ (Finset.univ : Finset (ZMod q)) with IsUnit x,
              residueInverseSawCoefficient q r x := by
                rw [← hpartition, hnonunit, add_zero]
        _ = ∑ x : {x : ZMod q // IsUnit x},
              residueInverseSawCoefficient q r x.val := by
                exact Finset.sum_subtype
                  ((Finset.univ : Finset (ZMod q)).filter IsUnit)
                  (by intro x; simp) (residueInverseSawCoefficient q r)
        _ = ∑ u : (ZMod q)ˣ,
              centeredSawtooth ((r : ZMod q) * u⁻¹.val) := by
                symm
                apply Fintype.sum_equiv unitsEquivIsUnit
                intro u
                simp only [residueInverseSawCoefficient,
                  dif_pos (unitsEquivIsUnit u).property]
                have hu : (unitsEquivIsUnit u).property.unit = u := by
                  apply Units.val_injective
                  exact (unitsEquivIsUnit u).property.unit_spec
                rw [hu]
    have hinverse :
        (∑ u : (ZMod q)ˣ,
            centeredSawtooth ((r : ZMod q) * u⁻¹.val)) =
          ∑ u : (ZMod q)ˣ,
            centeredSawtooth ((r : ZMod q) * u.val) := by
      let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := Equiv.inv _
      simpa [e] using e.sum_comp
        (fun u : (ZMod q)ˣ => centeredSawtooth ((r : ZMod q) * u.val))
    have hneg : ∀ u : (ZMod q)ˣ,
        centeredSawtooth ((r : ZMod q) * (-u).val) =
          -centeredSawtooth ((r : ZMod q) * u.val) := by
      intro u
      rw [Units.val_neg, mul_neg, centeredSawtooth_neg hq2]
    have hreindex :
        (∑ u : (ZMod q)ˣ,
            centeredSawtooth ((r : ZMod q) * (-u).val)) =
          ∑ u : (ZMod q)ˣ,
            centeredSawtooth ((r : ZMod q) * u.val) := by
      let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := Equiv.neg _
      simpa [e] using e.sum_comp
        (fun u : (ZMod q)ˣ => centeredSawtooth ((r : ZMod q) * u.val))
    have hsumzero :
        (∑ u : (ZMod q)ˣ,
            centeredSawtooth ((r : ZMod q) * u.val)) = 0 := by
      have hsumneg :
          (∑ u : (ZMod q)ˣ,
              centeredSawtooth ((r : ZMod q) * (-u).val)) =
            -∑ u : (ZMod q)ˣ,
              centeredSawtooth ((r : ZMod q) * u.val) := by
        simp_rw [hneg]
        rw [Finset.sum_neg_distrib]
      have hself := hreindex.symm.trans hsumneg
      have htwo : (2 : ℂ) ≠ 0 := by norm_num
      let S := ∑ u : (ZMod q)ˣ,
        centeredSawtooth ((r : ZMod q) * u.val)
      have hadd : S + S = S + -S := congrArg (fun z => S + z) hself
      apply (mul_eq_zero.mp (show (2 : ℂ) * S = 0 by
        rw [two_mul, hadd, add_neg_cancel])).resolve_left htwo
    calc
      (∑ n ∈ Finset.range q, inverseSawCoefficient q r n) =
          ∑ n : Fin q, inverseSawCoefficient q r n.val := by
            exact (Fin.sum_univ_eq_sum_range
              (inverseSawCoefficient q r) q).symm
      _ = ∑ x : ZMod q, residueInverseSawCoefficient q r x := by
            rw [← (ZMod.finEquiv q).toEquiv.sum_comp]
            apply Finset.sum_congr rfl
            intro n _hn
            rw [show ((ZMod.finEquiv q).toEquiv n : ZMod q) =
                (n.val : ZMod q) by
              simpa using
                NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast n]
            exact inverseSawCoefficient_eq_residue
      _ = ∑ u : (ZMod q)ˣ,
          centeredSawtooth ((r : ZMod q) * u⁻¹.val) := hresidue
      _ = ∑ u : (ZMod q)ˣ,
          centeredSawtooth ((r : ZMod q) * u.val) := hinverse
      _ = 0 := hsumzero

/-- Ordered partial sums of the manuscript's conditionally convergent
inverse-residue series.  The order is mathematically essential. -/
noncomputable def inverseSawPartial (q r N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, inverseSawTerm q r (n + 1)

theorem inverseSawPartial_eq_Icc (q r N : ℕ) :
    inverseSawPartial q r N =
      ∑ n ∈ Finset.Icc 1 N,
        (((n : ℝ)⁻¹) • inverseSawCoefficient q r n) := by
  unfold inverseSawPartial
  apply Finset.sum_bij (fun n _hn => n + 1)
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hn
      omega⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    omega
  · intro n hn
    have hI := Finset.mem_Icc.mp hn
    refine ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n hn
    simp [inverseSawTerm]

/-- Convergence of the actual ordered inverse-residue series.  Lean's
unconditional `Summable` predicate is deliberately not used here. -/
def InverseSawSeriesConverges (q r : ℕ) : Prop :=
  CauchySeq (inverseSawPartial q r)

theorem sum_shifted_inverseSawCoefficient_period_eq_zero
    {q r : ℕ} (hq : 0 < q) :
    (∑ n ∈ Finset.range q, inverseSawCoefficient q r (n + 1)) = 0 := by
  have hzero := sum_inverseSawCoefficient_period_eq_zero (q := q) (r := r) hq
  have hperiod := inverseSawCoefficient_add_period q r 0
  have hdecomp :
      inverseSawCoefficient q r 0 +
          ∑ n ∈ Finset.range q, inverseSawCoefficient q r (n + 1) =
        (∑ n ∈ Finset.range q, inverseSawCoefficient q r n) +
          inverseSawCoefficient q r q := by
    calc
      inverseSawCoefficient q r 0 +
          ∑ n ∈ Finset.range q, inverseSawCoefficient q r (n + 1) =
          (∑ n ∈ Finset.range q,
            inverseSawCoefficient q r (n + 1)) +
              inverseSawCoefficient q r 0 := add_comm _ _
      _ = ∑ n ∈ Finset.range (q + 1), inverseSawCoefficient q r n :=
        (Finset.sum_range_succ' (inverseSawCoefficient q r) q).symm
      _ = (∑ n ∈ Finset.range q, inverseSawCoefficient q r n) +
          inverseSawCoefficient q r q := Finset.sum_range_succ _ _
  have hperiod' : inverseSawCoefficient q r q =
      inverseSawCoefficient q r 0 := by simpa using hperiod
  rw [hzero, zero_add, hperiod'] at hdecomp
  have hcancel := congrArg
    (fun z : ℂ => z - inverseSawCoefficient q r 0) hdecomp
  simpa using hcancel

/-- Every inverse-residue series in the exact transform converges in its
natural order.  This is finite periodic cancellation plus Dirichlet's test,
not an external analytic input. -/
theorem inverseSawSeries_converges (q r : ℕ) :
    InverseSawSeriesConverges q r := by
  by_cases hq0 : q = 0
  · subst q
    unfold InverseSawSeriesConverges inverseSawPartial
    simpa [inverseSawTerm, inverseSawCoefficient] using
      (cauchySeq_const (0 : ℂ))
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    let z : ℕ → ℂ := fun n => inverseSawCoefficient q r (n + 1)
    let w : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
    have hzperiod : Function.Periodic z q := by
      intro n
      unfold z
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inverseSawCoefficient_add_period q r (n + 1)
    have hzzero : (∑ n ∈ Finset.range q, z n) = 0 := by
      exact sum_shifted_inverseSawCoefficient_period_eq_zero hq
    have hzbound : ∀ N,
        ‖∑ n ∈ Finset.range N, z n‖ ≤
          ∑ n ∈ Finset.range q, ‖z n‖ := by
      intro N
      exact norm_periodic_zeroMean_prefix_le hq z hzperiod hzzero N
    have hwanti : Antitone w := by
      intro a b hab
      unfold w
      simp only [inv_eq_one_div]
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.add_le_add_right hab 1
    have hwzero : Filter.Tendsto w Filter.atTop (nhds 0) := by
      simpa [w, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
            Filter.atTop (nhds 0))
    have hdirichlet :=
      hwanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hwzero hzbound
    unfold InverseSawSeriesConverges inverseSawPartial
    convert hdirichlet using 1
    funext N
    apply Finset.sum_congr rfl
    intro n _hn
    simp [inverseSawTerm, w, z]

/-- The manuscript's `B_q(r)`, defined as the limit of its natural ordered
partial sums.  `Filter.lim` is total, while the convergence predicate below
records when this value is characterized by an actual limit. -/
noncomputable def inverseSawSeries (q r : ℕ) : ℂ :=
  Filter.lim (Filter.map (inverseSawPartial q r) Filter.atTop)

/-- The defining ordered partial sums tend to the inverse-residue series. -/
theorem inverseSawPartial_tendsto (q r : ℕ) :
    Filter.Tendsto (inverseSawPartial q r) Filter.atTop
      (nhds (inverseSawSeries q r)) := by
  simpa only [inverseSawSeries, Filter.limUnder] using
    (inverseSawSeries_converges q r).tendsto_limUnder

/-- Paired reciprocal progressions attached to complementary nonzero
residues. -/
noncomputable def inverseProgressionPartial (q u M : ℕ) : ℂ :=
  ∑ j ∈ Finset.range M,
    (((u + j * q : ℕ) : ℂ)⁻¹ -
      (((q - u + j * q : ℕ) : ℂ)⁻¹))

theorem inverseProgressionPartial_eq_cotPartial
    {q u M : ℕ} (hq : 0 < q) (hu : 0 < u) (huq : u < q) :
    inverseProgressionPartial q u M =
      (q : ℂ)⁻¹ *
          (∑ j ∈ Finset.range M,
            cotTerm ((u : ℂ) / (q : ℂ)) j) +
        (u : ℂ)⁻¹ - ((u + M * q : ℕ) : ℂ)⁻¹ := by
  unfold inverseProgressionPartial
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hqu : 0 < q - u := Nat.sub_pos_of_lt huq
  have hpoint : ∀ j,
      (((u + j * q : ℕ) : ℂ)⁻¹ -
          (((q - u + j * q : ℕ) : ℂ)⁻¹)) =
        (q : ℂ)⁻¹ * cotTerm ((u : ℂ) / (q : ℂ)) j +
          (((u + j * q : ℕ) : ℂ)⁻¹ -
            (((u + (j + 1) * q : ℕ) : ℂ)⁻¹)) := by
    intro j
    simp only [cotTerm]
    have hpos1 : 0 < u + j * q := Nat.add_pos_left hu _
    have hpos2 : 0 < q - u + j * q := Nat.add_pos_left hqu _
    have hpos3 : 0 < u + (j + 1) * q := Nat.add_pos_left hu _
    have h1 : (((u + j * q : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos1.ne'
    have h2 : (((q - u + j * q : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos2.ne'
    have h3 : (((u + (j + 1) * q : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos3.ne'
    push_cast
    field_simp [hqC, huC, h1, h2, h3]
    rw [show ((q - u : ℕ) : ℂ) = (q : ℂ) - (u : ℂ) by
      rw [Nat.cast_sub (Nat.le_of_lt huq)]]
    rw [show (u : ℂ) - (q : ℂ) * ((j : ℂ) + 1) =
        -((q : ℂ) - (u : ℂ) + (j : ℂ) * (q : ℂ)) by ring,
      one_div_neg_eq_neg_one_div]
    ring
  have htelescope (a : ℕ → ℂ) (N : ℕ) :
      ∑ j ∈ Finset.range N, (a j - a (j + 1)) = a 0 - a N := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [Finset.sum_congr rfl (fun j _hj => hpoint j),
    Finset.sum_add_distrib, ← Finset.mul_sum,
    htelescope (fun j => (((u + j * q : ℕ) : ℂ)⁻¹)) M]
  simp
  ring

theorem inverseProgressionPartial_tendsto_cotangent
    {q u : ℕ} (hq : 0 < q) (hu : 0 < u) (huq : u < q) :
    Filter.Tendsto (inverseProgressionPartial q u) Filter.atTop
      (nhds ((Real.pi : ℂ) / (q : ℂ) *
        Complex.cot ((Real.pi : ℂ) * ((u : ℂ) / (q : ℂ))))) := by
  let x : ℂ := (u : ℂ) / (q : ℂ)
  have hxre : x.re = (u : ℝ) / (q : ℝ) := by
    simp [x, Complex.div_re]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [hqR]
  have hx0 : 0 < x.re := by
    rw [hxre]
    positivity
  have hx1 : x.re < 1 := by
    rw [hxre]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    exact (div_lt_one hqR).mpr (by exact_mod_cast huq)
  have hxInteger : x ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp only [Complex.intCast_re] at hre
    have hn0 : (0 : ℝ) < n := by linarith
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0' : (0 : ℤ) < n := by exact_mod_cast hn0
    have hn1' : n < (1 : ℤ) := by exact_mod_cast hn1
    omega
  have hcot := tendsto_logDeriv_euler_cot_sub hxInteger
  have hindex : Filter.Tendsto (fun M : ℕ => u + M * q)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    filter_upwards [Filter.eventually_ge_atTop b] with M hM
    have hqOne : 1 ≤ q := hq
    nlinarith
  have hinv : Filter.Tendsto
      (fun M : ℕ => (((u + M * q : ℕ) : ℂ)⁻¹))
      Filter.atTop (nhds 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp hindex
  have hconst : Filter.Tendsto (fun _ : ℕ => (u : ℂ)⁻¹)
      Filter.atTop (nhds (u : ℂ)⁻¹) := tendsto_const_nhds
  have hcombined := ((hcot.const_mul (q : ℂ)⁻¹).add
    (hconst.sub hinv))
  rw [show inverseProgressionPartial q u =
      fun M => (q : ℂ)⁻¹ *
          (∑ j ∈ Finset.range M, cotTerm x j) +
        (u : ℂ)⁻¹ - ((u + M * q : ℕ) : ℂ)⁻¹ by
    funext M
    simpa [x] using inverseProgressionPartial_eq_cotPartial
      (M := M) hq hu huq]
  convert hcombined using 1
  · funext M
    ring
  · have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    dsimp [x]
    congr 1
    field_simp [hqC, huC]
    ring

/-- The finite centered-sawtooth Fourier coefficient is exactly the
cotangent coefficient used in the manuscript. -/
theorem sawtoothFourier_eq_cotangent
    {q u : ℕ} (hq : 0 < q) (hu : 0 < u) (huq : u < q) :
    sawtoothFourier q u =
      Complex.I / 2 *
        Complex.cot ((Real.pi : ℂ) * ((u : ℂ) / (q : ℂ))) := by
  rw [sawtoothFourier_eq_root_ratio hq hu huq,
    Complex.cot_pi_eq_exp_ratio]
  let a : ℂ :=
    2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) / (q : ℂ))
  have hroot : negativeRoot q u = (Complex.exp a)⁻¹ := by
    unfold negativeRoot
    rw [← Complex.exp_neg]
    congr 1
    dsimp [a]
    ring
  have hw : Complex.exp a ≠ 0 := Complex.exp_ne_zero a
  rw [hroot]
  change -(1 + (Complex.exp a)⁻¹) /
      (2 * (1 - (Complex.exp a)⁻¹)) =
    Complex.I / 2 *
      ((Complex.exp a + 1) / (Complex.I * (1 - Complex.exp a)))
  field_simp [hw, Complex.I_ne_zero]
  rw [show Complex.exp a - 1 = -(1 - Complex.exp a) by ring, div_neg]
  ring

/-- The reciprocal progression belonging to one nonzero residue class. -/
noncomputable def inverseResidueProgressionPartial (q u M : ℕ) : ℂ :=
  ∑ j ∈ Finset.range M, (((u + j * q : ℕ) : ℂ)⁻¹)

/-- A natural partial sum cut after `M` complete residue blocks. -/
noncomputable def inverseSawBlockPartial (q r M : ℕ) : ℂ :=
  ∑ u ∈ Finset.Ico 1 q,
    inverseSawCoefficient q r u * inverseResidueProgressionPartial q u M

/-- Cutting the ordered inverse series after complete modulus blocks gives the
finite sum of its residue progressions. -/
theorem inverseSawPartial_mul_eq_block
    {q r M : ℕ} (hq : 2 ≤ q) :
    inverseSawPartial q r (M * q) = inverseSawBlockPartial q r M := by
  have hqpos : 0 < q := by omega
  have hperiod : Function.Periodic (inverseSawCoefficient q r) q :=
    inverseSawCoefficient_add_period q r
  have hzero : inverseSawCoefficient q r 0 = 0 := by
    simp [inverseSawCoefficient, hqpos.ne', Nat.coprime_zero_left,
      show q ≠ 1 by omega]
  have hqzero : inverseSawCoefficient q r q = 0 := by
    simpa using (hperiod 0).trans hzero
  unfold inverseSawPartial
  rw [sum_range_mul_blocks hqpos]
  have hinner : ∀ y ∈ Finset.range q,
      (∑ j ∈ Finset.range M,
          inverseSawTerm q r (y + j * q + 1)) =
        inverseSawCoefficient q r (y + 1) *
          inverseResidueProgressionPartial q (y + 1) M := by
    intro y _hy
    unfold inverseResidueProgressionPartial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    have hnpos : 0 < y + j * q + 1 := by omega
    have hcoefficient :
        inverseSawCoefficient q r (y + j * q + 1) =
          inverseSawCoefficient q r (y + 1) := by
      rw [show y + j * q + 1 = (y + 1) + j * q by ring]
      simpa [nsmul_eq_mul] using (hperiod.nsmul j (y + 1))
    unfold inverseSawTerm
    rw [if_pos hnpos, hcoefficient]
    rw [Complex.real_smul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hinner]
  have hdrop :
      (∑ y ∈ Finset.range q,
          inverseSawCoefficient q r (y + 1) *
            inverseResidueProgressionPartial q (y + 1) M) =
        ∑ y ∈ Finset.range (q - 1),
          inverseSawCoefficient q r (y + 1) *
            inverseResidueProgressionPartial q (y + 1) M := by
    conv_lhs =>
      rw [show q = (q - 1) + 1 by omega, Finset.sum_range_succ]
    rw [show q - 1 + 1 = q by omega, hqzero, zero_mul, add_zero]
  rw [hdrop]
  unfold inverseSawBlockPartial
  apply Finset.sum_bij (fun y _hy => y + 1)
  · intro y hy
    have hylt : y < q - 1 := Finset.mem_range.mp hy
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    omega
  · intro u hu
    have huIco := Finset.mem_Ico.mp hu
    refine ⟨u - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro y hy
    rfl

/-- Complementation permutes the nonzero representatives of a modulus. -/
theorem sum_Ico_one_complement
    {R : Type*} [AddCommMonoid R] (q : ℕ) (f : ℕ → R) :
    (∑ u ∈ Finset.Ico 1 q, f (q - u)) =
      ∑ u ∈ Finset.Ico 1 q, f u := by
  apply Finset.sum_bij (fun u _hu => q - u)
  · intro u hu
    have huIco := Finset.mem_Ico.mp hu
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro u₁ hu₁ u₂ hu₂ heq
    have h₁ := Finset.mem_Ico.mp hu₁
    have h₂ := Finset.mem_Ico.mp hu₂
    omega
  · intro v hv
    have hvIco := Finset.mem_Ico.mp hv
    refine ⟨q - v, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro u hu
    rfl

/-- The symmetric residue pairing used to pass from reciprocal progressions
to finite cotangents. -/
noncomputable def pairedInverseSawPartial (q r M : ℕ) : ℂ :=
  (1 / 2 : ℂ) * ∑ u ∈ Finset.Ico 1 q,
    inverseSawCoefficient q r u * inverseProgressionPartial q u M

/-- Complementary residues turn a complete inverse-series block into the
average of paired reciprocal progressions. -/
theorem inverseSawBlockPartial_eq_paired
    {q r M : ℕ} (hq : 2 ≤ q) :
    inverseSawBlockPartial q r M = pairedInverseSawPartial q r M := by
  let P : ℕ → ℂ := fun u => inverseResidueProgressionPartial q u M
  let c : ℕ → ℂ := fun u => inverseSawCoefficient q r u
  have hcomplement : ∀ u ∈ Finset.Ico 1 q, c (q - u) = -c u := by
    intro u hu
    have huq : u ≤ q := Nat.le_of_lt (Finset.mem_Ico.mp hu).2
    exact inverseSawCoefficient_complement hq huq
  have hreindex := sum_Ico_one_complement q (fun u => c u * P u)
  have hreindex' :
      (∑ u ∈ Finset.Ico 1 q, (-c u) * P (q - u)) =
        ∑ u ∈ Finset.Ico 1 q, c u * P u := by
    calc
      (∑ u ∈ Finset.Ico 1 q, (-c u) * P (q - u)) =
          ∑ u ∈ Finset.Ico 1 q, c (q - u) * P (q - u) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hcomplement u hu]
      _ = ∑ u ∈ Finset.Ico 1 q, c u * P u := hreindex
  have hreverse :
      (∑ u ∈ Finset.Ico 1 q, c u * P (q - u)) =
        -(∑ u ∈ Finset.Ico 1 q, c u * P u) := by
    have hneg :
        (∑ u ∈ Finset.Ico 1 q, (-c u) * P (q - u)) =
          -(∑ u ∈ Finset.Ico 1 q, c u * P (q - u)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro u _hu
      ring
    rw [hneg] at hreindex'
    calc
      (∑ u ∈ Finset.Ico 1 q, c u * P (q - u)) =
          -(-(∑ u ∈ Finset.Ico 1 q, c u * P (q - u))) := by ring
      _ = -(∑ u ∈ Finset.Ico 1 q, c u * P u) := by rw [hreindex']
  have hprogression : ∀ u,
      inverseProgressionPartial q u M = P u - P (q - u) := by
    intro u
    unfold inverseProgressionPartial P inverseResidueProgressionPartial
    rw [Finset.sum_sub_distrib]
  unfold inverseSawBlockPartial pairedInverseSawPartial
  change (∑ u ∈ Finset.Ico 1 q, c u * P u) =
    (1 / 2 : ℂ) * ∑ u ∈ Finset.Ico 1 q,
      c u * inverseProgressionPartial q u M
  have hsumProgression :
      (∑ u ∈ Finset.Ico 1 q,
          c u * inverseProgressionPartial q u M) =
        ∑ u ∈ Finset.Ico 1 q, c u * (P u - P (q - u)) := by
    apply Finset.sum_congr rfl
    intro u _hu
    rw [hprogression u]
  rw [hsumProgression]
  rw [show (∑ u ∈ Finset.Ico 1 q, c u * (P u - P (q - u))) =
      (∑ u ∈ Finset.Ico 1 q, c u * P u) -
        ∑ u ∈ Finset.Ico 1 q, c u * P (q - u) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _hu
    ring]
  rw [hreverse]
  ring_nf

/-- The finite cotangent sum attached to an inverse-residue coefficient
sequence. -/
noncomputable def finiteInverseCotangentSum (q r : ℕ) : ℂ :=
  ∑ u ∈ Finset.Ico 1 q,
    Complex.cot ((Real.pi : ℂ) * ((u : ℂ) / (q : ℂ))) *
      inverseSawCoefficient q r u

/-- The limit obtained term by term from the paired reciprocal
progressions. -/
noncomputable def pairedCotangentLimit (q r : ℕ) : ℂ :=
  (1 / 2 : ℂ) * ∑ u ∈ Finset.Ico 1 q,
    inverseSawCoefficient q r u *
      ((Real.pi : ℂ) / (q : ℂ) *
        Complex.cot ((Real.pi : ℂ) * ((u : ℂ) / (q : ℂ))))

theorem pairedInverseSawPartial_tendsto
    {q r : ℕ} (hq : 2 ≤ q) :
    Filter.Tendsto (pairedInverseSawPartial q r) Filter.atTop
      (nhds (pairedCotangentLimit q r)) := by
  have hqpos : 0 < q := by omega
  have hsum : Filter.Tendsto
      (fun M => ∑ u ∈ Finset.Ico 1 q,
        inverseSawCoefficient q r u * inverseProgressionPartial q u M)
      Filter.atTop
      (nhds (∑ u ∈ Finset.Ico 1 q,
        inverseSawCoefficient q r u *
          ((Real.pi : ℂ) / (q : ℂ) *
            Complex.cot ((Real.pi : ℂ) * ((u : ℂ) / (q : ℂ)))))) := by
    apply tendsto_finsetSum (Finset.Ico 1 q)
    intro u hu
    have huIco := Finset.mem_Ico.mp hu
    exact (inverseProgressionPartial_tendsto_cotangent
      hqpos huIco.1 huIco.2).const_mul (inverseSawCoefficient q r u)
  unfold pairedInverseSawPartial pairedCotangentLimit
  exact hsum.const_mul (1 / 2 : ℂ)

theorem pairedCotangentLimit_eq_finiteSum
    {q r : ℕ} (hq : 0 < q) :
    pairedCotangentLimit q r =
      (Real.pi : ℂ) / (2 * (q : ℂ)) * finiteInverseCotangentSum q r := by
  unfold pairedCotangentLimit finiteInverseCotangentSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp [hqC]

/-- The conditionally convergent inverse-residue series is exactly its finite
cotangent sum.  The proof uses natural-order block subsequences and uniqueness
of limits, so no unconditional rearrangement is hidden. -/
theorem inverseSawSeries_eq_cotangent_sum
    {q r : ℕ} (hq : 2 ≤ q) :
    inverseSawSeries q r =
      (Real.pi : ℂ) / (2 * (q : ℂ)) * finiteInverseCotangentSum q r := by
  have hqpos : 0 < q := by omega
  have hindex : Filter.Tendsto (fun M : ℕ => M * q)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    filter_upwards [Filter.eventually_ge_atTop b] with M hM
    have hqOne : 1 ≤ q := by omega
    nlinarith
  have hseries := (inverseSawPartial_tendsto q r).comp hindex
  have hblocks : (fun M => inverseSawPartial q r (M * q)) =
      pairedInverseSawPartial q r := by
    funext M
    exact (inverseSawPartial_mul_eq_block hq).trans
      (inverseSawBlockPartial_eq_paired hq)
  change Filter.Tendsto (fun M => inverseSawPartial q r (M * q))
    Filter.atTop (nhds (inverseSawSeries q r)) at hseries
  rw [hblocks] at hseries
  have hpaired := pairedInverseSawPartial_tendsto (q := q) (r := r) hq
  rw [← pairedCotangentLimit_eq_finiteSum hqpos]
  exact tendsto_nhds_unique hseries hpaired

theorem finiteInverseCotangentSum_eq_coprimeFilter
    {q r : ℕ} (hq : 0 < q) :
    finiteInverseCotangentSum q r =
      ∑ u ∈ (Finset.Ico 1 q).filter fun u => u.Coprime q,
        Complex.cot ((Real.pi : ℂ) * ((u : ℂ) / (q : ℂ))) *
          inverseSawCoefficient q r u := by
  unfold finiteInverseCotangentSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases hcop : u.Coprime q
  · rw [if_pos hcop]
  · rw [if_neg hcop]
    simp [inverseSawCoefficient, hq.ne', hcop]

/-- The finite cotangent form of the unrestricted Dedekind transform. -/
noncomputable def fullFiniteCotangentSide (K t : ℕ) : ℂ :=
  Complex.I / 2 *
    ∑ g ∈ (K.gcd t).divisors.filter fun g => 2 ≤ K / g,
      finiteInverseCotangentSum (K / g) (t / g)

/-- The unrestricted additive transform is exactly the finite cotangent sum
obtained by Fourier expansion and congruence-fiber descent. -/
theorem fullDedekindTransform_eq_finiteCotangent
    {K t : ℕ} (hK : 2 ≤ K) :
    fullDedekindTransform K t = fullFiniteCotangentSide K t := by
  have hKpos : 0 < K := by omega
  letI : NeZero K := ⟨hKpos.ne'⟩
  rw [fullDedekindTransform_eq_naturalFourierSolution hK,
    sum_Ico_gcd_unit_reindex hK]
  calc
    (∑ g ∈ K.divisors.filter fun g => 2 ≤ K / g,
        ∑ u ∈ (Finset.Ico 1 (K / g)).filter
            (fun u => u.Coprime (K / g)),
          sawtoothFourier K (g * u) *
            solutionSawSum K t ((g * u : ℕ) : ZMod K)) =
      ∑ g ∈ K.divisors.filter fun g => 2 ≤ K / g,
        if g ∣ t then
          Complex.I / 2 * finiteInverseCotangentSum (K / g) (t / g)
        else 0 := by
          apply Finset.sum_congr rfl
          intro g hg
          have hgDiv := (Finset.mem_filter.mp hg).1
          have hgK : g ∣ K := (Nat.mem_divisors.mp hgDiv).1
          have hgpos : 0 < g := Nat.pos_of_mem_divisors hgDiv
          have hq2 : 2 ≤ K / g := (Finset.mem_filter.mp hg).2
          have hqpos : 0 < K / g := by omega
          have hKfactor : K = g * (K / g) := (Nat.mul_div_cancel' hgK).symm
          by_cases hgt : g ∣ t
          · rw [if_pos hgt]
            have htfactor : t = g * (t / g) := (Nat.mul_div_cancel' hgt).symm
            letI : NeZero g := ⟨hgpos.ne'⟩
            letI : NeZero (K / g) := ⟨hqpos.ne'⟩
            calc
              (∑ u ∈ (Finset.Ico 1 (K / g)).filter
                    (fun u => u.Coprime (K / g)),
                  sawtoothFourier K (g * u) *
                    solutionSawSum K t ((g * u : ℕ) : ZMod K)) =
                ∑ u ∈ (Finset.Ico 1 (K / g)).filter
                    (fun u => u.Coprime (K / g)),
                  (Complex.I / 2 *
                    Complex.cot ((Real.pi : ℂ) *
                      ((u : ℂ) / ((K / g : ℕ) : ℂ)))) *
                    inverseSawCoefficient (K / g) (t / g) u := by
                      apply Finset.sum_congr rfl
                      intro u hu
                      have huData := Finset.mem_filter.mp hu
                      have huIco := Finset.mem_Ico.mp huData.1
                      have hcop := huData.2
                      have hguPos : 0 < g * u := Nat.mul_pos hgpos huIco.1
                      have hguLt : g * u < K := by
                        rw [hKfactor]
                        exact (Nat.mul_lt_mul_left hgpos).mpr huIco.2
                      have hangle :
                          ((g * u : ℕ) : ℂ) / (K : ℂ) =
                            (u : ℂ) / ((K / g : ℕ) : ℂ) := by
                        have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
                        have hqC : ((K / g : ℕ) : ℂ) ≠ 0 := by
                          exact_mod_cast hqpos.ne'
                        have hKfactorC : (K : ℂ) =
                            (g : ℂ) * ((K / g : ℕ) : ℂ) := by
                          exact_mod_cast hKfactor
                        rw [hKfactorC]
                        push_cast
                        field_simp [hgC, hqC]
                      have hsolution :
                          solutionSawSum K t ((g * u : ℕ) : ZMod K) =
                            inverseSawCoefficient (K / g) (t / g) u := by
                        exact solutionSawSum_scaled_of_eq
                          hKfactor htfactor hgpos hqpos hcop
                      rw [sawtoothFourier_eq_cotangent
                        hKpos hguPos hguLt, hangle, hsolution]
              _ = Complex.I / 2 *
                    ∑ u ∈ (Finset.Ico 1 (K / g)).filter
                        (fun u => u.Coprime (K / g)),
                      Complex.cot ((Real.pi : ℂ) *
                        ((u : ℂ) / ((K / g : ℕ) : ℂ))) *
                        inverseSawCoefficient (K / g) (t / g) u := by
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro u _hu
                          ring
              _ = Complex.I / 2 *
                    finiteInverseCotangentSum (K / g) (t / g) := by
                      rw [finiteInverseCotangentSum_eq_coprimeFilter hqpos]
          · rw [if_neg hgt]
            apply Finset.sum_eq_zero
            intro u _hu
            rw [solutionSawSum_eq_zero_of_not_dvd hgK hgt, mul_zero]
    _ = Complex.I / 2 *
        ∑ g ∈ K.divisors.filter fun g => 2 ≤ K / g,
          if g ∣ t then finiteInverseCotangentSum (K / g) (t / g) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g _hg
            by_cases hgt : g ∣ t <;> simp [hgt]
    _ = fullFiniteCotangentSide K t := by
          have hset :
              (K.divisors.filter fun g => 2 ≤ K / g).filter (fun g => g ∣ t) =
                (K.gcd t).divisors.filter fun g => 2 ≤ K / g := by
            ext g
            simp only [Finset.mem_filter, Nat.mem_divisors]
            have hgcd0 : K.gcd t ≠ 0 := Nat.gcd_ne_zero_left hKpos.ne'
            constructor
            · rintro ⟨⟨⟨hgK, _hK0⟩, hq⟩, hgt⟩
              exact ⟨⟨Nat.dvd_gcd hgK hgt, hgcd0⟩, hq⟩
            · rintro ⟨⟨hgGcd, _hgcd0⟩, hq⟩
              exact ⟨⟨⟨hgGcd.trans (Nat.gcd_dvd_left K t), hKpos.ne'⟩, hq⟩,
                hgGcd.trans (Nat.gcd_dvd_right K t)⟩
          unfold fullFiniteCotangentSide
          rw [← Finset.sum_filter, hset]

theorem inverseSawCoefficient_mod_numerator (q r n : ℕ) :
    inverseSawCoefficient q (r % q) n = inverseSawCoefficient q r n := by
  by_cases hq : q = 0
  · simp [hq, inverseSawCoefficient]
  · letI : NeZero q := ⟨hq⟩
    unfold inverseSawCoefficient
    rw [dif_neg hq, dif_neg hq]
    by_cases hn : n.Coprime q
    · rw [dif_pos hn, dif_pos hn]
      congr 1
      simp
    · rw [dif_neg hn, dif_neg hn]

theorem inverseSawPartial_mod_numerator (q r N : ℕ) :
    inverseSawPartial q (r % q) N = inverseSawPartial q r N := by
  unfold inverseSawPartial inverseSawTerm
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hn : 0 < n + 1
  · rw [if_pos hn, if_pos hn, inverseSawCoefficient_mod_numerator]
  · rw [if_neg hn, if_neg hn]

theorem inverseSawSeries_mod_numerator (q r : ℕ) :
    inverseSawSeries q (r % q) = inverseSawSeries q r := by
  unfold inverseSawSeries
  congr 2
  funext N
  exact inverseSawPartial_mod_numerator q r N

/-- The largest inverse-residue series on the unit classes of a nonzero
modulus. -/
noncomputable def inverseSawUnitMaximum (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    Finset.univ.sup' Finset.univ_nonempty
      (fun u : (ZMod q)ˣ => ‖inverseSawSeries q u.val.val‖)

theorem norm_inverseSawSeries_le_unitMaximum
    {q r : ℕ} [NeZero q] (hr : r.Coprime q) :
    ‖inverseSawSeries q r‖ ≤ inverseSawUnitMaximum q := by
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime r hr
  have huval : u.val.val = r % q := by
    simp [u, ZMod.val_natCast]
  have hseries : inverseSawSeries q r = inverseSawSeries q u.val.val := by
    rw [huval]
    exact (inverseSawSeries_mod_numerator q r).symm
  rw [hseries]
  rw [inverseSawUnitMaximum, dif_neg (NeZero.ne q)]
  exact Finset.le_sup'
    (fun v : (ZMod q)ˣ => ‖inverseSawSeries q v.val.val‖)
    (Finset.mem_univ u)

theorem inverseSawUnitMaximum_nonneg (q : ℕ) :
    0 ≤ inverseSawUnitMaximum q := by
  by_cases hq : q = 0
  · simp [inverseSawUnitMaximum, hq]
  · letI : NeZero q := ⟨hq⟩
    rw [inverseSawUnitMaximum, dif_neg hq]
    calc
      0 ≤ ‖inverseSawSeries q (1 : (ZMod q)ˣ).val.val‖ := norm_nonneg _
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun u : (ZMod q)ˣ => ‖inverseSawSeries q u.val.val‖) :=
        Finset.le_sup'
          (fun u : (ZMod q)ˣ => ‖inverseSawSeries q u.val.val‖)
          (Finset.mem_univ (1 : (ZMod q)ˣ))

/-- A pointwise bound on every unit numerator bounds the finite unit maximum.
This is the exact bridge used when the published inverse-fraction estimate is
inserted into numerator descent. -/
theorem inverseSawUnitMaximum_le
    {q : ℕ} (hq : 0 < q) {M : ℝ}
    (hunit : ∀ r, r.Coprime q → ‖inverseSawSeries q r‖ ≤ M) :
    inverseSawUnitMaximum q ≤ M := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [inverseSawUnitMaximum, dif_neg hq.ne']
  rw [Finset.sup'_le_iff]
  intro u _hu
  exact hunit u.val.val (ZMod.val_coe_unit_coprime u)

/-- The full-transform inverse-series side. -/
noncomputable def fullTransformSeriesSide (K t : ℕ) : ℂ :=
  -(1 / (Real.pi * Complex.I)) *
    ∑ g ∈ (K.gcd t).divisors.filter fun g => 2 ≤ K / g,
      (1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)

/-- Convergence of every descended ordered series that occurs in the full
transform formula. -/
def FullTransformSeriesConverges (K t : ℕ) : Prop :=
  ∀ g ∈ (K.gcd t).divisors.filter fun g => 2 ≤ K / g,
    InverseSawSeriesConverges (K / g) (t / g)

theorem fullTransformSeries_converges (K t : ℕ) :
    FullTransformSeriesConverges K t := by
  intro g _hg
  exact inverseSawSeries_converges (K / g) (t / g)

/-- The finite Möbius restriction of the unrestricted transforms. -/
noncomputable def unitTransformMobiusSide (K t : ℕ) : ℂ :=
  ∑ d ∈ K.divisors,
    (ArithmeticFunction.moebius d : ℂ) *
      fullDedekindTransform (K / d) t

/-- The remaining analytic passage in the exact additive transform: the
finite cotangent transform followed by the justified Abel limit. -/
def FullTransformSeriesIdentity (K : ℕ) : Prop :=
  ∀ t, fullDedekindTransform K t / (K : ℂ) =
    fullTransformSeriesSide K t

/-- The finite cotangent formula and the natural-order Abel limit prove the
full inverse-series transform identity. -/
theorem fullTransformSeries_identity
    {K : ℕ} (hK : 2 ≤ K) : FullTransformSeriesIdentity K := by
  intro t
  have hKpos : 0 < K := by omega
  rw [fullDedekindTransform_eq_finiteCotangent hK]
  unfold fullFiniteCotangentSide fullTransformSeriesSide
  let S := (K.gcd t).divisors.filter fun g => 2 ≤ K / g
  have hseriesTerms :
      (∑ g ∈ S, (1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)) =
        ∑ g ∈ S, (1 / (g : ℂ)) *
          ((Real.pi : ℂ) / (2 * ((K / g : ℕ) : ℂ)) *
            finiteInverseCotangentSum (K / g) (t / g)) := by
    apply Finset.sum_congr rfl
    intro g hg
    have hq2 : 2 ≤ K / g := (Finset.mem_filter.mp hg).2
    rw [inverseSawSeries_eq_cotangent_sum hq2]
  rw [hseriesTerms, div_eq_mul_inv]
  change
    (Complex.I / 2 *
          (∑ g ∈ S, finiteInverseCotangentSum (K / g) (t / g))) *
        (K : ℂ)⁻¹ =
      -(1 / ((Real.pi : ℂ) * Complex.I)) *
        ∑ g ∈ S, (1 / (g : ℂ)) *
          ((Real.pi : ℂ) / (2 * ((K / g : ℕ) : ℂ)) *
            finiteInverseCotangentSum (K / g) (t / g))
  rw [show
      (Complex.I / 2 *
          (∑ g ∈ S, finiteInverseCotangentSum (K / g) (t / g))) *
          (K : ℂ)⁻¹ =
        ∑ g ∈ S, (Complex.I / 2) *
          finiteInverseCotangentSum (K / g) (t / g) * (K : ℂ)⁻¹ by
    rw [Finset.mul_sum, Finset.sum_mul]]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hgDivGcd := (Finset.mem_filter.mp hg).1
  have hgGcd : g ∣ K.gcd t := (Nat.mem_divisors.mp hgDivGcd).1
  have hgK : g ∣ K := hgGcd.trans (Nat.gcd_dvd_left K t)
  have hgpos : 0 < g := Nat.pos_of_mem_divisors hgDivGcd
  have hq2 : 2 ≤ K / g := (Finset.mem_filter.mp hg).2
  have hqpos : 0 < K / g := by omega
  have hKfactor : K = g * (K / g) := (Nat.mul_div_cancel' hgK).symm
  have hKfactorC : (K : ℂ) =
      (g : ℂ) * ((K / g : ℕ) : ℂ) := by exact_mod_cast hKfactor
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hqC : ((K / g : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hKfactorC]
  field_simp [hgC, hqC, hpiC, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- Product of primes lost when a numerator descends from `q` to `Q`. -/
noncomputable def excludedPrimeProduct (q Q : ℕ) : ℕ :=
  ∏ ell ∈ q.primeFactors.filter fun ell => ¬ell ∣ Q, ell

theorem excludedPrimeProduct_pos (q Q : ℕ) :
    0 < excludedPrimeProduct q Q := by
  unfold excludedPrimeProduct
  apply Finset.prod_pos
  intro ell hell
  exact (Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp hell).1).pos

theorem excludedPrimeProduct_dvd (q Q : ℕ) :
    excludedPrimeProduct q Q ∣ q := by
  unfold excludedPrimeProduct
  exact (Finset.prod_dvd_prod_of_subset
    (q.primeFactors.filter fun ell => ¬ell ∣ Q)
    q.primeFactors id (Finset.filter_subset _ _)).trans
      q.prod_primeFactors_dvd

theorem excludedPrimeProduct_coprime_right (q Q : ℕ) :
    (excludedPrimeProduct q Q).Coprime Q := by
  by_contra hnot
  rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with
    ⟨ell, hellPrime, hellP, hellQ⟩
  have hellFactors : ell ∈
      (excludedPrimeProduct q Q).primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero
      (excludedPrimeProduct_pos q Q).ne').2 ⟨hellPrime, hellP⟩
  have hprimeFactors :
      (excludedPrimeProduct q Q).primeFactors =
        q.primeFactors.filter fun ell => ¬ell ∣ Q := by
    unfold excludedPrimeProduct
    apply Nat.primeFactors_prod
    intro prime hprime
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hprime).1
  rw [hprimeFactors] at hellFactors
  exact (Finset.mem_filter.mp hellFactors).2 hellQ

theorem coprime_upstairs_iff_coprime_excluded
    {q Q n : ℕ} (hq : 0 < q) (hnQ : n.Coprime Q) :
    n.Coprime q ↔ n.Coprime (excludedPrimeProduct q Q) := by
  constructor
  · intro hnq
    exact hnq.coprime_dvd_right (excludedPrimeProduct_dvd q Q)
  · intro hnP
    by_contra hnq
    rcases Nat.Prime.not_coprime_iff_dvd.mp hnq with
      ⟨ell, hellPrime, helln, hellq⟩
    by_cases hellQ : ell ∣ Q
    · exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨ell, hellPrime, helln, hellQ⟩) hnQ
    · have hellMem : ell ∈ q.primeFactors.filter fun prime => ¬prime ∣ Q :=
        Finset.mem_filter.mpr ⟨
          (Nat.mem_primeFactors_of_ne_zero hq.ne').2 ⟨hellPrime, hellq⟩,
          hellQ⟩
      have hellP : ell ∣ excludedPrimeProduct q Q := by
        unfold excludedPrimeProduct
        exact Finset.dvd_prod_of_mem id hellMem
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨ell, hellPrime, helln, hellP⟩) hnP

theorem sum_complex_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) =
      if n = 1 then 1 else 0 := by
  change (∑ d ∈ n.divisors,
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) d) = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.coe_moebius_mul_coe_zeta]
  simp [ArithmeticFunction.one_apply]

theorem complex_coprime_indicator_moebius
    {a k : ℕ} (hk : 0 < k) :
    (if a.Coprime k then (1 : ℂ) else 0) =
      ∑ d ∈ k.divisors,
        if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  rw [← Finset.sum_filter]
  have hfilter :
      {d ∈ k.divisors | d ∣ a} = (a.gcd k).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro hd
      exact ⟨Nat.dvd_gcd hd.2 hd.1.1,
        ne_zero_of_dvd_ne_zero hk.ne' (Nat.gcd_dvd_right a k)⟩
    · intro hd
      exact ⟨⟨hd.1.trans (Nat.gcd_dvd_right a k), hk.ne'⟩,
        hd.1.trans (Nat.gcd_dvd_left a k)⟩
  rw [hfilter, sum_complex_moebius_divisors]

/-- Unit support is exactly the finite Möbius restriction of the unrestricted
Dedekind transforms. -/
theorem unitDedekindTransform_eq_mobius
    {K t : ℕ} (hK : 0 < K) :
    unitDedekindTransform K t = unitTransformMobiusSide K t := by
  letI : NeZero K := ⟨hK.ne'⟩
  rw [unitDedekindTransform_eq_coprimeRange hK]
  let base : ℕ → ℂ := fun h =>
    (arithmeticDedekindSum h K : ℂ) *
      ZMod.stdAddChar (-((t : ZMod K) * (h : ZMod K)))
  change (∑ h ∈ (Finset.range K).filter fun h => h.Coprime K, base h) = _
  rw [Finset.sum_filter]
  unfold unitTransformMobiusSide
  calc
    (∑ h ∈ Finset.range K, if h.Coprime K then base h else 0) =
        ∑ h ∈ Finset.range K,
          base h * (if h.Coprime K then (1 : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro h _hh
            by_cases hcop : h.Coprime K <;> simp [hcop]
    _ = ∑ h ∈ Finset.range K,
        base h * ∑ d ∈ K.divisors,
          if d ∣ h then (ArithmeticFunction.moebius d : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro h _hh
            rw [complex_coprime_indicator_moebius hK]
    _ = ∑ d ∈ K.divisors,
        (ArithmeticFunction.moebius d : ℂ) *
          ∑ h ∈ Finset.range K, if d ∣ h then base h else 0 := by
            rw [show
              (∑ h ∈ Finset.range K,
                base h * ∑ d ∈ K.divisors,
                  if d ∣ h then (ArithmeticFunction.moebius d : ℂ) else 0) =
              ∑ h ∈ Finset.range K, ∑ d ∈ K.divisors,
                (ArithmeticFunction.moebius d : ℂ) *
                  (if d ∣ h then base h else 0) by
                    apply Finset.sum_congr rfl
                    intro h _hh
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro d _hd
                    by_cases hdh : d ∣ h <;> simp [hdh]
                    ring]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro d _hd
            rw [Finset.mul_sum]
    _ = ∑ d ∈ K.divisors,
        (ArithmeticFunction.moebius d : ℂ) *
          fullDedekindTransform (K / d) t := by
            apply Finset.sum_congr rfl
            intro d hdmem
            have hdK : d ∣ K := (Nat.mem_divisors.mp hdmem).1
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
            let q := K / d
            have hqpos : 0 < q := Nat.div_pos
              (Nat.le_of_dvd hK hdK) hdpos
            have hKfactor : K = d * q := by
              exact (Nat.mul_div_cancel' hdK).symm
            letI : NeZero d := ⟨hdpos.ne'⟩
            letI : NeZero q := ⟨hqpos.ne'⟩
            rw [sum_range_divisible_reindex hdpos hdK]
            have hpoint : ∀ b ∈ Finset.range q,
                base (d * b) =
                  (arithmeticDedekindSum b q : ℂ) *
                    ZMod.stdAddChar (-((t : ZMod q) * (b : ZMod q))) := by
              intro b _hb
              unfold base
              have hDedekind : arithmeticDedekindSum (d * b) K =
                  arithmeticDedekindSum b q := by
                simpa only [hKfactor] using
                  arithmeticDedekindSum_scale
                    (b := b) hdpos hqpos
              have hchar :
                  ZMod.stdAddChar
                      (-((t : ZMod K) * ((d * b : ℕ) : ZMod K))) =
                    ZMod.stdAddChar
                      (-((t : ZMod q) * (b : ZMod q))) := by
                rw [show -((t : ZMod K) * ((d * b : ℕ) : ZMod K)) =
                    ((-((t * d * b : ℕ) : ℤ) : ℤ) : ZMod K) by
                      push_cast
                      ring]
                rw [show -((t : ZMod q) * (b : ZMod q)) =
                    ((-((t * b : ℕ) : ℤ) : ℤ) : ZMod q) by
                      push_cast
                      ring]
                rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
                congr 1
                have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
                have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
                push_cast
                rw [hKfactor]
                field_simp [hdC, hqC]
                push_cast
                ring
              rw [hDedekind, hchar]
            rw [Finset.sum_congr rfl hpoint]
            rw [fullDedekindTransform_eq_range hqpos]

/-- The exact additive transform, including its finite Fourier formula,
natural-order cotangent limit, and finite Möbius restriction. -/
theorem exact_additive_transform
    {K : ℕ} (hK : 2 ≤ K) (t : ℕ) :
    FullTransformSeriesConverges K t ∧
      fullDedekindTransform K t / (K : ℂ) =
        fullTransformSeriesSide K t ∧
      unitDedekindTransform K t = unitTransformMobiusSide K t :=
  ⟨fullTransformSeries_converges K t, fullTransformSeries_identity hK t,
    unitDedekindTransform_eq_mobius (lt_of_lt_of_le (by omega) hK)⟩

theorem inverseSawCoefficient_mul
    {Q R d n : ℕ} (hQ : 0 < Q)
    (hd : d.Coprime Q) (hn : n.Coprime Q) :
    inverseSawCoefficient Q R (d * n) =
      inverseSawCoefficient Q (R * inverseResidue d Q) n := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hdn : (d * n).Coprime Q := hd.mul_left hn
  unfold inverseSawCoefficient
  rw [dif_neg hQ.ne', dif_pos hdn, dif_neg hQ.ne', dif_pos hn]
  have hudn : ZMod.unitOfCoprime (d * n) hdn =
      ZMod.unitOfCoprime d hd * ZMod.unitOfCoprime n hn := by
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime]
  rw [hudn, mul_inv_rev]
  unfold inverseResidue
  rw [dif_neg hQ.ne', dif_pos hd]
  have hcast :
      ((R * (ZMod.unitOfCoprime d hd)⁻¹.val.val : ℕ) : ZMod Q) =
        (R : ZMod Q) * (ZMod.unitOfCoprime d hd)⁻¹.val := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hcast]
  congr 1
  push_cast
  ring

theorem sum_Icc_divisible_reindex
    {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) {d N : ℕ} (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 N, if d ∣ n then f n else 0) =
      ∑ m ∈ Finset.Icc 1 (N / d), f (d * m) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun m _hm => d * m)
  · intro m hm
    have hmI := Finset.mem_Icc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hmI.1, ?_⟩,
      dvd_mul_right d m⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmI.2
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hd heq
  · intro n hn
    have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hdn := (Finset.mem_filter.mp hn).2
    let m := n / d
    have hdm : d * m = n := Nat.mul_div_cancel' hdn
    have hmpos : 0 < m := Nat.div_pos
      (Nat.le_of_dvd hnI.1 hdn) hd
    have hmle : m ≤ N / d := Nat.div_le_div_right hnI.2
    exact ⟨m, Finset.mem_Icc.mpr ⟨hmpos, hmle⟩, hdm⟩
  · intro m hm
    rfl

/-- Finite inclusion-exclusion side of numerator descent. -/
noncomputable def numeratorDescentPartialSide (q r N : ℕ) : ℂ :=
  let c := r.gcd q
  let Q := q / c
  ∑ d ∈ (excludedPrimeProduct q Q).divisors,
    (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
      inverseSawPartial Q ((r / c) * inverseResidue d Q) (N / d)

theorem inverseSawPartial_numeratorDescent
    {q r N : ℕ} (hQ : 2 ≤ q / r.gcd q) :
    inverseSawPartial q r N = numeratorDescentPartialSide q r N := by
  let c := r.gcd q
  let Q := q / c
  let R := r / c
  let P := excludedPrimeProduct q Q
  have hQbound : 2 ≤ Q := by simpa [Q, c] using hQ
  have hQpos : 0 < Q := by omega
  have hcdivq : c ∣ q := Nat.gcd_dvd_right r q
  have hcdivr : c ∣ r := Nat.gcd_dvd_left r q
  have hcpos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    simp [Q, hc0] at hQbound
  have hqeq : q = c * Q := by
    unfold Q
    exact (Nat.mul_div_cancel' hcdivq).symm
  have hreq : r = c * R := by
    unfold R
    exact (Nat.mul_div_cancel' hcdivr).symm
  have hqpos : 0 < q := by rw [hqeq]; positivity
  have hPpos : 0 < P := by
    exact excludedPrimeProduct_pos q Q
  have hPQ : P.Coprime Q := excludedPrimeProduct_coprime_right q Q
  let base : ℕ → ℂ := fun n =>
    ((n : ℝ)⁻¹) • inverseSawCoefficient Q R n
  have hpoint (n : ℕ) :
      ((n : ℝ)⁻¹) • inverseSawCoefficient q r n =
        base n * (if n.Coprime P then (1 : ℂ) else 0) := by
    by_cases hnQ : n.Coprime Q
    · have hniff : n.Coprime q ↔ n.Coprime P :=
        coprime_upstairs_iff_coprime_excluded hqpos hnQ
      by_cases hnP : n.Coprime P
      · have hnq : n.Coprime q := hniff.mpr hnP
        rw [if_pos hnP]
        simp only [mul_one, base]
        rw [inverseSawCoefficient_descend hcpos hQpos hqeq hreq hnq]
      · have hnq : ¬n.Coprime q := fun hn => hnP (hniff.mp hn)
        rw [if_neg hnP]
        simp [inverseSawCoefficient, hqpos.ne', hnq]
    · have hnq : ¬n.Coprime q := by
        intro hn
        exact hnQ (hn.coprime_dvd_right (by rw [hqeq]; exact dvd_mul_left Q c))
      simp [base, inverseSawCoefficient, hqpos.ne', hQpos.ne', hnq, hnQ]
  rw [inverseSawPartial_eq_Icc]
  unfold numeratorDescentPartialSide
  dsimp only
  change (∑ n ∈ Finset.Icc 1 N,
      ((n : ℝ)⁻¹) • inverseSawCoefficient q r n) = _
  calc
    (∑ n ∈ Finset.Icc 1 N,
        ((n : ℝ)⁻¹) • inverseSawCoefficient q r n) =
        ∑ n ∈ Finset.Icc 1 N,
          base n * (if n.Coprime P then (1 : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro n _hn
            exact hpoint n
    _ = ∑ n ∈ Finset.Icc 1 N,
          base n *
            ∑ d ∈ P.divisors,
              if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [← complex_coprime_indicator_moebius hPpos]
    _ = ∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℂ) *
            ∑ n ∈ Finset.Icc 1 N, if d ∣ n then base n else 0 := by
            rw [show
              (∑ n ∈ Finset.Icc 1 N,
                base n * ∑ d ∈ P.divisors,
                  if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0) =
              ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ P.divisors,
                (ArithmeticFunction.moebius d : ℂ) *
                  (if d ∣ n then base n else 0) by
                    apply Finset.sum_congr rfl
                    intro n _hn
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro d _hd
                    by_cases hdn : d ∣ n <;> simp [hdn]
                    ring]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro d _hd
            rw [Finset.mul_sum]
    _ = ∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / d), base (d * n) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
            rw [sum_Icc_divisible_reindex base hdpos]
    _ = ∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
            inverseSawPartial Q (R * inverseResidue d Q) (N / d) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
            have hdQ : d.Coprime Q := hPQ.coprime_dvd_left hdP
            rw [inverseSawPartial_eq_Icc]
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
            by_cases hnQ : n.Coprime Q
            · unfold base
              rw [inverseSawCoefficient_mul hQpos hdQ hnQ]
              simp only [Complex.real_smul]
              rw [Nat.cast_mul, mul_inv, Complex.ofReal_mul,
                Complex.ofReal_inv, Complex.ofReal_inv]
              have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
              have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
              field_simp [hdC, hnC]
              norm_num
              ring
            · have hdnQ : ¬(d * n).Coprime Q := by
                intro hcop
                exact hnQ (hcop.coprime_dvd_left (dvd_mul_left n d))
              simp [base, inverseSawCoefficient, hQpos.ne', hnQ, hdnQ]

/-- The inclusion-exclusion side of exact numerator descent. -/
noncomputable def numeratorDescentSide (q r : ℕ) : ℂ :=
  let c := r.gcd q
  let Q := q / c
  if hQ : Q = 0 then 0 else
    letI : NeZero Q := ⟨hQ⟩
    ∑ d ∈ (excludedPrimeProduct q Q).divisors,
      (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
        inverseSawSeries Q
          ((r / c) * inverseResidue d Q)

/-- The finite numerator-descent formula tends term by term to its exact
inclusion-exclusion side. -/
theorem numeratorDescentPartialSide_tendsto
    {q r : ℕ} (hQ : 2 ≤ q / r.gcd q) :
    Filter.Tendsto (numeratorDescentPartialSide q r) Filter.atTop
      (nhds (numeratorDescentSide q r)) := by
  let c := r.gcd q
  let Q := q / c
  let R := r / c
  let P := excludedPrimeProduct q Q
  have hQpos : 0 < Q := lt_of_lt_of_le (by omega) hQ
  have hPpos : 0 < P := excludedPrimeProduct_pos q Q
  have hlim :
      Filter.Tendsto
        (fun N => ∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
            inverseSawPartial Q (R * inverseResidue d Q) (N / d))
        Filter.atTop
        (nhds (∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
            inverseSawSeries Q (R * inverseResidue d Q))) := by
    apply tendsto_finsetSum P.divisors
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    exact ((inverseSawPartial_tendsto Q
      (R * inverseResidue d Q)).comp
        (Nat.tendsto_div_const_atTop hdpos.ne')).const_mul _
  change Filter.Tendsto
    (fun N => numeratorDescentPartialSide q r N) Filter.atTop
      (nhds (numeratorDescentSide q r))
  simpa [numeratorDescentPartialSide, numeratorDescentSide,
    c, Q, R, P, hQpos.ne'] using hlim

theorem inverseSawSeries_eq_zero_of_dvd
    {q r : ℕ} (hqr : q ∣ r) :
    inverseSawSeries q r = 0 := by
  have hcoefficient : ∀ n, inverseSawCoefficient q r n = 0 := by
    rcases hqr with ⟨d, rfl⟩
    intro n
    simp [inverseSawCoefficient, centeredSawtooth, mul_comm]
  have hterm : ∀ n, inverseSawTerm q r n = 0 := by
    intro n
    simp [inverseSawTerm, hcoefficient]
  have hpartial : inverseSawPartial q r = fun _ => 0 := by
    funext N
    unfold inverseSawPartial
    simp [hterm]
  unfold inverseSawSeries
  rw [hpartial]
  rw [Filter.map_const]
  exact lim_eq (pure_le_nhds 0)

theorem exact_numerator_descent
    {q r : ℕ} :
    let c := r.gcd q
    let Q := q / c
    (Q = 1 → inverseSawSeries q r = 0) ∧
      (2 ≤ Q → inverseSawSeries q r = numeratorDescentSide q r) :=
  by
    dsimp only
    constructor
    · intro hQ
      let c := r.gcd q
      have hcdiv : c ∣ q := Nat.gcd_dvd_right r q
      have hqc : q = c := by
        calc
          q = c * (q / c) := (Nat.mul_div_cancel' hcdiv).symm
          _ = c := by rw [hQ, mul_one]
      have hqr : q ∣ r := by
        rw [hqc]
        exact Nat.gcd_dvd_left r q
      exact inverseSawSeries_eq_zero_of_dvd hqr
    · intro hQ
      apply tendsto_nhds_unique (inverseSawPartial_tendsto q r)
      exact (numeratorDescentPartialSide_tendsto hQ).congr'
        (Filter.Eventually.of_forall fun N =>
          (inverseSawPartial_numeratorDescent (N := N) hQ).symm)

/-- The incomplete inverse-residue prefix `A_{q,r}(X)`. -/
noncomputable def inverseResiduePrefix (q r X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    if n.Coprime q then
      (rationalSawtooth (r * inverseResidue n q) q : ℝ)
    else 0

/-- The reciprocal divisor sum `sigma_{-1}`. -/
noncomputable def reciprocalDivisorSum (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, (d : ℝ)⁻¹

/-- The reciprocal square-root divisor sum `sigma_{-1/2}`. -/
noncomputable def reciprocalSqrtDivisorSum (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, ((d : ℝ).sqrt)⁻¹

theorem reciprocalDivisorSum_nonneg (q : ℕ) :
    0 ≤ reciprocalDivisorSum q := by
  unfold reciprocalDivisorSum
  positivity

/-- Reciprocal divisor mass can only grow when the ambient integer acquires
additional divisors. -/
theorem reciprocalDivisorSum_mono_of_dvd
    {q K : ℕ} (hK : K ≠ 0) (hqK : q ∣ K) :
    reciprocalDivisorSum q ≤ reciprocalDivisorSum K := by
  unfold reciprocalDivisorSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.divisors_subset_of_dvd hK hqK)
    (fun d _hdK _hdq => by positivity)

/-- The sharp triangle-inequality consequence of exact numerator descent.
The maximum is taken only over the true unit numerators modulo the descended
modulus, exactly as in the manuscript. -/
theorem exact_numerator_descent_bound
    {q r : ℕ} (hQ : 2 ≤ q / r.gcd q) :
    ‖inverseSawSeries q r‖ ≤
      reciprocalDivisorSum q *
        inverseSawUnitMaximum (q / r.gcd q) := by
  let c := r.gcd q
  let Q := q / c
  let R := r / c
  let P := excludedPrimeProduct q Q
  have hQbound : 2 ≤ Q := by simpa [Q, c] using hQ
  have hQpos : 0 < Q := by omega
  letI : NeZero Q := ⟨hQpos.ne'⟩
  have hqpos : 0 < q := by
    by_contra hq
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    simp [hq0] at hQ
  have hcpos : 0 < c := by
    exact Nat.gcd_pos_of_pos_right r hqpos
  have hR : R.Coprime Q := by
    simpa [R, Q, c] using Nat.coprime_div_gcd_div_gcd hcpos
  have hPpos : 0 < P := excludedPrimeProduct_pos q Q
  have hPQ : P.Coprime Q := excludedPrimeProduct_coprime_right q Q
  have hdesc : inverseSawSeries q r = numeratorDescentSide q r :=
    (exact_numerator_descent (q := q) (r := r)).2 hQ
  rw [hdesc]
  unfold numeratorDescentSide
  simp only [c, Q, hQpos.ne', dite_false]
  change ‖∑ d ∈ P.divisors,
      (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
        inverseSawSeries Q (R * inverseResidue d Q)‖ ≤ _
  have hterm : ∀ d ∈ P.divisors,
      ‖(ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
          inverseSawSeries Q (R * inverseResidue d Q)‖ ≤
        (d : ℝ)⁻¹ * inverseSawUnitMaximum Q := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
    have hdQ : d.Coprime Q := hPQ.coprime_dvd_left hdP
    have hinvQ : (inverseResidue d Q).Coprime Q :=
      inverseResidue_coprime hQpos hdQ
    have hunit : (R * inverseResidue d Q).Coprime Q :=
      hR.mul_left hinvQ
    have hseries := norm_inverseSawSeries_le_unitMaximum hunit
    rw [norm_mul, norm_div, Complex.norm_intCast, Complex.norm_natCast]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have habsCast : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| =
        ((|(ArithmeticFunction.moebius d)| : ℤ) : ℝ) := by
      norm_cast
    rw [habsCast]
    have hmu : ((|(ArithmeticFunction.moebius d)| : ℤ) : ℝ) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hcoeff : ((|(ArithmeticFunction.moebius d)| : ℤ) : ℝ) / (d : ℝ) ≤
        1 / (d : ℝ) := div_le_div_of_nonneg_right hmu hdR.le
    calc
      ((|(ArithmeticFunction.moebius d)| : ℤ) : ℝ) / (d : ℝ) *
            ‖inverseSawSeries Q (R * inverseResidue d Q)‖ ≤
          1 / (d : ℝ) * inverseSawUnitMaximum Q :=
            mul_le_mul hcoeff hseries (norm_nonneg _) (by positivity)
      _ = (d : ℝ)⁻¹ * inverseSawUnitMaximum Q := by
            rw [one_div]
  have hsubset : P.divisors ⊆ q.divisors :=
    Nat.divisors_subset_of_dvd hqpos.ne' (excludedPrimeProduct_dvd q Q)
  calc
    ‖∑ d ∈ P.divisors,
        (ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
          inverseSawSeries Q (R * inverseResidue d Q)‖ ≤
        ∑ d ∈ P.divisors,
          ‖(ArithmeticFunction.moebius d : ℂ) / (d : ℂ) *
            inverseSawSeries Q (R * inverseResidue d Q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ P.divisors,
        (d : ℝ)⁻¹ * inverseSawUnitMaximum Q :=
      Finset.sum_le_sum fun d hd => hterm d hd
    _ = (∑ d ∈ P.divisors, (d : ℝ)⁻¹) *
        inverseSawUnitMaximum Q := by rw [Finset.sum_mul]
    _ ≤ reciprocalDivisorSum q * inverseSawUnitMaximum Q := by
      apply mul_le_mul_of_nonneg_right
      · unfold reciprocalDivisorSum
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun d _hdq _hdP => by positivity)
      · exact inverseSawUnitMaximum_nonneg Q

/-- Numerator descent converts a unit estimate at every descended modulus into
an estimate for an arbitrary numerator.  The ambient modulus is explicit so
that later divisor sums do not conceal a uniformity assumption. -/
theorem norm_inverseSawSeries_le_of_ambient_unit_bound
    {K q r : ℕ} (hq : 2 ≤ q) (hqK : q ≤ K)
    {C : ℝ} (scale : ℕ → ℝ) (hC : 0 ≤ C)
    (hscale : 0 ≤ scale K)
    (hunit : ∀ Q u, 2 ≤ Q → Q ≤ K → u.Coprime Q →
      ‖inverseSawSeries Q u‖ ≤ C * scale K) :
    ‖inverseSawSeries q r‖ ≤
      C * scale K * reciprocalDivisorSum q := by
  let c := r.gcd q
  let Q := q / c
  have hqpos : 0 < q := by omega
  have hcpos : 0 < c := by
    exact Nat.gcd_pos_of_pos_right r hqpos
  have hQpos : 0 < Q := by
    exact Nat.div_pos (Nat.gcd_le_right r hqpos) hcpos
  have hQq : Q ∣ q := by
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right r q)
  have hQK : Q ≤ K :=
    (Nat.le_of_dvd hqpos hQq).trans hqK
  by_cases hQone : Q = 1
  · have hzero := (exact_numerator_descent (q := q) (r := r)).1 hQone
    rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg hC hscale)
      (reciprocalDivisorSum_nonneg q)
  · have hQtwo : 2 ≤ Q := by omega
    have hmax : inverseSawUnitMaximum Q ≤ C * scale K := by
      apply inverseSawUnitMaximum_le hQpos
      intro u hu
      exact hunit Q u hQtwo hQK hu
    calc
      ‖inverseSawSeries q r‖ ≤
          reciprocalDivisorSum q * inverseSawUnitMaximum Q :=
        exact_numerator_descent_bound (by simpa [Q, c] using hQtwo)
      _ ≤ reciprocalDivisorSum q * (C * scale K) := by
        exact mul_le_mul_of_nonneg_left hmax
          (reciprocalDivisorSum_nonneg q)
      _ = C * scale K * reciprocalDivisorSum q := by ring

/-- The full additive transform costs two reciprocal-divisor factors once all
descended unit series are controlled at one ambient modulus. -/
theorem norm_fullDedekindTransform_div_le_of_ambient_unit_bound
    {A K t : ℕ} (hK : 2 ≤ K) (hKA : K ≤ A)
    {C : ℝ} (scale : ℕ → ℝ)
    (hC : 0 ≤ C) (hscale : 0 ≤ scale A)
    (hunit : ∀ Q u, 2 ≤ Q → Q ≤ A → u.Coprime Q →
      ‖inverseSawSeries Q u‖ ≤ C * scale A) :
    ‖fullDedekindTransform K t‖ / (K : ℝ) ≤
      C * scale A * reciprocalDivisorSum K ^ 2 := by
  have hKpos : 0 < K := by omega
  have hKne : K ≠ 0 := hKpos.ne'
  let S := (K.gcd t).divisors.filter fun g => 2 ≤ K / g
  have hidentity := fullTransformSeries_identity hK t
  have hnormIdentity :
      ‖fullDedekindTransform K t‖ / (K : ℝ) =
        ‖fullTransformSeriesSide K t‖ := by
    calc
      ‖fullDedekindTransform K t‖ / (K : ℝ) =
          ‖fullDedekindTransform K t‖ / ‖(K : ℂ)‖ := by
            rw [Complex.norm_natCast]
      _ = ‖fullDedekindTransform K t / (K : ℂ)‖ := by
            rw [norm_div]
      _ = ‖fullTransformSeriesSide K t‖ := by rw [hidentity]
  rw [hnormIdentity]
  unfold fullTransformSeriesSide
  change ‖-(1 / ((Real.pi : ℂ) * Complex.I)) *
      ∑ g ∈ S, (1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)‖ ≤ _
  have hcoefficient : ‖-(1 / ((Real.pi : ℂ) * Complex.I))‖ ≤ (1 : ℝ) := by
    rw [norm_neg, norm_div, norm_one, norm_mul, Complex.norm_real,
      Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
    exact (div_le_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
  have hterm : ∀ g ∈ S,
      ‖(1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)‖ ≤
        (g : ℝ)⁻¹ *
          (C * scale A * reciprocalDivisorSum K) := by
    intro g hg
    have hgDivGcd := (Finset.mem_filter.mp hg).1
    have hqTwo := (Finset.mem_filter.mp hg).2
    have hgK : g ∣ K :=
      (Nat.mem_divisors.mp hgDivGcd).1.trans (Nat.gcd_dvd_left K t)
    have hgpos : 0 < g := Nat.pos_of_mem_divisors hgDivGcd
    have hqK : K / g ∣ K := Nat.div_dvd_of_dvd hgK
    have hqA : K / g ≤ A :=
      (Nat.le_of_dvd hKpos hqK).trans hKA
    have hseries := norm_inverseSawSeries_le_of_ambient_unit_bound
      (K := A) (r := t / g) hqTwo hqA scale hC hscale hunit
    have hsigma := reciprocalDivisorSum_mono_of_dvd hKne hqK
    have hseries' : ‖inverseSawSeries (K / g) (t / g)‖ ≤
        C * scale A * reciprocalDivisorSum K := by
      calc
        ‖inverseSawSeries (K / g) (t / g)‖ ≤
            C * scale A * reciprocalDivisorSum (K / g) := hseries
        _ ≤ C * scale A * reciprocalDivisorSum K := by
          exact mul_le_mul_of_nonneg_left hsigma (mul_nonneg hC hscale)
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    rw [one_div]
    exact mul_le_mul_of_nonneg_left hseries' (inv_nonneg.mpr hgR.le)
  have hsum :
      ‖∑ g ∈ S, (1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)‖ ≤
        reciprocalDivisorSum K *
          (C * scale A * reciprocalDivisorSum K) := by
    calc
      ‖∑ g ∈ S, (1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)‖ ≤
          ∑ g ∈ S,
            ‖(1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ g ∈ S, (g : ℝ)⁻¹ *
            (C * scale A * reciprocalDivisorSum K) := by
        exact Finset.sum_le_sum fun g hg => hterm g hg
      _ = (∑ g ∈ S, (g : ℝ)⁻¹) *
            (C * scale A * reciprocalDivisorSum K) := by
        rw [Finset.sum_mul]
      _ ≤ reciprocalDivisorSum K *
            (C * scale A * reciprocalDivisorSum K) := by
        apply mul_le_mul_of_nonneg_right
        · unfold reciprocalDivisorSum
          have hsubset : S ⊆ K.divisors := by
            intro g hg
            have hgDivGcd := (Finset.mem_filter.mp hg).1
            exact Nat.mem_divisors.mpr
              ⟨(Nat.mem_divisors.mp hgDivGcd).1.trans
                  (Nat.gcd_dvd_left K t), hKne⟩
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun d _hdK _hdS => by positivity)
        · exact mul_nonneg (mul_nonneg hC hscale)
            (reciprocalDivisorSum_nonneg K)
  calc
    ‖-(1 / ((Real.pi : ℂ) * Complex.I)) *
        ∑ g ∈ S, (1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)‖ ≤
      ‖-(1 / ((Real.pi : ℂ) * Complex.I))‖ *
        ‖∑ g ∈ S, (1 / (g : ℂ)) * inverseSawSeries (K / g) (t / g)‖ :=
      norm_mul_le _ _
    _ ≤ 1 * (reciprocalDivisorSum K *
          (C * scale A * reciprocalDivisorSum K)) := by
      exact mul_le_mul hcoefficient hsum (norm_nonneg _)
        (by norm_num)
    _ = C * scale A * reciprocalDivisorSum K ^ 2 := by ring

theorem fullDedekindTransform_one (t : ℕ) :
    fullDedekindTransform 1 t = 0 := by
  have h := fullDedekindTransform_eq_range (K := 1) (t := t) (by omega)
  simpa [arithmeticDedekindSum, rationalSawtooth] using h

/-- Möbius restriction costs the third reciprocal-divisor factor.  Together
with the preceding theorem this proves the manuscript's additive-transform
assembly from the descended unit-series estimate. -/
theorem norm_unitDedekindTransform_div_le_of_ambient_unit_bound
    {A K t : ℕ} (hK : 2 ≤ K) (hKA : K ≤ A)
    {C : ℝ} (scale : ℕ → ℝ)
    (hC : 0 ≤ C) (hscale : 0 ≤ scale A)
    (hunit : ∀ Q u, 2 ≤ Q → Q ≤ A → u.Coprime Q →
      ‖inverseSawSeries Q u‖ ≤ C * scale A) :
    ‖unitDedekindTransform K t‖ / (K : ℝ) ≤
      C * scale A * reciprocalDivisorSum K ^ 3 := by
  have hKpos : 0 < K := by omega
  have hKne : K ≠ 0 := hKpos.ne'
  rw [unitDedekindTransform_eq_mobius hKpos]
  unfold unitTransformMobiusSide
  let B := C * scale A * reciprocalDivisorSum K ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hterm : ∀ d ∈ K.divisors,
      ‖(ArithmeticFunction.moebius d : ℂ) *
          fullDedekindTransform (K / d) t‖ / (K : ℝ) ≤
        (d : ℝ)⁻¹ * B := by
    intro d hd
    have hdK : d ∣ K := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hqpos : 0 < K / d := Nat.div_pos (Nat.le_of_dvd hKpos hdK) hdpos
    have hfactorNat : K = d * (K / d) := (Nat.mul_div_cancel' hdK).symm
    by_cases hqOne : K / d = 1
    · rw [hqOne, fullDedekindTransform_one, mul_zero, norm_zero, zero_div]
      exact mul_nonneg (inv_nonneg.mpr (by positivity)) hB
    · have hqTwo : 2 ≤ K / d := by omega
      have hqK : K / d ∣ K := Nat.div_dvd_of_dvd hdK
      have hfull := norm_fullDedekindTransform_div_le_of_ambient_unit_bound
        (A := A) (t := t) hqTwo
          ((Nat.le_of_dvd hKpos hqK).trans hKA) scale hC hscale hunit
      have hsigma := reciprocalDivisorSum_mono_of_dvd hKne hqK
      have hfullB : ‖fullDedekindTransform (K / d) t‖ /
          ((K / d : ℕ) : ℝ) ≤ B := by
        calc
          ‖fullDedekindTransform (K / d) t‖ / ((K / d : ℕ) : ℝ) ≤
              C * scale A * reciprocalDivisorSum (K / d) ^ 2 := hfull
          _ ≤ C * scale A * reciprocalDivisorSum K ^ 2 := by
            have hsq : reciprocalDivisorSum (K / d) ^ 2 ≤
                reciprocalDivisorSum K ^ 2 := by
              exact pow_le_pow_left₀
                (reciprocalDivisorSum_nonneg (K / d)) hsigma 2
            exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hC hscale)
          _ = B := rfl
      have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ (1 : ℝ) := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hqR : (0 : ℝ) < (K / d : ℕ) := by exact_mod_cast hqpos
      have hfactorR : (K : ℝ) = (d : ℝ) * ((K / d : ℕ) : ℝ) := by
        exact_mod_cast hfactorNat
      rw [norm_mul, hfactorR]
      calc
        ‖(ArithmeticFunction.moebius d : ℂ)‖ *
              ‖fullDedekindTransform (K / d) t‖ /
                ((d : ℝ) * ((K / d : ℕ) : ℝ)) ≤
            1 * ‖fullDedekindTransform (K / d) t‖ /
                ((d : ℝ) * ((K / d : ℕ) : ℝ)) := by
              gcongr
        _ = (d : ℝ)⁻¹ *
              (‖fullDedekindTransform (K / d) t‖ /
                ((K / d : ℕ) : ℝ)) := by
              field_simp [hdR.ne', hqR.ne']
        _ ≤ (d : ℝ)⁻¹ * B := by
              exact mul_le_mul_of_nonneg_left hfullB (inv_nonneg.mpr hdR.le)
  calc
    ‖∑ d ∈ K.divisors,
        (ArithmeticFunction.moebius d : ℂ) *
          fullDedekindTransform (K / d) t‖ / (K : ℝ) ≤
      (∑ d ∈ K.divisors,
        ‖(ArithmeticFunction.moebius d : ℂ) *
          fullDedekindTransform (K / d) t‖) / (K : ℝ) := by
        apply div_le_div_of_nonneg_right (norm_sum_le _ _)
        positivity
    _ = ∑ d ∈ K.divisors,
        ‖(ArithmeticFunction.moebius d : ℂ) *
          fullDedekindTransform (K / d) t‖ / (K : ℝ) := by
        rw [Finset.sum_div]
    _ ≤ ∑ d ∈ K.divisors, (d : ℝ)⁻¹ * B := by
        exact Finset.sum_le_sum fun d hd => hterm d hd
    _ = reciprocalDivisorSum K * B := by
        unfold reciprocalDivisorSum
        rw [Finset.sum_mul]
    _ = C * scale A * reciprocalDivisorSum K ^ 3 := by
        dsimp [B]
        ring

/-- Exact Weil--Estermann completion input used in the manuscript. -/
def CompletedInversePrefixEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q r X,
    2 ≤ q → r.Coprime q → 1 ≤ X → X ≤ q →
    |inverseResiduePrefix q r X| ≤
      C * (q : ℝ).sqrt * q.divisors.card *
        reciprocalSqrtDivisorSum q * (Real.log (2 * q)) ^ 2

/-- Exact Korolev-scale inverse harmonic conclusion. -/
noncomputable def inverseResidueHarmonicScale (q : ℕ) : ℝ :=
  Real.log (2 * q) / Real.log (Real.log (3 * q))

theorem inverseResidueHarmonicScale_nonneg
    {q : ℕ} (hq : 2 ≤ q) :
    0 ≤ inverseResidueHarmonicScale q := by
  unfold inverseResidueHarmonicScale
  have hthree : (1 : ℝ) < Real.log (3 * q) := by
    have harg : Real.exp 1 < 3 * (q : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_three
        _ ≤ 3 * (q : ℝ) := by exact_mod_cast (show 3 ≤ 3 * q by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity)).2 harg
  have hden : 0 < Real.log (Real.log (3 * q)) := Real.log_pos hthree
  exact div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))) hden.le

def InverseResidueHarmonicEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q r,
    2 ≤ q → r.Coprime q →
    ‖inverseSawSeries q r‖ ≤ C * inverseResidueHarmonicScale q

/-- The lower edge of the range in Korolev's published inverse-fraction
estimate. -/
noncomputable def korolevLowerRange (q : ℕ) : ℝ :=
  Real.exp (Real.rpow (Real.log q) (4 / 5 : ℝ) *
    Real.rpow (Real.log (Real.log q)) (73 / 5 : ℝ))

/-- The upper edge of the range in Korolev's published inverse-fraction
estimate. -/
noncomputable def korolevUpperRange (q : ℕ) : ℝ :=
  Real.rpow q (4 / 7 : ℝ)

/-- The exact logarithmic factor in the Korolev range estimate used by the
manuscript. -/
noncomputable def korolevPrefixDecay (q X : ℕ) : ℝ :=
  Real.rpow (Real.log X) (-5 / 24 : ℝ) *
    Real.rpow (Real.log q) (1 / 6 : ℝ) *
      Real.rpow (Real.log (Real.log q)) (49 / 24 : ℝ)

/-- Source-level statement of the published Korolev range estimate, on the
actual centered inverse-residue prefix used by the manuscript. -/
def KorolevInverseFractionRangeEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ (q r X : ℕ),
    threshold ≤ q → r.Coprime q →
      korolevLowerRange q ≤ (X : ℝ) →
      (X : ℝ) ≤ korolevUpperRange q →
        |inverseResiduePrefix q r X| ≤
          C * (X : ℝ) * korolevPrefixDecay q X

/-- Uniform harmonic bound on every finite inverse-saw partial sum.  This is
the target of the manuscript's Korolev plus completion range split, not the
published Korolev theorem itself. -/
def UniformInverseSawPartialHarmonicEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ K q r N,
    2 ≤ q → q ≤ K → r.Coprime q →
      ‖inverseSawPartial q r N‖ ≤ C * inverseResidueHarmonicScale K

/-- Uniformity required by the carrier transform after passing from the
completed finite partial sums to their natural-order limit. -/
def KorolevAmbientInverseResidueEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ K q r,
    2 ≤ q → q ≤ K → r.Coprime q →
      ‖inverseSawSeries q r‖ ≤ C * inverseResidueHarmonicScale K

/-- Convergence of the internally constructed natural-order series transfers
the uniform completed-Korolev bound from every finite partial sum to the
actual inverse-residue series. -/
theorem korolevAmbientInverseResidueEstimate_of_partials
    (hpartials : UniformInverseSawPartialHarmonicEstimate) :
    KorolevAmbientInverseResidueEstimate := by
  rcases hpartials with ⟨C, hC, hpartials⟩
  refine ⟨C, hC, ?_⟩
  intro K q r hq hqK hr
  have htendsto := (inverseSawPartial_tendsto q r).norm
  exact le_of_tendsto htendsto
    (Filter.Eventually.of_forall fun N => hpartials K q r N hq hqK hr)

/-- Actual uniform additive-transform estimate. -/
def UniformAdditiveTransformEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k t,
    2 ≤ k →
    ‖unitDedekindTransform k t‖ / (k : ℝ) ≤
      C * inverseResidueHarmonicScale k * reciprocalDivisorSum k ^ 3

/-- Actual bounded reciprocal-divisor moments. -/
def BoundedReciprocalDivisorMoments : Prop :=
  ∀ j, 0 < j → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, ∑ k ∈ Finset.Icc 1 x,
      reciprocalDivisorSum k ^ j ≤ C * x

theorem inverse_residue_harmonic_bound
    (hKorolev : KorolevAmbientInverseResidueEstimate) :
    InverseResidueHarmonicEstimate := by
  rcases hKorolev with ⟨C, hC, hKorolev⟩
  refine ⟨C, hC, ?_⟩
  intro q r hq hr
  exact hKorolev q q r hq (le_refl q) hr

theorem uniform_additive_transform_bound
    (hKorolev : KorolevAmbientInverseResidueEstimate) :
    UniformAdditiveTransformEstimate := by
  rcases hKorolev with ⟨C, hC, hKorolev⟩
  refine ⟨C, hC, ?_⟩
  intro k t hk
  apply norm_unitDedekindTransform_div_le_of_ambient_unit_bound
    hk (le_refl k) inverseResidueHarmonicScale hC
  · exact inverseResidueHarmonicScale_nonneg hk
  · intro Q u hQ hQk hu
    exact hKorolev k Q u hQ hQk hu

end NField.Alignment.DedekindInverseResidueTransform
