/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPeriodicLValue
import NField.Alignment.CollisionCotangentSeries
import NField.Alignment.CollisionRamanujan

/-!
# Cotangent coefficients at the ordered L(1) endpoint

Oddness pairs complementary reciprocal progressions. Their actual limits
are cotangents, and finite Fourier inversion independently identifies the
same naturally ordered limit with the continued L-function.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionCotangentLValue

open scoped BigOperators Topology
open Filter CollisionPeriodicLValue DedekindInverseResidueTransform

def finiteCotangentCoefficient {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) : ℂ :=
  ∑ u ∈ Finset.Ico 1 q, Φ (u : ZMod q) *
    (Real.cot (Real.pi*(u : ℝ)/(q : ℝ)) : ℂ)

theorem orderedLPartial_blocks {q : ℕ} [NeZero q]
    (Φ : ZMod q → ℂ) (hΦ : Φ 0=0) (M : ℕ) :
    orderedLPartial Φ (M*q)=∑ u ∈ Finset.Ico 1 q,
      Φ (u : ZMod q)*inverseResidueProgressionPartial q u M := by
  have hq : 0 < q := NeZero.pos q
  unfold orderedLPartial
  rw [sum_range_mul_blocks hq]
  have hi (y : ℕ) (_hy : y ∈ Finset.range q) :
      (∑ j ∈ Finset.range M,
        Φ ((y+j*q+1 : ℕ) : ZMod q)/((y+j*q+1 : ℕ) : ℂ))=
      Φ ((y+1 : ℕ) : ZMod q)*inverseResidueProgressionPartial q (y+1) M := by
    rw [inverseResidueProgressionPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : ((y+j*q+1 : ℕ) : ZMod q)=((y+1 : ℕ) : ZMod q) := by simp
    rw [he]
    simp only [show y+j*q+1=y+1+j*q by omega, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hi]
  have hqzero : Φ (q : ZMod q)=0 := by simpa using hΦ
  have hdrop :
      (∑ y ∈ Finset.range q,
        Φ ((y+1 : ℕ) : ZMod q)*inverseResidueProgressionPartial q (y+1) M)=
      ∑ y ∈ Finset.range (q-1),
        Φ ((y+1 : ℕ) : ZMod q)*inverseResidueProgressionPartial q (y+1) M := by
    conv_lhs => rw [show Finset.range q=Finset.range ((q-1)+1) by congr 1; omega,
      Finset.sum_range_succ]
    rw [show q-1+1=q by omega, hqzero, zero_mul, add_zero]
  rw [hdrop]
  apply Finset.sum_bij (fun y _ => y+1)
  · intro y hy
    have := Finset.mem_range.mp hy
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  · intro a _ b _ he
    omega
  · intro u hu
    have := Finset.mem_Ico.mp hu
    exact ⟨u-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro _ _
    rfl

theorem odd_residue_blocks_paired {q : ℕ} [NeZero q]
    (Φ : ZMod q → ℂ) (hΦ : Function.Odd Φ) (M : ℕ) :
    orderedLPartial Φ (M*q)=(1/2 : ℂ)*∑ u ∈ Finset.Ico 1 q,
      Φ (u : ZMod q)*inverseProgressionPartial q u M := by
  let P := fun u => inverseResidueProgressionPartial q u M
  have hc (u : ℕ) (hu : u ∈ Finset.Ico 1 q) :
      Φ ((q-u : ℕ) : ZMod q)= -Φ (u : ZMod q) := by
    rw [Nat.cast_sub (Finset.mem_Ico.mp hu).2.le, ZMod.natCast_self, zero_sub]
    exact hΦ _
  have hr := sum_Ico_one_complement q (fun u => Φ (u : ZMod q)*P u)
  have hn : (∑ u ∈ Finset.Ico 1 q, Φ (u : ZMod q)*P (q-u))=
      -(∑ u ∈ Finset.Ico 1 q, Φ (u : ZMod q)*P u) := by
    rw [← hr, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hc u hu]
    ring
  have hp (u : ℕ) : inverseProgressionPartial q u M=P u-P (q-u) := by
    simp only [inverseProgressionPartial,P,inverseResidueProgressionPartial,
      Finset.sum_sub_distrib]
  rw [orderedLPartial_blocks Φ hΦ.map_zero]
  simp_rw [hp, mul_sub]
  rw [Finset.sum_sub_distrib, hn]
  change (∑ u ∈ Finset.Ico 1 q, Φ (u : ZMod q)*P u)=_
  ring

theorem complex_cotangent_real (q u : ℕ) :
    Complex.cot ((Real.pi : ℂ)*((u : ℂ)/(q : ℂ)))=
      (Real.cot (Real.pi*(u : ℝ)/(q : ℝ)) : ℂ) := by
  rw [Complex.ofReal_cot]
  congr 1
  push_cast
  ring

theorem odd_blocks_cotangent_limit {q : ℕ} [NeZero q]
    (Φ : ZMod q → ℂ) (hΦ : Function.Odd Φ) :
    Tendsto (fun M => orderedLPartial Φ (M*q)) atTop
      (𝓝 ((Real.pi : ℂ)/(2*(q : ℂ))*finiteCotangentCoefficient Φ)) := by
  have ht := (tendsto_finsetSum (Finset.Ico 1 q) (fun u hu =>
    (inverseProgressionPartial_tendsto_cotangent (NeZero.pos q)
      (Finset.mem_Ico.mp hu).1 (Finset.mem_Ico.mp hu).2).const_mul
        (Φ (u : ZMod q)))).const_mul (1/2 : ℂ)
  have he : (1/2 : ℂ)*∑ u ∈ Finset.Ico 1 q, Φ (u : ZMod q)*
      ((Real.pi : ℂ)/(q : ℂ)*Complex.cot ((Real.pi : ℂ)*((u : ℂ)/(q : ℂ)) ))=
      (Real.pi : ℂ)/(2*(q : ℂ))*finiteCotangentCoefficient Φ := by
    simp_rw [complex_cotangent_real]
    rw [finiteCotangentCoefficient, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    ring
  rw [he] at ht
  simpa only [odd_residue_blocks_paired Φ hΦ] using ht

theorem odd_cotangent_coefficient {q : ℕ} [NeZero q]
    (Φ : ZMod q → ℂ) (hΦ : Function.Odd Φ) :
    finiteCotangentCoefficient Φ=(2*(q : ℂ)/(Real.pi : ℂ))*ZMod.LFunction Φ 1 := by
  have hi : Tendsto (fun M : ℕ => M*q) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    have hq : 1 ≤ q := NeZero.pos q
    nlinarith
  have hL := (orderedLPartial_tendsto Φ hΦ.sum_eq_zero).comp hi
  have he := tendsto_nhds_unique hL (odd_blocks_cotangent_limit Φ hΦ)
  rw [he]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem odd_character_cotangent_coefficient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) :
    finiteCotangentCoefficient χ=(2*(q : ℂ)/(Real.pi : ℂ))*
      DirichletCharacter.LFunction χ 1 :=
  odd_cotangent_coefficient χ (fun x => DirichletCharacter.Odd.eval_neg χ x hχ)

theorem cotangent_complement {q u : ℕ} (hq : 0 < q) (hu : u ≤ q) :
    Real.cot (Real.pi*((q-u : ℕ) : ℝ)/(q : ℝ))=
      -Real.cot (Real.pi*(u : ℝ)/(q : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : Real.pi*((q-u : ℕ) : ℝ)/(q : ℝ)=
      Real.pi-Real.pi*(u : ℝ)/(q : ℝ) := by
    rw [Nat.cast_sub hu]
    field_simp
  rw [he, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

theorem even_cotangent_coefficient_zero {q : ℕ} [NeZero q]
    (Φ : ZMod q → ℂ) (hΦ : Function.Even Φ) : finiteCotangentCoefficient Φ=0 := by
  have he : finiteCotangentCoefficient Φ= -finiteCotangentCoefficient Φ := by
    unfold finiteCotangentCoefficient
    calc
      _ = ∑ u ∈ Finset.Ico 1 q, Φ ((q-u : ℕ) : ZMod q)*
          (Real.cot (Real.pi*((q-u : ℕ) : ℝ)/(q : ℝ)) : ℂ) :=
        (sum_Ico_one_complement q (fun u => Φ (u : ZMod q)*
          (Real.cot (Real.pi*(u : ℝ)/(q : ℝ)) : ℂ))).symm
      _ = _ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u hu
        have huq := (Finset.mem_Ico.mp hu).2.le
        rw [Nat.cast_sub huq, ZMod.natCast_self, zero_sub, hΦ,
          cotangent_complement (NeZero.pos q) huq, Complex.ofReal_neg]
        ring
  linear_combination (1/2 : ℂ)*he

theorem cotangent_coefficient_eq_units {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    finiteCotangentCoefficient χ=∑ a : (ZMod q)ˣ, χ a.val *
      (Real.cot (Real.pi*(a.val.val : ℝ)/(q : ℝ)) : ℂ) := by
  have hu := Fintype.sum_of_injective
    (fun a : (ZMod q)ˣ => a.val) Units.val_injective
    (fun a : (ZMod q)ˣ => χ a.val *
      (Real.cot (Real.pi*(a.val.val : ℝ)/(q : ℝ)) : ℂ))
    (fun a : ZMod q => χ a *
      (Real.cot (Real.pi*(a.val : ℝ)/(q : ℝ)) : ℂ)) (by
      intro a ha
      have hnu : ¬ IsUnit a := by
        rintro ⟨u,hu⟩
        exact ha ⟨u,hu⟩
      rw [MulChar.map_nonunit χ hnu, zero_mul]) (fun _ => rfl)
  rw [hu]
  have he := CollisionRamanujan.sum_zmod_val_complex q (fun u =>
    χ (u : ZMod q)*(Real.cot (Real.pi*(u : ℝ)/(q : ℝ)) : ℂ))
  simp only [ZMod.natCast_zmod_val] at he
  rw [he, DedekindReciprocity.sum_range_eq_sum_Ico_one _ (NeZero.pos q)
    (by simp [Complex.cot_eq_cos_div_sin])]
  rfl

theorem odd_character_unit_cotangent {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) :
    (∑ a : (ZMod q)ˣ, χ a.val *
      (Real.cot (Real.pi*(a.val.val : ℝ)/(q : ℝ)) : ℂ))=
      (2*(q : ℂ)/(Real.pi : ℂ))*DirichletCharacter.LFunction χ 1 := by
  rw [← cotangent_coefficient_eq_units]
  exact odd_character_cotangent_coefficient χ hχ

theorem even_character_unit_cotangent {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Even) :
    (∑ a : (ZMod q)ˣ, χ a.val *
      (Real.cot (Real.pi*(a.val.val : ℝ)/(q : ℝ)) : ℂ))=0 := by
  rw [← cotangent_coefficient_eq_units]
  exact even_cotangent_coefficient_zero χ
    (fun x => DirichletCharacter.Even.eval_neg χ x hχ)

theorem conjugate_character_value {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ⁻¹ a=star (χ a) := (MulChar.star_apply' χ a).symm

theorem odd_inverse_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) : χ⁻¹.Odd := by
  change χ⁻¹ (-1)= -1
  rw [conjugate_character_value, show χ (-1)= -1 from hχ]
  simp

theorem literal_odd_character_cotangent {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) :
    (∑ a : (ZMod q)ˣ, star (χ a.val) *
      (Real.cot (Real.pi*(a.val.val : ℝ)/(q : ℝ)) : ℂ))=
      (2*(q : ℂ)/(Real.pi : ℂ))*DirichletCharacter.LFunction χ⁻¹ 1 := by
  simpa only [conjugate_character_value] using
    odd_character_unit_cotangent χ⁻¹ (odd_inverse_character χ hχ)

end NField.Alignment.CollisionCotangentLValue
