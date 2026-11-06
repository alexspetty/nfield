/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSpectralNuBounds
import NField.Alignment.CollisionSpectralProductEnclosure
import NField.Alignment.CollisionAmplitudeConstantsEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionSpectralMomentEnclosure
open scoped BigOperators
open CollisionSpectralPrimeMoments CollisionSpectralNuBounds CollisionConductorArithmetic
open CollisionAmplitudeConstantsEnclosure CollisionDirichletRationalEnclosure
open CollisionZetaMoments CollisionDivisorSeries

def firstPrefix (P : ℕ) : ℝ := ∑ n ∈ Finset.range (P+1), firstPrimeTerm n
def secondPrefix (P : ℕ) : ℝ := ∑ n ∈ Finset.range (P+1), secondPrimeTerm n

theorem first_tail_split (P : ℕ) :
    firstPrimeMoment-firstPrefix P=∑' n, firstPrimeTerm (n+P+1) := by
  have h := firstPrimeTerm_summable.sum_add_tsum_nat_add (P+1)
  change firstPrefix P+(∑' n, firstPrimeTerm (n+(P+1)))=firstPrimeMoment at h
  simp only [← Nat.add_assoc] at h
  linarith

theorem second_tail_split (P : ℕ) :
    secondPrimeMoment-secondPrefix P=∑' n, secondPrimeTerm (n+P+1) := by
  have h := secondPrimeTerm_summable.sum_add_tsum_nat_add (P+1)
  change secondPrefix P+(∑' n, secondPrimeTerm (n+(P+1)))=secondPrimeMoment at h
  simp only [← Nat.add_assoc] at h
  linarith

theorem first_tail_bound {P b : ℕ} (hP : 1 ≤ P) (hb : 2*P ≤ 2^b) :
    0 ≤ firstPrimeMoment-firstPrefix P ∧
      firstPrimeMoment-firstPrefix P ≤ 2*(2*(b : ℝ)+3)/(P : ℝ) := by
  rw [first_tail_split]
  constructor
  · exact tsum_nonneg (fun _ => firstPrimeTerm_nonneg _)
  have hs := firstPrimeTerm_summable.comp_injective
    (show Function.Injective (fun n : ℕ => n+P+1) from fun a b h => by dsimp at h; omega)
  have hl := logSquareTerm_summable.comp_injective
    (show Function.Injective (fun n : ℕ => n+P+1) from fun a b h => by dsimp at h; omega)
  have h := hs.tsum_le_tsum (fun n => firstPrimeTerm_bound (n+P+1)) (hl.mul_left 2)
  rw [tsum_mul_left,← logMoment_tail_split] at h
  have ht := (logMoment_binary_tail hP hb).2
  calc
    _ ≤ 2*(logSquareMoment-logMomentPrefix P) := h
    _ ≤ 2*((2*(b : ℝ)+3)/(P : ℝ)) := mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = _ := by ring

theorem second_tail_bound {P : ℕ} (hP : 1 ≤ P) :
    0 ≤ secondPrimeMoment-secondPrefix P ∧
      secondPrimeMoment-secondPrefix P ≤ 16/(P : ℝ) := by
  rw [second_tail_split]
  constructor
  · exact tsum_nonneg (fun _ => secondPrimeTerm_nonneg _)
  have hs := secondPrimeTerm_summable.comp_injective
    (show Function.Injective (fun n : ℕ => n+P+1) from fun a b h => by dsimp at h; omega)
  have hk : ∀ n, powerKernel 2 n=zetaKernel 2 n := by
    intro n
    rw [zetaKernel_rpow (by norm_num : (2 : ℝ) ≠ 0),Real.rpow_neg (Nat.cast_nonneg n)]
    norm_num [powerKernel]
  have hz := (zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).comp_injective
    (show Function.Injective (fun n : ℕ => n+P+1) from fun a b h => by dsimp at h; omega)
  have h := hs.tsum_le_tsum (fun n => by simpa only [hk,Function.comp_def] using secondPrimeTerm_bound (n+P+1))
    (hz.mul_left 16)
  rw [tsum_mul_left] at h
  have ht := zeta_tail_bound (by norm_num : (1 : ℝ) < 2) hP
  norm_num at ht
  rw [Real.rpow_neg_one] at ht
  calc
    _ ≤ 16*∑' n, zetaKernel 2 (n+P+1) := h
    _ ≤ 16*(P : ℝ)⁻¹ := mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = _ := by ring

def profile (L : ℕ → ℝ) (p : ℕ) : ℝ := if p.Prime then L p/((p : ℝ)-1) else 0
def firstComputed (L : ℕ → ℝ) (P : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (P+1), profile L p/(p : ℝ)
def secondComputed (L : ℕ → ℝ) (P : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (P+1), (profile L p)^2/(p : ℝ)
def nuComputed (L : ℕ → ℝ) (n : ℕ) : ℝ := ∑ p ∈ n.primeFactors, profile L p

theorem profile_enclosure {L U : ℕ → ℝ} (p : ℕ)
    (h : L p ≤ Real.log p ∧ Real.log p ≤ U p) :
    profile L p ≤ primeProfile p ∧ primeProfile p ≤ profile U p := by
  by_cases hp : p.Prime
  · have hn : (0 : ℝ) ≤ (p : ℝ)-1 := by
      have hh : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    simp only [profile,primeProfile_apply,if_pos hp,primeLogWeight]
    exact ⟨div_le_div_of_nonneg_right h.1 hn,div_le_div_of_nonneg_right h.2 hn⟩
  · simp [profile,primeProfile_apply,hp]

theorem profile_nonneg {L : ℕ → ℝ} {p : ℕ} (hL : 0 ≤ L p) : 0 ≤ profile L p := by
  by_cases hp : p.Prime
  · rw [profile,if_pos hp]
    apply div_nonneg hL
    have hh : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  · simp [profile,hp]

theorem first_computed_enclosure {P b : ℕ} (hP : 1 ≤ P) (hb : 2*P ≤ 2^b)
    {L U : ℕ → ℝ} (h : ∀ p ∈ Finset.range (P+1), L p ≤ Real.log p ∧ Real.log p ≤ U p) :
    firstComputed L P ≤ firstPrimeMoment ∧
      firstPrimeMoment ≤ firstComputed U P+2*(2*(b : ℝ)+3)/(P : ℝ) := by
  have hp : firstComputed L P ≤ firstPrefix P ∧ firstPrefix P ≤ firstComputed U P := by
    constructor <;> apply Finset.sum_le_sum <;> intro p hp
    · have hh := div_le_div_of_nonneg_right (profile_enclosure p (h p hp)).1 (Nat.cast_nonneg p)
      simpa only [firstPrimeTerm,primeProfile_apply,profile,primeLogWeight,ite_div,zero_div] using hh
    · have hh := div_le_div_of_nonneg_right (profile_enclosure p (h p hp)).2 (Nat.cast_nonneg p)
      simpa only [firstPrimeTerm,primeProfile_apply,profile,primeLogWeight,ite_div,zero_div] using hh
  have ht := first_tail_bound hP hb
  constructor <;> linarith [hp.1,hp.2,ht.1,ht.2]

theorem second_computed_enclosure {P : ℕ} (hP : 1 ≤ P)
    {L U : ℕ → ℝ} (hL : ∀ p ∈ Finset.range (P+1),0 ≤ L p)
    (h : ∀ p ∈ Finset.range (P+1), L p ≤ Real.log p ∧ Real.log p ≤ U p) :
    secondComputed L P ≤ secondPrimeMoment ∧
      secondPrimeMoment ≤ secondComputed U P+16/(P : ℝ) := by
  have hp : secondComputed L P ≤ secondPrefix P ∧ secondPrefix P ≤ secondComputed U P := by
    constructor <;> apply Finset.sum_le_sum <;> intro p hp
    · have hh := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (profile_nonneg (hL p hp)) (profile_enclosure p (h p hp)).1 2) (Nat.cast_nonneg p)
      by_cases hprime : p.Prime <;> simpa [secondPrimeTerm,primeProfile_apply,profile,primeLogWeight,hprime] using hh
    · have hh := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (primeProfile_nonneg p) (profile_enclosure p (h p hp)).2 2) (Nat.cast_nonneg p)
      by_cases hprime : p.Prime <;> simpa [secondPrimeTerm,primeProfile_apply,profile,primeLogWeight,hprime] using hh
  have ht := second_tail_bound hP
  constructor <;> linarith [hp.1,hp.2,ht.1,ht.2]

theorem nu_computed_enclosure {n : ℕ} {L U : ℕ → ℝ}
    (h : ∀ p ∈ n.primeFactors,L p ≤ Real.log p ∧ Real.log p ≤ U p) :
    nuComputed L n ≤ nu n ∧ nu n ≤ nuComputed U n := by
  have he : nu n=∑ p ∈ n.primeFactors,primeProfile p := by
    unfold nu
    apply Finset.sum_congr rfl
    intro p hp
    simp [primeProfile_apply,primeLogWeight,(Nat.mem_primeFactors.mp hp).1]
  rw [he]
  exact ⟨Finset.sum_le_sum (fun p hp => (profile_enclosure p (h p hp)).1),
    Finset.sum_le_sum (fun p hp => (profile_enclosure p (h p hp)).2)⟩

theorem nu_rational_mean_bounds {x u v : ℝ} (hx : 0 < x)
    (hu : firstPrimeMoment ≤ u) (hv : secondPrimeMoment ≤ v) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,nu n)/x ≤ u ∧
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,(nu n)^2)/x ≤ u^2+v := by
  have hf := Nat.floor_le hx.le
  have h1 := nu_first_bound ⌊x⌋₊
  have h2 := nu_second_bound ⌊x⌋₊
  constructor
  · apply (div_le_iff₀ hx).mpr
    calc
      _ ≤ (⌊x⌋₊ : ℝ)*firstPrimeMoment := h1
      _ ≤ x*firstPrimeMoment := mul_le_mul_of_nonneg_right hf firstPrimeMoment_nonneg
      _ ≤ u*x := by nlinarith
  · apply (div_le_iff₀ hx).mpr
    have hu2 := pow_le_pow_left₀ firstPrimeMoment_nonneg hu 2
    calc
      _ ≤ (⌊x⌋₊ : ℝ)*(firstPrimeMoment^2+secondPrimeMoment) := h2
      _ ≤ x*(firstPrimeMoment^2+secondPrimeMoment) :=
        mul_le_mul_of_nonneg_right hf (add_nonneg (sq_nonneg _) secondPrimeMoment_nonneg)
      _ ≤ (u^2+v)*x := by nlinarith

theorem nu_finite_computed_enclosure {N : ℕ} {L U : ℕ → ℝ}
    (hL : ∀ n ∈ Finset.Ioc 0 N,∀ p ∈ n.primeFactors,0 ≤ L p)
    (h : ∀ n ∈ Finset.Ioc 0 N,∀ p ∈ n.primeFactors,L p ≤ Real.log p ∧ Real.log p ≤ U p) :
    (∑ n ∈ Finset.Ioc 0 N,nuComputed L n) ≤ (∑ n ∈ Finset.Ioc 0 N,nu n) ∧
    (∑ n ∈ Finset.Ioc 0 N,nu n) ≤ (∑ n ∈ Finset.Ioc 0 N,nuComputed U n) ∧
    (∑ n ∈ Finset.Ioc 0 N,(nuComputed L n)^2) ≤ (∑ n ∈ Finset.Ioc 0 N,(nu n)^2) ∧
    (∑ n ∈ Finset.Ioc 0 N,(nu n)^2) ≤ (∑ n ∈ Finset.Ioc 0 N,(nuComputed U n)^2) := by
  have hh := fun n hn => nu_computed_enclosure (h n hn)
  refine ⟨Finset.sum_le_sum (fun n hn => (hh n hn).1),
    Finset.sum_le_sum (fun n hn => (hh n hn).2),?_,?_⟩
  · apply Finset.sum_le_sum
    intro n hn
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => profile_nonneg (hL n hn p hp))) (hh n hn).1 2
  · exact Finset.sum_le_sum (fun n hn => pow_le_pow_left₀ (nu_nonneg n) (hh n hn).2 2)

end NField.Alignment.CollisionSpectralMomentEnclosure
