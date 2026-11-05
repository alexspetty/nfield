/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRemainderDynamics
import NField.Alignment.CollisionMassReadout
import Mathlib.Data.Nat.Totient

/-!
# Harmonic bounds for weights on multiples

Pairing primitive numerators with their complements gives the lower
harmonic bound needed for positive finite Mobius regrouping.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionWeightMultiples

open scoped BigOperators Classical
open SecondaryCapacityLedger CollisionRemainderDynamics CollisionMassReadout

def primitiveNumerators (d : ℕ) : Finset ℕ :=
  (Finset.Ico 1 d).filter (fun a => a.Coprime d)

theorem primitiveNumerators_card {d : ℕ} (hd : 2 ≤ d) :
    (primitiveNumerators d).card=d.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [primitiveNumerators,Finset.mem_filter,Finset.mem_Ico,Finset.mem_range]
  constructor
  · rintro ⟨⟨_,ha⟩,hc⟩
    exact ⟨ha,hc.symm⟩
  · rintro ⟨ha,hc⟩
    have ha0 : a≠0 := by
      intro hz
      rw [hz,Nat.coprime_zero_right] at hc
      omega
    exact ⟨⟨by omega,ha⟩,hc.symm⟩

theorem primitiveNumerators_complement {d a : ℕ} (ha : a ∈ primitiveNumerators d) :
    d-a ∈ primitiveNumerators d := by
  obtain ⟨haI,hc⟩ := Finset.mem_filter.mp ha
  obtain ⟨ha1,had⟩ := Finset.mem_Ico.mp haI
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,(Nat.coprime_self_sub_left had.le).mpr hc⟩

theorem reciprocal_complement_sum (d : ℕ) :
    (∑ a ∈ primitiveNumerators d, ((d-a : ℕ) : ℝ)⁻¹)=reducedHarmonicStar d := by
  change (∑ a ∈ primitiveNumerators d, ((d-a : ℕ) : ℝ)⁻¹)=
    ∑ a ∈ primitiveNumerators d, (a : ℝ)⁻¹
  apply Finset.sum_nbij' (fun a => d-a) (fun a => d-a)
    (fun _ ha => primitiveNumerators_complement ha)
    (fun _ ha => primitiveNumerators_complement ha)
  · intro a ha
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
    omega
  · intro a ha
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
    omega
  · intro a _
    rfl

theorem reciprocal_pair_lower {d a : ℕ} (ha : a ∈ primitiveNumerators d) :
    4/(d : ℝ) ≤ (a : ℝ)⁻¹+((d-a : ℕ) : ℝ)⁻¹ := by
  obtain ⟨ha1,had⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
  have haR : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hdR : (a : ℝ) < d := by exact_mod_cast had
  have hda : (0 : ℝ) < (d : ℝ)-(a : ℝ) := by linarith
  have hd0 : (0 : ℝ) < d := haR.trans hdR
  rw [Nat.cast_sub had.le]
  field_simp
  nlinarith [sq_nonneg ((d : ℝ)-2*(a : ℝ))]

theorem reducedHarmonicStar_totient_lower {d : ℕ} (hd : 2 ≤ d) :
    2*(d.totient : ℝ)/(d : ℝ) ≤ reducedHarmonicStar d := by
  have h := Finset.sum_le_sum (s := primitiveNumerators d) (fun a ha => reciprocal_pair_lower ha)
  rw [Finset.sum_add_distrib,reciprocal_complement_sum] at h
  simp only [Finset.sum_const,primitiveNumerators_card hd,nsmul_eq_mul] at h
  change (d.totient : ℝ)*(4/(d : ℝ)) ≤ reducedHarmonicStar d+reducedHarmonicStar d at h
  have he : (d.totient : ℝ)*(4/(d : ℝ))=2*(2*(d.totient : ℝ)/(d : ℝ)) := by ring
  rw [he] at h
  linarith

def harmonicBlock (d j : ℕ) : ℝ :=
  ∑ a ∈ primitiveNumerators d, ((j*d+a : ℕ) : ℝ)⁻¹

def harmonicBlocks (d m : ℕ) : ℝ := ∑ j ∈ Finset.range m, harmonicBlock d j

theorem primitive_multiple_block_mem {d m a : ℕ} (hd : 2 ≤ d)
    (ha : a ∈ primitiveNumerators (d*m)) :
    (a/d,a%d) ∈ (Finset.range m) ×ˢ primitiveNumerators d := by
  obtain ⟨haI,hc⟩ := Finset.mem_filter.mp ha
  obtain ⟨_,hadm⟩ := Finset.mem_Ico.mp haI
  have hcd : a.Coprime d := hc.of_dvd_right (Nat.dvd_mul_right d m)
  have hcm : (a%d).Coprime d := by
    change (a%d).gcd d=1
    rw [← Nat.gcd_rec d a]
    exact hcd.symm
  have hm0 : a%d≠0 := by
    intro hz
    rw [hz,Nat.coprime_zero_left] at hcm
    omega
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_range.mpr ?_,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,?_⟩,hcm⟩⟩
  · apply (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mpr
    simpa only [Nat.mul_comm m d] using hadm
  · exact Nat.mod_lt a (by omega)

theorem reducedHarmonicStar_le_blocks {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    reducedHarmonicStar (d*m) ≤ harmonicBlocks d m := by
  let f : ℕ → ℕ × ℕ := fun a => (a/d,a%d)
  have hi : Set.InjOn f (primitiveNumerators (d*m)) := by
    intro a _ b _ hab
    have hq : a/d=b/d := congrArg Prod.fst hab
    have hr : a%d=b%d := congrArg Prod.snd hab
    have ha := Nat.div_add_mod a d
    have hb := Nat.div_add_mod b d
    rw [hq,hr] at ha
    omega
  have he (a : ℕ) : (f a).1*d+(f a).2=a := by
    dsimp only [f]
    simpa only [Nat.mul_comm d (a/d)] using Nat.div_add_mod a d
  have hs : (primitiveNumerators (d*m)).image f ⊆ (Finset.range m) ×ˢ primitiveNumerators d := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact primitive_multiple_block_mem hd ha
  calc
    reducedHarmonicStar (d*m) = ∑ p ∈ (primitiveNumerators (d*m)).image f,
        ((p.1*d+p.2 : ℕ) : ℝ)⁻¹ := by
      rw [Finset.sum_image hi]
      simp only [he]
      rfl
    _ ≤ ∑ p ∈ (Finset.range m) ×ˢ primitiveNumerators d, ((p.1*d+p.2 : ℕ) : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ = harmonicBlocks d m := by rw [Finset.sum_product]; rfl

theorem harmonicBlock_zero (d : ℕ) : harmonicBlock d 0=reducedHarmonicStar d := by
  simp only [harmonicBlock,Nat.zero_mul,Nat.zero_add]
  rfl

theorem harmonicBlock_bound {d j : ℕ} (hd : 2 ≤ d) (hj : 1 ≤ j) :
    harmonicBlock d j ≤ (d.totient : ℝ)/((j : ℝ)*(d : ℝ)) := by
  have hden : (0 : ℝ) < (j : ℝ)*(d : ℝ) := by positivity
  have hb (a : ℕ) (_ha : a ∈ primitiveNumerators d) :
      ((j*d+a : ℕ) : ℝ)⁻¹ ≤ ((j : ℝ)*(d : ℝ))⁻¹ := by
    rw [Nat.cast_add,Nat.cast_mul]
    simpa only [one_div] using one_div_le_one_div_of_le hden
      (le_add_of_nonneg_right (Nat.cast_nonneg a))
  have h := Finset.sum_le_sum hb
  simpa only [harmonicBlock,Finset.sum_const,primitiveNumerators_card hd,nsmul_eq_mul,
    div_eq_mul_inv] using h

theorem harmonicBlocks_split {m : ℕ} (hm : 1 ≤ m) (d : ℕ) :
    harmonicBlocks d m=reducedHarmonicStar d+∑ j ∈ Finset.Ico 1 m, harmonicBlock d j := by
  have h := Finset.sum_Ico_eq_sub (harmonicBlock d) hm
  simp only [Finset.sum_range_one,harmonicBlock_zero] at h
  unfold harmonicBlocks
  linarith

theorem harmonic_predecessor_Ico {m : ℕ} (_hm : 1 ≤ m) :
    (∑ j ∈ Finset.Ico 1 m, (j : ℝ)⁻¹)=(harmonic (m-1) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  congr 1

theorem reducedHarmonicStar_multiple_bound {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) :
    reducedHarmonicStar (d*m) ≤ reducedHarmonicStar d+
      (d.totient : ℝ)/(d : ℝ)*(harmonic (m-1) : ℝ) := by
  have hb : (∑ j ∈ Finset.Ico 1 m, harmonicBlock d j) ≤
      (d.totient : ℝ)/(d : ℝ)*(harmonic (m-1) : ℝ) := by
    rw [← harmonic_predecessor_Ico hm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have h := harmonicBlock_bound hd (Finset.mem_Ico.mp hj).1
    convert! h using 1
    ring
  have h := reducedHarmonicStar_le_blocks hd m
  rw [harmonicBlocks_split hm d] at h
  exact h.trans (add_le_add le_rfl hb)

theorem collisionWeight_multiple_bound {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) :
    collisionWeight (d*m) ≤ collisionWeight d/(m : ℝ)^2*(1+(harmonic (m-1) : ℝ)/2) := by
  have hH : 0 ≤ (harmonic (m-1) : ℝ) := by rw [harmonic]; positivity
  have hl : (d.totient : ℝ)/(d : ℝ) ≤ reducedHarmonicStar d/2 := by
    have h := div_le_div_of_nonneg_right (reducedHarmonicStar_totient_lower hd)
      (by norm_num : (0 : ℝ) ≤ 2)
    convert! h using 1
    ring
  have h := reducedHarmonicStar_multiple_bound hd hm
  have hu : reducedHarmonicStar (d*m) ≤
      reducedHarmonicStar d*(1+(harmonic (m-1) : ℝ)/2) := by
    nlinarith [mul_le_mul_of_nonneg_right hl hH]
  unfold collisionWeight
  rw [Nat.cast_mul]
  have hb := div_le_div_of_nonneg_right hu (sq_nonneg ((d : ℝ)*(m : ℝ)))
  convert! hb using 1
  rw [mul_pow,div_mul_eq_div_div]
  ring

end NField.Alignment.CollisionWeightMultiples
