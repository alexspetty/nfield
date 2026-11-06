/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.FejerSmallArc
import NField.Alignment.ReciprocalSecondMoment
import NField.Alignment.ReciprocalBlockDiscrepancy

/-! # Uniform small-arc count in a reciprocal dyadic block -/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalArcBlock
open scoped BigOperators
open FejerSmallArc ReciprocalSecondMoment ReciprocalWeightedBlocks

theorem reciprocal_arc_block (p M : ℕ) (X C T : ℝ) (s : Finset ℕ)
    (hp : 1 ≤ p) (hM : M ≤ p) (hpX : (p:ℝ) ≤ X)
    (hC : 0 ≤ C) (hCT : C ≤ T) (hT : 0 < T)
    (hX : X^2 ≤ T^3) (hlog : (p:ℝ)*(1+Real.log (p:ℝ)) ≤ 4*T^2)
    (hs : s ⊆ Finset.range M)
    (harc : ∀ i ∈ s, ∃ z : ℤ, |X^2/((p+i+1:ℕ):ℝ)-z| ≤ C/(p:ℝ)) :
    (s.card:ℝ) ≤ 1160*T := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hX0 : 0 < X := hp0.trans_le hpX
  by_cases hsmall : (p:ℝ) ≤ 32*T
  · have hc : (s.card:ℝ) ≤ p := by
      exact_mod_cast (Finset.card_le_card hs).trans (by simpa using hM)
    exact hc.trans (hsmall.trans (by linarith))
  let a := (p:ℝ)/(16*T)
  let H : ℕ := ⌊a⌋₊
  have ha2 : 2 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ (by positivity : 0 < 16*T)).mpr
    linarith
  have hHa : (H:ℝ) ≤ a := Nat.floor_le (by linarith)
  have haH : a < (H:ℝ)+1 := Nat.lt_floor_add_one a
  have hH1 : 1 ≤ H := by
    have hh : (1:ℝ) ≤ H := by linarith
    exact_mod_cast hh
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hHlo : (p:ℝ)/(32*T) ≤ (H:ℝ) := by
    have he : (p:ℝ)/(32*T) = a/2 := by dsimp [a]; ring
    rw [he]
    linarith
  have hfreq (d : ℕ) (hd : d ∈ Finset.Icc 1 H) :
      ‖∑ i ∈ Finset.range M,
        fourier (d:ℤ) ((X^2/((p+i+1:ℕ):ℝ):ℝ):AddCircle (1:ℝ))‖ ≤ 129*T := by
    have hd' := Finset.mem_Icc.mp hd
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd'.1
    have hdH : (d:ℝ) ≤ H := by exact_mod_cast hd'.2
    have hPQ : (p:ℝ)^2 ≤ (d:ℝ)*X^2 := by
      have hsquare := pow_le_pow_left₀ hp0.le hpX 2
      nlinarith [sq_nonneg X]
    have hb := reciprocal_prefix_sq_bound p M ((d:ℝ)*X^2) hp hM hPQ
    have hfirst : 32*(d:ℝ)*X^2/(p:ℝ) ≤ 2*T^2 := by
      calc
        _ ≤ 32*a*X^2/(p:ℝ) := by gcongr; exact hdH.trans hHa
        _ = 2*X^2/T := by dsimp [a]; field_simp; ring
        _ ≤ 2*T^2 := by
          apply (div_le_iff₀ hT).mpr
          nlinarith
    have hb' : ‖reciprocalPrefix p M ((d:ℝ)*X^2)‖^2 ≤ (129*T)^2 := by
      calc
        _ ≤ 32*((d:ℝ)*X^2)/(p:ℝ)+4096*(p:ℝ)*(1+Real.log (p:ℝ)) := hb
        _ ≤ 2*T^2+4096*(4*T^2) := by
          apply add_le_add
          · simpa only [mul_assoc] using hfirst
          · nlinarith [hlog]
        _ ≤ _ := by nlinarith [sq_nonneg T]
    have hn : ‖reciprocalPrefix p M ((d:ℝ)*X^2)‖ ≤ 129*T := by
      nlinarith [norm_nonneg (reciprocalPrefix p M ((d:ℝ)*X^2))]
    simpa only [ReciprocalBlockDiscrepancy.reciprocal_frequency,reciprocalPrefix] using hn
  have harc' (i : ℕ) (hi : i ∈ s) :
      ∃ z : ℤ, 16*(H:ℝ)*|X^2/((p+i+1:ℕ):ℝ)-z| ≤ 1 := by
    obtain ⟨z,hz⟩ := harc i hi
    refine ⟨z,?_⟩
    calc
      _ ≤ 16*(H:ℝ)*(C/(p:ℝ)) := mul_le_mul_of_nonneg_left hz (by positivity)
      _ ≤ 16*a*(T/(p:ℝ)) := by gcongr
      _ = 1 := by dsimp [a]; field_simp
  have hc := short_arc_count s (fun i => X^2/((p+i+1:ℕ):ℝ)) M H hH1 hs harc'
    (fun _ => 129*T) (fun _ _ => by positivity) hfreq
  have hcard : (Finset.Icc 1 H).card = H := by simp
  simp only [Finset.sum_const,hcard,nsmul_eq_mul] at hc
  have hPH : (p:ℝ)/(H:ℝ) ≤ 32*T := by
    calc
      _ ≤ (p:ℝ)/((p:ℝ)/(32*T)) :=
        div_le_div_of_nonneg_left hp0.le (by positivity) hHlo
      _ = _ := by field_simp
  calc
    _ ≤ 4/(H:ℝ)*((M:ℝ)+2*((H:ℝ)*(129*T))) := hc
    _ = 4*((M:ℝ)/(H:ℝ))+1032*T := by field_simp; ring
    _ ≤ 4*((p:ℝ)/(H:ℝ))+1032*T := by gcongr
    _ ≤ 4*(32*T)+1032*T := by gcongr
    _ = _ := by ring

end NField.Alignment.ReciprocalArcBlock
