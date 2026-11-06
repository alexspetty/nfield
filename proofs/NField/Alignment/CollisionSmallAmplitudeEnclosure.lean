/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRootIdentityEnclosure
import NField.Alignment.CollisionSmallConductorAmplitudes
import NField.Alignment.CollisionCotangentFiniteDescent

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionSmallAmplitudeEnclosure
open scoped BigOperators
open CollisionSmallConductorCharacters CollisionSmallConductorAmplitudes
open CollisionCharacterLValueEnclosure CollisionHarmonicSeed CollisionFourierEnclosure
open CollisionAmplitudeConstantsEnclosure CollisionJordanVariance

def signedResidue (q n : ℕ) : ℝ := if n%q=1 then 1 else if n%q=q-1 then -1 else 0
def signedSquarePrefix (q N : ℕ) : ℝ := ∑ n∈Finset.range (N+1),signedResidue q n/(n : ℝ)^2

theorem residue_three_character (n : ℕ) : (signedResidue 3 n : ℂ)=chiMinusThree (n : ZMod 3) := by
  have ht (a : ℕ) (ha : a<3) : (signedResidue 3 a : ℂ)=chiMinusThree (a : ZMod 3) := by
    interval_cases a <;> norm_num [signedResidue,chiMinusThree,MulChar.ringHomComp_apply,chiMinusThreeInt]
  simpa [signedResidue,ZMod.natCast_mod] using ht (n%3) (Nat.mod_lt n (by norm_num))

theorem residue_four_character (n : ℕ) : (signedResidue 4 n : ℂ)=chiMinusFour (n : ZMod 4) := by
  have ht (a : ℕ) (ha : a<4) : (signedResidue 4 a : ℂ)=chiMinusFour (a : ZMod 4) := by
    interval_cases a <;> norm_num [signedResidue,chiMinusFour,MulChar.ringHomComp_apply,ZMod.χ₄]
  simpa [signedResidue,ZMod.natCast_mod] using ht (n%4) (Nat.mod_lt n (by norm_num))

theorem residue_six_character (n : ℕ) : (signedResidue 6 n : ℂ)=chiInducedSix (n : ZMod 6) := by
  have ht (a : ℕ) (ha : a<6) : (signedResidue 6 a : ℂ)=chiInducedSix (a : ZMod 6) := by
    rw [chiInducedSix_nat]
    interval_cases a <;> norm_num [signedResidue,chiMinusThree,MulChar.ringHomComp_apply,chiMinusThreeInt]
  simpa [signedResidue,ZMod.natCast_mod] using ht (n%6) (Nat.mod_lt n (by norm_num))

theorem signed_prefix_character {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : ∀ n,(signedResidue q n : ℂ)=χ (n : ZMod q)) (N : ℕ) :
    (signedSquarePrefix q N : ℂ)=characterLTwoPrefix χ N := by
  simp only [signedSquarePrefix,characterLTwoPrefix,Complex.ofReal_sum,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,h]

theorem signed_L_two_enclosure {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : ∀ n,(signedResidue q n : ℂ)=χ (n : ZMod q)) (hN : 1≤N) :
    signedSquarePrefix q N-1/(N : ℝ) ≤ (DirichletCharacter.LFunction χ 2).re ∧
    (DirichletCharacter.LFunction χ 2).re ≤ signedSquarePrefix q N+1/(N : ℝ) := by
  have he := (Complex.abs_re_le_norm (DirichletCharacter.LFunction χ 2-characterLTwoPrefix χ N)).trans
    (character_L_two_tail χ hN)
  rw [← signed_prefix_character χ h N,Complex.sub_re,Complex.ofReal_re] at he
  have he' := abs_le.mp he
  constructor <;> linarith [he'.1,he'.2]

theorem all_small_L_two_enclosures {N : ℕ} (hN : 1≤N) :
    (signedSquarePrefix 3 N-1/(N : ℝ) ≤ (DirichletCharacter.LFunction chiMinusThree 2).re ∧
      (DirichletCharacter.LFunction chiMinusThree 2).re ≤ signedSquarePrefix 3 N+1/(N : ℝ)) ∧
    (signedSquarePrefix 4 N-1/(N : ℝ) ≤ (DirichletCharacter.LFunction chiMinusFour 2).re ∧
      (DirichletCharacter.LFunction chiMinusFour 2).re ≤ signedSquarePrefix 4 N+1/(N : ℝ)) ∧
    (signedSquarePrefix 6 N-1/(N : ℝ) ≤ (DirichletCharacter.LFunction chiInducedSix 2).re ∧
      (DirichletCharacter.LFunction chiInducedSix 2).re ≤ signedSquarePrefix 6 N+1/(N : ℝ)) :=
  ⟨signed_L_two_enclosure chiMinusThree residue_three_character hN,
    signed_L_two_enclosure chiMinusFour residue_four_character hN,
    signed_L_two_enclosure chiInducedSix residue_six_character hN⟩

theorem induced_full_L_two_enclosure {l u : ℝ}
    (h : l ≤ (DirichletCharacter.LFunction chiMinusThree 2).re ∧
      (DirichletCharacter.LFunction chiMinusThree 2).re ≤ u) :
    (5/4 : ℝ)*l ≤ (DirichletCharacter.LFunction chiInducedSix 2).re ∧
      (DirichletCharacter.LFunction chiInducedSix 2).re ≤ (5/4 : ℝ)*u := by
  rw [induced_six_L_two_factor]
  norm_num [Complex.mul_re]
  constructor <;> linarith [h.1,h.2]

theorem sqrt_three_cotangent_enclosure {l u : ℝ}
    (h : l≤Real.cot (Real.pi/6) ∧ Real.cot (Real.pi/6)≤u) :
    l≤Real.sqrt 3 ∧ Real.sqrt 3≤u := by simpa only [cotangent_pi_sixth] using h

theorem sqrt_pi_zeta_enclosure {sl su pl pu zl zu : ℝ}
    (hs0 : 0 ≤ sl) (hp0 : 0 ≤ pl) (hz0 : 0<zl)
    (hs : sl ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ su)
    (hp : pl≤Real.pi ∧ Real.pi≤pu) (hz : zl≤zetaThree ∧ zetaThree≤zu) :
    sl*pl/zu ≤ Real.sqrt 3*Real.pi/zetaThree ∧ Real.sqrt 3*Real.pi/zetaThree ≤ su*pu/zl := by
  apply positive_division_enclosure (mul_nonneg hs0 hp0) hz0 _ hz
  exact ⟨mul_le_mul hs.1 hp.1 hp0 (Real.sqrt_nonneg _),
    mul_le_mul hs.2 hp.2 Real.pi_pos.le (hs0.trans hs.1 |>.trans hs.2)⟩

theorem amplitude_three_formula_enclosure {al au ll lu : ℝ}
    (ha : al≤3*Real.sqrt 3*Real.pi/(52*zetaThree) ∧ 3*Real.sqrt 3*Real.pi/(52*zetaThree)≤au)
    (hl : ll≤(DirichletCharacter.LFunction chiMinusThree 2).re ∧
      (DirichletCharacter.LFunction chiMinusThree 2).re≤lu) :
    1/2-productUpper al au ll lu ≤ amplitude 3 ∧ amplitude 3 ≤ 1/2-productLower al au ll lu := by
  rw [literal_amplitude_three]
  have h := product_interval ha hl
  constructor <;> linarith [h.1,h.2]

theorem amplitude_four_formula_enclosure {al au ll lu : ℝ}
    (ha : al≤Real.pi/(7*zetaThree) ∧ Real.pi/(7*zetaThree)≤au)
    (hl : ll≤(DirichletCharacter.LFunction chiMinusFour 2).re ∧
      (DirichletCharacter.LFunction chiMinusFour 2).re≤lu) :
    1/2-productUpper al au ll lu ≤ amplitude 4 ∧ amplitude 4 ≤ 1/2-productLower al au ll lu := by
  rw [literal_amplitude_four]
  have h := product_interval ha hl
  have he : Real.pi*(DirichletCharacter.LFunction chiMinusFour 2).re/(7*zetaThree)=
      (Real.pi/(7*zetaThree))*(DirichletCharacter.LFunction chiMinusFour 2).re := by ring
  rw [he]
  constructor <;> linarith [h.1,h.2]

theorem amplitude_six_relation_enclosure {l u : ℝ} (h : l≤amplitude 3 ∧ amplitude 3≤u) :
    (15*l-4)/7 ≤ amplitude 6 ∧ amplitude 6 ≤ (15*u-4)/7 := by
  rw [literal_amplitude_six]
  constructor <;> linarith [h.1,h.2]

theorem amplitude_six_direct_formula : amplitude 6=
    1/2-(9*Real.sqrt 3*Real.pi/(91*zetaThree))*(DirichletCharacter.LFunction chiInducedSix 2).re := by
  have h := congrArg Complex.re unitCotangentSum_six
  norm_num [Complex.mul_re] at h
  rw [CollisionAmplitudeCotangent.literal_amplitude_cotangent (by norm_num : 1<6),deltaThree_six,h]
  norm_num
  field_simp [zetaThree_pos.ne']
  ring

theorem amplitude_six_direct_enclosure {al au ll lu : ℝ}
    (ha : al≤9*Real.sqrt 3*Real.pi/(91*zetaThree) ∧ 9*Real.sqrt 3*Real.pi/(91*zetaThree)≤au)
    (hl : ll≤(DirichletCharacter.LFunction chiInducedSix 2).re ∧
      (DirichletCharacter.LFunction chiInducedSix 2).re≤lu) :
    1/2-productUpper al au ll lu ≤ amplitude 6 ∧ amplitude 6 ≤ 1/2-productLower al au ll lu := by
  rw [amplitude_six_direct_formula]
  have h := product_interval ha hl
  constructor <;> linarith [h.1,h.2]

theorem residue_three_even (n : ℕ) : signedResidue 3 (2*n)= -signedResidue 3 n := by
  unfold signedResidue
  split_ifs <;> norm_num at * <;> omega

theorem residue_six_remove_even (n : ℕ) :
    signedResidue 6 n=if 2∣n then 0 else signedResidue 3 n := by
  unfold signedResidue
  simp only [Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> norm_num at * <;> omega

open CollisionCotangentFiniteDescent

theorem finite_even_three_prefix (N : ℕ) :
    (∑' n,if 2∣n then cutoff (fun n => signedResidue 3 n/(n : ℝ)^2) N n else 0)=
      -(1/4 : ℝ)*signedSquarePrefix 3 (N/2) := by
  have hi : Function.Injective (fun n : ℕ => 2*n) := fun _ _ h => Nat.mul_left_cancel (by norm_num) h
  have ht := hi.tsum_eq (f := fun n => if 2∣n then cutoff (fun n => signedResidue 3 n/(n : ℝ)^2) N n else 0)
    (by
      intro n hn
      by_cases hd : 2∣n
      · rcases hd with ⟨m,hm⟩
        exact ⟨m,hm.symm⟩
      · simp [Function.mem_support,hd] at hn)
  rw [← ht]
  have he (n : ℕ) : (if 2∣2*n then cutoff (fun n => signedResidue 3 n/(n : ℝ)^2) N (2*n) else 0)=
      -(1/4 : ℝ)*cutoff (fun n => signedResidue 3 n/(n : ℝ)^2) (N/2) n := by
    rw [if_pos (dvd_mul_right 2 n)]
    have hn : 2*n≤N ↔ n≤N/2 := by omega
    simp only [cutoff,hn,residue_three_even,Nat.cast_mul,Nat.cast_ofNat]
    split_ifs <;> ring
  simp_rw [he]
  rw [tsum_mul_left,cutoff_tsum]
  rfl

theorem finite_induced_six_prefix (N : ℕ) :
    signedSquarePrefix 6 N=signedSquarePrefix 3 N+(1/4 : ℝ)*signedSquarePrefix 3 (N/2) := by
  let f : ℕ → ℝ := fun n => signedResidue 3 n/(n : ℝ)^2
  have he (n : ℕ) : cutoff (fun n => signedResidue 6 n/(n : ℝ)^2) N n=
      cutoff f N n-(if 2∣n then cutoff f N n else 0) := by
    simp only [cutoff,residue_six_remove_even]
    by_cases hn : n≤N <;> by_cases hd : 2∣n <;> simp [hn,hd,f]
  have hs := cutoff_summable f N
  have hs' : Summable (fun n => if 2∣n then cutoff f N n else 0) := by
    apply (hs.indicator {n : ℕ | 2∣n}).congr
    intro n
    simp [Set.indicator_apply]
  rw [signedSquarePrefix,← cutoff_tsum]
  simp_rw [he]
  rw [hs.tsum_sub hs',cutoff_tsum,finite_even_three_prefix]
  change signedSquarePrefix 3 N-(-(1/4 : ℝ)*signedSquarePrefix 3 (N/2))=_
  ring

end NField.Alignment.CollisionSmallAmplitudeEnclosure
