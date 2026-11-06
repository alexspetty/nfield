/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetBandScale
import NField.Alignment.CommonResetBandPhases
import NField.Alignment.CommonResetLocalAbel

/-! # The actual signed three-phase conductor band after finite partial summation -/

noncomputable section

namespace NField.Alignment.CommonResetBandWeighted

open scoped BigOperators
open Set CommonResetBandParameters CommonResetBandGeometry CommonResetBandScale
open CommonResetBandPhases CommonResetAmplitude CommonResetCompletedDerivative
open CommonResetDerivativeFirst CommonResetLocalAbel InverseAdditiveCompletion

def bandSummandScale (p m u v j : ℕ) : ℝ :=
  (p : ℝ)/((m : ℝ)*u*v*j)*bandPhaseScale p m u v j

theorem bandSummandScale_nonneg (p m u v j : ℕ) (hu : 0 < u) :
    0 ≤ bandSummandScale p m u v j :=
  mul_nonneg (by positivity) (bandPhaseScale_nonneg p m u v j hu)

def linkedBandSum (p u v j : ℕ) (η : ℤ) (a N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N+1), gatedPhase p (a+i) u v η j

/-- Title: `Every original linked phase satisfies the conductor-band estimate after partial summation`. -/
theorem linked_band_bound {p m u v j a N : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hmsq : m^2 ≤ p) (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (hua : 2*u < a) (hva : 2*v < a) (hja : 2*j < a)
    (η : ℤ) (hη : η=0 ∨ η=1 ∨ η=-1)
    (hsub : Icc (a : ℝ) (a+N) ⊆ Icc (bandLeft p m) (bandRight p m)) :
    |linkedBandSum p u v j η a N| ≤
      97200*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j := by
  letI : NeZero u := ⟨hu.ne'⟩
  let w (i : ℕ) := bandAmplitude (η == 0) (a+i) u v j
  let g (i : ℕ) := inversePhase 1 (bandFrequency p u v j) ((a+i : ℕ) : ZMod u)*
    phase (reciprocalCoefficient p u v j η/((a+i : ℕ) : ℝ))
  let W : ℝ := (p : ℝ)/(4*(m : ℝ)*u*v*j)
  let M : ℝ := 129600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandPhaseScale p m u v j
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hM : 0 ≤ M := mul_nonneg (by positivity) (bandPhaseScale_nonneg p m u v j hu)
  have hsample (i : ℕ) (hi : i ≤ N) : ((a+i : ℕ) : ℝ) ∈ Icc (bandLeft p m) (bandRight p m) := by
    apply hsub
    push_cast
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg i)
    · exact add_le_add (le_refl _) (Nat.cast_le.mpr hi)
  have hw (i : ℕ) (hi : i < N+1) : 0 ≤ w i ∧ w i ≤ W := by
    refine ⟨bandAmplitude_nonneg _ hu (by omega) hv (by omega) hj (by omega), ?_⟩
    have hit : ((a+i : ℕ) : ℝ) ≤ (p : ℝ)/(m : ℝ) := by
      calc
        _ ≤ bandRight p m := (hsample i (by omega)).2
        _ ≤ _ := div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le p 1)) hmR.le
    calc
      _ ≤ ((a+i : ℕ) : ℝ)/(4*(u : ℝ)*v*j) :=
        bandAmplitude_bound _ hu (by omega) hv (by omega) hj (by omega)
      _ ≤ ((p : ℝ)/m)/(4*(u : ℝ)*v*j) :=
        div_le_div_of_nonneg_right hit (by positivity)
      _ = W := by dsimp [W]; ring
  have hmono (i k : ℕ) (hik : i ≤ k) (_ : k < N+1) : w i ≤ w k :=
    bandAmplitude_monotone _ (Nat.add_le_add_left hik a) hu (by omega) hv (by omega) hj (by omega)
  have hprefix (n : ℕ) (hn : n ≤ N+1) : ‖∑ i ∈ Finset.range n, g i‖ ≤ M := by
    cases n with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty, norm_zero] using hM
    | succ k =>
      have hsubk : Icc (a : ℝ) (a+k) ⊆ Icc (bandLeft p m) (bandRight p m) := by
        intro x hx
        apply hsub
        exact ⟨hx.1, hx.2.trans (add_le_add (le_refl _) (Nat.cast_le.mpr (by omega : k ≤ N)))⟩
      have hb := reciprocal_band_bound hp.two_le hm hmsq hu hup hv hj η hη
        (bandFrequency p u v j) (a : ℤ) k (by simpa only [Int.cast_natCast] using hsubk)
      rw [bandFrequency_gcd hp (by omega)] at hb
      simpa only [M, g, reciprocalInterval, Nat.succ_eq_add_one, Nat.cast_add, Int.cast_add,
        Int.cast_natCast] using hb
  have hweighted := monotone_weighted_interval w g (N+1) W M hW hM hw hmono hprefix
  have he : linkedBandSum p u v j η a N =
      (if η=0 then 1 else -1 : ℝ)*(∑ i ∈ Finset.range (N+1), (w i : ℂ)*g i).im := by
    rw [Complex.im_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact gatedPhase_completed (by omega : 0 < a+i) η j
  have hs : |(if η=0 then 1 else -1 : ℝ)|=1 := by split_ifs <;> norm_num
  rw [he, abs_mul, hs, one_mul]
  calc
    _ ≤ ‖∑ i ∈ Finset.range (N+1), (w i : ℂ)*g i‖ := Complex.abs_im_le_norm _
    _ ≤ 3*W*M := hweighted
    _ = _ := by dsimp [W, M, bandSummandScale]; ring

def frequencyBandSum (p u v j a N : ℕ) : ℝ :=
  linkedBandSum p u v j 0 a N+linkedBandSum p u v j 1 a N+linkedBandSum p u v j (-1) a N

/-- Title: `All three original linked phases obey the uniform conductor-band bound together`. -/
theorem frequency_band_bound {p m u v j a N : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hmsq : m^2 ≤ p) (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hj : 0 < j)
    (hua : 2*u < a) (hva : 2*v < a) (hja : 2*j < a)
    (hsub : Icc (a : ℝ) (a+N) ⊆ Icc (bandLeft p m) (bandRight p m)) :
    |frequencyBandSum p u v j a N| ≤
      291600*(u.divisors.card : ℝ)*Real.sqrt ((j*v).gcd u : ℝ)*bandSummandScale p m u v j := by
  have h0 := linked_band_bound hp hm hmsq hu hup hv hj hua hva hja 0 (Or.inl rfl) hsub
  have h1 := linked_band_bound hp hm hmsq hu hup hv hj hua hva hja 1 (Or.inr (Or.inl rfl)) hsub
  have hn := linked_band_bound hp hm hmsq hu hup hv hj hua hva hja (-1) (Or.inr (Or.inr rfl)) hsub
  unfold frequencyBandSum
  calc
    _ ≤ |linkedBandSum p u v j 0 a N|+|linkedBandSum p u v j 1 a N|+
        |linkedBandSum p u v j (-1) a N| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ _ := by linarith

end NField.Alignment.CommonResetBandWeighted
