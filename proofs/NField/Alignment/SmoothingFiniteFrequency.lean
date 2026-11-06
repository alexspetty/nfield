/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SmoothingCoefficientSums

/-! # Summing the absolutely convergent smoothed Fourier expansion -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SmoothingFiniteFrequency
open scoped BigOperators ComplexConjugate Classical
open Complex BernoulliSymmetricSmoothing BernoulliSmoothingFourier SmoothingCoefficientSums

def phase (j : ℤ) (y : ℝ) : ℂ := exp (2*(Real.pi : ℂ)*I*j*y)

theorem phase_neg (j : ℤ) (y : ℝ) : phase (-j) y=conj (phase j y) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I,map_intCast,
    Int.cast_neg,mul_neg,neg_mul]

theorem coefficient_neg (δ : ℝ) (j : ℤ) :
    smoothingCoefficient δ (-j)=conj (smoothingCoefficient δ j) := by
  unfold smoothingCoefficient
  simp only [Int.cast_neg,map_div₀,map_neg,map_sub,map_mul,map_pow,map_ofNat,
    Complex.conj_ofReal,Complex.conj_I,map_intCast,← Complex.exp_conj,
    mul_neg,neg_mul,neg_neg,neg_sq]

set_option maxHeartbeats 800000 in
theorem smoothed_finite_frequency_bound {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    {H : ℕ} (hH : 1 ≤ H) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfreq : ∀ n : ℕ, 1 ≤ n → ‖∑ i ∈ s, phase n (y i)‖ ≤ A*Real.sqrt (n : ℝ)+B) :
    |∑ i ∈ s, smoothedSaw (1/(H : ℝ)) (y i)| ≤
      8*A*Real.sqrt (H : ℝ)+2*B*((harmonic H : ℝ)+1) := by
  have hH0 : (0 : ℝ)<H := by exact_mod_cast (by omega : 0<H)
  let δ : ℝ := 1/(H : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let a : ℕ → ℝ := fun n => ‖smoothingCoefficient δ (n : ℤ)‖
  have har : ∀ n, 1 ≤ n → a n ≤ 1/(n : ℝ) := fun n hn => coefficient_harmonic_bound hδ hn
  have hsq : ∀ n, 1 ≤ n → a n ≤ (H : ℝ)/(n : ℝ)^2 := by
    intro n hn
    have h := coefficient_square_bound hδ hn
    have he : 1/(δ*(n : ℝ)^2)=(H : ℝ)/(n : ℝ)^2 := by dsimp [δ]; field_simp
    rwa [he] at h
  obtain ⟨ha,haw,hamass,hawmas⟩ := coefficient_mass_bounds hH a (fun _ => norm_nonneg _) har hsq
  let f : ℤ → ℂ := fun j => smoothingCoefficient δ j*(∑ i ∈ s,phase j (y i))
  have hf : HasSum f ((∑ i ∈ s, smoothedSaw δ (y i) : ℝ) : ℂ) := by
    have h := hasSum_sum (fun i (hi : i∈s) => smoothing_hasSum δ (y i))
    have he : (fun j : ℤ => ∑ i ∈ s,
        smoothingCoefficient δ j*exp (2*(Real.pi : ℂ)*I*j*y i))=f := by
      funext j
      simp only [f,phase,Finset.mul_sum]
    rw [he] at h
    simpa only [Complex.ofReal_sum] using h
  have hfnorm : Summable (fun j : ℤ => ‖f j‖) := hf.summable.norm
  have hfp : Summable (fun n : ℕ => ‖f (n : ℤ)‖) :=
    hfnorm.comp_injective (fun a b h => by omega)
  have hfm : Summable (fun n : ℕ => ‖f (-(n : ℤ))‖) :=
    hfnorm.comp_injective (fun a b h => by omega)
  have hneg (j : ℤ) : f (-j)=conj (f j) := by
    simp only [f,coefficient_neg,phase_neg,map_mul,map_sum]
  have hzero : f 0=0 := by simp [f,smoothingCoefficient]
  have hfull : (∑' j : ℤ, ‖f j‖)=2*∑' n : ℕ, ‖f ((n+1 : ℕ) : ℤ)‖ := by
    have hpzero := Summable.tsum_eq_zero_add (f := fun n : ℕ => ‖f (n : ℤ)‖) hfp
    simp only [Nat.cast_zero,hzero,norm_zero,zero_add] at hpzero
    have he := Summable.tsum_of_nat_of_neg (f := fun j : ℤ => ‖f j‖) hfp hfm
    simp_rw [hneg,norm_conj] at he
    simp only [hzero,norm_zero,sub_zero] at he
    rw [hpzero] at he
    simpa only [two_mul] using he
  have hmajor : Summable (fun n : ℕ => A*(a (n+1)*Real.sqrt (n+1 : ℕ))+B*a (n+1)) :=
    (haw.mul_left A).add (ha.mul_left B)
  have hpositive : (∑' n : ℕ, ‖f ((n+1 : ℕ) : ℤ)‖) ≤
      A*(4*Real.sqrt (H : ℝ))+B*((harmonic H : ℝ)+1) := by
    calc
      _ ≤ ∑' n : ℕ, (A*(a (n+1)*Real.sqrt (n+1 : ℕ))+B*a (n+1)) := by
        apply Summable.tsum_le_tsum _ ((summable_nat_add_iff 1).mpr hfp) hmajor
        intro n
        dsimp [f]
        rw [norm_mul]
        have h := mul_le_mul_of_nonneg_left (hfreq (n+1) (by omega))
          (norm_nonneg (smoothingCoefficient δ ((n+1 : ℕ) : ℤ)))
        dsimp [a]
        convert h using 1 <;> simp only [Nat.cast_add,Nat.cast_one] <;> ring
      _ = A*(∑' n : ℕ, a (n+1)*Real.sqrt (n+1 : ℕ))+B*(∑' n : ℕ, a (n+1)) := by
        rw [(haw.mul_left A).tsum_add (ha.mul_left B),tsum_mul_left,tsum_mul_left]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hawmas hA)
        (mul_le_mul_of_nonneg_left hamass hB)
  have hn := norm_tsum_le_tsum_norm hfnorm
  rw [hf.tsum_eq,hfull,Complex.norm_real,Real.norm_eq_abs] at hn
  change |∑ i ∈ s,smoothedSaw δ (y i)| ≤ _
  nlinarith

end NField.Alignment.SmoothingFiniteFrequency
