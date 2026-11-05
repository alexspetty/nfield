/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.MagnitudeFourthMomentBound
import NField.Alignment.PrimeSquareMagnitudeTwist

/-!
# Uniform moments of the actual primitive odd L-values

The full-character finite-polynomial bound is restricted by positivity and
the exact family population. The proved ordered L-value tail then transfers
it to the actual analytic fourth moment.
-/

set_option autoImplicit false

namespace NField.Alignment.MagnitudeLMomentBound

open scoped BigOperators Topology
open Filter
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionPeriodicLValue
open NField.Alignment.PrimeSquareMagnitudeFamily
open NField.Alignment.SpectralRepulsion
open NField.Alignment.FiniteMagnitudeDecorrelation
open NField.Alignment.MagnitudeLTruncation
open NField.Alignment.MagnitudeFourthMomentBound

theorem primitive_family_average_le {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : p ≠ 2) (f : Character (p^2) → ℝ)
    (hf : ∀ χ, 0 ≤ f χ) :
    uniformAverage (fun χ : PrimitiveOddFamily p => f χ.val) ≤
      (2*(p : ℝ)/((p : ℝ)-1))*uniformAverage f := by
  classical
  have hsum : (∑ χ : PrimitiveOddFamily p, f χ.val) ≤ ∑ χ : Character (p^2), f χ := by
    have heq := Finset.sum_subtype (p := fun χ : Character (p^2) => χ.IsPrimitive ∧ χ.Odd)
      (F := familyFintype p)
      (Finset.univ.filter (fun χ : Character (p^2) => χ.IsPrimitive ∧ χ.Odd)) (by simp) f
    rw [← heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun χ _ _ => hf χ)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
  have hratio : (Fintype.card (PrimitiveOddFamily p) : ℝ)⁻¹ =
      (2*(p : ℝ)/((p : ℝ)-1))*(Fintype.card (Character (p^2)) : ℝ)⁻¹ := by
    rw [family_population hp hpodd, character_card_eq_totient,
      Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
    simp only [Nat.reduceSub, pow_one, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    field_simp
  unfold uniformAverage
  calc
    _ ≤ (Fintype.card (PrimitiveOddFamily p) : ℝ)⁻¹ * ∑ χ : Character (p^2), f χ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [hratio]; ring

theorem primitive_family_factor_le_three {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    2*(p : ℝ)/((p : ℝ)-1) ≤ 3 := by
  have hpn : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hpn
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ)-1)).mpr
  linarith

theorem uniform_primitive_polynomial_fourth_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ (p : ℕ) [NeZero p] [NeZero (p^2)],
      p.Prime → p≠2 →
      uniformAverage (fun χ : PrimitiveOddFamily p => ‖orderedLPartial χ.val (p^4)‖^4) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := uniform_polynomial_fourth_moment_bound
  refine ⟨3*M, by positivity, ?_⟩
  intro p _ _ hp hpodd
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : (p^2)^2 = p^4 := by ring
  calc
    _ ≤ (2*(p : ℝ)/((p : ℝ)-1))*
        uniformAverage (fun χ : Character (p^2) => ‖orderedLPartial χ (p^4)‖^4) :=
      primitive_family_average_le hp hpodd _ (fun _ => by positivity)
    _ ≤ (2*(p : ℝ)/((p : ℝ)-1))*M := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hb := hbound (p^2)
      rw [hpow] at hb
      exact hb
    _ ≤ 3*M := mul_le_mul_of_nonneg_right (primitive_family_factor_le_three hp hpodd) hM.le

theorem actual_l_fourth_transfer {p : ℕ} [NeZero (p^2)]
    (hp : 0 < p) (χ : PrimitiveOddFamily p) :
    lMagnitude p χ ^ 4 ≤ 8*(‖orderedLPartial χ.val (p^4)‖^4 + 16) := by
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have herror : ‖DirichletCharacter.LFunction χ.val 1 - orderedLPartial χ.val (p^4)‖ ≤ 2 := by
    calc
      _ ≤ 2/(p : ℝ)^2 := primitive_odd_l_truncation χ
      _ ≤ 2/1 := by gcongr; nlinarith
      _ = 2 := by norm_num
  have hnorm : lMagnitude p χ ≤ ‖orderedLPartial χ.val (p^4)‖+2 := by
    unfold lMagnitude
    calc
      _ = ‖orderedLPartial χ.val (p^4) +
          (DirichletCharacter.LFunction χ.val 1 - orderedLPartial χ.val (p^4))‖ := by
        congr 1
        abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl herror)
  calc
    _ ≤ (‖orderedLPartial χ.val (p^4)‖+2)^4 :=
      pow_le_pow_left₀ (l_magnitude_nonneg p χ) hnorm 4
    _ ≤ 8*(‖orderedLPartial χ.val (p^4)‖^4+16) := by
      simpa only [show (4 : ℕ)-1=3 by norm_num, show (2 : ℝ)^3=8 by norm_num,
        show (2 : ℝ)^4=16 by norm_num]
        using add_pow_le (norm_nonneg (orderedLPartial χ.val (p^4))) (by norm_num : (0 : ℝ) ≤ 2) 4

/-- The actual fourth L-moment, with one constant for all odd prime bases. -/
theorem uniform_l_fourth_moment_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ (p : ℕ) [NeZero p] [NeZero (p^2)],
      p.Prime → p≠2 → uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 4) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := uniform_primitive_polynomial_fourth_bound
  refine ⟨8*(M+16), by positivity, ?_⟩
  intro p _ _ hp hpodd
  letI : Nonempty (PrimitiveOddFamily p) := family_nonempty hp hpodd
  calc
    _ ≤ uniformAverage (fun χ : PrimitiveOddFamily p =>
        8*(‖orderedLPartial χ.val (p^4)‖^4+16)) :=
      average_mono (actual_l_fourth_transfer hp.pos)
    _ = 8*(uniformAverage (fun χ : PrimitiveOddFamily p => ‖orderedLPartial χ.val (p^4)‖^4)+16) := by
      rw [uniformAverage_mul_left, uniformAverage_add, average_const]
    _ ≤ 8*(M+16) := by gcongr; exact hbound p hp hpodd

/-- The normalized finite Holder step used to pass from the fourth moment
to the third. The sample is complete and nonempty. -/
theorem average_third_le_fourth {ι : Type*} [Fintype ι] [Nonempty ι]
    (Y : ι → ℝ) (hY : ∀ i, 0 ≤ Y i) :
    uniformAverage (fun i => Y i ^ 3) ≤
      (uniformAverage (fun i => Y i ^ 4))^(3/4 : ℝ) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hN (f : ι → ℝ) :
      (∑ i, f i) = (Fintype.card ι : ℝ)*uniformAverage f := by
    unfold uniformAverage
    field_simp
  have hpq : (4/3 : ℝ).HolderConjugate 4 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h34 (i : ι) : (Y i ^ 3)^(4/3 : ℝ) = Y i ^ 4 := by
    rw [← Real.rpow_natCast (Y i) 3, ← Real.rpow_mul (hY i)]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun i => Y i ^ 3) (g := fun _ => (1 : ℝ)) hpq
    (fun i _ => pow_nonneg (hY i) 3) (fun _ _ => by norm_num)
  simp only [mul_one, h34, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, show (1/(4/3) : ℝ)=3/4 by norm_num] at h
  rw [hN (fun i => Y i ^ 3), hN (fun i => Y i ^ 4),
    Real.mul_rpow hn.le (average_nonneg (fun i => pow_nonneg (hY i) 4))] at h
  have hcard : (Fintype.card ι : ℝ)^(3/4 : ℝ) *
      (Fintype.card ι : ℝ)^(1/4 : ℝ) = (Fintype.card ι : ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    _ ≤ _ := h
    _ = (Fintype.card ι : ℝ)*(uniformAverage (fun i => Y i ^ 4))^(3/4 : ℝ) := by
      calc
        _ = ((Fintype.card ι : ℝ)^(3/4 : ℝ) * (Fintype.card ι : ℝ)^(1/4 : ℝ)) *
            (uniformAverage (fun i => Y i ^ 4))^(3/4 : ℝ) := by ring
        _ = _ := by rw [hcard]

/-- Whole Proposition 10: absolute uniform fourth and third moments of the
actual L magnitudes, on every odd prime base (hence also on those at least five). -/
theorem uniform_l_fourth_and_third_moments :
    ∃ M₄ M₃ : ℝ, 0 < M₄ ∧ 0 < M₃ ∧ ∀ (p : ℕ) [NeZero p] [NeZero (p^2)],
      p.Prime → p≠2 →
      uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 4) ≤ M₄ ∧
      uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 3) ≤ M₃ := by
  obtain ⟨M, hM, hbound⟩ := uniform_l_fourth_moment_bound
  refine ⟨M, M^(3/4 : ℝ), hM, Real.rpow_pos_of_pos hM _, ?_⟩
  intro p _ _ hp hpodd
  letI : Nonempty (PrimitiveOddFamily p) := family_nonempty hp hpodd
  refine ⟨hbound p hp hpodd, ?_⟩
  calc
    _ ≤ (uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 4))^(3/4 : ℝ) :=
      average_third_le_fourth _ (l_magnitude_nonneg p)
    _ ≤ M^(3/4 : ℝ) := Real.rpow_le_rpow
      (average_nonneg fun χ => pow_nonneg (l_magnitude_nonneg p χ) 4)
      (hbound p hp hpodd) (by norm_num)

/-- The actual-family correlation limit now retains only the short
fractional-moment limit. The uniform third L-moment is proved here. -/
theorem correlation_limit_from_short_moment
    {α : Type*} {l : Filter α} (base : α → ℕ)
    [∀ a, NeZero (base a ^ 2)]
    (hprime : ∀ a, (base a).Prime) (hbase : ∀ a, 5 ≤ base a)
    (hHarper : Tendsto
      (fun a => magnitudeMoment (3/2) (shortMagnitude (base a))) l (𝓝 0)) :
    Tendsto (fun a => familyCorrelation (base a)) l (𝓝 0) := by
  letI : ∀ a, NeZero (base a) := fun a => ⟨(hprime a).ne_zero⟩
  obtain ⟨M₄, M₃, _, _, hbound⟩ := uniform_l_fourth_and_third_moments
  apply correlation_limit_from_final_analytic_inputs base hprime hbase M₃ _ hHarper
  intro a
  have h := (hbound (base a) (hprime a) (by have := hbase a; omega)).2
  have hpow (x : ℝ) : x^(3 : ℝ) = x^(3 : ℕ) := Real.rpow_natCast x 3
  simpa only [magnitudeMoment, hpow] using h

end NField.Alignment.MagnitudeLMomentBound
