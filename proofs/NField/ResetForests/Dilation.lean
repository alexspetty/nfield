/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreBasisTrace
/-! # Exact continuous and complete-grid work under integer dilation -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.GramDecomposition

open scoped BigOperators
open MeasureTheory NField.Alignment CommonResetGram CollisionRampEnergy
open DedekindFourierMoment FibreReconstruction

theorem weighted_profile_periodic (N : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (weightedProfile N c) 1 := by
  intro x
  unfold weightedProfile
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by rw [midpointRow_periodic])

theorem periodic_grid_mod {f : ℝ → ℝ} (hf : Function.Periodic f 1)
    {Q : ℕ} (hQ : 0 < Q) (a : ℕ) :
    f ((a : ℝ)/(Q : ℝ))=f (((a%Q : ℕ) : ℝ)/(Q : ℝ)) := by
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have he : (a : ℝ)/(Q : ℝ)=((a%Q : ℕ) : ℝ)/(Q : ℝ)+((a/Q : ℕ) : ℝ) := by
    have hmod : ((a%Q : ℕ) : ℝ)+(Q : ℝ)*((a/Q : ℕ) : ℝ)=(a : ℝ) := by
      exact_mod_cast Nat.mod_add_div a Q
    field_simp
    nlinarith
  rw [he]
  simpa only [mul_one] using hf.nat_mul (a/Q) (((a%Q : ℕ) : ℝ)/(Q : ℝ))

theorem periodic_complete_grid_dilation {Q m : ℕ} (hQ : 0 < Q)
    (hm : m.Coprime Q) {f : ℝ → ℝ} (hf : Function.Periodic f 1) :
    (∑ a ∈ Finset.range Q, f ((m : ℝ)*((a : ℝ)/(Q : ℝ)) ))=
      ∑ a ∈ Finset.range Q, f ((a : ℝ)/(Q : ℝ)) := by
  have hpoint (a : ℕ) : f ((m : ℝ)*((a : ℝ)/(Q : ℝ)))=
      f (((m*a%Q : ℕ) : ℝ)/(Q : ℝ)) := by
    rw [← mul_div_assoc, ← Nat.cast_mul, periodic_grid_mod hf hQ]
  simp_rw [hpoint]
  exact sum_mul_mod_coprime hQ hm (fun a : ℕ => f ((a : ℝ)/(Q : ℝ)))

theorem periodic_integer_dilation_integral {m : ℕ} (hm : 0 < m)
    {f : ℝ → ℝ} (hf : Function.Periodic f 1)
    (hint : ∀ a b, IntervalIntegrable f volume a b) :
    (∫ x in (0 : ℝ)..1, f ((m : ℝ)*x))=∫ x in (0 : ℝ)..1, f x := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hperiod := hf.intervalIntegral_add_zsmul_eq (m : ℤ) 0 hint
  simp only [Int.cast_natCast, zsmul_eq_mul, mul_one, zero_add] at hperiod
  have hchange := intervalIntegral.mul_integral_comp_mul_left (f := f)
    (a := (0 : ℝ)) (b := 1) (m : ℝ)
  simp only [mul_zero, mul_one] at hchange
  rw [hperiod] at hchange
  exact (mul_left_cancel₀ hmR hchange)

theorem continuous_work_dilation (N : ℕ) (c e : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    (∫ x in (0 : ℝ)..1,
      weightedProfile N c ((m : ℝ)*x)*weightedProfile N e ((m : ℝ)*x))=
        continuousWork N c e := by
  exact periodic_integer_dilation_integral hm
    ((weighted_profile_periodic N c).mul (weighted_profile_periodic N e))
    (weighted_product_interval_integrable N c e)

theorem sampled_work_dilation (N : ℕ) (c e : ℕ → ℝ) {Q m : ℕ}
    (hQ : 0 < Q) (hm : m.Coprime Q) :
    (1/(Q : ℝ))*(∑ a ∈ Finset.range Q,
      weightedProfile N c ((m : ℝ)*((a : ℝ)/(Q : ℝ)))*
        weightedProfile N e ((m : ℝ)*((a : ℝ)/(Q : ℝ))))=sampledWork N Q c e := by
  unfold sampledWork
  congr 1
  simpa only [Pi.mul_apply] using periodic_complete_grid_dilation hQ hm
    ((weighted_profile_periodic N c).mul (weighted_profile_periodic N e))

theorem successor_square_coprime (p : ℕ) : (p+1).Coprime (p^2) := by
  apply Nat.Coprime.pow_right
  rw [Nat.add_comm, Nat.coprime_add_self_left]
  exact Nat.coprime_one_left p

theorem prime_square_bilinear_dilation {p : ℕ} (hp : p.Prime) (c e : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1,
      weightedProfile (p-1) c (((p+1 : ℕ) : ℝ)*x)*
        weightedProfile (p-1) e (((p+1 : ℕ) : ℝ)*x))=continuousWork (p-1) c e ∧
    (1/((p^2 : ℕ) : ℝ))*(∑ a ∈ Finset.range (p^2),
      weightedProfile (p-1) c (((p+1 : ℕ) : ℝ)*((a : ℝ)/((p^2 : ℕ) : ℝ)))*
        weightedProfile (p-1) e (((p+1 : ℕ) : ℝ)*((a : ℝ)/((p^2 : ℕ) : ℝ))))=
          sampledWork (p-1) (p^2) c e :=
  ⟨continuous_work_dilation _ c e (by omega),
    sampled_work_dilation _ c e (pow_pos hp.pos 2) (successor_square_coprime p)⟩

end NField.ResetForests.GramDecomposition
