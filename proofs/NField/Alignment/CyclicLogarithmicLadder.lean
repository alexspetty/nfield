/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SecondaryFiniteConsequences
import NField.Alignment.CyclicCorrelationReservoir

/-! # Each separate conditional rung of the printed cyclic-correlation ladder -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CyclicLogarithmicLadder
open scoped BigOperators Topology
open Filter Asymptotics CyclicCorrelationReservoir EndpointReservoirAlias
  EndpointReciprocityBridge ExactSamplingReservoirBridge BernoulliCurvature
  SquareLockAsymptoticScales PrimeSecondaryCoefficient

theorem jump_reservoir_log_bound {p : ℕ} (hp : 3 ≤ p) (j : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hcorr : ∀ k, 2 ≤ k → k ≤ p-1 →
      |(cyclicCorrelation k ((p-1)%k) (p^2) : ℝ)| ≤ C*k*Real.log (2*k)^j) :
    |(jumpPhaseReservoir p : ℝ)| ≤ C*(p : ℝ)^2*(2*Real.log p)^j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ p by omega))
  have hterm : ∀ k ∈ Finset.Icc 2 (p-1),
      |((((p-1)/k : ℕ) : ℝ)*(cyclicCorrelation k ((p-1)%k) (p^2) : ℝ))| ≤
        C*(p : ℝ)*(2*Real.log p)^j := by
    intro k hk
    obtain ⟨hk2,hkp⟩ := Finset.mem_Icc.mp hk
    have hquot : (((p-1)/k : ℕ) : ℝ)*(k : ℝ) ≤ p := by
      exact_mod_cast (Nat.div_mul_le_self (p-1) k).trans (Nat.sub_le p 1)
    have hlog : Real.log (2*(k : ℝ)) ≤ 2*Real.log p :=
      (Real.log_le_log (by positivity) (by exact_mod_cast (show 2*k ≤ 2*p by omega))).trans
        (log_double_le (by omega : 2 ≤ p)).2
    have hlog0 : 0 ≤ Real.log (2*(k : ℝ)) := Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ 2*k by omega))
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (((p-1)/k : ℕ) : ℝ)*(C*k*Real.log (2*k)^j) := by gcongr; exact hcorr k hk2 hkp
      _ ≤ (((p-1)/k : ℕ) : ℝ)*(C*k*(2*Real.log p)^j) := by gcongr
      _ = C*((((p-1)/k : ℕ) : ℝ)*k)*(2*Real.log p)^j := by ring
      _ ≤ C*(p : ℝ)*(2*Real.log p)^j := by gcongr
  have hcard : ((Finset.Icc 2 (p-1)).card : ℝ) ≤ p := by
    exact_mod_cast (show (Finset.Icc 2 (p-1)).card ≤ p by simp; omega)
  rw [jumpPhaseReservoir_eq_cyclicCorrelations]
  push_cast
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 (p-1),
        |((((p-1)/k : ℕ) : ℝ)*(cyclicCorrelation k ((p-1)%k) (p^2) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 2 (p-1), C*(p : ℝ)*(2*Real.log p)^j := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 2 (p-1)).card : ℝ)*(C*(p : ℝ)*(2*Real.log p)^j) := by simp
    _ ≤ (p : ℝ)*(C*(p : ℝ)*(2*Real.log p)^j) := by gcongr
    _ = _ := by ring

theorem curvature_correction_le_one {p : ℕ} (hp : p.Prime) :
    0 ≤ 2*(boundarySlope p : ℝ)*(carrierBernoulliCurvature p : ℝ)/(p : ℝ)^4 ∧
    2*(boundarySlope p : ℝ)*(carrierBernoulliCurvature p : ℝ)/(p : ℝ)^4 ≤ 1 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hN : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hH := (SecondaryRealFractionalParts.harmonic_real_le_index (p-1)).trans hN
  have hH0 : 0 ≤ (harmonic (p-1) : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
  rw [carrierBernoulliCurvature_eq_harmonic hp]
  unfold boundarySlope
  push_cast
  constructor
  · positivity
  · calc
      _ ≤ 2*((p : ℝ)*(p : ℝ))*((p : ℝ)/6)/(p : ℝ)^4 := by gcongr
      _ ≤ 1 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [mul_nonneg (show 0 ≤ (p : ℝ)-1 by linarith) (show 0 ≤ (p : ℝ)^3 by positivity)]

theorem sampling_le_jump {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |samplingDefect hp| ≤ 2+4/(p : ℝ)^2*|(jumpPhaseReservoir p : ℝ)| := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have he : ((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2 ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    gcongr
  have hc := curvature_correction_le_one hp
  rw [exact_endpoint_reservoir_alias_formula hp hpodd]
  calc
    _ ≤ |((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2|+
        |4*(jumpPhaseReservoir p : ℝ)/(p : ℝ)^2|+
        |2*(boundarySlope p : ℝ)*(carrierBernoulliCurvature p : ℝ)/(p : ℝ)^4| := by
      have h := abs_sub (((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2+4*(jumpPhaseReservoir p : ℝ)/(p : ℝ)^2)
        (2*(boundarySlope p : ℝ)*(carrierBernoulliCurvature p : ℝ)/(p : ℝ)^4)
      have h' := abs_add_le (((p-1 : ℕ) : ℝ)^2/(p : ℝ)^2)
        (4*(jumpPhaseReservoir p : ℝ)/(p : ℝ)^2)
      linarith
    _ ≤ 1+4/(p : ℝ)^2*|(jumpPhaseReservoir p : ℝ)|+1 := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg hc.1]
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ p^2)]
      norm_num
      rw [show 4*|(jumpPhaseReservoir p : ℝ)|/(p : ℝ)^2 =
        4/(p : ℝ)^2*|(jumpPhaseReservoir p : ℝ)| by ring]
      nlinarith
    _ = _ := by ring

/-- The exponent is shared only as a parameter; each rung has its own hypothesis. -/
theorem correlation_rung (j : ℕ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ k s c : ℕ, 2 ≤ k →
      |(cyclicCorrelation k s c : ℝ)| ≤ C*k*Real.log (2*k)^j) :
    primeSamplingDefect =O[primeAtTop] (fun p => Real.log (p : ℝ)^j) := by
  obtain ⟨C,hC,hcorr⟩ := h
  apply IsBigO.of_bound (2+4*C*2^j)
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with p hp hpprime
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hl : 1 ≤ Real.log (p : ℝ) :=
    (by linarith [Real.log_three_gt_d9] : (1 : ℝ) ≤ Real.log 3).trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hp))
  have hpower : 1 ≤ Real.log (p : ℝ)^j := one_le_pow₀ hl
  have ha := jump_reservoir_log_bound hp j hC (fun k hk _ => hcorr k _ _ hk)
  rw [primeSamplingDefect, dif_pos hpprime, Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ 2+4/(p : ℝ)^2*|(jumpPhaseReservoir p : ℝ)| := sampling_le_jump hpprime (by omega)
    _ ≤ 2+4/(p : ℝ)^2*(C*(p : ℝ)^2*(2*Real.log p)^j) := by gcongr
    _ = 2+4*C*2^j*Real.log p^j := by rw [mul_pow]; field_simp
    _ ≤ (2+4*C*2^j)*Real.log p^j := by nlinarith

/-- Title: `The quadratic logarithmic correlation rung`. -/
theorem quadratic_correlation_rung
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ k s c : ℕ, 2 ≤ k →
      |(cyclicCorrelation k s c : ℝ)| ≤ C*k*Real.log (2*k)^2) :
    primeSamplingDefect =O[primeAtTop] (fun p => Real.log (p : ℝ)^2) := correlation_rung 2 h

/-- Title: `The logarithmic correlation rung`. -/
theorem logarithmic_correlation_rung
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ k s c : ℕ, 2 ≤ k →
      |(cyclicCorrelation k s c : ℝ)| ≤ C*k*Real.log (2*k)) :
    primeSamplingDefect =O[primeAtTop] (fun p => Real.log (p : ℝ)) := by
  simpa only [pow_one] using correlation_rung 1 (by simpa only [pow_one] using h)

/-- Title: `The bounded correlation rung`. -/
theorem bounded_correlation_rung
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ k s c : ℕ, 2 ≤ k →
      |(cyclicCorrelation k s c : ℝ)| ≤ C*k) :
    primeSamplingDefect =O[primeAtTop] (fun _ => (1 : ℝ)) := by
  simpa only [pow_zero] using correlation_rung 0 (by simpa only [pow_zero,mul_one] using h)

end NField.Alignment.CyclicLogarithmicLadder
