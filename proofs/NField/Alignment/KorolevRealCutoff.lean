/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.KorolevWeakRange
import NField.Alignment.IntegerInversePrefix

/-! # The published Korolev range with real cutoffs and signed numerators -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevRealCutoff
open scoped Topology
open Filter DedekindInverseResidueTransform IntegerInversePrefix

def realPrefixDecay (q : ℕ) (X : ℝ) : ℝ :=
  Real.rpow (Real.log X) (-5/24 : ℝ) * Real.rpow (Real.log q) (1/6 : ℝ) *
    Real.rpow (Real.log (Real.log q)) (49/24 : ℝ)

theorem published_lower_spare_unit {q : ℕ}
    (hL : 1 ≤ Real.log (q : ℝ)) (hv : 2 ≤ Real.log (Real.log q)) :
    Real.exp ((Real.log q)^(4/5 : ℝ)*(Real.log (Real.log q))^5) + 1 ≤
      korolevLowerRange q := by
  let L := Real.log (q : ℝ)
  let v := Real.log L
  have hv1 : 1 ≤ v := by dsimp [v,L]; linarith
  have hpow : (1 : ℝ) ≤ L^(4/5 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hv5 : (1 : ℝ) ≤ v^5 := one_le_pow₀ hv1
  have hv6 : 2*v^5 ≤ v^(6 : ℕ) := by
    rw [pow_succ]
    nlinarith [show 2 ≤ v from hv]
  have hvp : v^(6 : ℕ) ≤ v^(73/5 : ℝ) := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num : (6 : ℝ) ≤ 73/5)
  let A := L^(4/5 : ℝ)*v^5
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hpow hv5
  have hB : 2*A ≤ L^(4/5 : ℝ)*v^(73/5 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hv6.trans hvp) (by positivity : 0 ≤ L^(4/5 : ℝ))
    dsimp [A]
    nlinarith
  have heA : 2 ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
  have hstep : Real.exp A + 1 ≤ Real.exp (2*A) := by
    rw [show 2*A=A+A by ring,Real.exp_add]
    nlinarith
  exact hstep.trans (Real.exp_le_exp.mpr hB)

theorem floor_log_half {X : ℝ} (hX : 4 ≤ X) :
    Real.log X/2 ≤ Real.log (⌊X⌋₊ : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hf : X/2 ≤ (⌊X⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one X]
  have hlog := Real.log_le_log (by positivity : 0 < X/2) hf
  rw [Real.log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  have hlogX := Real.log_le_log (by norm_num : (0 : ℝ)<4) hX
  have hfour : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hfour] at hlogX
  linarith

theorem floor_decay_bound (q : ℕ) (hv : 0 ≤ Real.log (Real.log q))
    {X : ℝ} (hX : 4 ≤ X) :
    korolevPrefixDecay q ⌊X⌋₊ ≤ 2*realPrefixDecay q X := by
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < Real.log X/2)
    (floor_log_half hX) (by norm_num : (-5/24 : ℝ) ≤ 0)
  have ht : Real.rpow (2 : ℝ) (5/24 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (5/24 : ℝ) ≤ 1)
  have hh : Real.rpow (Real.log X/2) (-5/24 : ℝ) ≤
      2*Real.rpow (Real.log X) (-5/24 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow hlog.le (by norm_num),
      show (-5/24 : ℝ)= -(5/24) by ring,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul]
    simpa only [Real.rpow_eq_pow,mul_comm] using
      mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hlog.le (- (5/24 : ℝ)))
  have h := mul_le_mul_of_nonneg_right (hp.trans hh)
    (mul_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg q) (1/6 : ℝ))
      (Real.rpow_nonneg hv (49/24 : ℝ)))
  unfold korolevPrefixDecay realPrefixDecay
  simp only [Real.rpow_eq_pow] at *
  nlinarith

/-- Title: `Korolev's exact range for real cutoffs and signed integer numerators`. -/
theorem korolev_real_cutoff : ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ,
    ∀ (q : ℕ) (r : ℤ) (X : ℝ), threshold ≤ q → Int.gcd r (q : ℤ)=1 →
      korolevLowerRange q ≤ X → X ≤ korolevUpperRange q →
      |integerRealPrefix q r X| ≤ C*X*realPrefixDecay q X := by
  obtain ⟨K,hK,hbound⟩ := KorolevWeakRange.weak_range_estimate
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hvlim := Real.tendsto_log_atTop.comp hlog
  have hevent : ∀ᶠ q : ℕ in atTop, ∀ (r : ℤ) (X : ℝ), Int.gcd r (q : ℤ)=1 →
      korolevLowerRange q ≤ X → X ≤ korolevUpperRange q →
      |integerRealPrefix q r X| ≤ (2*K)*X*realPrefixDecay q X := by
    filter_upwards [hbound,hlog.eventually_ge_atTop 1,hvlim.eventually_ge_atTop 2,
      eventually_ge_atTop (2 : ℕ)] with q hb hL hv hq r X hr hlo hhi
    dsimp only [Function.comp_apply] at hv
    have hspare := published_lower_spare_unit hL hv
    have hpow : (1 : ℝ) ≤ (Real.log q)^(4/5 : ℝ) :=
      Real.one_le_rpow hL (by norm_num)
    have hv5 : (32 : ℝ) ≤ (Real.log (Real.log q))^5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hv 5
      norm_num at h ⊢
      exact h
    have hA : 32 ≤ (Real.log q)^(4/5 : ℝ)*(Real.log (Real.log q))^5 := by
      nlinarith
    have hexp := Real.add_one_le_exp ((Real.log q)^(4/5 : ℝ)*(Real.log (Real.log q))^5)
    have hX : 4 ≤ X := by linarith
    have hweak : Real.exp ((Real.log q)^(4/5 : ℝ)*(Real.log (Real.log q))^5) ≤
        (⌊X⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one X]
    have hfloor : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hdecay := floor_decay_bound q (by linarith) hX
    have hnonneg : 0 ≤ realPrefixDecay q X := by
      unfold realPrefixDecay
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
          (Real.rpow_nonneg (by linarith : 0 ≤ Real.log (q : ℝ)) _))
        (Real.rpow_nonneg (by linarith) _)
    have hnat (a : ℕ) (ha : a.Coprime q) :
        |inverseResiduePrefix q a ⌊X⌋₊| ≤ (2*K)*X*realPrefixDecay q X := by
      calc
        _ ≤ K*(⌊X⌋₊ : ℝ)*korolevPrefixDecay q ⌊X⌋₊ :=
          hb a ⌊X⌋₊ ha hweak (hfloor.trans hhi)
        _ ≤ K*(⌊X⌋₊ : ℝ)*(2*realPrefixDecay q X) :=
          mul_le_mul_of_nonneg_left hdecay (mul_nonneg hK (Nat.cast_nonneg _))
        _ ≤ K*X*(2*realPrefixDecay q X) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor hK) (by positivity)
        _ = _ := by ring
    cases r with
    | ofNat r =>
        change |integerRealPrefix q (r : ℤ) X| ≤ _
        rw [integer_real_prefix_nat (by omega)]
        exact hnat r hr
    | negSucc r =>
        change |integerRealPrefix q (-((r+1 : ℕ) : ℤ)) X| ≤ _
        rw [integer_real_prefix_neg,abs_neg,integer_real_prefix_nat (by omega)]
        exact hnat (r+1) hr
  obtain ⟨threshold,hthreshold⟩ := eventually_atTop.mp hevent
  exact ⟨2*K,by positivity,threshold,fun q r X hq => hthreshold q hq r X⟩

end NField.Alignment.KorolevRealCutoff
