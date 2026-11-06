/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionSharpSpectralTail
import NField.Alignment.CollisionSpectralMomentEnclosure
import NField.Alignment.CollisionInverseRationalBound
import NField.Alignment.CollisionAmplitudeRationalEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionSpectralTailEnclosure
open scoped BigOperators
open Set MeasureTheory
open CollisionLogTailKernel CollisionSpectralAbel CollisionSpectralArithmetic
open CollisionJordanVariance CollisionSharpSpectralTail CollisionSpectralErrorBound
open CollisionInverseRationalBound CollisionPositiveLogTail CollisionDivisorSeries
open CollisionDirichletRationalEnclosure CollisionConductorArithmetic

def finiteBand (f : ℕ → ℝ) (Q B : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (B-Q),f (n+Q+1)

theorem indicator_tail_shift {f : ℕ → ℝ} (hf : Summable f) (Q : ℕ) :
    (∑' n : ℕ,if (Q : ℝ) < n then f n else 0)=∑' n,f (n+Q+1) := by
  have hs : Summable (fun n : ℕ => if (Q : ℝ) < n then f n else 0) := by
    apply (hf.indicator {n : ℕ | (Q : ℝ) < n}).congr
    intro n
    simp only [Set.indicator_apply,Set.mem_setOf_eq]
  have h := hs.sum_add_tsum_nat_add (Q+1)
  have hz : (∑ n ∈ Finset.range (Q+1),if (Q : ℝ) < n then f n else 0)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnQ : n ≤ Q := by have hh := Finset.mem_range.mp hn; omega
    simp only [if_neg (not_lt_of_ge (by exact_mod_cast hnQ : (n : ℝ) ≤ Q))]
  rw [hz,zero_add] at h
  rw [← h]
  apply tsum_congr
  intro n
  have hn : (Q : ℝ) < (n+(Q+1) : ℕ) := by exact_mod_cast (show Q < n+(Q+1) by omega)
  rw [if_pos hn]
  simp only [← Nat.add_assoc]

theorem tail_band_split {f : ℕ → ℝ} (hf : Summable f) {Q B : ℕ} (hQB : Q ≤ B) :
    (∑' n,f (n+Q+1))=finiteBand f Q B+∑' n,f (n+B+1) := by
  have hs : Summable (fun n : ℕ => f (n+Q+1)) :=
    hf.comp_injective (fun a b h => by omega)
  have h := hs.sum_add_tsum_nat_add (B-Q)
  rw [← h]
  congr 1
  apply tsum_congr
  intro n
  congr 1
  omega

theorem log_ge_one_of_four_le {x : ℝ} (hx : 4 ≤ x) : 1 ≤ Real.log x := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
  rw [he] at h
  norm_num at h2
  linarith

theorem square_log_antitone {B : ℕ} (hB : 4 ≤ B) :
    AntitoneOn (logPowerKernel 2) (Ici (B : ℝ)) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hd : ∀ x ∈ Ici (B : ℝ),HasDerivAt (logPowerKernel 2)
      (2*Real.log x*(1-Real.log x)/x^3) x := by
    intro x hx
    exact squareLogKernel_hasDerivAt (ne_of_gt (hB0.trans_le hx))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hBx : (B : ℝ) ≤ x := interior_subset hx
  have hl := log_ge_one_of_four_le ((by exact_mod_cast hB : (4 : ℝ) ≤ B).trans hBx)
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  · exact (pow_pos (hB0.trans_le hBx) 3).le

theorem square_log_tail_bound {B : ℕ} (hB : 4 ≤ B) :
    (∑' n : ℕ,logPowerKernel 2 (n+B+1 : ℕ)) ≤ kernelTail B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have h := (square_log_antitone hB).tsum_comp_add_le_integral B
    (squareLogKernel_integrableOn hB0) (fun x _ => squareLogKernel_nonneg x)
  rw [squareLogKernel_integral hB0] at h
  convert! h using 1

theorem weighted_tail_bound {B : ℕ} (hB : 4 ≤ B) :
    0 ≤ weightedTail B ∧ weightedTail B ≤ kernelTail B := by
  rw [weightedTail,indicator_tail_shift weightedTerm_summable]
  constructor
  · exact tsum_nonneg (fun _ => weightedTerm_nonneg _)
  have hs : Summable (fun n : ℕ => weightedTerm (n+B+1)) :=
    weightedTerm_summable.comp_injective (fun a b h => by omega)
  have hk : Summable (fun n : ℕ => logPowerKernel 2 (n+B+1 : ℕ)) :=
    (logPowerKernel_nat_summable 2).comp_injective (fun a b h => by omega)
  apply (hs.tsum_le_tsum (fun n =>
    mul_le_of_le_one_right (squareLogKernel_nonneg _) (spectralWeight_bound _)) hk).trans
  exact square_log_tail_bound hB

theorem kernelTail_log_upper {B : ℕ} (hB : 1 ≤ B) {u : ℝ} (hu : Real.log B ≤ u) :
    kernelTail B ≤ (u^2+2*u+2)/(B : ℝ) := by
  have hb := pow_le_pow_left₀ (Real.log_natCast_nonneg B) hu 2
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg B)
  linarith

theorem weighted_term_enclosure {n : ℕ} {l u : ℝ} (hl : 0 ≤ l)
    (h : l ≤ Real.log n ∧ Real.log n ≤ u) :
    spectralWeight n*l^2/(n : ℝ)^2 ≤ weightedTerm n ∧
      weightedTerm n ≤ spectralWeight n*u^2/(n : ℝ)^2 := by
  have hlo := pow_le_pow_left₀ hl h.1 2
  have hhi := pow_le_pow_left₀ (Real.log_natCast_nonneg n) h.2 2
  unfold weightedTerm logPowerKernel
  constructor
  · calc
      _ ≤ spectralWeight n*(Real.log n)^2/(n : ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlo (spectralWeight_nonneg n)) (sq_nonneg _)
      _ = _ := by ring
  · calc
      _ = spectralWeight n*(Real.log n)^2/(n : ℝ)^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhi (spectralWeight_nonneg n)) (sq_nonneg _)

theorem conductor_energy_majorant (q : ℕ) :
    conductorEnergy q ≤ 32*(zetaKernel 2 q+logPowerKernel 2 q) := by
  by_cases hq : 2 ≤ q
  · have hq0 : 0 < q := by omega
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have ha := pow_le_pow_left₀ (amplitude_nonneg q) (amplitude_four_log_bound hq) 2
    have h := mul_le_mul (jordanTwo_le_square hq0) ha (sq_nonneg _) (sq_nonneg (q : ℝ))
    rw [conductorEnergy,if_pos hq]
    apply h.trans
    have hz : zetaKernel 2 q=1/(q : ℝ)^2 := CollisionPositiveConstants.zetaKernel_nat (by norm_num) q
    rw [hz]
    unfold positiveLogKernel logPowerKernel
    have hl := sq_nonneg (Real.log q-1)
    field_simp
    nlinarith
  · rw [conductorEnergy,if_neg hq]
    exact mul_nonneg (by norm_num) (add_nonneg (zetaKernel_nonneg 2 q) (squareLogKernel_nonneg q))

theorem energy_tail_bound {B : ℕ} (hB : 4 ≤ B) :
    0 ≤ spectralEnergyTail B ∧ spectralEnergyTail B ≤ 32*(1/(B : ℝ)+kernelTail B) := by
  rw [spectralEnergyTail,indicator_tail_shift conductorEnergy_summable]
  constructor
  · exact tsum_nonneg (fun _ => conductorEnergy_nonneg _)
  have hs : Summable (fun n : ℕ => conductorEnergy (n+B+1)) :=
    conductorEnergy_summable.comp_injective (fun a b h => by omega)
  have hz : Summable (fun n : ℕ => zetaKernel 2 (n+B+1)) :=
    (zetaKernel_summable (by norm_num : (1 : ℝ) < 2)).comp_injective (fun a b h => by omega)
  have hk : Summable (fun n : ℕ => logPowerKernel 2 (n+B+1 : ℕ)) :=
    (logPowerKernel_nat_summable 2).comp_injective (fun a b h => by omega)
  have h := hs.tsum_le_tsum (fun n => conductor_energy_majorant (n+B+1)) ((hz.add hk).mul_left 32)
  rw [tsum_mul_left,Summable.tsum_add hz hk] at h
  have ht := zeta_tail_bound (by norm_num : (1 : ℝ) < 2) (show 1 ≤ B by omega)
  norm_num at ht
  rw [Real.rpow_neg_one] at ht
  have hl := square_log_tail_bound hB
  simpa only [one_div] using h.trans (mul_le_mul_of_nonneg_left (add_le_add ht hl) (by norm_num : (0 : ℝ) ≤ 32))

theorem band_computed_enclosure {f L U : ℕ → ℝ} {Q B : ℕ}
    (h : ∀ n ∈ Finset.range (B-Q),L (n+Q+1) ≤ f (n+Q+1) ∧ f (n+Q+1) ≤ U (n+Q+1)) :
    finiteBand L Q B ≤ finiteBand f Q B ∧ finiteBand f Q B ≤ finiteBand U Q B :=
  ⟨Finset.sum_le_sum (fun n hn => (h n hn).1),Finset.sum_le_sum (fun n hn => (h n hn).2)⟩

theorem weighted_band_tail_enclosure {Q B : ℕ} (hQB : Q ≤ B) (hB : 4 ≤ B)
    {l u logu : ℝ} (hlog : Real.log B ≤ logu)
    (h : l ≤ finiteBand weightedTerm Q B ∧ finiteBand weightedTerm Q B ≤ u) :
    l ≤ weightedTail Q ∧ weightedTail Q ≤ u+(logu^2+2*logu+2)/(B : ℝ) := by
  have he : weightedTail Q=finiteBand weightedTerm Q B+weightedTail B := by
    simp only [weightedTail,indicator_tail_shift weightedTerm_summable]
    exact tail_band_split weightedTerm_summable hQB
  have ht := weighted_tail_bound hB
  have hk := kernelTail_log_upper (show 1 ≤ B by omega) hlog
  rw [he]
  constructor <;> linarith [ht.1,ht.2,h.1,h.2]

theorem energy_term_enclosure {q : ℕ} (hq : 2 ≤ q) {l u : ℝ}
    (hl : 0 ≤ l) (h : l ≤ amplitude q ∧ amplitude q ≤ u) :
    jordanTwo q*l^2/27 ≤ conductorEnergy q/27 ∧
      conductorEnergy q/27 ≤ jordanTwo q*u^2/27 := by
  rw [conductorEnergy,if_pos hq]
  exact ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hl h.1 2) (jordanTwo_nonneg q)) (by norm_num),
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (amplitude_nonneg q) h.2 2) (jordanTwo_nonneg q)) (by norm_num)⟩

theorem projection_tail_enclosure {Q B : ℕ} (hQ : 1 ≤ Q) (hQB : Q ≤ B) (hB : 4 ≤ B)
    {l u logu : ℝ} (hlog : Real.log B ≤ logu)
    (h : l ≤ finiteBand (fun q => conductorEnergy q/27) Q B ∧
      finiteBand (fun q => conductorEnergy q/27) Q B ≤ u) :
    l ≤ spectralProjectionError Q ∧
      spectralProjectionError Q ≤ u+32*((logu^2+2*logu+3)/(B : ℝ))/27 := by
  have he : spectralEnergyTail Q=finiteBand conductorEnergy Q B+spectralEnergyTail B := by
    simp only [spectralEnergyTail,indicator_tail_shift conductorEnergy_summable]
    exact tail_band_split conductorEnergy_summable hQB
  have ht := energy_tail_bound hB
  have hk := kernelTail_log_upper (show 1 ≤ B by omega) hlog
  have hb : finiteBand (fun q => conductorEnergy q/27) Q B=finiteBand conductorEnergy Q B/27 := by
    simp only [finiteBand,Finset.sum_div]
  rw [hb] at h
  rw [spectralProjectionError_exact (by exact_mod_cast hQ),he]
  have hr : 32*((logu^2+2*logu+3)/(B : ℝ))/27=
      32*(1/(B : ℝ)+(logu^2+2*logu+2)/(B : ℝ))/27 := by ring
  rw [hr]
  constructor <;> linarith [h.1,h.2,ht.1,ht.2]

theorem amplitude_intersection_enclosure {q M b : ℕ} (hq : 2 ≤ q) (hM : 1 ≤ M)
    (hb : 2*M ≤ 2^b) {u : ℝ} (hu : Real.log q ≤ u) :
    finiteAmplitude CollisionRemainderDynamics.collisionWeight q M ≤ amplitude q ∧
    amplitude q ≤ min (CollisionAmplitudeEnclosure.amplitudeUpper q M)
      (min (finiteAmplitude CollisionRemainderDynamics.collisionWeight q M+(2*(b : ℝ)+3)/((q : ℝ)*(M : ℝ)))
        (4*(1+u)/(q : ℝ)^2)) := by
  have h := CollisionAmplitudeEnclosure.amplitude_mem_enclosure q M
  refine ⟨h.1,le_min h.2 (le_min ?_ ?_)⟩
  · exact CollisionAmplitudeRationalEnclosure.amplitude_period_tail_enclosure (by omega : 0 < q) hM hb
  · apply (amplitude_four_log_bound hq).trans
    unfold positiveLogKernel
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg (q : ℝ))

theorem leading_term_enclosures {Q : ℕ} (hQ : 1 ≤ Q) {cl cu al au ll lu : ℝ}
    (hc0 : 0 ≤ cl) (ha0 : 0 ≤ al) (hl0 : 0 ≤ ll)
    (hc : cl ≤ CollisionSpectralEuler.spectralConstant ∧ CollisionSpectralEuler.spectralConstant ≤ cu)
    (ha : al ≤ CollisionZetaMoments.amplitudeLeading ∧ CollisionZetaMoments.amplitudeLeading ≤ au)
    (hl : ll ≤ Real.log Q ∧ Real.log Q ≤ lu) :
    cl*ll^2/(Q : ℝ) ≤ CollisionSpectralEuler.spectralConstant*(Real.log Q)^2/(Q : ℝ) ∧
    CollisionSpectralEuler.spectralConstant*(Real.log Q)^2/(Q : ℝ) ≤ cu*lu^2/(Q : ℝ) ∧
    al^2*(cl*ll^2/(Q : ℝ))/27 ≤
      CollisionZetaMoments.amplitudeLeading^2*(CollisionSpectralEuler.spectralConstant*(Real.log Q)^2/(Q : ℝ))/27 ∧
    CollisionZetaMoments.amplitudeLeading^2*(CollisionSpectralEuler.spectralConstant*(Real.log Q)^2/(Q : ℝ))/27 ≤
      au^2*(cu*lu^2/(Q : ℝ))/27 := by
  have hC := CollisionSpectralEuler.spectralConstant_pos.le
  have hA := CollisionSpectralEnergyError.spectralLeading_pos.le
  have hlo := div_le_div_of_nonneg_right
    (mul_le_mul hc.1 (pow_le_pow_left₀ hl0 hl.1 2) (sq_nonneg _) hC) (Nat.cast_nonneg Q)
  have hhi := div_le_div_of_nonneg_right
    (mul_le_mul hc.2 (pow_le_pow_left₀ (Real.log_natCast_nonneg Q) hl.2 2) (sq_nonneg _) (hC.trans hc.2))
    (Nat.cast_nonneg Q)
  refine ⟨hlo,hhi,?_,?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ ha0 ha.1 2) hlo
      (div_nonneg (mul_nonneg hc0 (sq_nonneg _)) (Nat.cast_nonneg Q)) (sq_nonneg _)) (by norm_num)
  · exact div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ hA ha.2 2) hhi
      (div_nonneg (mul_nonneg hC (sq_nonneg _)) (Nat.cast_nonneg Q)) (sq_nonneg _)) (by norm_num)

end NField.Alignment.CollisionSpectralTailEnclosure
