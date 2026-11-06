/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealSawtoothLimits
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Multiplication and integrability of the real midpoint sawtooth -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealSawtoothDistribution
open scoped BigOperators Topology Classical
open MeasureTheory Set CollisionDedekindPairing RealSawtoothLimits

theorem sawtooth_periodic : Function.Periodic periodicSawtooth 1 := by
  intro x
  simp [periodicSawtooth,Int.fract_add_one]

theorem sawtooth_add_int (x : ℝ) (n : ℤ) : periodicSawtooth (x+n)=periodicSawtooth x := by
  simpa using sawtooth_periodic.int_mul n x

theorem sawtooth_add_nat (x : ℝ) (n : ℕ) : periodicSawtooth (x+n)=periodicSawtooth x := by
  simpa using sawtooth_periodic.nat_mul n x

theorem periodic_eq_fract {f : ℝ→ℝ} (hf : Function.Periodic f 1) (x : ℝ) :
    f (Int.fract x)=f x := by
  simpa only [Int.fract,mul_one] using hf.sub_int_mul_eq (x := x) (Int.floor x)

theorem sawtooth_measurable : Measurable periodicSawtooth := by
  exact measurable_const.ite (measurableSet_eq_fun measurable_fract measurable_const)
    (measurable_fract.sub measurable_const)

theorem sawtooth_abs_bound (x : ℝ) : |periodicSawtooth x|≤1/2 := by
  unfold periodicSawtooth
  split_ifs with h
  · norm_num
  · rw [abs_le]
    constructor <;> linarith [Int.fract_nonneg x,Int.fract_lt_one x]

theorem sawtooth_integrable (c d a b : ℝ) :
    IntervalIntegrable (fun x => periodicSawtooth (c*x+d)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/2:ℝ)) volume a b).mono_fun'
  · exact (sawtooth_measurable.comp ((measurable_const.mul measurable_id).add measurable_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using sawtooth_abs_bound (c*x+d))

theorem sawtooth_pair_integrable (r s a b : ℝ) :
    IntervalIntegrable (fun x => periodicSawtooth (r*x)*periodicSawtooth (s*x)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/4:ℝ)) volume a b).mono_fun'
  · exact ((sawtooth_measurable.comp (measurable_const.mul measurable_id)).mul
      (sawtooth_measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    change |periodicSawtooth (r*x)*periodicSawtooth (s*x)|≤1/4
    rw [abs_mul]
    have h := mul_le_mul (sawtooth_abs_bound (r*x)) (sawtooth_abs_bound (s*x)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
    nlinarith

def distributionSum (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, periodicSawtooth ((x+j)/m)

theorem distribution_sum_periodic {m : ℕ} (hm : 0 < m) : Function.Periodic (distributionSum m) 1 := by
  intro x
  have he (j : ℕ) : (x+1+(j:ℝ))/(m:ℝ)=(x+(j+1:ℕ))/(m:ℝ) := by push_cast; ring
  unfold distributionSum
  simp_rw [he]
  have hsum := Finset.sum_range_succ' (fun j : ℕ => periodicSawtooth ((x+j)/m)) m
  have hsum' := Finset.sum_range_succ (fun j : ℕ => periodicSawtooth ((x+j)/m)) m
  have hend : periodicSawtooth ((x+(m:ℝ))/m)=periodicSawtooth ((x+(0:ℕ))/m) := by
    have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
    have he' : (x+(m:ℝ))/m=x/m+1 := by field_simp
    rw [he',sawtooth_periodic]
    simp
  rw [hend] at hsum'
  linarith

theorem distribution_sum_cell {m : ℕ} (hm : 0 < m) {x : ℝ} (hx0 : 0≤x) (hx1 : x<1) :
    distributionSum m x=periodicSawtooth x := by
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have hterm (j : ℕ) (hj : j∈Finset.range m) :
      periodicSawtooth ((x+j)/m)=(x+j)/m-1/2+(if x=0 ∧ j=0 then 1/2 else 0) := by
    have hjm : (j:ℝ)+1≤ m := by exact_mod_cast (Finset.mem_range.mp hj)
    have hlo : 0≤(x+j)/m := by positivity
    have hhi : (x+j)/m<1 := (div_lt_one hmR).mpr (by linarith)
    have hf : Int.fract ((x+j)/m)=(x+j)/m := Int.fract_eq_self.mpr ⟨hlo,hhi⟩
    have hz : (x+j)/m=0 ↔ x=0 ∧ j=0 := by
      rw [div_eq_zero_iff]
      simp only [hmR.ne',or_false]
      constructor
      · intro h
        have hj0 : (0:ℝ)≤j := Nat.cast_nonneg j
        have hx : x=0 := by linarith
        have hjz : (j:ℝ)=0 := by linarith
        exact ⟨hx,by exact_mod_cast hjz⟩
      · rintro ⟨rfl,rfl⟩; simp
    simp only [periodicSawtooth,hf]
    by_cases hz0 : x=0 ∧ j=0
    · have he0 := hz.mpr hz0
      rw [if_pos he0,if_pos hz0,he0]
      ring
    · have he0 : (x+j)/m≠0 := fun hh => hz0 (hz.mp hh)
      rw [if_neg he0,if_neg hz0]
      ring
  have hs : (∑ j ∈ Finset.range m, (j:ℝ))=(m:ℝ)*((m:ℝ)-1)/2 := by
    have h := Finset.sum_range_id_mul_two m
    have hR := congrArg (fun n : ℕ => (n:ℝ)) h
    push_cast only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] at hR
    rw [Nat.cast_sub (by omega : 1≤ m),Nat.cast_one] at hR
    linarith
  have hcorr : (∑ j ∈ Finset.range m, if x=0 ∧ j=0 then (1/2:ℝ) else 0)=
      if x=0 then 1/2 else 0 := by
    by_cases hx : x=0 <;> simp [hx,hm]
  have hf : Int.fract x=x := Int.fract_eq_self.mpr ⟨hx0,hx1⟩
  unfold distributionSum
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul,hcorr,hs]
  have hbase : ((m:ℝ)*x+(m:ℝ)*((m:ℝ)-1)/2)/m-(m:ℝ)*1/2=x-1/2 := by field_simp; ring
  rw [hbase]
  simp only [periodicSawtooth,hf]
  split_ifs with hx
  · rw [hx]; ring
  · ring

/-- Title: `Multiplication formula for the real sawtooth`. -/
theorem sawtooth_distribution {m : ℕ} (hm : 0 < m) (x : ℝ) :
    (∑ j ∈ Finset.range m, periodicSawtooth (x+(j:ℝ)/m))=periodicSawtooth ((m:ℝ)*x) := by
  have he : distributionSum m ((m:ℝ)*x)=periodicSawtooth ((m:ℝ)*x) := by
    rw [← periodic_eq_fract (distribution_sum_periodic hm)]
    rw [distribution_sum_cell hm (Int.fract_nonneg _) (Int.fract_lt_one _)]
    exact periodic_eq_fract sawtooth_periodic _
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  simpa only [distributionSum,add_div,mul_div_cancel_left₀ x hmR] using he

end NField.Alignment.RealSawtoothDistribution
