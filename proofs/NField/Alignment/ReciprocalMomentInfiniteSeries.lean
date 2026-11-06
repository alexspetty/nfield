/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.ReciprocalDivisorMomentBound
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # The actual infinite triple-LCM majorant in the third reciprocal-divisor moment -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.ReciprocalMomentInfiniteSeries
open scoped BigOperators Classical
open ReciprocalDivisorMomentBound DedekindInverseResidueTransform

theorem natural_tuple_majorant {j : ℕ} (hj : 0<j) (d : Fin j → ℕ)
    (hd : ∀ i,0<d i) :
    (∏ i,(d i : ℝ)⁻¹)/(tupleLcm d : ℝ)≤
      ∏ i,1/(d i : ℝ)^momentPSeriesExponent j := by
  let X := Finset.univ.sup d
  let e : Fin j → Fin (X+1) := fun i => ⟨d i,Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  have he : e∈positiveTuples j X := by
    simp only [positiveTuples,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hd
  simpa only [tupleReciprocalWeight,e] using tupleReciprocalWeight_div_lcm_le_pseriesProduct hj he

theorem triple_lcm (a b c : ℕ) : tupleLcm ![a,b,c]=Nat.lcm a (Nat.lcm b c) := by
  apply Nat.dvd_antisymm
  · rw [tupleLcm_dvd_iff]
    intro i
    fin_cases i
    · exact Nat.dvd_lcm_left _ _
    · exact (Nat.dvd_lcm_left b c).trans (Nat.dvd_lcm_right a (Nat.lcm b c))
    · exact (Nat.dvd_lcm_right b c).trans (Nat.dvd_lcm_right a (Nat.lcm b c))
  · apply Nat.lcm_dvd
    · exact tuple_dvd_tupleLcm ![a,b,c] 0
    · exact Nat.lcm_dvd (tuple_dvd_tupleLcm ![a,b,c] 1) (tuple_dvd_tupleLcm ![a,b,c] 2)

theorem triple_weight_identity (a b c : ℕ) :
    (∏ i : Fin 3,(![a,b,c] i : ℝ)⁻¹)/(tupleLcm ![a,b,c] : ℝ)=
      1/((a : ℝ)*b*c*(Nat.lcm a (Nat.lcm b c) : ℝ)) := by
  rw [triple_lcm,Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Fin.succ_zero_eq_one,
    div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

def tripleWeight (v : ℕ × ℕ × ℕ) : ℝ :=
  1/(((v.1+1 : ℕ) : ℝ)*(v.2.1+1 : ℕ)*(v.2.2+1 : ℕ)*
    (Nat.lcm (v.1+1) (Nat.lcm (v.2.1+1) (v.2.2+1)) : ℝ))

theorem triple_weight_majorant (v : ℕ × ℕ × ℕ) :
    tripleWeight v≤(1/((v.1+1 : ℕ) : ℝ)^momentPSeriesExponent 3)*
      ((1/((v.2.1+1 : ℕ) : ℝ)^momentPSeriesExponent 3)*
       (1/((v.2.2+1 : ℕ) : ℝ)^momentPSeriesExponent 3)) := by
  have h := natural_tuple_majorant (by norm_num : 0<3) ![v.1+1,v.2.1+1,v.2.2+1]
    (by intro i; fin_cases i <;> simp)
  rw [triple_weight_identity,Fin.prod_univ_three] at h
  simpa only [tripleWeight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,mul_assoc] using h

/-- The infinite triple series in the source converges without a cutoff. -/
theorem triple_weight_summable : Summable tripleWeight := by
  let f : ℕ → ℝ := fun n => 1/((n+1 : ℕ) : ℝ)^momentPSeriesExponent 3
  have hs : Summable f := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_rpow.mpr (one_lt_momentPSeriesExponent (by norm_num : 0<3)))
  have hn : ∀ n,0≤f n := fun n => by dsimp [f]; positivity
  have hs2 := hs.mul_of_nonneg hs hn hn
  have hs3 := hs.mul_of_nonneg hs2 hn (fun v => mul_nonneg (hn v.1) (hn v.2))
  exact hs3.of_nonneg_of_le (fun v => by unfold tripleWeight; positivity) triple_weight_majorant

theorem finite_triple_series_le_infinite (x : ℕ) :
    (∑ d ∈ positiveTuples 3 x,tupleReciprocalWeight d/(tupleLcm (fun i => (d i).val) : ℝ))≤
      ∑' v : ℕ × ℕ × ℕ,tripleWeight v := by
  let g : (Fin 3 → Fin (x+1)) → ℕ × ℕ × ℕ := fun d => ((d 0).val-1,(d 1).val-1,(d 2).val-1)
  have hinj : Set.InjOn g (positiveTuples 3 x) := by
    intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have h0 := congrArg Prod.fst he
    have h1 := congrArg (fun v : ℕ × ℕ × ℕ => v.2.1) he
    have h2 := congrArg (fun v : ℕ × ℕ × ℕ => v.2.2) he
    have ha0 := ha' 0
    have ha1 := ha' 1
    have ha2 := ha' 2
    have hb0 := hb' 0
    have hb1 := hb' 1
    have hb2 := hb' 2
    funext i
    fin_cases i <;> apply Fin.ext <;> dsimp [g] at h0 h1 h2 ⊢ <;> omega
  have hterm (d : Fin 3 → Fin (x+1)) (hd : d∈positiveTuples 3 x) :
      tripleWeight (g d)=tupleReciprocalWeight d/(tupleLcm (fun i => (d i).val) : ℝ) := by
    have hpos := (Finset.mem_filter.mp hd).2
    have he : (fun i => (d i).val)=![(d 0).val,(d 1).val,(d 2).val] := by
      funext i; fin_cases i <;> rfl
    unfold tupleReciprocalWeight
    rw [he,triple_lcm,Fin.prod_univ_three]
    simp only [tripleWeight,g,Nat.sub_add_cancel (hpos 0),Nat.sub_add_cancel (hpos 1),
      Nat.sub_add_cancel (hpos 2),div_eq_mul_inv,mul_inv_rev,one_mul]
    ring
  calc
    _ = ∑ v ∈ (positiveTuples 3 x).image g,tripleWeight v := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun d hd => (hterm d hd).symm)
    _ ≤ _ := triple_weight_summable.sum_le_tsum _ (fun v _ => by unfold tripleWeight; positivity)

/-- Title: `The third moment is bounded by the full triple-LCM series`. -/
theorem third_moment_infinite_majorant (x : ℕ) :
    (∑ k ∈ Finset.Icc 1 x,reciprocalDivisorSum k^3)≤
      (x : ℝ)*(∑' v : ℕ × ℕ × ℕ,tripleWeight v) := by
  exact reciprocalDivisorMomentSum_le_tupleLcmSeries.trans
    (mul_le_mul_of_nonneg_left (finite_triple_series_le_infinite x) (Nat.cast_nonneg x))

theorem real_third_moment_infinite_majorant (x : ℝ) (hx : 0≤x) :
    (∑ k ∈ Finset.Icc 1 ⌊x⌋₊,reciprocalDivisorSum k^3)≤
      x*(∑' v : ℕ × ℕ × ℕ,tripleWeight v) := by
  exact (third_moment_infinite_majorant ⌊x⌋₊).trans
    (mul_le_mul_of_nonneg_right (Nat.floor_le hx)
      (tsum_nonneg fun v => by unfold tripleWeight; positivity))

end NField.Alignment.ReciprocalMomentInfiniteSeries
