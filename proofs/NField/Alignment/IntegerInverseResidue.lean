/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.DedekindInverseResidueTransform
import NField.Alignment.RealSawtoothDistribution

/-! # Literal signed numerators in the ordered inverse-residue series -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerInverseResidue
open scoped BigOperators Topology Classical
open Filter CarryBoundarySpectra DedekindInverseResidueTransform

def integerInverseCoefficient (q : ℕ) (r : ℤ) (n : ℕ) : ℂ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    if hn : n.Coprime q then centeredSawtooth ((r:ZMod q)*(ZMod.unitOfCoprime n hn)⁻¹.val) else 0

def integerInversePartial (q : ℕ) (r : ℤ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (((n+1:ℕ):ℝ)⁻¹) • integerInverseCoefficient q r (n+1)

def integerInverseSeries (q : ℕ) (r : ℤ) : ℂ :=
  Filter.lim (Filter.map (integerInversePartial q r) atTop)

theorem integer_coefficient_nat (q r n : ℕ) :
    integerInverseCoefficient q (r:ℤ) n=inverseSawCoefficient q r n := by
  simp only [integerInverseCoefficient,inverseSawCoefficient,Int.cast_natCast]

theorem centered_sawtooth_neg_all {q : ℕ} [NeZero q] (x : ZMod q) :
    centeredSawtooth (-x)=-centeredSawtooth x := by
  by_cases hq : q=1
  · subst q
    have hx : x=0 := Subsingleton.elim _ _
    simp [hx,centeredSawtooth]
  · exact centeredSawtooth_neg (by have := NeZero.ne q; omega) x

theorem integer_coefficient_neg (q n : ℕ) (r : ℤ) :
    integerInverseCoefficient q (-r) n= -integerInverseCoefficient q r n := by
  unfold integerInverseCoefficient
  split_ifs with hq hn
  · simp
  · letI : NeZero q := ⟨hq⟩
    simp only [Int.cast_neg,neg_mul,centered_sawtooth_neg_all]
  · simp

theorem integer_partial_nat (q r N : ℕ) :
    integerInversePartial q (r:ℤ) N=inverseSawPartial q r N := by
  simp only [integerInversePartial,inverseSawPartial,inverseSawTerm,integer_coefficient_nat,Nat.succ_pos,if_true]

theorem integer_partial_neg (q N : ℕ) (r : ℤ) :
    integerInversePartial q (-r) N= -integerInversePartial q r N := by
  simp only [integerInversePartial,integer_coefficient_neg,smul_neg,Finset.sum_neg_distrib]

theorem integer_partial_nat_fn (q r : ℕ) :
    integerInversePartial q (r:ℤ)=inverseSawPartial q r := funext (integer_partial_nat q r)

theorem integer_partial_neg_fn (q : ℕ) (r : ℤ) :
    integerInversePartial q (-r)=(fun N => -integerInversePartial q r N) :=
  funext (fun N => integer_partial_neg q N r)

theorem integer_series_nat (q r : ℕ) :
    integerInverseSeries q (r:ℤ)=inverseSawSeries q r := by
  unfold integerInverseSeries inverseSawSeries
  rw [integer_partial_nat_fn]

theorem integer_partial_negative_tendsto (q r : ℕ) :
    Tendsto (integerInversePartial q (-(r:ℤ))) atTop (𝓝 (-inverseSawSeries q r)) := by
  have h := (inverseSawPartial_tendsto q r).neg
  simpa only [integer_partial_neg_fn,integer_partial_nat_fn] using h

theorem integer_series_neg_nat (q r : ℕ) :
    integerInverseSeries q (-(r:ℤ))= -inverseSawSeries q r :=
  (integer_partial_negative_tendsto q r).limUnder_eq

/-- Title: `Ordered inverse-residue convergence for every integer numerator`. -/
theorem integer_inverse_series_tendsto (q : ℕ) (r : ℤ) :
    Tendsto (integerInversePartial q r) atTop (𝓝 (integerInverseSeries q r)) := by
  cases r with
  | ofNat r =>
      change Tendsto (integerInversePartial q (r:ℤ)) atTop (𝓝 (integerInverseSeries q (r:ℤ)))
      rw [integer_series_nat,integer_partial_nat_fn]
      exact inverseSawPartial_tendsto q r
  | negSucc r =>
      change Tendsto (integerInversePartial q (-((r+1:ℕ):ℤ))) atTop
        (𝓝 (integerInverseSeries q (-((r+1:ℕ):ℤ))))
      rw [integer_series_neg_nat]
      exact integer_partial_negative_tendsto q (r+1)

theorem integer_series_neg (q : ℕ) (r : ℤ) :
    integerInverseSeries q (-r)= -integerInverseSeries q r := by
  apply tendsto_nhds_unique (integer_inverse_series_tendsto q (-r))
  simpa only [integer_partial_neg_fn] using (integer_inverse_series_tendsto q r).neg

theorem integer_series_congr_mod {q : ℕ} (hq : 0<q) {r s : ℤ}
    (he : (r:ZMod q)=(s:ZMod q)) : integerInverseSeries q r=integerInverseSeries q s := by
  have hc : ∀ n, integerInverseCoefficient q r n=integerInverseCoefficient q s n := by
    intro n
    simp only [integerInverseCoefficient,dif_neg hq.ne',he]
  have hp : integerInversePartial q r=integerInversePartial q s := by
    funext N
    simp only [integerInversePartial,hc]
  simp only [integerInverseSeries,hp]

end NField.Alignment.IntegerInverseResidue
