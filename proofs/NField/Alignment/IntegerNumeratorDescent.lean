/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerInverseResidue

/-! # Exact gcd descent for every signed inverse numerator -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerNumeratorDescent
open scoped BigOperators Topology Classical
open DedekindInverseResidueTransform IntegerInverseResidue

def integerNumeratorDescentSide (q : ℕ) (r : ℤ) : ℂ :=
  let c := Int.gcd r (q:ℤ)
  let Q := q/c
  ∑ d ∈ (excludedPrimeProduct q Q).divisors,
    (ArithmeticFunction.moebius d:ℂ)/(d:ℂ)*
      integerInverseSeries Q ((r/(c:ℤ))*(inverseResidue d Q:ℤ))

theorem integer_descent_side_nat {q r : ℕ} (hQ : 2≤q/r.gcd q) :
    integerNumeratorDescentSide q (r:ℤ)=numeratorDescentSide q r := by
  have hQne : q/r.gcd q≠0 := by omega
  simp only [integerNumeratorDescentSide,numeratorDescentSide,
    Int.gcd_eq_natAbs_gcd_natAbs,Int.natAbs_natCast,dif_neg hQne,
    ← Int.natCast_ediv,← Nat.cast_mul,integer_series_nat]

theorem integer_descent_side_neg_nat (q r : ℕ) :
    integerNumeratorDescentSide q (-(r:ℤ))= -integerNumeratorDescentSide q (r:ℤ) := by
  have hdiv : ((r.gcd q:ℕ):ℤ)∣(r:ℤ) := by exact_mod_cast Nat.gcd_dvd_left r q
  simp only [integerNumeratorDescentSide,Int.gcd_eq_natAbs_gcd_natAbs,
    Int.natAbs_neg,Int.natAbs_natCast,Int.neg_ediv_of_dvd hdiv,neg_mul,integer_series_neg,mul_neg,
    Finset.sum_neg_distrib]

/-- Title: `Exact numerator descent for signed integers`. -/
theorem integer_numerator_descent (q : ℕ) (r : ℤ) :
    let c := Int.gcd r (q:ℤ)
    let Q := q/c
    (Q=1 → integerInverseSeries q r=0) ∧
    (2≤Q → integerInverseSeries q r=integerNumeratorDescentSide q r) := by
  cases r with
  | ofNat r =>
      change (q/r.gcd q=1 → integerInverseSeries q (r:ℤ)=0) ∧
        (2≤q/r.gcd q → integerInverseSeries q (r:ℤ)=integerNumeratorDescentSide q (r:ℤ))
      constructor
      · intro hQ
        rw [integer_series_nat]
        exact exact_numerator_descent.1 hQ
      · intro hQ
        rw [integer_series_nat,integer_descent_side_nat hQ]
        exact exact_numerator_descent.2 hQ
  | negSucc r =>
      change (q/(r+1).gcd q=1 → integerInverseSeries q (-((r+1:ℕ):ℤ))=0) ∧
        (2≤q/(r+1).gcd q → integerInverseSeries q (-((r+1:ℕ):ℤ))=
          integerNumeratorDescentSide q (-((r+1:ℕ):ℤ)))
      constructor
      · intro hQ
        rw [integer_series_neg_nat,exact_numerator_descent.1 hQ,neg_zero]
      · intro hQ
        rw [integer_series_neg_nat,integer_descent_side_neg_nat,integer_descent_side_nat hQ,
          exact_numerator_descent.2 hQ]

/-- Title: `Uniform bound after signed numerator descent`. -/
theorem integer_numerator_descent_bound {q : ℕ} {r : ℤ}
    (hQ : 2≤q/Int.gcd r (q:ℤ)) :
    ‖integerInverseSeries q r‖≤reciprocalDivisorSum q*inverseSawUnitMaximum (q/Int.gcd r (q:ℤ)) := by
  cases r with
  | ofNat r =>
      change ‖integerInverseSeries q (r:ℤ)‖≤_
      rw [integer_series_nat]
      exact exact_numerator_descent_bound hQ
  | negSucc r =>
      change ‖integerInverseSeries q (-((r+1:ℕ):ℤ))‖≤_
      rw [integer_series_neg_nat,norm_neg]
      exact exact_numerator_descent_bound hQ

end NField.Alignment.IntegerNumeratorDescent
