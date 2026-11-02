/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.OddBernoulliMoments
import NField.Alignment.MagnitudeDoublingMoment
import NField.Alignment.PrimeSquareSawtoothEnergy

/-!
# Full and lifted prime-square odd Bernoulli tables

These finite identities follow the written proof in Magnitude Decorrelation:
evaluate the complete doubling sum, remove exactly the prime multiples, and
then identify the odd characters lifted from the prime level.
-/

set_option autoImplicit false

namespace NField.Alignment.OddBernoulliMoments

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.PrimeSquareMagnitudeFamily
open NField.Alignment.PrimeSquareSawtoothEnergy
open NField.Alignment.PrimeCarryFiberCentering
open NField.Alignment.CenteredCollisionSum

attribute [local instance] Classical.propDecidable

noncomputable def doublingWeight (q : ℕ) (x : ZMod q) : ℂ :=
  (x.val : ℂ) * (2 * (((2*x.val)%q : ℕ) : ℂ) - q)

theorem sum_zmod_val {q : ℕ} [NeZero q] (F : ℕ → ℂ) :
    (∑ x : ZMod q, F x.val) = ∑ c ∈ Finset.range q, F c := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
  intro c
  have he : (ZMod.finEquiv q).toEquiv c = (c.val : ZMod q) := by
    simpa using NField.Alignment.ConductorDepthSawtooth.finEquiv_eq_natCast c
  simp only [he, ZMod.val_natCast, Nat.mod_eq_of_lt c.isLt]

theorem doublingWeight_sum {q : ℕ} [NeZero q] (hq : Odd q) :
    (∑ x : ZMod q, doublingWeight q x) =
      (q : ℂ) * (q-1) * (q-5) / 12 := by
  unfold doublingWeight
  rw [sum_zmod_val (fun c => (c : ℂ) * (2 * (((2*c)%q : ℕ) : ℂ) - q))]
  have h := congrArg (fun t : ℝ => (t : ℂ)) (odd_doubling_sum_range hq)
  push_cast at h
  exact h

theorem doublingWeight_primeMultiple {p : ℕ} [NeZero p] [NeZero (p^2)]
    (x : ZMod p) :
    doublingWeight (p^2) (primeMultiple x) = (p : ℂ)^2 * doublingWeight p x := by
  unfold doublingWeight
  rw [primeMultiple_val]
  have hm : (2*(p*x.val))%(p^2) = p*((2*x.val)%p) := by
    rw [show 2*(p*x.val) = p*(2*x.val) by ring, pow_two, Nat.mul_mod_mul_left]
  rw [hm]
  push_cast
  ring

/-- The unit restriction really removes every multiple of the prime. -/
theorem doublingWeight_primeSquare_units {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : Odd p) :
    (∑ x : UnitClass (p^2), doublingWeight (p^2) x.val) =
      (p : ℂ)^2 * (p-1) * ((p : ℂ)^3-5) / 12 := by
  have h := sum_primeSquare_eq_units_add_multiples hp (doublingWeight (p^2))
  simp_rw [doublingWeight_primeMultiple] at h
  rw [← Finset.mul_sum, doublingWeight_sum hpodd,
    doublingWeight_sum (q := p^2) hpodd.pow] at h
  push_cast at h
  linear_combination -h

theorem primeSquare_unit_doubling_restriction
    {p : ℕ} [NeZero p] [NeZero (p^2)] (hp : p.Prime) (hpodd : Odd p) :
    (∑ x : UnitClass (p^2), doublingWeight (p^2) x.val) =
      (∑ c ∈ Finset.Ico 1 (p^2),
        (c : ℂ) * (2 * (((2*c)%(p^2) : ℕ) : ℂ) - (p^2:ℕ))) -
      (p : ℂ)^2 * (∑ c ∈ Finset.Ico 1 p,
        (c : ℂ) * (2 * (((2*c)%p : ℕ) : ℂ) - p)) := by
  rw [doublingWeight_primeSquare_units hp hpodd]
  have h := congrArg (fun t : ℝ => (t : ℂ)) (odd_doubling_square_subtraction hpodd)
  push_cast at h ⊢
  exact h.symm

/-- At prime level the only excluded residue is zero, whose weight is zero. -/
theorem sum_prime_units {p : ℕ} [NeZero p] (hp : p.Prime)
    (F : ZMod p → ℂ) (hzero : F 0 = 0) :
    (∑ x : UnitClass p, F x.val) = ∑ x : ZMod p, F x := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have heq : (∑ x : UnitClass p, F x.val) =
      ∑ x : ZMod p with x ≠ 0, F x := by
    apply Finset.sum_bij (fun x _ => x.val)
    · intro x _
      simp [Units.ne_zero x]
    · intro x _ y _ h
      exact Units.ext h
    · intro x hx
      exact ⟨Units.mk0 x (Finset.mem_filter.mp hx).2, Finset.mem_univ _, rfl⟩
    · intro x _
      rfl
  rw [heq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0
  · simp [hx, hzero]
  · simp [hx]

theorem full_odd_prime_twist {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpodd : Odd p) :
    (∑ χ : Character p with χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ) * χ 2) =
      ((p : ℂ)-1)^2 * (p-5) / (24*p) := by
  rw [odd_bernoulli_twist_two hpodd]
  change (p.totient : ℂ) / (2 * (p : ℂ)^2) *
    (∑ x : UnitClass p, doublingWeight p x.val) = _
  rw [sum_prime_units hp _ (by simp [doublingWeight]), doublingWeight_sum hpodd,
    Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  push_cast
  field_simp
  ring

theorem full_odd_primeSquare_twist {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : Odd p) :
    (∑ χ : Character (p^2) with χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ) * χ 2) =
      ((p : ℂ)-1)^2 * ((p : ℂ)^3-5) / (24*p) := by
  rw [odd_bernoulli_twist_two hpodd.pow]
  change ((p^2).totient : ℂ) / (2 * (p^2 : ℕ)^2) *
    (∑ x : UnitClass (p^2), doublingWeight (p^2) x.val) = _
  rw [doublingWeight_primeSquare_units hp hpodd,
    Nat.totient_prime_pow hp (by omega : 0 < 2)]
  simp only [Nat.reduceSub, pow_one]
  rw [Nat.cast_mul, Nat.cast_sub hp.one_le]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  push_cast
  field_simp
  ring

theorem odd_character_unit_sum {q : ℕ} [NeZero q]
    (χ : Character q) (hχ : χ.Odd) :
    (∑ x : UnitClass q, χ x.val) = 0 := by
  have h : (∑ x : UnitClass q, χ x.val) = -(∑ x : UnitClass q, χ x.val) := by
    calc
      _ = ∑ x : UnitClass q, χ (-x).val :=
        (Equiv.sum_comp (Equiv.neg (UnitClass q)) (fun x => χ x.val)).symm
      _ = _ := by simp only [Units.val_neg, hχ.eval_neg, Finset.sum_neg_distrib]
  linear_combination h / 2

/-- The normalized coordinate sum in a prime-square reduction fiber. -/
theorem bernoulli_coordinate_fiber_sum {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (u : UnitClass p) :
    (∑ x : Fiber (squareUnitReduction p) u, (x.val.val.val : ℂ) / (p : ℂ)^2) =
      (u.val.val : ℂ) / p + ((p : ℂ)-1)/2 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hc : Fintype.card (Fiber (squareUnitReduction p) u) = p :=
    (Fintype.card_congr (squareFiberEquiv hp u)).symm.trans (Fintype.card_fin p)
  have h := bernoulli_fiber_mean hp u
  unfold fiberMean at h
  simp only [bernoulliInput, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, hc, nsmul_eq_mul, mul_one] at h
  calc
    _ = (p : ℂ) * ((p : ℂ)⁻¹ *
        ((∑ x : Fiber (squareUnitReduction p) u, (x.val.val.val : ℂ) / (p : ℂ)^2) - p)) + p := by
      field_simp
      ring
    _ = (p : ℂ) * ((u.val.val : ℂ)/(p : ℂ)^2 + ((p : ℂ)-1)/(2*p) - 1) + p := by
      rw [h]
    _ = _ := by field_simp; ring

/-- Lifting an odd character from `p` to `p²` preserves its Bernoulli sum. -/
theorem bernoulli_lift_primeSquare {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (ψ : Character p) (hψ : ψ.Odd) :
    generalizedBernoulliOne
        (DirichletCharacter.changeLevel (dvd_pow_self p (by omega : 2 ≠ 0)) ψ) =
      generalizedBernoulliOne ψ := by
  let hd : p ∣ p^2 := dvd_pow_self p (by omega)
  have hlift (x : UnitClass (p^2)) :
      DirichletCharacter.changeLevel hd ψ x.val = ψ (squareUnitReduction p x).val :=
    liftedCharacter_apply_unit hd ψ x
  rw [← bernoulli_flux, ← bernoulli_flux]
  unfold boundaryFlux
  simp_rw [hlift]
  push_cast
  rw [← Fintype.sum_fiberwise (squareUnitReduction p)]
  have hf (u : UnitClass p) :
      (∑ x : Fiber (squareUnitReduction p) u,
        (x.val.val.val : ℂ)/(p : ℂ)^2 * ψ (squareUnitReduction p x.val).val) =
        ((u.val.val : ℂ)/p + ((p : ℂ)-1)/2) * ψ u.val := by
    have hx (x : Fiber (squareUnitReduction p) u) : squareUnitReduction p x.val = u :=
      x.property
    simp_rw [hx]
    rw [← Finset.sum_mul, bernoulli_coordinate_fiber_sum hp u]
  simp_rw [hf, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, odd_character_unit_sum ψ hψ,
    mul_zero, add_zero]

theorem lift_character_two {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hpodd : Odd p) (ψ : Character p) :
    DirichletCharacter.changeLevel (dvd_pow_self p (by omega : 2 ≠ 0)) ψ 2 = ψ 2 := by
  let hd : p ∣ p^2 := dvd_pow_self p (by omega)
  let z : UnitClass (p^2) := ZMod.unitOfCoprime 2 hpodd.pow.coprime_two_left
  have hz : z.val = 2 := by simp [z]
  have hred : (ZMod.unitsMap hd z).val = (2 : ZMod p) := by
    change ZMod.cast z.val = (2 : ZMod p)
    rw [hz]
    exact ZMod.cast_natCast hd 2
  simpa only [hz, hred] using liftedCharacter_apply_unit hd ψ z

/-- Every imprimitive odd character at `p²` is counted exactly once by lifting. -/
theorem nonprimitive_odd_sum_primeSquare {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (F : Character (p^2) → ℂ) :
    (∑ χ : Character (p^2) with ¬χ.IsPrimitive ∧ χ.Odd, F χ) =
      ∑ ψ : Character p with ψ.Odd,
        F (DirichletCharacter.changeLevel (dvd_pow_self p (by omega : 2 ≠ 0)) ψ) := by
  classical
  let hd : p ∣ p^2 := dvd_pow_self p (by omega)
  have hfactor (χ : Character (p^2)) : ¬χ.IsPrimitive ↔ χ.FactorsThrough p := by
    simpa using nonprimitive_iff_factorsThrough_previous hp (by omega : 2 ≤ 2) χ
  symm
  apply Finset.sum_bij (fun ψ _ => DirichletCharacter.changeLevel hd ψ)
  · intro ψ hψ
    have hodd := (Finset.mem_filter.mp hψ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(hfactor _).2 (DirichletCharacter.changeLevel_factorsThrough ψ hd),
      (changeLevel_odd_iff hd ψ).2 hodd⟩
  · intro ψ _ ψ' _ heq
    exact DirichletCharacter.changeLevel_injective hd heq
  · intro χ hχ
    have hχ' := (Finset.mem_filter.mp hχ).2
    obtain ⟨hd', ψ, heq⟩ := (hfactor χ).1 hχ'.1
    have hψ : ψ.Odd := (changeLevel_odd_iff hd ψ).1 (by rw [← heq]; exact hχ'.2)
    exact ⟨ψ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψ⟩, heq.symm⟩
  · intro ψ _
    rfl

/-- The complete imprimitive odd twisted contribution, rather than one lift. -/
theorem lifted_odd_primeSquare_twist {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : Odd p) :
    (∑ χ : Character (p^2) with ¬χ.IsPrimitive ∧ χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ) * χ 2) =
      ((p : ℂ)-1)^2 * (p-5) / (24*p) := by
  rw [nonprimitive_odd_sum_primeSquare hp, ← full_odd_prime_twist hp hpodd]
  apply Finset.sum_congr rfl
  intro ψ hψ
  have hodd := (Finset.mem_filter.mp hψ).2
  simp only [generalizedBernoulliOne_inv, ← starRingEnd_apply, Complex.normSq_conj,
    bernoulli_lift_primeSquare hp ψ hodd, lift_character_two hpodd]

noncomputable def squareWeight (q : ℕ) (x : ZMod q) : ℂ :=
  2 * (x.val : ℂ)^2 - q * x.val

private theorem sum_quadratic (n : ℕ) (A B C : ℂ) :
    (∑ k ∈ Finset.range n, (A*(k:ℂ)^2+B*k+C)) =
      A*n*(n-1)*(2*n-1)/6 + B*n*(n-1)/2 + C*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The literal conjugated double sum displayed in the lifting calculation. -/
theorem bernoulli_lift_double_sum {p : ℕ} [NeZero p]
    (hp : p.Prime) (ψ : Character p) (hψ : ψ.Odd) :
    (p : ℂ)⁻¹^2 * (∑ r ∈ Finset.Ico 1 p, ∑ t ∈ Finset.range p,
      ((r : ℂ) + p*t) * star (ψ (r : ZMod p))) =
      (p : ℂ)⁻¹ * ∑ r ∈ Finset.Ico 1 p, (r : ℂ) * star (ψ (r : ZMod p)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hs : (∑ r ∈ Finset.Ico 1 p, star (ψ (r : ZMod p))) = 0 := by
    have hfull : (∑ x : ZMod p, star (ψ x)) = 0 := by
      rw [← sum_prime_units hp _ (by simp [MulChar.map_zero]), ← star_sum, odd_character_unit_sum ψ hψ,
        star_zero]
    have hrange : (∑ r ∈ Finset.range p, star (ψ (r : ZMod p))) = 0 := by
      rw [← sum_zmod_val (fun r => star (ψ (r : ZMod p)))]
      simpa only [ZMod.natCast_zmod_val] using hfull
    rw [← hrange]
    apply Finset.sum_subset
    · intro r hr
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2
    · intro r hr hnot
      have hr' := Finset.mem_range.mp hr
      have hr0 : r = 0 := by
        simp only [Finset.mem_Ico, not_and] at hnot
        omega
      simp [hr0, MulChar.map_zero]
  have hnat : (∑ t ∈ Finset.range p, (t : ℂ)) = (p : ℂ)*(p-1)/2 := by
    simpa using sum_quadratic p 0 1 0
  have hinner (r : ℕ) :
      (∑ t ∈ Finset.range p, ((r : ℂ)+p*t) * star (ψ (r : ZMod p))) =
        ((p : ℂ)*r + (p : ℂ)^2*(p-1)/2) * star (ψ (r : ZMod p)) := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hnat]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  simp_rw [hinner, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, mul_zero,
    add_zero]
  field_simp

theorem squareWeight_sum {q : ℕ} [NeZero q] :
    (∑ x : ZMod q, squareWeight q x) = (q : ℂ)*(q-1)*(q-2)/6 := by
  unfold squareWeight
  rw [sum_zmod_val (fun c => 2 * (c : ℂ)^2 - q*c)]
  have h := sum_quadratic q 2 (-(q : ℂ)) 0
  simp only [add_zero, neg_mul, ← sub_eq_add_neg] at h
  rw [h]
  ring

theorem squareWeight_primeMultiple {p : ℕ} [NeZero p] [NeZero (p^2)]
    (x : ZMod p) :
    squareWeight (p^2) (primeMultiple x) = (p : ℂ)^2 * squareWeight p x := by
  unfold squareWeight
  rw [primeMultiple_val]
  push_cast
  ring

/-- The literal unit power sum in the marginal proof. -/
theorem squareWeight_primeSquare_units {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) :
    (∑ x : UnitClass (p^2), squareWeight (p^2) x.val) =
      (p : ℂ)^2 * (p-1) * ((p : ℂ)^3-2) / 6 := by
  have h := sum_primeSquare_eq_units_add_multiples hp (squareWeight (p^2))
  simp_rw [squareWeight_primeMultiple] at h
  rw [← Finset.mul_sum, squareWeight_sum, squareWeight_sum] at h
  push_cast at h
  linear_combination -h

theorem full_odd_prime_square {p : ℕ} [NeZero p] (hp : p.Prime) :
    (∑ χ : Character p with χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ)) =
      ((p : ℂ)-1)^2 * (p-2) / (12*p) := by
  have h := congrArg (fun t : ℝ => (t : ℂ)) (odd_bernoulli_square (q := p))
  push_cast at h
  rw [h]
  change (p.totient : ℂ) / (2 * (p : ℂ)^2) *
    (∑ x : UnitClass p, squareWeight p x.val) = _
  rw [sum_prime_units hp _ (by simp [squareWeight]), squareWeight_sum,
    Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  push_cast
  field_simp
  ring

theorem full_odd_primeSquare_square {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) :
    (∑ χ : Character (p^2) with χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ)) =
      ((p : ℂ)-1)^2 * ((p : ℂ)^3-2) / (12*p) := by
  have h := congrArg (fun t : ℝ => (t : ℂ))
    (odd_bernoulli_square (q := p^2))
  push_cast at h
  rw [h]
  have hs := squareWeight_primeSquare_units hp
  unfold squareWeight at hs
  push_cast at hs
  rw [hs, Nat.totient_prime_pow hp (by omega : 0 < 2)]
  simp only [Nat.reduceSub, pow_one]
  rw [Nat.cast_mul, Nat.cast_sub hp.one_le]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  push_cast
  field_simp
  ring

theorem lifted_odd_primeSquare_square {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) :
    (∑ χ : Character (p^2) with ¬χ.IsPrimitive ∧ χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ)) =
      ((p : ℂ)-1)^2 * (p-2) / (12*p) := by
  rw [nonprimitive_odd_sum_primeSquare hp, ← full_odd_prime_square hp]
  apply Finset.sum_congr rfl
  intro ψ hψ
  have hodd := (Finset.mem_filter.mp hψ).2
  simp only [generalizedBernoulliOne_inv, ← starRingEnd_apply, Complex.normSq_conj,
    bernoulli_lift_primeSquare hp ψ hodd]

theorem odd_sum_split_primitive {q : ℕ} [NeZero q] (F : Character q → ℂ) :
    (∑ χ : Character q with χ.Odd, F χ) =
      (∑ χ : Character q with χ.IsPrimitive ∧ χ.Odd, F χ) +
      (∑ χ : Character q with ¬χ.IsPrimitive ∧ χ.Odd, F χ) := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hprim : χ.IsPrimitive <;> by_cases hodd : χ.Odd <;>
    simp [hprim, hodd]

/-- The primitive total obtained by the manuscript's full-minus-lifted route. -/
theorem primitive_odd_primeSquare_twist_total {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) (hpodd : Odd p) :
    (∑ χ : Character (p^2) with χ.IsPrimitive ∧ χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ) * χ 2) =
      ((p : ℂ)-1)^3 * (p+1) / 24 := by
  have h := odd_sum_split_primitive
    (fun χ : Character (p^2) => (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ) * χ 2)
  rw [full_odd_primeSquare_twist hp hpodd, lifted_odd_primeSquare_twist hp hpodd] at h
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp at h ⊢
  apply (mul_left_cancel₀ hp0)
  linear_combination -h

theorem primitive_odd_primeSquare_square_total {p : ℕ} [NeZero p] [NeZero (p^2)]
    (hp : p.Prime) :
    (∑ χ : Character (p^2) with χ.IsPrimitive ∧ χ.Odd,
      (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ)) =
      ((p : ℂ)-1)^3 * (p+1) / 12 := by
  have h := odd_sum_split_primitive
    (fun χ : Character (p^2) => (Complex.normSq (generalizedBernoulliOne χ⁻¹) : ℂ))
  rw [full_odd_primeSquare_square hp, lifted_odd_primeSquare_square hp] at h
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp at h ⊢
  apply (mul_left_cancel₀ hp0)
  linear_combination -h

end NField.Alignment.OddBernoulliMoments
