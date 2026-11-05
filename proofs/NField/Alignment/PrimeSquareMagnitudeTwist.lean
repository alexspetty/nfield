/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeBernoulliMoment
import NField.Alignment.MagnitudeDoublingMoment
import NField.Alignment.PrimitiveOddBoundaryCrossMoment

/-!
# The exact twist and variance of prime-square L magnitudes

This closes both complex identities in Proposition 8 and both inequalities
in Corollary 9 for the actual primitive odd family, at primes at least five.
The first character mean follows from the primitive kernel. Balanced
Bernoulli coordinates, both doubling carries and the mixed boundary
criterion give the weighted identity with the full family and its exact
population retained. The existing Bernoulli/L relation identifies the
actual analytic values; finite Cauchy gives their positive variance.

The new correlation deduction no longer assumes that variance. Its uniform
third L-moment bound and vanishing short fractional moment remain explicit
analytic inputs. It does not assert the quantitative logarithmic rate.
-/

set_option autoImplicit false

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareBoundaryFlux

attribute [local instance] Classical.propDecidable

noncomputable def doubleUnit {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    UnitClass (p ^ 2) :=
  firstWindowUnit hp ⟨1, by omega⟩

theorem doubleUnit_val {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (doubleUnit hp hp5).val = (2 : ZMod (p ^ 2)) := by
  simp [doubleUnit, firstWindowUnit, firstWindowNat]

theorem primitive_odd_mean_two {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ χ : PrimitiveOddFamily p, χ.val (2 : ZMod (p ^ 2))) = 0 := by
  classical
  let x := doubleUnit hp hp5
  have hx : x.val = (2 : ZMod (p ^ 2)) := doubleUnit_val hp hp5
  have hprev :
      (previousUnit (p := p) (N := 2) (by omega) x).val =
        (2 : ZMod (p ^ (2-1))) := by
    change ZMod.cast x.val = (2 : ZMod (p ^ (2-1)))
    rw [hx]
    simpa using ZMod.cast_natCast (primePower_previous_dvd (p := p) (by omega : 1 ≤ 2)) 2
  have hlo : previousUnit (p := p) (N := 2) (by omega) x ≠ 1 := by
    intro h
    have hv := congrArg Units.val h
    rw [hprev, Units.val_one] at hv
    have hv' := congrArg ZMod.val hv
    simp only [ZMod.val_ofNat, ZMod.val_one_eq_one_mod, Nat.reduceSub, pow_one] at hv'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv'
    omega
  have hanti : -(previousUnit (p := p) (N := 2) (by omega) x) ≠ 1 := by
    intro h
    have hv := congrArg Units.val h
    rw [Units.val_neg, hprev, Units.val_one] at hv
    have hz : (3 : ZMod (p ^ (2-1))) = 0 := by linear_combination -hv
    have hz' := congrArg ZMod.val hz
    simp only [ZMod.val_ofNat, ZMod.val_zero, Nat.reduceSub, pow_one] at hz'
    rw [Nat.mod_eq_of_lt (by omega)] at hz'
    simp at hz'
  have hhi : x ≠ 1 := by
    intro h
    apply hlo
    rw [h]
    simp [previousUnit]
  have hhianti : -x ≠ 1 := by
    intro h
    apply hanti
    have hh := congrArg (previousUnit (p := p) (N := 2) (by omega)) h
    have hn : previousUnit (p := p) (N := 2) (by omega) (-x) =
        -(previousUnit (p := p) (N := 2) (by omega) x) := by
      apply Units.ext
      change ZMod.cast (-x.val) = -ZMod.cast x.val
      exact ZMod.cast_neg (primePower_previous_dvd (p := p) (by omega : 1 ≤ 2)) _
    rw [hn] at hh
    simpa [previousUnit] using hh
  have h := primitiveOddKernel_eq_primePowerKernel hp (by omega : 2 ≤ 2) x 1
  have hp1 : previousUnit (p := p) (N := 2) (by omega) (1 : UnitClass (p ^ 2)) = 1 := by
    simp [previousUnit]
  rw [hp1, if_neg hhi, if_neg hhianti, if_neg hlo, if_neg hanti] at h
  have hz : primitiveOddKernel x 1 = 0 := by simpa using h
  unfold primitiveOddKernel at hz
  rw [Finset.sum_subtype (p := fun χ : Character (p ^ 2) => χ.IsPrimitive ∧ χ.Odd)
    (F := familyFintype p) _ (by simp)
    (fun χ => χ x.val * star (χ (1 : UnitClass (p ^ 2)).val))] at hz
  simpa [hx] using hz

end NField.Alignment.PrimeSquareMagnitudeFamily

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.AnalyticCollisionTransform
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.NeutralityTheorem

theorem balancedBernoulli_val {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (x : UnitClass (p ^ 2)) :
    balancedBernoulli p x =
      (((x.val.val/p:ℕ):ℂ)-((p:ℂ)-1)/2)/p := by
  let u := squareUnitReduction p x
  let q := (squareFiberEquiv hp u).symm ⟨x,rfl⟩
  have hcoord : squareFiberCoordinate hp u q = x := by
    exact congrArg Subtype.val ((squareFiberEquiv hp u).apply_symm_apply ⟨x,rfl⟩)
  have hv : x.val.val/p = q.val := by
    rw [← hcoord, squareFiberCoordinate_val, Nat.add_mul_div_left _ _ hp.pos,
      Nat.div_eq_of_lt u.val.val_lt, Nat.zero_add]
  have h := balancedBernoulli_coordinate hp u q
  rw [hcoord] at h
  simpa only [hv] using h

theorem balancedBernoulli_double_coordinate {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) (u : UnitClass p) (q : Fin p) :
    balancedBernoulli p (doubleUnit hp hp5 * squareFiberCoordinate hp u q) =
      (((((2*q.val+(2*u.val.val)/p)%p:ℕ):ℂ)-((p:ℂ)-1)/2)/p) := by
  have hz : (doubleUnit hp hp5).val.val = 2 := by
    rw [doubleUnit_val]
    exact ZMod.val_ofNat_of_lt (by nlinarith)
  have hd : (doubleUnit hp hp5 * squareFiberCoordinate hp u q).val.val / p =
      (2*q.val+(2*u.val.val)/p)%p := by
    rw [Units.val_mul, ZMod.val_mul, hz, squareFiberCoordinate_val,
      pow_two, Nat.mod_mul_right_div_self]
    rw [show 2*(u.val.val+p*q.val) = 2*u.val.val+p*(2*q.val) by ring,
      Nat.add_mul_div_left _ _ hp.pos]
    rw [Nat.add_comm]
  rw [balancedBernoulli_val hp, hd]

theorem balancedBernoulli_double_fiber {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) (u : UnitClass p) :
    (∑ q : Fin p,
      balancedBernoulli p (squareFiberCoordinate hp u q) *
        star (balancedBernoulli p (doubleUnit hp hp5 * squareFiberCoordinate hp u q))) =
      ((p:ℂ)^2-1)/(24*p) := by
  have hε : (2*u.val.val)/p ≤ 1 := by
    have hu := u.val.val_lt
    have hh : (2*u.val.val)/p < 2 :=
      (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
    omega
  have h := centered_double_moment (hp.odd_of_ne_two (by omega))
    ((2*u.val.val)/p) hε
  have hc := congrArg (fun t : ℝ => (t:ℂ)) h
  push_cast at hc
  simp_rw [balancedBernoulli_coordinate hp, balancedBernoulli_double_coordinate hp hp5]
  simp only [star_div₀, star_sub, star_natCast, star_ofNat, star_one]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      (((k:ℂ)-((p:ℂ)-1)/2)/p) *
        (((((2*k+(2*u.val.val)/p)%p:ℕ):ℂ)-((p:ℂ)-1)/2)/p)) p]
  exact hc

/-- Exact spatial pairing of the centered Bernoulli signal with its doubled
argument. Every unit and both carry cases are included. -/
theorem balancedBernoulli_double_pairing {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ x : UnitClass (p ^ 2), balancedBernoulli p x *
      star (balancedBernoulli p (doubleUnit hp hp5*x))) =
      ((p:ℂ)-1)*((p:ℂ)^2-1)/(24*p) := by
  classical
  have hf : ∀ u : UnitClass p,
      (∑ x : Fiber (squareUnitReduction p) u,
        balancedBernoulli p x.val *
          star (balancedBernoulli p (doubleUnit hp hp5*x.val))) =
        ((p:ℂ)^2-1)/(24*p) := by
    intro u
    rw [← balancedBernoulli_double_fiber hp hp5 u]
    symm
    apply Fintype.sum_equiv (squareFiberEquiv hp u)
    intro q
    rfl
  rw [← Fintype.sum_fiberwise (squareUnitReduction p)
    (fun x => balancedBernoulli p x * star (balancedBernoulli p (doubleUnit hp hp5*x)))]
  simp_rw [hf]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ZMod.card_units_eq_totient, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le]
  push_cast
  ring

end NField.Alignment.PrimeSquareMagnitudeFamily

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.SpectralRepulsion
open NField.Alignment.MagnitudeMomentArithmetic

theorem bernoulli_twist_total {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ χ : PrimitiveOddFamily p,
      ((‖bernoulliSum p χ‖^2 : ℝ) : ℂ) * χ.val (2 : ZMod (p ^ 2))) =
      ((p:ℂ)-1)^2*((p:ℂ)^2-1)/24 := by
  classical
  have hbalance : ∀ r : UnitClass (p ^ (2-1)),
      (∑ x : UnitClass (p ^ 2) with previousUnit (by omega : 1 ≤ 2) x = r,
        balancedBernoulli p x) = 0 := by
    have hf : ∀ (d : ℕ) (hd : d ∣ p ^ 2), d = p →
        ∀ r : UnitClass d,
          (∑ x : UnitClass (p ^ 2) with ZMod.unitsMap hd x = r,
            balancedBernoulli p x) = 0 := by
      intro d hd heq
      subst d
      exact balancedBernoulli_fiber_zero hp
    exact hf (p ^ (2-1)) (primePower_previous_dvd (by omega : 1 ≤ 2)) (by simp)
  have h := boundary_twist_criterion hp (by omega : 2 ≤ 2)
    (balancedBernoulli p) (doubleUnit hp hp5) hbalance (balancedBernoulli_odd hp)
  rw [balancedBernoulli_double_pairing hp hp5] at h
  rw [Finset.sum_subtype (p := fun χ : Character (p ^ 2) => χ.IsPrimitive ∧ χ.Odd)
    (F := familyFintype p) _ (by simp)
    (fun χ => (Complex.normSq (boundaryFlux (balancedBernoulli p) χ) : ℂ) *
      χ (doubleUnit hp hp5).val)] at h
  have hnorm (χ : PrimitiveOddFamily p) :
      ‖bernoulliSum p χ‖^2 = Complex.normSq (boundaryFlux (balancedBernoulli p) χ.val) := by
    unfold bernoulliSum
    rw [generalizedBernoulliOne_inv, norm_star,
      bernoulli_eq_balanced_flux hp χ.val χ.property.1, Complex.sq_norm]
  simp_rw [hnorm]
  simp only [doubleUnit_val] at h
  rw [h, Nat.totient_prime_pow hp (by omega : 0 < 2)]
  norm_num
  push_cast [Nat.cast_sub hp.one_le]
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp

/-- The complex uniform Bernoulli twist on the full primitive odd family. -/
theorem bernoulli_twist_mean {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Fintype.card (PrimitiveOddFamily p):ℂ)⁻¹ *
      (∑ χ : PrimitiveOddFamily p,
        ((‖bernoulliSum p χ‖^2 : ℝ) : ℂ) * χ.val (2 : ZMod (p ^ 2))) =
      ((p:ℂ)^2-1)/12 := by
  have hpop := congrArg (fun x:ℝ => (x:ℂ))
    (family_population hp (by omega))
  push_cast [Nat.cast_sub hp.one_le] at hpop
  rw [bernoulli_twist_total hp hp5, hpop]
  have hp1 : (p:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  field_simp
  ring

/-- The first complex identity of Proposition 8, including its base restriction. -/
theorem character_two_mean {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Fintype.card (PrimitiveOddFamily p):ℂ)⁻¹ *
      (∑ χ : PrimitiveOddFamily p, χ.val (2 : ZMod (p ^ 2))) = 0 := by
  rw [primitive_odd_mean_two hp hp5, mul_zero]

/-- The second complex identity of Proposition 8 for actual analytic L-values. -/
theorem l_magnitude_twist {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Fintype.card (PrimitiveOddFamily p):ℂ)⁻¹ *
      (∑ χ : PrimitiveOddFamily p,
        ((lMagnitude p χ ^ 2 : ℝ) : ℂ) * χ.val (2 : ZMod (p ^ 2))) =
      (marginalL p : ℂ)/2 := by
  classical
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpoint : ∀ χ : PrimitiveOddFamily p,
      lMagnitude p χ ^ 2 = Real.pi^2 / (p:ℝ)^2 * ‖bernoulliSum p χ‖^2 := by
    intro χ
    have h := bernoulli_l_magnitude_sq hp χ
    unfold lMagnitude
    simp only [Complex.sq_norm]
    push_cast at h
    rw [h]
    field_simp [Real.pi_ne_zero]
  have heq :
      (Fintype.card (PrimitiveOddFamily p):ℂ)⁻¹ *
        (∑ χ : PrimitiveOddFamily p,
          ((lMagnitude p χ ^ 2 : ℝ) : ℂ) * χ.val (2 : ZMod (p ^ 2))) =
      ((Real.pi^2/(p:ℝ)^2 : ℝ) : ℂ) *
        ((Fintype.card (PrimitiveOddFamily p):ℂ)⁻¹ *
          ∑ χ : PrimitiveOddFamily p,
            ((‖bernoulliSum p χ‖^2 : ℝ) : ℂ) * χ.val (2 : ZMod (p ^ 2))) := by
    simp_rw [hpoint, Complex.ofReal_mul, mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [heq, bernoulli_twist_mean hp hp5]
  have hnorm := congrArg (fun t:ℝ => (t:ℂ))
    (twist_to_l_normalization (p:ℝ) hp0)
  push_cast at hnorm
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using hnorm

end NField.Alignment.PrimeSquareMagnitudeFamily

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators Topology
open Filter
open NField.Alignment.SpectralRepulsion
open NField.Alignment.MagnitudeMomentArithmetic
open NField.Alignment.FiniteMagnitudeDecorrelation

private theorem complex_average_re {ι : Type*} [Fintype ι] (F : ι → ℂ) :
    ((Fintype.card ι:ℂ)⁻¹ * ∑ i, F i).re = uniformAverage (fun i => (F i).re) := by
  have hc : (Fintype.card ι:ℂ)⁻¹ = (((Fintype.card ι:ℝ)⁻¹ : ℝ):ℂ) := by
    push_cast
    rfl
  rw [hc]
  simp [uniformAverage, Complex.mul_re]

/-- Exact positive variance for actual L magnitudes, with no twist assumption. -/
theorem l_magnitude_variance_lower {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    marginalL p / 16 ≤ uniformVariance (lMagnitude p) := by
  letI : Nonempty (PrimitiveOddFamily p) := family_nonempty hp (by omega)
  let Z := fun χ : PrimitiveOddFamily p => (χ.val (2 : ZMod (p ^ 2))).re
  have hzero : uniformAverage Z = 0 := by
    have h := congrArg Complex.re (character_two_mean hp hp5)
    rw [complex_average_re] at h
    exact h
  have hbound : ∀ χ : PrimitiveOddFamily p, |Z χ| ≤ 1 := by
    intro χ
    exact (Complex.abs_re_le_norm _).trans (χ.val.norm_le_one _)
  have htwist : uniformAverage (fun χ : PrimitiveOddFamily p =>
      lMagnitude p χ ^ 2 * Z χ) = marginalL p / 2 := by
    have h := congrArg Complex.re (l_magnitude_twist hp hp5)
    rw [complex_average_re] at h
    simpa [Z, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, pow_two] using h
  exact twist_forces_variance (lMagnitude p) Z (marginalL p)
    (marginal_positive (p:ℝ) (by exact_mod_cast hp.one_lt))
    (l_magnitude_second_moment hp (by omega)) hzero hbound htwist

/-- The complete two-stage lower bound stated in Corollary 9. -/
theorem l_magnitude_variance_bounds {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    marginalL p / 16 ≤ uniformVariance (lMagnitude p) ∧
      Real.pi ^ 2 / 100 ≤ marginalL p / 16 := by
  exact ⟨l_magnitude_variance_lower hp hp5,
    variance_constant (p:ℝ) (by exact_mod_cast hp5)⟩

theorem l_magnitude_variance_floor {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.pi ^ 2 / 100 ≤ uniformVariance (lMagnitude p) := by
  obtain ⟨hlower, hconstant⟩ := l_magnitude_variance_bounds hp hp5
  exact hconstant.trans hlower

/-- The concrete family limit now requires only the two remaining analytic
inputs. Its finite moments and positive variance are proved, not assumed.
The quantitative logarithmic rate is not asserted here. -/
theorem correlation_limit_from_final_analytic_inputs
    {α : Type*} {l : Filter α} (base : α → ℕ)
    [∀ a, NeZero (base a ^ 2)]
    (hprime : ∀ a, (base a).Prime) (hbase : ∀ a, 5 ≤ base a)
    (M : ℝ)
    (hthird : ∀ a, magnitudeMoment 3 (lMagnitude (base a)) ≤ M)
    (hHarper : Tendsto
      (fun a => magnitudeMoment (3/2) (shortMagnitude (base a))) l (𝓝 0)) :
    Tendsto (fun a => familyCorrelation (base a)) l (𝓝 0) := by
  letI : ∀ a, NeZero (base a) := fun a => ⟨(hprime a).ne_zero⟩
  apply correlation_limit_from_analytic_inputs base hprime
    (fun a => by have := hbase a; omega) M (Real.pi^2/100) (by positivity) hthird
  · intro a
    exact l_magnitude_variance_floor (hprime a) (hbase a)
  · exact hHarper

end NField.Alignment.PrimeSquareMagnitudeFamily
