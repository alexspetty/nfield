/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareMagnitudeShortMoment
import NField.Alignment.MagnitudeMomentArithmetic

/-!
# The Bernoulli and L-value marginals for prime-square magnitudes

The native prime-square fiber coordinates identify the balanced Bernoulli
signal exactly. A primitive character annihilates every coarse pullback,
so fiber centering preserves the literal Bernoulli transform. Reflection,
the finite square mass and the existing primitive-odd boundary criterion
give its exact second moment. Conjugation agrees with bernoulliSum, and the
proved Bernoulli-to-L identity gives the actual L-value marginal.

Together with PrimeSquareMagnitudeShortMoment, this closes Proposition 3
for every odd prime, including the manuscript's domain of bases at least
five. The twisted and mixed moments, uniform third-moment estimate, positive
variance, Harper transfer and quantitative correlation rate remain separate.
-/

set_option autoImplicit false

namespace NField.Alignment.PrimeSquareMagnitudeFamily

open scoped BigOperators ComplexConjugate ZMod Topology
open Filter
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PrimitiveOddBoundaryMean
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionTransform
open NField.Alignment.AnalyticCollisionTransform
open NField.Alignment.NeutralityTheorem
open NField.Alignment.PrimeCarryFiberCentering
open NField.Alignment.CollisionSpectrumLandscape
open NField.Alignment.SpectralRepulsion
open NField.Alignment.FiniteMagnitudeDecorrelation

attribute [local instance] Classical.propDecidable

local instance {p : ℕ} [NeZero (p ^ 2)] : NeZero (allLagModulus p 1) := by
  simpa [allLagModulus] using (inferInstance : NeZero (p ^ 2))

/-- The native lag-one reduction with an explicit prime-square domain. -/
noncomputable def squareUnitReduction (p : ℕ) [NeZero p] [NeZero (p ^ 2)] :
    UnitClass (p ^ 2) → UnitClass p := coarseUnitReduction p 1

noncomputable def squareFiberCoordinate {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (u : UnitClass p) (q : Fin p) : UnitClass (p ^ 2) :=
  primeFiberCoordinate hp u q

noncomputable def squareFiberEquiv {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (u : UnitClass p) : Fin p ≃ Fiber (squareUnitReduction p) u :=
  primeFiberEquiv hp u

theorem squareFiberCoordinate_val {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (u : UnitClass p) (q : Fin p) :
    (squareFiberCoordinate hp u q).val.val = u.val.val + p*q.val :=
  primeFiberCoordinate_val hp u q

theorem squareUnitReduction_coordinate {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (u : UnitClass p) (q : Fin p) :
    squareUnitReduction p (squareFiberCoordinate hp u q) = u :=
  coarseUnitReduction_primeFiberCoordinate hp u q

/-- Every primitive character annihilates a signal pulled back from the
coarse unit group. No parity restriction is needed for this identification. -/
theorem primitive_coarse_pullback_zero {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (χ : Character (p ^ 2)) (hχ : χ.IsPrimitive)
    (f : UnitClass p → ℂ) :
    (∑ x : UnitClass (p ^ 2), f (squareUnitReduction p x) * χ x.val) = 0 := by
  classical
  let hd : p ∣ p ^ 2 := dvd_pow_self p (by omega)
  have hnot : ¬ χ.FactorsThrough p := by
    intro h
    exact ((nonprimitive_iff_factorsThrough_previous hp (by omega : 2 ≤ 2) χ).2
      (by simpa using h)) hχ
  have hk : ¬ (ZMod.unitsMap hd).ker ≤ χ.toUnitHom.ker :=
    fun h => hnot ((DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).2 h)
  change ¬ ∀ z, z ∈ (ZMod.unitsMap hd).ker → z ∈ χ.toUnitHom.ker at hk
  push Not at hk
  obtain ⟨z, hz, hzχ⟩ := hk
  have hzmap : ZMod.unitsMap hd z = 1 := hz
  have hzne : χ z.val ≠ 1 := by
    intro h
    apply hzχ
    change χ.toUnitHom z = 1
    apply Units.ext
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using h
  let S := ∑ x : UnitClass (p ^ 2), f (squareUnitReduction p x) * χ x.val
  have hscale : S = χ z.val * S := by
    calc
      S = ∑ x : UnitClass (p ^ 2),
          f (squareUnitReduction p (z * x)) * χ (z * x).val := by
        exact (Equiv.sum_comp (Equiv.mulLeft z)
          (fun x => f (squareUnitReduction p x) * χ x.val)).symm
      _ = χ z.val * S := by
        unfold S
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        have hr : squareUnitReduction p (z * x) = squareUnitReduction p x := by
          change ZMod.unitsMap hd (z * x) = ZMod.unitsMap hd x
          rw [map_mul, hzmap, one_mul]
        rw [hr, Units.val_mul, map_mul]
        ring
  have hh : (χ z.val - 1) * S = 0 := by linear_combination -hscale
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hzne)

noncomputable def bernoulliInput (p : ℕ) [NeZero (p ^ 2)]
    (x : UnitClass (p ^ 2)) : ℂ := (x.val.val : ℂ) / (p : ℂ)^2 - 1

noncomputable def balancedBernoulli (p : ℕ) [NeZero p] [NeZero (p ^ 2)]
    (x : UnitClass (p ^ 2)) : ℂ :=
  centeredSignal (squareUnitReduction p) (bernoulliInput p) x

theorem bernoulliInput_reflection {p : ℕ} [NeZero (p ^ 2)]
    (hp : p.Prime) (x : UnitClass (p ^ 2)) :
    bernoulliInput p x + bernoulliInput p (-x) = -1 := by
  letI : Fact (1 < p ^ 2) := ⟨by nlinarith [hp.two_le]⟩
  have hx : x.val ≠ 0 := Units.ne_zero x
  have hle : x.val.val ≤ p ^ 2 := Nat.le_of_lt x.val.val_lt
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold bernoulliInput
  rw [Units.val_neg, ZMod.neg_val, if_neg hx, Nat.cast_sub hle]
  push_cast
  field_simp
  ring

theorem balancedBernoulli_odd {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (x : UnitClass (p ^ 2)) :
    balancedBernoulli p (-x) = -balancedBernoulli p x := by
  apply centeredSignal_reflection_odd (squareUnitReduction p)
    (bernoulliInput p) Neg.neg Neg.neg neg_neg neg_neg
  · intro a
    apply Units.ext
    change ZMod.cast (-a.val) = -ZMod.cast a.val
    exact ZMod.cast_neg (show p ∣ p ^ 2 from dvd_pow_self p (by omega)) _
  · exact bernoulliInput_reflection hp
  · exact ZMod.unitsMap_surjective _

/-- Exact correspondence with the literal generalized Bernoulli sum. The
discarded fiber mean and constant have zero primitive transform. -/
theorem bernoulli_eq_balanced_flux {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (χ : Character (p ^ 2)) (hχ : χ.IsPrimitive) :
    generalizedBernoulliOne χ = boundaryFlux (balancedBernoulli p) χ := by
  have hz := primitive_coarse_pullback_zero hp χ hχ
    (fun u => 1 + fiberMean (squareUnitReduction p) (bernoulliInput p) u)
  unfold generalizedBernoulliOne boundaryFlux balancedBernoulli centeredSignal
  push_cast
  rw [Finset.mul_sum]
  have heq :
      (∑ x : UnitClass (p ^ 2),
        (((x.val.val : ℂ) / (p : ℂ)^2 - 1) -
          fiberMean (squareUnitReduction p) (bernoulliInput p)
            (squareUnitReduction p x)) * χ x.val) =
      (∑ x : UnitClass (p ^ 2), ((p : ℂ)^2)⁻¹ * ((x.val.val : ℂ) * χ x.val)) -
        ∑ x : UnitClass (p ^ 2),
          (1 + fiberMean (squareUnitReduction p) (bernoulliInput p)
            (squareUnitReduction p x)) * χ x.val := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  change _ = ∑ x : UnitClass (p ^ 2),
    (((x.val.val : ℂ) / (p : ℂ)^2 - 1) -
      fiberMean (squareUnitReduction p) (bernoulliInput p)
        (squareUnitReduction p x)) * χ x.val
  rw [heq, hz, sub_zero]

private theorem sum_range_cast (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : K)) = (n : K) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_sq_real (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ)^2) = (n : ℝ) * (n - 1) * (2*n-1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem bernoulli_fiber_mean {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (u : UnitClass p) :
    fiberMean (squareUnitReduction p) (bernoulliInput p) u =
      (u.val.val : ℂ) / (p : ℂ)^2 + ((p : ℂ)-1)/(2*p) - 1 := by
  classical
  have hc : Fintype.card (Fiber (squareUnitReduction p) u) = p := by
    simpa using Fintype.card_congr (squareFiberEquiv hp u).symm
  have hs : (∑ q : Fin p, (q.val : ℂ)) = (p : ℂ) * (p-1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun q : ℕ => (q : ℂ)) p]
    exact sum_range_cast ℂ p
  have hreindex : (∑ x : Fiber (squareUnitReduction p) u, bernoulliInput p x.val) =
      ∑ q : Fin p, ((u.val.val : ℂ) / (p : ℂ)^2 - 1 + (q.val : ℂ) / p) := by
    symm
    apply Fintype.sum_equiv (squareFiberEquiv hp u)
    intro q
    change _ = bernoulliInput p (squareFiberCoordinate hp u q)
    unfold bernoulliInput
    rw [squareFiberCoordinate_val]
    push_cast
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp
    ring
  unfold fiberMean
  rw [hc, hreindex, Finset.sum_add_distrib, ← Finset.sum_div, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem balancedBernoulli_coordinate {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (u : UnitClass p) (q : Fin p) :
    balancedBernoulli p (squareFiberCoordinate hp u q) =
      ((q.val : ℂ) - ((p : ℂ)-1)/2) / p := by
  unfold balancedBernoulli centeredSignal
  rw [squareUnitReduction_coordinate, bernoulli_fiber_mean hp]
  unfold bernoulliInput
  rw [squareFiberCoordinate_val]
  push_cast
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem balancedBernoulli_fiber_zero {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (u : UnitClass p) :
    (∑ x : UnitClass (p ^ 2) with squareUnitReduction p x = u,
      balancedBernoulli p x) = 0 := by
  classical
  rw [Finset.sum_subtype (p := fun x : UnitClass (p ^ 2) =>
    squareUnitReduction p x = u) _ (by simp) (balancedBernoulli p)]
  exact centeredSignal_fiber_sum_zero (squareUnitReduction p) (bernoulliInput p) u
    ⟨⟨squareFiberCoordinate hp u ⟨0, hp.pos⟩,
      squareUnitReduction_coordinate hp u ⟨0, hp.pos⟩⟩⟩

private theorem centered_digit_square_sum {p : ℕ} (hp : 0 < p) :
    (∑ q : Fin p, (((q.val : ℝ)-((p : ℝ)-1)/2)/p)^2) =
      ((p : ℝ)^2-1)/(12*p) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => (((q : ℝ)-((p : ℝ)-1)/2)/p)^2) p]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have heq : ∀ q : ℕ,
      (((q : ℝ)-((p : ℝ)-1)/2)/p)^2 =
      ((q : ℝ)^2 - ((p : ℝ)-1)*q + ((p : ℝ)-1)^2/4)/p^2 := by
    intro q
    ring
  simp_rw [heq]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_range_cast, sum_range_sq_real]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- Exact square mass of the balanced Bernoulli signal on every unit. -/
theorem balancedBernoulli_square_mass {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) :
    (∑ x : UnitClass (p ^ 2), ‖balancedBernoulli p x‖^2) =
      ((p : ℝ)-1)*((p : ℝ)^2-1)/(12*p) := by
  classical
  have hf : ∀ u : UnitClass p,
      (∑ x : Fiber (squareUnitReduction p) u, ‖balancedBernoulli p x.val‖^2) =
      ((p : ℝ)^2-1)/(12*p) := by
    intro u
    rw [← centered_digit_square_sum hp.pos]
    symm
    apply Fintype.sum_equiv (squareFiberEquiv hp u)
    intro q
    change _ = ‖balancedBernoulli p (squareFiberCoordinate hp u q)‖^2
    rw [balancedBernoulli_coordinate hp]
    have hcast : ((q.val : ℂ)-((p : ℂ)-1)/2)/p =
        ((((q.val : ℝ)-((p : ℝ)-1)/2)/p : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Fintype.sum_fiberwise (squareUnitReduction p)
    (fun x => ‖balancedBernoulli p x‖^2)]
  simp_rw [hf]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ZMod.card_units_eq_totient, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le]
  push_cast
  ring

theorem generalizedBernoulliOne_inv {q : ℕ} [NeZero q] (χ : Character q) :
    generalizedBernoulliOne χ⁻¹ = star (generalizedBernoulliOne χ) := by
  unfold generalizedBernoulliOne
  simp only [← MulChar.star_eq_inv, MulChar.star_apply, star_mul, star_sum,
    star_natCast, star_inv₀]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The exact Bernoulli square mean for the complete primitive odd sample. -/
theorem bernoulli_magnitude_second_moment {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily p => ‖bernoulliSum p χ‖^2) =
      ((p : ℝ)^2-1)/6 := by
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
  have hm := boundaryMeanCriterion_average hp hpodd (by omega : 2 ≤ 2)
    (balancedBernoulli p) hbalance (balancedBernoulli_odd hp)
  have heq : primitiveOddBoundaryMomentReal (balancedBernoulli p) =
      ∑ χ : PrimitiveOddFamily p, ‖bernoulliSum p χ‖^2 := by
    unfold primitiveOddBoundaryMomentReal
    rw [Finset.sum_subtype (p := fun χ : Character (p ^ 2) => χ.IsPrimitive ∧ χ.Odd)
      (F := familyFintype p) _ (by simp)
      (fun χ => ‖boundaryFlux (balancedBernoulli p) χ‖^2)]
    apply Finset.sum_congr rfl
    intro χ _
    rw [← bernoulli_eq_balanced_flux hp χ.val χ.property.1]
    unfold bernoulliSum
    rw [generalizedBernoulliOne_inv, norm_star]
  rw [heq, balancedBernoulli_square_mass hp] at hm
  unfold uniformAverage
  rw [family_card_eq_count, ← div_eq_inv_mul, hm]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  field_simp
  ring

/-- The second marginal identity in the manuscript uses the actual analytic
L-value, with no moment estimate supplied as a hypothesis. -/
theorem l_magnitude_second_moment {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    uniformAverage (fun χ : PrimitiveOddFamily p => lMagnitude p χ ^ 2) =
      Real.pi^2 / 6 * (1 - 1/(p : ℝ)^2) := by
  classical
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpoint : ∀ χ : PrimitiveOddFamily p,
      lMagnitude p χ ^ 2 = Real.pi^2 / (p : ℝ)^2 * ‖bernoulliSum p χ‖^2 := by
    intro χ
    have h := bernoulli_l_magnitude_sq hp χ
    unfold lMagnitude
    simp only [Complex.sq_norm]
    push_cast at h
    rw [h]
    field_simp [Real.pi_ne_zero]
  have hm := bernoulli_magnitude_second_moment hp hpodd
  unfold uniformAverage at hm ⊢
  simp_rw [hpoint]
  rw [← Finset.mul_sum, ← mul_assoc,
    mul_comm (Fintype.card (PrimitiveOddFamily p) : ℝ)⁻¹, mul_assoc, hm]
  field_simp

/-- Both marginal second moments and population nonemptiness are now proved.
The uniform third moment, positive variance and vanishing short fractional
moment remain explicit inputs. This is not a logarithmic-rate theorem. -/
theorem correlation_limit_from_analytic_inputs
    {α : Type*} {l : Filter α} (base : α → ℕ)
    [∀ a, NeZero (base a ^ 2)]
    (hprime : ∀ a, (base a).Prime) (hodd : ∀ a, base a ≠ 2)
    (M v : ℝ) (hv : 0 < v)
    (hthird : ∀ a, magnitudeMoment 3 (lMagnitude (base a)) ≤ M)
    (hvariance : ∀ a, v ≤ uniformVariance (lMagnitude (base a)))
    (hHarper : Tendsto
      (fun a => magnitudeMoment (3/2) (shortMagnitude (base a))) l (𝓝 0)) :
    Tendsto (fun a => familyCorrelation (base a)) l (𝓝 0) := by
  letI : ∀ a, NeZero (base a) := fun a => ⟨(hprime a).ne_zero⟩
  apply correlation_limit_from_remaining_inputs base hprime hodd (Real.pi^2/6) M v hv
  · intro a
    rw [l_magnitude_second_moment (hprime a) (hodd a)]
    exact MagnitudeMomentArithmetic.marginal_upper (base a)
  · exact hthird
  · exact hvariance
  · exact hHarper

end NField.Alignment.PrimeSquareMagnitudeFamily
