/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnitOrderGap
import NField.Alignment.CyclicShiftCounts
import NField.Golden.WeightedRepetendRigidity

/-!
# Rational rigidity of periodic reference tails

The orbit interpolant uses the actual base order when applied to a coprime
base and modulus. Fibonacci coordinates force every larger even exponent into
the forbidden unit-order interval. Odd exponents have a positive rational
coordinate. Only the two period-one square endpoints remain.

The existing one-digit and digit-tail definitions are unchanged. The literal
cyclic-shift finite score agrees with this interpolant, and retains the
scale-one exception and exact finite-replication/rationality boundary.
This module proves Theorem 12 and its finite-score links; cumulative closure
and the final closure corollary are not asserted here. The earlier real-weight
classification still concerns the one-digit profile alone.
-/

namespace NField.Golden

open NField.Alignment

/-- The real continuation of the cyclic-shift score, with a period parameter. -/
noncomputable def orbitReferenceInterpolant (q h : ℕ) (lambda x : ℝ) : ℝ :=
  (((h : ℝ) + lambda) * x - lambda) / ((q : ℝ) * x - 1)

theorem orbitReferenceInterpolant_one (q : ℕ) (lambda x : ℝ) :
    orbitReferenceInterpolant q 1 lambda x = weightedReferenceInterpolant q lambda x := by
  unfold orbitReferenceInterpolant weightedReferenceInterpolant
  push_cast
  ring

/-- The exact golden-power equation for an orbit of length h. -/
noncomputable def orbitGoldenPowerEquation (q h r : ℕ) (lambda : ℝ) : ℝ :=
  goldenReciprocal ^ (r + 1) - lambda * goldenReciprocal ^ r -
    (q : ℝ) * goldenReciprocal + lambda + h

/-- At an admissible reciprocal golden power, clearing the positive denominator
gives the exact orbit power equation. -/
theorem orbitWeightedInterpolant_goldenPower_iff {q h r : ℕ} {lambda : ℝ}
    (hq : 2 ≤ q) (hr : 1 ≤ r) :
    orbitReferenceInterpolant q h lambda
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      orbitGoldenPowerEquation q h r lambda = 0 := by
  have htau := goldenReciprocal_unit_interval
  have hpowpos : 0 < goldenReciprocal ^ r := pow_pos htau.1 r
  have hpowlt : goldenReciprocal ^ r < 1 :=
    pow_lt_one₀ htau.1.le htau.2 (by omega)
  have hinv : 1 < (goldenReciprocal ^ r)⁻¹ := (one_lt_inv₀ hpowpos).2 hpowlt
  have hden : (q : ℝ) * (goldenReciprocal ^ r)⁻¹ - 1 ≠ 0 := by
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hpowne : goldenReciprocal ^ r ≠ 0 := ne_of_gt hpowpos
  unfold orbitReferenceInterpolant orbitGoldenPowerEquation
  rw [div_eq_iff hden]
  constructor
  · intro heq
    have hscaled := congrArg (fun z : ℝ => z * goldenReciprocal ^ r) heq
    field_simp [hpowne] at hscaled
    rw [pow_succ]
    nlinarith
  · intro heq
    have hcross : lambda + h - lambda * goldenReciprocal ^ r =
        goldenReciprocal * ((q : ℝ) - goldenReciprocal ^ r) := by
      rw [pow_succ] at heq
      nlinarith
    field_simp [hpowne]
    nlinarith

/-- The two rational Fibonacci coordinates of the orbit power equation. -/
theorem orbitGoldenPowerEquation_coordinates {q h r : ℕ} {lambda : ℚ}
    (hr : 1 ≤ r) :
    orbitGoldenPowerEquation q h r (lambda : ℝ) = 0 ↔
      rationalGoldenCoefficientA q r lambda = 0 ∧
      rationalGoldenCoefficientB r lambda + (h : ℚ) - 1 = 0 := by
  have heq : orbitGoldenPowerEquation q h r (lambda : ℝ) =
      (rationalGoldenCoefficientA q r lambda : ℝ) * goldenReciprocal +
        ((rationalGoldenCoefficientB r lambda + (h : ℚ) - 1 : ℚ) : ℝ) := by
    have hcoords := goldenPowerEquation_rational_coordinates (q := q) (lambda := lambda) hr
    unfold orbitGoldenPowerEquation goldenPowerEquation at *
    push_cast
    linarith
  rw [heq]
  constructor
  · exact goldenReciprocal_rational_coordinates
  · rintro ⟨hA, hB⟩
    rw [hA, hB]
    norm_num

theorem orbit_even_coordinates {q h r : ℕ} {lambda : ℚ}
    (heven : Even r)
    (hA : rationalGoldenCoefficientA q r lambda = 0)
    (hB : rationalGoldenCoefficientB r lambda + (h : ℚ) - 1 = 0) :
    (q : ℚ) = Nat.fib (r + 1) + lambda * Nat.fib r ∧
    (h : ℚ) = Nat.fib r + lambda * ((Nat.fib (r - 1) : ℚ) - 1) := by
  unfold rationalGoldenCoefficientA at hA
  unfold rationalGoldenCoefficientB at hB
  rw [heven.neg_one_pow, one_mul] at hA
  rw [heven.add_one.neg_one_pow, neg_one_mul] at hB
  constructor <;> linarith

/-- Every coordinate solution at exponent at least four forces the forbidden
unit-order interval. Both ends are exact rational inequalities. -/
theorem orbit_large_coordinates_force_gap {q h r : ℕ} {lambda : ℚ}
    (hr : 4 ≤ r) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (hA : (q : ℚ) = Nat.fib (r + 1) + lambda * Nat.fib r)
    (hB : (h : ℚ) = Nat.fib r + lambda * ((Nat.fib (r - 1) : ℚ) - 1)) :
    5 ≤ q ∧ q ≤ 2 * h ∧ 3 * h < 2 * q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hn1 : 1 ≤ Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have hf2 := Nat.fib_add_two (n := n)
  have hf3 := Nat.fib_add_two (n := n + 1)
  have hf4 := Nat.fib_add_two (n := n + 2)
  have hf5 := Nat.fib_add_two (n := n + 3)
  norm_num only [Nat.add_assoc] at hf2 hf3 hf4 hf5
  have heq3 : Nat.fib (4 + n - 1) = Nat.fib n + 2 * Nat.fib (n + 1) := by
    rw [show 4 + n - 1 = n + 3 by omega]
    omega
  have heq4 : Nat.fib (4 + n) = 2 * Nat.fib n + 3 * Nat.fib (n + 1) := by
    rw [show 4 + n = n + 4 by omega]
    omega
  have heq5 : Nat.fib (4 + n + 1) = 3 * Nat.fib n + 5 * Nat.fib (n + 1) := by
    rw [show 4 + n + 1 = n + 5 by omega]
    omega
  rw [heq4, heq5] at hA
  rw [heq3, heq4] at hB
  push_cast at hA hB
  have ha : (0 : ℚ) ≤ Nat.fib n := by positivity
  have hb : (1 : ℚ) ≤ Nat.fib (n + 1) := by exact_mod_cast hn1
  have hla := mul_nonneg hl0 ha
  have hlb := mul_nonneg hl0 (show (0 : ℚ) ≤ Nat.fib (n + 1) by linarith)
  have hlbm := mul_nonneg hl0 (show (0 : ℚ) ≤ (Nat.fib (n + 1) : ℚ) - 1 by linarith)
  have hq5 : (5 : ℚ) ≤ q := by nlinarith
  have hlo : (q : ℚ) ≤ 2 * h := by nlinarith
  have hhi : 3 * (h : ℚ) < 2 * q := by nlinarith
  exact ⟨by exact_mod_cast hq5, by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem orbitPowerEquation_rational_classification {q h r : ℕ} {lambda : ℚ}
    (hq : 2 ≤ q) (hh : 1 ≤ h) (hr : 1 ≤ r)
    (hgap : 5 ≤ q → ¬ (q ≤ 2 * h ∧ 3 * h < 2 * q))
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    orbitGoldenPowerEquation q h r (lambda : ℝ) = 0 ↔
      h = 1 ∧ ((q = 2 ∧ lambda = 0 ∧ r = 2) ∨
        (q = 3 ∧ lambda = 1 ∧ r = 2)) := by
  constructor
  · intro heq
    obtain ⟨hA, hB⟩ := (orbitGoldenPowerEquation_coordinates hr).mp heq
    rcases Nat.even_or_odd r with heven | hodd
    · obtain ⟨hqF, hhF⟩ := orbit_even_coordinates heven hA hB
      by_cases hr2 : r = 2
      · subst r
        norm_num at hqF hhF
        have hh1 : h = 1 := by exact_mod_cast hhF
        refine ⟨hh1, ?_⟩
        have hq3 : q ≤ 3 := by
          have : (q : ℚ) ≤ 3 := by linarith
          exact_mod_cast this
        interval_cases q
        · left
          refine ⟨rfl, ?_, rfl⟩
          norm_num at hqF
          linarith
        · right
          refine ⟨rfl, ?_, rfl⟩
          norm_num at hqF
          linarith
      · have hr4 : 4 ≤ r := by
          obtain ⟨k, hk⟩ := heven
          omega
        have hforced := orbit_large_coordinates_force_gap hr4 hl0 hl1 hqF hhF
        exact (hgap hforced.1 hforced.2).elim
    · have hpos := rationalGoldenCoefficientB_pos_of_odd hr hodd hl0
      have hhQ : (1 : ℚ) ≤ h := by exact_mod_cast hh
      nlinarith
  · rintro ⟨rfl, (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)⟩
    · norm_num [orbitGoldenPowerEquation]
      nlinarith [goldenReciprocal_quadratic_weighted]
    · norm_num [orbitGoldenPowerEquation]
      nlinarith [goldenReciprocal_quadratic_weighted]

theorem coprimeBasePeriod_eq_one_iff {b q : ℕ} (hq : 1 < q)
    (hcop : Nat.Coprime q b) :
    coprimeBasePeriod b q hcop = 1 ↔ b % q = 1 := by
  rw [coprimeBasePeriod, orderOf_eq_one_iff]
  constructor
  · intro heq
    have hc := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) heq
    have hcast : (b : ZMod q) = ((1 : ℕ) : ZMod q) := by
      simpa [ZMod.coe_unitOfCoprime] using hc
    simpa [Nat.mod_eq_of_lt hq] using (ZMod.natCast_eq_natCast_iff' b 1 q).mp hcast
  · intro heq
    apply Units.ext
    have hcast := (ZMod.natCast_eq_natCast_iff' b 1 q).mpr
      (heq.trans (Nat.mod_eq_of_lt hq).symm)
    simpa [ZMod.coe_unitOfCoprime] using hcast

/-- For arbitrary coprime integer bases and rational weights in the unit interval,
the golden-power equality forces period one and exactly the two square endpoints.
The period is the actual modular order, not a freely chosen parameter. -/
theorem orbit_rational_period_rigidity {b q r : ℕ} {lambda : ℚ}
    (_hb : 2 ≤ b) (hq : 2 ≤ q) (hr : 1 ≤ r) (hcop : Nat.Coprime q b)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    orbitReferenceInterpolant q (coprimeBasePeriod b q hcop) (lambda : ℝ)
        ((goldenReciprocal ^ r)⁻¹) = goldenReciprocal ↔
      b % q = 1 ∧ ((q = 2 ∧ lambda = 0 ∧ r = 2) ∨
        (q = 3 ∧ lambda = 1 ∧ r = 2)) := by
  have hh : 1 ≤ coprimeBasePeriod b q hcop := coprimeBasePeriod_pos hcop
  have hgap : 5 ≤ q → ¬ (q ≤ 2 * coprimeBasePeriod b q hcop ∧
      3 * coprimeBasePeriod b q hcop < 2 * q) := by
    intro hq5
    exact unit_order_gap hq5 (ZMod.unitOfCoprime b hcop.symm)
  rw [orbitWeightedInterpolant_goldenPower_iff hq hr,
    orbitPowerEquation_rational_classification hq hh hr hgap hl0 hl1,
    coprimeBasePeriod_eq_one_iff (by omega)]

/-- The interpolant agrees with the weighted average of the literal cyclic-shift
and terminating rows at every admissible positive integer scale. -/
theorem cyclicShiftScore_eq_orbitInterpolant {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) (lambda : ℝ) :
    cyclicShiftScore b q m D lambda =
      orbitReferenceInterpolant q (coprimeBasePeriod b q hcop) lambda (m : ℝ) := by
  rw [cyclicShiftScore_eq hb hq hm hcop hD, orbitReferenceInterpolant]
  have hqm : 1 ≤ q * m := Nat.mul_pos (by omega) hm
  rw [Nat.cast_sub hqm, Nat.cast_sub (show 1 ≤ m by omega)]
  push_cast
  ring

theorem cyclicShiftScore_one {b q D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hcop : Nat.Coprime q b) (lambda : ℝ) :
    cyclicShiftScore b q 1 D lambda =
      (coprimeBasePeriod b q hcop : ℝ) / (q - 1 : ℕ) := by
  simp [cyclicShiftScore_eq hb hq (by omega : 0 < 1) hcop (one_dvd _) lambda]

theorem cyclicShiftScore_injective {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 1 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) : Function.Injective (cyclicShiftScore b q m D) := by
  have hqm : 4 ≤ q * m := Nat.mul_le_mul hq hm
  have hrowsR : ((q * m - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show q * m - 1 ≠ 0 by omega)
  have htermR : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show m - 1 ≠ 0 by omega)
  intro lambda mu heq
  rw [cyclicShiftScore_eq hb hq (by omega) hcop hD,
    cyclicShiftScore_eq hb hq (by omega) hcop hD] at heq
  have hnum := congrArg (fun x : ℝ => x * ((q * m - 1 : ℕ) : ℝ)) heq
  simp only [div_mul_cancel₀ _ hrowsR] at hnum
  exact mul_right_cancel₀ htermR (add_left_cancel hnum)

theorem cyclicShiftScore_irrational_iff {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 1 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) (lambda : ℝ) :
    Irrational (cyclicShiftScore b q m D lambda) ↔ Irrational lambda := by
  rw [cyclicShiftScore_eq hb hq (by omega) hcop hD, ← Nat.cast_mul]
  have hqm : 4 ≤ q * m := Nat.mul_le_mul hq hm
  have hrows : q * m - 1 ≠ 0 := by omega
  have hterm : m - 1 ≠ 0 := by omega
  rw [irrational_div_natCast_iff, irrational_natCast_add_iff,
    irrational_mul_natCast_iff]
  norm_cast
  simp [hrows, hterm]

theorem cyclicShiftScore_finiteReplication {b q m D a d : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) (hd : 0 < d) :
    ((d * (cyclicShiftNumerators b q m D).card +
        a * (terminatingAtDepthNumerators b q m D).card : ℕ) : ℝ) /
      ((d * (q * m - 1) : ℕ) : ℝ) =
        cyclicShiftScore b q m D ((a : ℝ) / (d : ℝ)) := by
  rw [cyclicShiftNumerators_card hb hq hm hcop hD,
    terminatingAtDepthNumerators_card (by omega) hm hcop hD,
    cyclicShiftScore_eq hb hq hm hcop hD]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The orbit score is weight-independent at scale one, identifies its weight
above scale one, is irrational exactly when that weight is irrational, and
agrees with the stated finite replicated-row proportion for rational weights. -/
theorem cyclic_shift_finite_weight_interpretation {b q m D : ℕ}
    (hb : 2 ≤ b) (hq : 1 < q) (hm : 0 < m) (hcop : Nat.Coprime q b)
    (hD : m ∣ b ^ D) :
    (m = 1 → ∀ lambda : ℝ, cyclicShiftScore b q m D lambda =
      (coprimeBasePeriod b q hcop : ℝ) / (q - 1 : ℕ)) ∧
    (1 < m → Function.Injective (cyclicShiftScore b q m D) ∧
      ∀ lambda : ℝ, Irrational (cyclicShiftScore b q m D lambda) ↔ Irrational lambda) ∧
    (∀ a d : ℕ, 0 < d →
      ((d * (cyclicShiftNumerators b q m D).card +
          a * (terminatingAtDepthNumerators b q m D).card : ℕ) : ℝ) /
        ((d * (q * m - 1) : ℕ) : ℝ) =
          cyclicShiftScore b q m D ((a : ℝ) / (d : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    subst m
    exact cyclicShiftScore_one hb hq hcop
  · intro hm1
    exact ⟨cyclicShiftScore_injective hb hq hm1 hcop hD,
      cyclicShiftScore_irrational_iff hb hq hm1 hcop hD⟩
  · intro a d hd
    exact cyclicShiftScore_finiteReplication hb hq hm hcop hD hd


end NField.Golden
