/-
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarryTableColumnLaw

/-!
# Collision to Bernoulli straightening

The lag-one response is kept on all residues modulo `p^2`.  This proves the
floor-to-fractional identity and the exact change of variables by `1-p`
without restricting to the unit group.
-/

namespace NField.Alignment.CollisionBernoulliStraightening

open scoped BigOperators ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.PrimeCarryTableColumnLaw

/-- The fractional part represented by the canonical residue. -/
noncomputable def residueFraction {M : ℕ} [NeZero M] (x : ZMod M) : ℂ :=
  (x.val : ℂ) / (M : ℂ)

/-- The lag-one collision response in the manuscript's floor coordinates. -/
noncomputable def collisionResponse (p : ℕ) (a : ZMod (p ^ 2)) : ℂ :=
  (carryThresholdCount p a.val : ℂ) -
    (p : ℂ) * (a.val : ℂ) / ((p ^ 2 : ℕ) : ℂ)

/-- The same response in fractional-part coordinates. -/
def collisionPoint (p d : ℕ) : ZMod (p ^ 2) := ((p + 1) * d : ℕ)

/-- The successor of one lag-one collision point. -/
def collisionPointNext (p d : ℕ) : ZMod (p ^ 2) := ((p + 1) * d + 1 : ℕ)

/-- The same response in fractional-part coordinates. -/
noncomputable def fractionalResponse
    {p : ℕ} (hp : p.Prime) (a : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ d ∈ Finset.range p,
    (residueFraction (collisionPoint p d * a) -
      residueFraction (collisionPointNext p d * a))

/-- The straightened finite Bernoulli boundary. -/
noncomputable def bernoulliBoundary
    {p : ℕ} (_hp : p.Prime) (a : ZMod (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 _hp.ne_zero⟩
  exact 2 * ∑ r ∈ Finset.Ico 1 p,
    centeredSawtooth (((r : ℕ) : ZMod (p ^ 2)) * a)

/-- One floor jump is its linear drift plus the exact difference of the two
fractional residues. -/
theorem floorJump_eq_fractionalDifference
    {M a n : ℕ} (hM : 0 < M) :
    (floorJump M a n : ℂ) =
      (a : ℂ) / (M : ℂ) +
        (((((n * a) % M : ℕ) : ℂ) / (M : ℂ)) -
          (((((n + 1) * a) % M : ℕ) : ℂ) / (M : ℂ))) := by
  have hMℂ : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hn := Nat.mod_add_div (n * a) M
  have hnext := Nat.mod_add_div ((n + 1) * a) M
  have hnℂ := congrArg (fun x : ℕ => (x : ℂ)) hn
  have hnextℂ := congrArg (fun x : ℕ => (x : ℂ)) hnext
  simp only [Nat.cast_add, Nat.cast_mul] at hnℂ hnextℂ
  unfold floorJump
  simp only [Int.cast_sub, Int.cast_natCast]
  field_simp [hMℂ]
  linear_combination hnextℂ - hnℂ

/-- Manuscript Lemma `Floor-to-fractional response`, on every carrier
residue. -/
theorem collisionResponse_eq_fractionalResponse
    {p : ℕ} (hp : p.Prime) (a : ZMod (p ^ 2)) :
    collisionResponse p a = fractionalResponse hp a := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2ℂ : ((p ^ 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 hp.ne_zero)
  have hpoint (d : ℕ) (_hd : d ∈ Finset.range p) :
      (floorJump (p ^ 2) a.val ((p + 1) * d) : ℂ) =
        (a.val : ℂ) / ((p ^ 2 : ℕ) : ℂ) +
          (residueFraction
              (collisionPoint p d * a) -
            residueFraction
              (collisionPointNext p d * a)) := by
    rw [floorJump_eq_fractionalDifference hp2pos]
    simp only [residueFraction, collisionPoint, collisionPointNext,
      ZMod.val_mul, ZMod.val_natCast]
    congr 2 <;> rw [Nat.mul_mod] <;>
      simp only [Nat.mod_eq_of_lt a.val_lt]
  unfold collisionResponse fractionalResponse carryThresholdCount
  have hcast :
      ((∑ d ∈ Finset.range p,
          floorJump (p ^ 2) a.val ((p + 1) * d) : ℤ) : ℂ) =
        ∑ d ∈ Finset.range p,
          (floorJump (p ^ 2) a.val ((p + 1) * d) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  rw [show (∑ _d ∈ Finset.range p,
      (a.val : ℂ) / ((p ^ 2 : ℕ) : ℂ)) =
        (p : ℂ) * ((a.val : ℂ) / ((p ^ 2 : ℕ) : ℂ)) by simp]
  field_simp [hpℂ, hp2ℂ]
  ring

/-- The multiplier `1-p` is a unit modulo `p^2`; its displayed inverse is
`1+p`. -/
def straighteningUnit (p : ℕ) : (ZMod (p ^ 2))ˣ where
  val := 1 - (p : ZMod (p ^ 2))
  inv := 1 + (p : ZMod (p ^ 2))
  val_inv := by
    change (1 - (p : ZMod (p ^ 2))) * (1 + p) = 1
    have hp2 : (p : ZMod (p ^ 2)) * p = 0 := by
      rw [← Nat.cast_mul, show p * p = p ^ 2 by ring, ZMod.natCast_self]
    linear_combination -hp2
  inv_val := by
    change (1 + (p : ZMod (p ^ 2))) * (1 - p) = 1
    have hp2 : (p : ZMod (p ^ 2)) * p = 0 := by
      rw [← Nat.cast_mul, show p * p = p ^ 2 by ring, ZMod.natCast_self]
    linear_combination -hp2

/-- A fractional residue minus its reflected residue is twice the centered
sawtooth. -/
theorem residueFraction_sub_neg
    {M : ℕ} [NeZero M] (hM : 2 ≤ M) (x : ZMod M) :
    residueFraction x - residueFraction (-x) = 2 * centeredSawtooth x := by
  have hMℂ : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  by_cases hx : x = 0
  · subst x
    simp [residueFraction, centeredSawtooth]
  · have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
    unfold residueFraction centeredSawtooth
    rw [if_neg hx, ZMod.neg_val, if_neg hx]
    push_cast [Nat.cast_sub (Nat.le_of_lt x.val_lt)]
    field_simp [hMℂ]
    ring

/-- Multiplication by the straightening unit converts the fractional collision
boundary to the Bernoulli boundary pointwise. -/
theorem fractional_to_bernoulli_straightening
    {p : ℕ} (hp : p.Prime) (A : ZMod (p ^ 2)) :
    fractionalResponse hp ((straighteningUnit p).val * A) =
      bernoulliBoundary hp A := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp2 : 2 ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hbase :
      ((p + 1 : ℕ) : ZMod (p ^ 2)) * (straighteningUnit p).val = 1 := by
    change ((p + 1 : ℕ) : ZMod (p ^ 2)) * (1 - p) = 1
    have hp2zero : (p : ZMod (p ^ 2)) * p = 0 := by
      rw [← Nat.cast_mul, show p * p = p ^ 2 by ring, ZMod.natCast_self]
    push_cast
    linear_combination -hp2zero
  have hpoint (d : ℕ) (hd : d ∈ Finset.range p) :
      residueFraction
          ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) *
            ((straighteningUnit p).val * A)) -
        residueFraction
          (((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            ((straighteningUnit p).val * A))) =
      residueFraction (((d : ℕ) : ZMod (p ^ 2)) * A) -
        residueFraction
          (-(((p - 1 - d : ℕ) : ZMod (p ^ 2)) * A)) := by
    have hdlt : d < p := Finset.mem_range.mp hd
    have hfirst :
        ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) *
            ((straighteningUnit p).val * A)) =
          ((d : ℕ) : ZMod (p ^ 2)) * A := by
      rw [show (((p + 1) * d : ℕ) : ZMod (p ^ 2)) =
          ((p + 1 : ℕ) : ZMod (p ^ 2)) * (d : ZMod (p ^ 2)) by
        push_cast
        rfl]
      calc
        (((p + 1 : ℕ) : ZMod (p ^ 2)) * d) *
            ((straighteningUnit p).val * A) =
            (d : ZMod (p ^ 2)) *
              ((((p + 1 : ℕ) : ZMod (p ^ 2)) *
                (straighteningUnit p).val) * A) := by ring
        _ = (d : ZMod (p ^ 2)) * A := by rw [hbase, one_mul]
    have hsecondCoeff :
        ((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            (straighteningUnit p).val) =
          -((p - 1 - d : ℕ) : ZMod (p ^ 2)) := by
      calc
        ((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            (straighteningUnit p).val) =
            ((((p + 1 : ℕ) : ZMod (p ^ 2)) * d + 1) *
              (straighteningUnit p).val) := by
                congr 1
                push_cast
                rfl
        _ = (d : ZMod (p ^ 2)) *
              (((p + 1 : ℕ) : ZMod (p ^ 2)) *
                (straighteningUnit p).val) + (straighteningUnit p).val := by ring
        _ = (d : ZMod (p ^ 2)) + (straighteningUnit p).val := by rw [hbase, mul_one]
        _ = -((p - 1 - d : ℕ) : ZMod (p ^ 2)) := by
          change (d : ZMod (p ^ 2)) + (1 - p) = _
          have hnat : d + (p - 1 - d) = p - 1 := by omega
          have hcast := congrArg
            (fun n : ℕ => (n : ZMod (p ^ 2))) hnat
          rw [Nat.cast_add, Nat.cast_sub hp.one_le] at hcast
          linear_combination hcast
    rw [hfirst]
    congr 1
    apply congrArg residueFraction
    calc
      (((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
          ((straighteningUnit p).val * A))) =
          (((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) *
            (straighteningUnit p).val) * A) := by ring
      _ = -(((p - 1 - d : ℕ) : ZMod (p ^ 2)) * A) := by
        rw [hsecondCoeff]
        ring
  unfold fractionalResponse bernoulliBoundary
  simp only [collisionPoint, collisionPointNext]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hreflect := Finset.sum_range_reflect
    (fun d : ℕ => residueFraction
      (-(((d : ℕ) : ZMod (p ^ 2)) * A))) p
  have hsecond :
      (∑ d ∈ Finset.range p,
          residueFraction (-(((p - 1 - d : ℕ) : ZMod (p ^ 2)) * A))) =
        ∑ d ∈ Finset.range p,
          residueFraction (-(((d : ℕ) : ZMod (p ^ 2)) * A)) := by
    simpa using hreflect
  rw [hsecond, ← Finset.sum_sub_distrib]
  have hpair (d : ℕ) (_hd : d ∈ Finset.range p) :
      residueFraction (((d : ℕ) : ZMod (p ^ 2)) * A) -
          residueFraction (-(((d : ℕ) : ZMod (p ^ 2)) * A)) =
        2 * centeredSawtooth (((d : ℕ) : ZMod (p ^ 2)) * A) :=
    residueFraction_sub_neg hp2 _
  rw [Finset.sum_congr rfl hpair]
  rw [show Finset.range p = insert 0 (Finset.Ico 1 p) by
    have hp0 := hp.pos
    ext d
    simp
    omega]
  rw [Finset.sum_insert (by simp)]
  simp [Finset.mul_sum, centeredSawtooth]

/-- Manuscript Theorem `Collision-to-Bernoulli straightening`. -/
theorem collision_to_bernoulli_straightening
    {p : ℕ} (hp : p.Prime) (A : ZMod (p ^ 2)) :
    collisionResponse p ((straighteningUnit p).val * A) =
      bernoulliBoundary hp A := by
  rw [collisionResponse_eq_fractionalResponse hp,
    fractional_to_bernoulli_straightening hp]

/-- The finite square energy before straightening. -/
noncomputable def collisionEnergy {p : ℕ} (hp : p.Prime) : ℝ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ a : ZMod (p ^ 2), ‖collisionResponse p a‖ ^ 2

/-- The finite Bernoulli square energy after straightening. -/
noncomputable def bernoulliEnergy {p : ℕ} (hp : p.Prime) : ℝ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ A : ZMod (p ^ 2), ‖bernoulliBoundary hp A‖ ^ 2

/-- The pointwise straightening is an exact equality of finite square
energies because the multiplier is a permutation of the carrier grid. -/
theorem collision_energy_eq_bernoulli_energy
    {p : ℕ} (hp : p.Prime) : collisionEnergy hp = bernoulliEnergy hp := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold collisionEnergy bernoulliEnergy
  let e : ZMod (p ^ 2) ≃ ZMod (p ^ 2) := (straighteningUnit p).mulLeft
  have hreindex := e.sum_comp (fun a : ZMod (p ^ 2) => ‖collisionResponse p a‖ ^ 2)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro A _
  change ‖collisionResponse p ((straighteningUnit p).val * A)‖ ^ 2 = _
  rw [collision_to_bernoulli_straightening hp]

end NField.Alignment.CollisionBernoulliStraightening
