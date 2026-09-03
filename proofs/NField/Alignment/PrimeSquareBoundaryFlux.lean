/-
Author: Alexander S. Petty
-/

import NField.Alignment.PairedBoundaryFlux
import NField.Alignment.PrimeSquareCollisionWindow

/-!
# The lag-one prime-square boundary flux

The short window `1, ..., p - 1` and the step `p + 1` determine the two
oriented endpoint families of the lag-one collision diagonal modulo `p^2`.
Their antipodal pairing proves the manuscript's phase-sensitive factor two for
every odd character.
-/

namespace NField.Alignment.PrimeSquareBoundaryFlux

open scoped BigOperators ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.PairedBoundary
open NField.Alignment.PairedBoundaryFlux
open NField.Alignment.PrimeSquareCollisionWindow

theorem step_coprime_primeSquare {p : ℕ} :
    (p + 1).Coprime (p ^ 2) := by
  rw [Nat.coprime_pow_right_iff (by omega : 0 < 2)]
  simp

/-- The diagonal step `p + 1`, represented as a unit modulo `p^2`. -/
noncomputable def lagOneStepUnit (p : ℕ) :
    UnitClass (p ^ 2) :=
  ZMod.unitOfCoprime (p + 1) (step_coprime_primeSquare (p := p))

/-- Left endpoint `c(p + 1)`, with `1 <= c < p`. -/
noncomputable def lagOneBoundaryLeft
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    UnitClass (p ^ 2) :=
  lagOneStepUnit p * firstWindowUnit hp i

/-- Right endpoint, indexed so that it is the antipode of the reflected left
endpoint.  Its least representative is `i(p + 1) + 1`. -/
noncomputable def lagOneBoundaryRight
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    UnitClass (p ^ 2) :=
  -(lagOneBoundaryLeft hp (Fin.rev i))

/-- The signed boundary attached to the lag-one diagonal. -/
noncomputable def lagOneUnitBoundary
    {p : ℕ} (hp : p.Prime) : UnitClass (p ^ 2) → ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact pairedBoundary (lagOneBoundaryLeft hp) (lagOneBoundaryRight hp)

/-- The first-window character sum in intrinsic unit coordinates. -/
noncomputable def shortWindowSum
    {p : ℕ} (hp : p.Prime) (χ : Character (p ^ 2)) : ℂ :=
  ∑ i : FirstWindowIndex p, χ (firstWindowUnit hp i).val

/-- The same first window, now viewed as the complete unit group modulo the
prime. -/
noncomputable def lowerFirstWindowUnit
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) : UnitClass p :=
  ZMod.unitOfCoprime (firstWindowNat i) (by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt
      (firstWindowNat_pos i) (firstWindowNat_lt hp.two_le i))

theorem lowerFirstWindowUnit_val
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    (lowerFirstWindowUnit hp i).val.val = firstWindowNat i := by
  unfold lowerFirstWindowUnit
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt (firstWindowNat_lt hp.two_le i)]

theorem lowerFirstWindowUnit_injective
    {p : ℕ} (hp : p.Prime) :
    Function.Injective (lowerFirstWindowUnit hp) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg (fun u : UnitClass p => u.val.val) hij
  rw [lowerFirstWindowUnit_val hp i,
    lowerFirstWindowUnit_val hp j] at hv
  unfold firstWindowNat at hv
  omega

/-- The first window is exactly, not merely injectively, the unit group modulo
the prime. -/
noncomputable def lowerFirstWindowEquiv
    {p : ℕ} (hp : p.Prime) : FirstWindowIndex p ≃ UnitClass p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply Equiv.ofBijective (lowerFirstWindowUnit hp)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨lowerFirstWindowUnit_injective hp, ?_⟩
  simp only [FirstWindowIndex, Fintype.card_fin]
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]

/-- A nonprincipal character has zero sum on the complete unit group. -/
theorem unitCharacterSum_eq_zero
    {m : ℕ} [NeZero m] (χ : Character m) (hne : χ ≠ 1) :
    ∑ u : UnitClass m, χ u.val = 0 := by
  classical
  have hexists : ∃ a : UnitClass m, χ a.val ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    rw [MulChar.ext_iff]
    intro a
    simpa using h a
  obtain ⟨a, ha⟩ := hexists
  let shift : UnitClass m ≃ UnitClass m := Equiv.mulLeft a
  have hshift :
      (∑ u : UnitClass m, χ u.val) =
        ∑ u : UnitClass m, χ (a * u).val := by
    symm
    exact shift.sum_comp (fun u : UnitClass m => χ u.val)
  have hscale :
      (∑ u : UnitClass m, χ (a * u).val) =
        χ a.val * ∑ u : UnitClass m, χ u.val := by
    simp_rw [Units.val_mul, map_mul]
    rw [Finset.mul_sum]
  have hzero :
      (χ a.val - 1) * ∑ u : UnitClass m, χ u.val = 0 := by
    rw [sub_mul, one_mul, ← hscale, ← hshift]
    ring
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ha)

/-- Orthogonality of the complete lower-level first window. -/
theorem lowerShortWindowSum_eq_zero
    {p : ℕ} (hp : p.Prime) (ψ : Character p) (hne : ψ ≠ 1) :
    (∑ i : FirstWindowIndex p, ψ (lowerFirstWindowUnit hp i).val) = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  calc
    (∑ i : FirstWindowIndex p, ψ (lowerFirstWindowUnit hp i).val) =
        ∑ u : UnitClass p, ψ u.val :=
      by
        change (∑ i : FirstWindowIndex p,
          ψ ((lowerFirstWindowEquiv hp) i).val) = _
        exact (lowerFirstWindowEquiv hp).sum_comp
          (fun u : UnitClass p => ψ u.val)
    _ = 0 := unitCharacterSum_eq_zero ψ hne

/-- Raising a nonprincipal character from `p` to `p^2` makes its prime-square
short window vanish exactly. -/
theorem shortWindowSum_changeLevel_zero
    {p : ℕ} (hp : p.Prime) (ψ : Character p) (hne : ψ ≠ 1) :
    shortWindowSum hp
      (DirichletCharacter.changeLevel (dvd_pow_self p (by omega)) ψ) = 0 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold shortWindowSum
  have hpoint (i : FirstWindowIndex p) :
      DirichletCharacter.changeLevel (dvd_pow_self p (by omega)) ψ
          (firstWindowUnit hp i).val =
        ψ (lowerFirstWindowUnit hp i).val := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ψ
      (dvd_pow_self p (by omega)) (firstWindowUnit hp i)]
    unfold firstWindowUnit lowerFirstWindowUnit
    rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast (dvd_pow_self p (by omega)) (firstWindowNat i)]
  simp_rw [hpoint]
  exact lowerShortWindowSum_eq_zero hp ψ hne

/-- Character flux of the concrete lag-one boundary. -/
noncomputable def lagOneBoundaryFlux
    {p : ℕ} (hp : p.Prime) (χ : Character (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ x : UnitClass (p ^ 2), lagOneUnitBoundary hp x * χ x.val

theorem lagOneBoundary_antipodal
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    -(lagOneBoundaryLeft hp i) =
      lagOneBoundaryRight hp (Fin.rev i) := by
  simp [lagOneBoundaryRight]

/-- The left endpoint character sum separates into the diagonal step and the
short window. -/
theorem leftEndpointSum_factor
    {p : ℕ} (hp : p.Prime) (χ : Character (p ^ 2)) :
    (∑ i : FirstWindowIndex p, χ (lagOneBoundaryLeft hp i).val) =
      χ (lagOneStepUnit p).val * shortWindowSum hp χ := by
  classical
  unfold lagOneBoundaryLeft shortWindowSum
  calc
    (∑ i : FirstWindowIndex p,
        χ (lagOneStepUnit p * firstWindowUnit hp i).val) =
      ∑ i : FirstWindowIndex p,
        χ (lagOneStepUnit p).val * χ (firstWindowUnit hp i).val := by
          apply Finset.sum_congr rfl
          intro i _
          exact map_mul χ _ _
    _ = χ (lagOneStepUnit p).val *
        ∑ i : FirstWindowIndex p, χ (firstWindowUnit hp i).val := by
          rw [Finset.mul_sum]

/-- Exact phase-sensitive lag-one boundary reduction. -/
theorem lagOneBoundaryFlux_eq_shortWindow
    {p : ℕ} (hp : p.Prime) (χ : Character (p ^ 2)) (hodd : χ.Odd) :
    lagOneBoundaryFlux hp χ =
      -2 * χ (lagOneStepUnit p).val * shortWindowSum hp χ := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold lagOneBoundaryFlux lagOneUnitBoundary
  rw [pairedBoundary_pairing_odd
    (lagOneBoundaryLeft hp) (lagOneBoundaryRight hp)
    (Fin.revPerm : Equiv.Perm (FirstWindowIndex p))
    (lagOneBoundary_antipodal hp)
    (fun x : UnitClass (p ^ 2) => χ x.val)]
  · rw [leftEndpointSum_factor hp χ]
    ring
  · intro x
    exact DirichletCharacter.Odd.eval_neg χ x.val hodd

/-- A Dirichlet character has squared modulus one on a unit residue. -/
theorem character_unit_normSq
    {m : ℕ} [NeZero m] (χ : Character m) (u : UnitClass m) :
    Complex.normSq (χ u.val) = 1 := by
  have hcomplex : ((Complex.normSq (χ u.val) : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    calc
      (starRingEnd ℂ) (χ u.val) * χ u.val =
          ((χ : MulChar (ZMod m) ℂ)⁻¹) u.val * χ u.val := by
            rw [← Complex.star_def, MulChar.star_apply']
      _ = χ (u⁻¹ : UnitClass m).val * χ u.val := by
            rw [MulChar.inv_apply, Ring.inverse_unit]
      _ = χ ((u⁻¹ * u : UnitClass m).val) := by
            calc
              χ (u⁻¹ : UnitClass m).val * χ u.val =
                  χ ((u⁻¹ : UnitClass m).val * u.val) :=
                    (map_mul χ _ _).symm
              _ = χ ((u⁻¹ * u : UnitClass m).val) := by
                    rw [Units.val_mul]
      _ = 1 := by simp
  exact_mod_cast hcomplex

/-- Squaring removes the phase of the unit step. -/
theorem lagOneBoundaryFlux_normSq
    {p : ℕ} (hp : p.Prime) (χ : Character (p ^ 2)) (hodd : χ.Odd) :
    Complex.normSq (lagOneBoundaryFlux hp χ) =
      4 * Complex.normSq (shortWindowSum hp χ) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [lagOneBoundaryFlux_eq_shortWindow hp χ hodd]
  rw [Complex.normSq_mul, Complex.normSq_mul,
    character_unit_normSq]
  norm_num [Complex.normSq_apply]

/-- The complete imprimitive odd sector induced from the prime level has zero
lag-one boundary flux. -/
theorem lagOneBoundaryFlux_changeLevel_zero
    {p : ℕ} (hp : p.Prime) (ψ : Character p)
    (hne : ψ ≠ 1) (hodd : ψ.Odd) :
    lagOneBoundaryFlux hp
      (DirichletCharacter.changeLevel (dvd_pow_self p (by omega)) ψ) = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let hlevel : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
  have hliftOdd :
      (DirichletCharacter.changeLevel hlevel ψ).Odd :=
    (NField.Alignment.PrimitiveOddBoundaryMean.changeLevel_odd_iff
      hlevel ψ).2 hodd
  rw [lagOneBoundaryFlux_eq_shortWindow hp _ hliftOdd,
    shortWindowSum_changeLevel_zero hp ψ hne]
  ring

end NField.Alignment.PrimeSquareBoundaryFlux
