/-
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarryTableColumnLaw
import NField.Alignment.PrimeSquareDedekindCorrection
import NField.Alignment.TheCollisionSpectrum
import NField.Alignment.EndpointNormalization

/-!
# Prime carry energy bridge

This module connects the concrete prime carry table to the sawtooth and
Dedekind descriptions of the same finite energy.  It keeps the energy attached
to the actual floor-jump table and proves each change of coordinates.
-/

namespace NField.Alignment.PrimeCarryEnergyBridge

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.EndpointNormalization
open NField.Alignment.PrimeCarryTableColumnLaw
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareDedekindCorrection

/-- The exact class-centered carry statistic on a prime-square unit. -/
noncomputable def primeCarryCentered
    {p : ℕ} (_hp : p.Prime) (a : UnitClass (p ^ 2)) : ℂ :=
  (fluctuationTable p a.val.val : ℂ) +
    ((p - a.val.val % p : ℕ) : ℂ) / (p : ℂ)

/-- The manuscript's collision energy, defined from the concrete centered
floor-jump table. -/
noncomputable def primeCarryEnergy
    {p : ℕ} (hp : p.Prime) : ℝ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ a : UnitClass (p ^ 2), ‖primeCarryCentered hp a‖ ^ 2

/-- The diagonal sawtooth carry signal before taking its square mass. -/
noncomputable def primeDiagonalSawtoothSignal
    {p : ℕ} (_hp : p.Prime) (a : UnitClass (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 _hp.ne_zero⟩
  exact -∑ d ∈ Finset.range p,
    (centeredSawtooth ((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) * a.val) -
      centeredSawtooth ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) * a.val))

/-- Multiplying a proper nonzero natural residue by a unit cannot produce
zero modulo the ambient modulus. -/
theorem natCast_mul_unit_ne_zero
    {M n : ℕ} [NeZero M] (a : UnitClass M)
    (hnpos : 0 < n) (hnlt : n < M) :
    (n : ZMod M) * a.val ≠ 0 := by
  intro hzero
  have hnzero : (n : ZMod M) = 0 := by
    calc
      (n : ZMod M) = ((n : ZMod M) * a.val) * (a⁻¹).val := by
        rw [mul_assoc, ← Units.val_mul]
        simp
      _ = 0 := by rw [hzero]; simp
  have hval := congrArg ZMod.val hnzero
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hnlt] at hval
  simp at hval
  omega

/-- Away from the two cyclic endpoints, one centered-sawtooth step is the
linear increment minus the exact floor jump. -/
theorem centeredSawtooth_step_interior
    {M n : ℕ} [NeZero M] (hM : 0 < M) (a : UnitClass M)
    (hnpos : 0 < n) (hnnext : n + 1 < M) :
    centeredSawtooth (((n + 1 : ℕ) : ZMod M) * a.val) -
        centeredSawtooth ((n : ZMod M) * a.val) =
      (a.val.val : ℂ) / (M : ℂ) - (floorJump M a.val.val n : ℂ) := by
  have hnlt : n < M := by omega
  have hleft := natCast_mul_unit_ne_zero a hnpos hnlt
  have hright := natCast_mul_unit_ne_zero a (by omega) hnnext
  have hvalLeft : (((n : ℕ) : ZMod M) * a.val).val =
      (n * a.val.val) % M := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hnlt]
  have hvalRight : ((((n + 1 : ℕ) : ZMod M) * a.val).val) =
      ((n + 1) * a.val.val) % M := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hnnext]
  have hdecompLeft := Nat.mod_add_div (n * a.val.val) M
  have hdecompRight := Nat.mod_add_div ((n + 1) * a.val.val) M
  have hresidue :
      (((((n + 1) * a.val.val) % M : ℕ) : ℤ) -
          (((n * a.val.val) % M : ℕ) : ℤ)) =
        (a.val.val : ℤ) -
          (M : ℤ) * floorJump M a.val.val n := by
    have hdecompLeftZ := congrArg (fun z : ℕ => (z : ℤ)) hdecompLeft
    have hdecompRightZ := congrArg (fun z : ℕ => (z : ℤ)) hdecompRight
    simp only [Nat.cast_add, Nat.cast_mul] at hdecompLeftZ hdecompRightZ
    unfold floorJump
    linear_combination hdecompRightZ - hdecompLeftZ
  unfold centeredSawtooth
  rw [if_neg hright, if_neg hleft, hvalRight, hvalLeft]
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hresidueC := congrArg (fun z : ℤ => (z : ℂ)) hresidue
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at hresidueC
  field_simp [hMC]
  ring_nf at hresidueC ⊢
  have htwice := congrArg (fun z : ℂ => 2 * z) hresidueC
  ring_nf at htwice
  exact htwice

/-- The endpoint corrections in the diagonal sawtooth sum cancel exactly. -/
theorem diagonal_endpoint_correction_sum
    {p : ℕ} (hp : p.Prime) :
    (∑ d ∈ Finset.range p,
      (if (p + 1) * d = 0 then (1 / 2 : ℂ)
       else if (p + 1) * d = p ^ 2 - 1 then -(1 / 2 : ℂ) else 0)) = 0 := by
  classical
  have hp2 := hp.two_le
  have hlast : (p + 1) * (p - 1) = p ^ 2 - 1 := by
    rw [Nat.mul_sub_left_distrib]
    simp only [mul_one]
    have hmul : (p + 1) * p = p ^ 2 + p := by ring
    rw [hmul]
    omega
  have hsplit : Finset.range p =
      insert 0 (Finset.Ico 1 (p - 1) ∪ {p - 1}) := by
    ext d
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hsplit]
  have hzero_not_mem : 0 ∉ Finset.Ico 1 (p - 1) ∪ {p - 1} := by
    simp
    omega
  rw [Finset.sum_insert hzero_not_mem]
  have hlast_not_mem : p - 1 ∉ Finset.Ico 1 (p - 1) := by simp
  rw [Finset.sum_union (by simp), Finset.sum_singleton]
  have hinterior :
      (∑ d ∈ Finset.Ico 1 (p - 1),
        (if (p + 1) * d = 0 then (1 / 2 : ℂ)
         else if (p + 1) * d = p ^ 2 - 1 then -(1 / 2 : ℂ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hdpos := (Finset.mem_Ico.mp hd).1
    have hdlt := (Finset.mem_Ico.mp hd).2
    have hnezero : (p + 1) * d ≠ 0 := by positivity
    have hnelt : (p + 1) * d ≠ p ^ 2 - 1 := by
      intro h
      have hbound : (p + 1) * d < (p + 1) * (p - 1) :=
        (Nat.mul_lt_mul_left (Nat.succ_pos p)).2 hdlt
      rw [hlast] at hbound
      omega
    simp [hnezero, hnelt]
  rw [hinterior, hlast]
  have hp4 : 4 ≤ p ^ 2 := by nlinarith
  have hsquarepred : p ^ 2 - 1 ≠ 0 := by omega
  simp [hsquarepred]

/-- The diagonal sawtooth signal is the raw threshold count minus its exact
linear drift. -/
theorem primeDiagonalSawtoothSignal_eq_threshold
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    primeDiagonalSawtoothSignal hp a =
      (carryThresholdCount p a.val.val : ℂ) -
        (p : ℂ) * (a.val.val : ℂ) / ((p ^ 2 : ℕ) : ℂ) := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp2sq : 2 ≤ p ^ 2 := by nlinarith [hp.two_le]
  letI : Fact (1 < p ^ 2) := ⟨by omega⟩
  have hAvalPos : 1 ≤ a.val.val := by
    have hne : a.val ≠ 0 := IsUnit.ne_zero a.isUnit
    exact ZMod.val_pos.mpr hne
  have hAvalLt : a.val.val < p ^ 2 := a.val.val_lt
  have hcop : a.val.val.Coprime (p ^ 2) := by
    have hu : IsUnit (a.val.val : ZMod (p ^ 2)) := by
      simpa only [ZMod.natCast_zmod_val] using a.isUnit
    exact (ZMod.isUnit_iff_coprime a.val.val (p ^ 2)).mp hu
  have hpoint (d : ℕ) (hd : d ∈ Finset.range p) :
      -(centeredSawtooth
          ((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2)) * a.val) -
        centeredSawtooth
          ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) * a.val)) =
        (floorJump (p ^ 2) a.val.val ((p + 1) * d) : ℂ) -
          (a.val.val : ℂ) / ((p ^ 2 : ℕ) : ℂ) +
          (if (p + 1) * d = 0 then (1 / 2 : ℂ)
           else if (p + 1) * d = p ^ 2 - 1 then -(1 / 2 : ℂ) else 0) := by
    have hdlt : d < p := Finset.mem_range.mp hd
    have hnlt : (p + 1) * d < p ^ 2 := by nlinarith
    have hcarry := sawtooth_carry_step hp2sq hAvalPos hAvalLt hcop hnlt
      (n := (p + 1) * d)
    have hle : ((p + 1) * d) * a.val.val / p ^ 2 ≤
        (((p + 1) * d) + 1) * a.val.val / p ^ 2 :=
      Nat.div_le_div_right
        (Nat.mul_le_mul_right a.val.val (Nat.le_succ ((p + 1) * d)))
    have hjump :
        (floorJump (p ^ 2) a.val.val ((p + 1) * d) : ℂ) =
          (carryStep (p ^ 2) a.val.val ((p + 1) * d) : ℂ) := by
      unfold floorJump carryStep
      rw [Nat.cast_sub hle]
      push_cast
      rfl
    rw [hjump]
    push_cast at hcarry
    rw [ZMod.natCast_zmod_val] at hcarry
    push_cast
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hcarry
  unfold primeDiagonalSawtoothSignal
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [diagonal_endpoint_correction_sum hp]
  unfold carryThresholdCount
  push_cast
  simp
  ring

/-- The actual class-centered carry table is exactly its diagonal sawtooth
signal, point by point on the prime-square unit group. -/
theorem primeCarryCentered_eq_diagonalSawtooth
    {p : ℕ} (hp : p.Prime)
    (a : UnitClass (p ^ 2)) :
    primeCarryCentered hp a = primeDiagonalSawtoothSignal hp a := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let A := a.val.val
  let q := A / p
  let s := A % p
  have hp0 : 0 < p := hp.pos
  have hA : A = p * q + s := by
    dsimp [q, s]
    simpa [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div A p).symm
  have hcopA : A.Coprime (p ^ 2) := by
    have hu : IsUnit (A : ZMod (p ^ 2)) := by
      rw [show (A : ZMod (p ^ 2)) = a.val by
        exact ZMod.natCast_zmod_val a.val]
      exact a.isUnit
    exact (ZMod.isUnit_iff_coprime A (p ^ 2)).mp hu
  have hspos : 0 < s := by
    dsimp [s]
    have hcopBase : A.Coprime p :=
      hcopA.of_dvd_right (dvd_pow_self p (by omega))
    exact Nat.pos_of_ne_zero (fun hs0 => by
      have hpdiv : p ∣ A := Nat.dvd_iff_mod_eq_zero.mpr hs0
      have hpone : p = 1 :=
        Nat.eq_one_of_dvd_coprimes hcopBase hpdiv dvd_rfl
      exact hp.ne_one hpone)
  have hslt : s < p := Nat.mod_lt A hp0
  rw [primeDiagonalSawtoothSignal_eq_threshold hp]
  unfold primeCarryCentered
  rw [show a.val.val = p * q + s by exact hA]
  rw [fluctuationTable_eq_thresholdCount hp0 hslt]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmod : (p * q + s) % p = s := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hslt]
  rw [hmod, Nat.cast_sub (Nat.le_of_lt hslt)]
  push_cast
  field_simp [hpC]
  ring

end NField.Alignment.PrimeCarryEnergyBridge
