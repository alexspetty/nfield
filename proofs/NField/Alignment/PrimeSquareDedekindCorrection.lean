/-
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareBoundaryFlux

/-!
# Cancellation of the lower-modulus Dedekind correction

Reduction from units modulo `p^2` to units modulo `p` sends the first collision
window bijectively onto the complete lower unit group.  Consequently the
weighted lower-modulus Dedekind correction becomes a double ratio sum in which
every inner sum is the full unit sum, hence zero by odd reflection.
-/

namespace NField.Alignment.PrimeSquareDedekindCorrection

open scoped BigOperators ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionRatioCompression
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeSquareCollisionWindow

/-- Reduction of prime-square units to prime-level units. -/
noncomputable def primeReduction
    {p : ℕ} (_hp : p.Prime) : UnitClass (p ^ 2) →* UnitClass p := by
  have hp := _hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ZMod.unitsMap (dvd_pow_self p (by omega))

/-- Dedekind sum at the prime level, with nonzero modulus discharged by
primality. -/
noncomputable def primeDedekindSum
    {p : ℕ} (hp : p.Prime) (h : UnitClass p) : ℂ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact dedekindSum h

/-- Reduction carries each prime-square first-window unit to the corresponding
prime-level first-window unit. -/
theorem primeReduction_firstWindow
    {p : ℕ} (hp : p.Prime) (i : FirstWindowIndex p) :
    primeReduction hp (firstWindowUnit hp i) =
      lowerFirstWindowUnit hp i := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  apply Units.ext
  unfold primeReduction firstWindowUnit lowerFirstWindowUnit
  simp [ZMod.unitsMap_val, ZMod.cast_natCast]

/-- The lower-modulus kernel that occurs before the manuscript cancels its
correction term. -/
noncomputable def lowerDedekindKernel
    {p : ℕ} (hp : p.Prime) (v : UnitClass (p ^ 2)) : ℂ := by
  exact primeDedekindSum hp (primeReduction hp v)

/-- Weighted lower-modulus correction in collision-ratio coordinates. -/
noncomputable def weightedLowerDedekindCorrection
    {p : ℕ} (hp : p.Prime) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact weightedRatioSum (firstCollisionWindow hp)
    (lowerDedekindKernel hp)

/-- Reindexing an image finset through an injective parametrization. -/
theorem sum_image_injective
    {ι κ R : Type*} [Fintype ι] [DecidableEq κ] [AddCommMonoid R]
    (f : ι → κ) (hf : Function.Injective f) (F : κ → R) :
    (∑ x ∈ Finset.univ.image f, F x) = ∑ i : ι, F (f i) := by
  classical
  rw [Finset.sum_image]
  exact hf.injOn

/-- The correction double sum is the same sum written in intrinsic first-window
indices at the lower modulus. -/
theorem lowerCorrectionDoubleSum_reindex
    {p : ℕ} (hp : p.Prime) :
    collisionDoubleSum (firstCollisionWindow hp)
        (lowerDedekindKernel hp) =
      ∑ k : FirstWindowIndex p, ∑ u : FirstWindowIndex p,
        primeDedekindSum hp
          ((lowerFirstWindowUnit hp k)⁻¹ * lowerFirstWindowUnit hp u) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold collisionDoubleSum firstCollisionWindow
  rw [sum_image_injective (firstWindowUnit hp)
    (firstWindowUnit_injective hp)]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_image_injective (firstWindowUnit hp)
    (firstWindowUnit_injective hp)]
  apply Finset.sum_congr rfl
  intro u _
  unfold lowerDedekindKernel
  congr 1
  rw [map_mul, map_inv, primeReduction_firstWindow,
    primeReduction_firstWindow]

/-- Each fixed left coordinate sees every lower-level Dedekind argument once. -/
theorem fixedLowerWindowDedekindSum_zero
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (k : FirstWindowIndex p) :
    (∑ u : FirstWindowIndex p,
      primeDedekindSum hp
        ((lowerFirstWindowUnit hp k)⁻¹ * lowerFirstWindowUnit hp u)) = 0 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 := hp.two_le
  calc
    (∑ u : FirstWindowIndex p,
      primeDedekindSum hp
        ((lowerFirstWindowUnit hp k)⁻¹ * lowerFirstWindowUnit hp u)) =
        ∑ v : UnitClass p,
          primeDedekindSum hp ((lowerFirstWindowUnit hp k)⁻¹ * v) :=
      (lowerFirstWindowEquiv hp).sum_comp
        (fun v : UnitClass p =>
          primeDedekindSum hp ((lowerFirstWindowUnit hp k)⁻¹ * v))
    _ = ∑ v : UnitClass p, primeDedekindSum hp v := by
      let shift : UnitClass p ≃ UnitClass p :=
        Equiv.mulLeft (lowerFirstWindowUnit hp k)⁻¹
      exact shift.sum_comp (primeDedekindSum hp)
    _ = 0 := by
      unfold primeDedekindSum
      exact sum_dedekindSum_units_zero (by omega)

/-- The complete collision-weighted lower-modulus correction vanishes. -/
theorem weightedLowerDedekindCorrection_eq_zero
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    weightedLowerDedekindCorrection hp = 0 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold weightedLowerDedekindCorrection
  rw [weightedRatioSum_eq_collisionDoubleSum,
    lowerCorrectionDoubleSum_reindex hp]
  apply Finset.sum_eq_zero
  intro k _
  exact fixedLowerWindowDedekindSum_zero hp hpodd k

end NField.Alignment.PrimeSquareDedekindCorrection
