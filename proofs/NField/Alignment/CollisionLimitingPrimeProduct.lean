/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionLcmFactorErrors
import NField.Alignment.CollisionMertensInput

/-!
# The limiting prime product and the sharp alignment constants

The square-complement product is evaluated by an absolutely convergent
Euler product. Combining that limit with the proved Mertens theorem gives
the coefficient of the limiting product over primes up to a real cutoff.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLimitingPrimeProduct

open scoped Classical
open Filter Asymptotics CollisionZetaMoments CollisionMertensInput

def squareReciprocalHom : ℕ →*₀ ℝ where
  toFun := powerKernel 2
  map_zero' := by simp [powerKernel]
  map_one' := by norm_num [powerKernel]
  map_mul' m n := by simp [powerKernel,Nat.cast_mul,mul_pow,one_div,mul_comm]

def primeSquareComplementNat (m : ℕ) : ℝ := ∏ p ∈ Nat.primesLE m, (1-1/(p : ℝ)^2)
def primeSquareComplement (x : ℝ) : ℝ := ∏ p ∈ primesUpTo x, (1-1/(p : ℝ)^2)
def limitingPrimeProduct (x : ℝ) : ℝ := ∏ p ∈ primesUpTo x, (1+(p : ℝ)⁻¹)
def alignmentKappa : ℝ := Real.exp Real.eulerMascheroniConstant/zetaNat 2
def alignmentGamma : ℝ := alignmentKappa/3

theorem squareReciprocalHom_norm_summable : Summable (fun n : ℕ => ‖squareReciprocalHom n‖) := by
  change Summable (fun n : ℕ => ‖powerKernel 2 n‖)
  exact (powerKernel_summable (by norm_num : 1 < (2 : ℕ))).norm

theorem inverse_square_prime_product_tendsto :
    Tendsto (fun m : ℕ => ∏ p ∈ Nat.primesLE m, (1-1/(p : ℝ)^2)⁻¹)
      atTop (nhds (zetaNat 2)) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative squareReciprocalHom_norm_summable
  have hshift : Tendsto (fun m : ℕ => m+1) atTop atTop := tendsto_add_atTop_nat 1
  exact h.comp hshift

theorem primeSquareComplementNat_tendsto :
    Tendsto primeSquareComplementNat atTop (nhds ((zetaNat 2)⁻¹)) := by
  have h := inverse_square_prime_product_tendsto.inv₀ (zetaNat_pos (by norm_num : 1 < (2 : ℕ))).ne'
  change Tendsto (fun m : ℕ => ∏ p ∈ Nat.primesLE m, (1-1/(p : ℝ)^2)) atTop _
  simpa only [← Finset.prod_inv_distrib,inv_inv] using h

theorem primesUpTo_eq_primesLE_floor (x : ℝ) : primesUpTo x=Nat.primesLE ⌊x⌋₊ := by
  ext p
  rw [primesUpTo_mem,Nat.mem_primesLE]
  constructor
  · rintro ⟨hp,hpx⟩
    exact ⟨(Nat.le_floor_iff' hp.ne_zero).mpr hpx,hp⟩
  · rintro ⟨hpx,hp⟩
    exact ⟨hp,(Nat.le_floor_iff' hp.ne_zero).mp hpx⟩

theorem primeSquareComplement_tendsto :
    Tendsto primeSquareComplement atTop (nhds ((zetaNat 2)⁻¹)) := by
  have h := primeSquareComplementNat_tendsto.comp (tendsto_nat_floor_atTop (α := ℝ))
  convert! h using 1
  funext x
  unfold primeSquareComplement primeSquareComplementNat
  rw [primesUpTo_eq_primesLE_floor]
  rfl

theorem limitingPrimeProduct_factorization (x : ℝ) :
    limitingPrimeProduct x=inversePrimeProduct x*primeSquareComplement x := by
  unfold limitingPrimeProduct inversePrimeProduct primeSquareComplement
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (primesUpTo_mem.mp hp).1.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hpm : (p : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have hd : 1-(p : ℝ)⁻¹=((p : ℝ)-1)/(p : ℝ) := by field_simp
  rw [hd]
  field_simp
  ring

theorem alignmentKappa_pos : 0 < alignmentKappa :=
  div_pos (Real.exp_pos _) (zetaNat_pos (by norm_num : 1 < (2 : ℕ)))

theorem alignmentGamma_pos : 0 < alignmentGamma := div_pos alignmentKappa_pos (by norm_num)

theorem zetaNat_two_value : zetaNat 2=Real.pi^2/6 := by
  exact hasSum_zeta_two.tsum_eq

theorem alignmentGamma_value : alignmentGamma=2*Real.exp Real.eulerMascheroniConstant/Real.pi^2 := by
  unfold alignmentGamma alignmentKappa
  rw [zetaNat_two_value]
  ring

theorem limitingPrimeProduct_asymptotic :
    limitingPrimeProduct ~[atTop] (fun x : ℝ => alignmentKappa*Real.log x) := by
  have hz : (zetaNat 2)⁻¹ ≠ 0 := inv_ne_zero (zetaNat_pos (by norm_num : 1 < (2 : ℕ))).ne'
  have hC : primeSquareComplement ~[atTop] (fun _ : ℝ => (zetaNat 2)⁻¹) :=
    (isEquivalent_const_iff_tendsto hz).mpr primeSquareComplement_tendsto
  have h := mertens_inverse_product.mul hC
  convert! h using 1
  · funext x
    exact limitingPrimeProduct_factorization x
  · funext x
    dsimp only [Pi.mul_apply]
    unfold alignmentKappa
    ring

end NField.Alignment.CollisionLimitingPrimeProduct
