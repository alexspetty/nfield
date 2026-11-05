/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperGaussianSmoothingScales

/-!
# Actual prime-block variance from the proved second Mertens theorem

At upper endpoint X the block is exactly X^(1/e)<q<=X. Subtraction of
the two prime-prefix sums gives twice the Gaussian variance parameter
as 1+E2p(X)-E2p(X^(1/e)). The imported proved Mertens remainder tends to
zero, so the variance tends to one half and is eventually between one
quarter and three quarters. This is uniform in the original block index
once its upper endpoint is large enough.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeBlockVariance
open scoped BigOperators Topology
open Filter Asymptotics CollisionMertensInput HarperPrimeBlocks HarperPrimeRangeCharacteristic

def upperBlock (X : ℝ) : Finset ℕ := by
  classical
  exact (primesUpTo X).filter (fun q => sourceCutoff X < (q : ℝ))
def blockVariance (X : ℝ) : ℝ := rangeVariance (upperBlock X)

theorem primeBlock_eq_upperBlock {x : ℝ} (hx : 0 ≤ x) (l : ℕ) :
    primeBlock x l = upperBlock (blockUpper x l) := by
  classical
  unfold primeBlock upperBlock
  rw [blockLower_power hx]
  rfl

theorem upperBlock_sdiff (X : ℝ) :
    upperBlock X = primesUpTo X \ primesUpTo (sourceCutoff X) := by
  classical
  ext q
  simp only [upperBlock, Finset.mem_filter, Finset.mem_sdiff, primesUpTo_mem]
  by_cases hp : q.Prime <;> simp [hp, not_le]

theorem sourceCutoff_le {X : ℝ} (hX : 1 ≤ X) : sourceCutoff X ≤ X := by
  conv_rhs => rw [← Real.rpow_one X]
  apply Real.rpow_le_rpow_of_exponent_le hX
  rw [div_le_one (Real.exp_pos 1)]
  linarith [Real.exp_one_gt_two]

theorem sourceCutoff_log_log {X : ℝ} (hX : 1 < X) :
    Real.log (Real.log (sourceCutoff X)) = Real.log (Real.log X)-1 := by
  rw [sourceCutoff, Real.log_rpow (by linarith)]
  rw [Real.log_mul (by positivity) (Real.log_pos hX).ne', Real.log_div (by norm_num)
    (Real.exp_ne_zero 1), Real.log_one, Real.log_exp]
  ring

theorem blockVariance_nonneg (X : ℝ) : 0 ≤ blockVariance X := by
  unfold blockVariance rangeVariance
  exact Finset.sum_nonneg (fun q _ => div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q)) (by norm_num))

theorem blockVariance_mertens_identity {X : ℝ} (hX : 1 < X) :
    2*blockVariance X = 1+Mertens.E₂p X-Mertens.E₂p (sourceCutoff X) := by
  have hs : primesUpTo (sourceCutoff X) ⊆ primesUpTo X := by
    intro q hq
    rcases primesUpTo_mem.mp hq with ⟨hp,hq⟩
    exact primesUpTo_mem.mpr ⟨hp,hq.trans (sourceCutoff_le hX.le)⟩
  have he := Finset.sum_sdiff (f := fun q : ℕ => (1 : ℝ)/q) hs
  rw [← upperBlock_sdiff] at he
  have htwice : 2*blockVariance X = ∑ q ∈ upperBlock X, (1 : ℝ)/q := by
    unfold blockVariance rangeVariance
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [one_div]
    ring
  rw [htwice]
  change (∑ q ∈ upperBlock X, (1 : ℝ)/q)+
    (∑ q ∈ (Finset.Ioc 0 ⌊sourceCutoff X⌋₊).filter Nat.Prime, (1 : ℝ)/q) =
    ∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime, (1 : ℝ)/q at he
  rw [Mertens.sum_prime_div_eq, Mertens.sum_prime_div_eq, sourceCutoff_log_log hX] at he
  linarith

theorem blockVariance_tendsto : Tendsto blockVariance atTop (𝓝 (1/2 : ℝ)) := by
  have hE : Tendsto Mertens.E₂p atTop (𝓝 (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have hY : Tendsto sourceCutoff atTop atTop :=
    tendsto_rpow_atTop (by positivity : 0 < 1/Real.exp 1)
  have ht : Tendsto (fun X => (1+Mertens.E₂p X-Mertens.E₂p (sourceCutoff X))/2)
      atTop (𝓝 (1/2 : ℝ)) := by
    convert (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hE).sub
      (hE.comp hY)).div_const 2 using 1 <;> norm_num
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have h := blockVariance_mertens_identity hX
  linarith

theorem eventual_blockVariance_bounds :
    ∀ᶠ X : ℝ in atTop, (1/4 : ℝ) ≤ blockVariance X ∧ blockVariance X ≤ 3/4 := by
  filter_upwards [blockVariance_tendsto.eventually_const_lt (by norm_num : (1/4 : ℝ)<1/2),
    blockVariance_tendsto.eventually_lt_const (by norm_num : (1/2 : ℝ)<3/4)] with X h1 h2
  exact ⟨h1.le,h2.le⟩

theorem source_blockVariance {x : ℝ} (hx : 0 ≤ x) (l : ℕ) :
    rangeVariance (primeBlock x l) = blockVariance (blockUpper x l) := by
  rw [primeBlock_eq_upperBlock hx]
  rfl

end NField.Alignment.HarperPrimeBlockVariance
