/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeArithmetic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Positive harmonic seeds for exact amplitude refinement

The reciprocal-cube constant is identified with the actual zeta value.
Absolute summability precedes the divisor-fiber reindexing.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionHarmonicSeed

open scoped BigOperators Classical
open Filter
open CollisionRemainderDynamics CollisionMassReadout CollisionAmplitudeArithmetic

def cubeKernel (n : ℕ) : ℝ := 1/(n : ℝ)^3
def zetaThree : ℝ := ∑' n, cubeKernel n

@[simp] theorem cubeKernel_zero : cubeKernel 0=0 := by simp [cubeKernel]
@[simp] theorem cubeKernel_one : cubeKernel 1=1 := by norm_num [cubeKernel]

theorem cubeKernel_nonneg (n : ℕ) : 0≤cubeKernel n := by unfold cubeKernel; positivity

theorem cubeKernel_summable : Summable cubeKernel := by
  unfold cubeKernel
  simp only [one_div]
  exact Real.summable_nat_pow_inv.mpr (by norm_num : 1<(3 : ℕ))

theorem zetaThree_pos : 0<zetaThree := by
  have h := cubeKernel_summable.le_tsum 1 (fun n _ => cubeKernel_nonneg n)
  rw [cubeKernel_one] at h
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) h

theorem zetaThree_eq_riemannZeta : (zetaThree : ℂ)=riemannZeta 3 := by
  have hz := zeta_nat_eq_tsum_of_gt_one (by norm_num : 1<(3 : ℕ))
  norm_num only [Nat.cast_ofNat] at hz
  rw [zetaThree, Complex.ofReal_tsum, hz]
  apply tsum_congr
  intro n
  simp [cubeKernel]

theorem divisor_product_fiber (f g : ℕ → ℝ) (hf : f 0=0) (hg : g 0=0) (n : ℕ) :
    (∑' p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}, f p.val.1*g p.val.2) =
      ∑ d ∈ n.divisors, f d*g (n/d) := by
  by_cases hn : n=0
  · subst n
    simp only [Nat.divisors_zero, Finset.sum_empty]
    have hz : (fun p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {0} => f p.val.1*g p.val.2)=0 := by
      funext p
      have hp : p.val.1*p.val.2=0 := p.property
      rcases Nat.mul_eq_zero.mp hp with hp|hp
      · simp only [hp, hf, zero_mul, Pi.zero_apply]
      · simp only [hp, hg, mul_zero, Pi.zero_apply]
    rw [hz]
    exact tsum_zero
  rw [tsum_subtype ((fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}) (fun p => f p.1*g p.2)]
  have he (p : ℕ×ℕ) (hp : p∉n.divisorsAntidiagonal) :
      ((fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}).indicator (fun p => f p.1*g p.2) p=0 := by
    apply Set.indicator_of_notMem
    intro hm
    exact hp (Nat.mem_divisorsAntidiagonal.mpr ⟨hm,hn⟩)
  rw [tsum_eq_sum he]
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal, f p.1*g p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Set.indicator_of_mem
        (show p∈(fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n} from
          (Nat.mem_divisorsAntidiagonal.mp hp).1) _
    _ = _ := Nat.sum_divisorsAntidiagonal (fun a b => f a*g b)

def weightedCube (p : ℕ×ℕ) : ℝ := collisionWeight p.1*cubeKernel p.2

theorem weightedCube_nonneg (p : ℕ×ℕ) : 0≤weightedCube p :=
  mul_nonneg (collisionWeight_nonneg p.1) (cubeKernel_nonneg p.2)

theorem weightedCube_summable : Summable weightedCube := by
  have hs := collisionWeight_summable.mul_of_nonneg cubeKernel_summable
    collisionWeight_nonneg cubeKernel_nonneg
  convert! hs using 1

theorem weightedCube_fiber (n : ℕ) :
    (∑' p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}, weightedCube p.val)=harmonicKernel n := by
  unfold weightedCube
  rw [divisor_product_fiber collisionWeight cubeKernel (by simp) cubeKernel_zero]
  by_cases hn : n=0
  · simp [hn, harmonicKernel]
  rw [harmonicKernel_divisor n (Nat.pos_of_ne_zero hn)]
  apply Finset.sum_congr rfl
  intro d _
  simp only [cubeKernel, mul_one_div]

theorem harmonicKernel_hasSum : HasSum harmonicKernel zetaThree := by
  have hs := collisionWeight_hasSum.mul cubeKernel_summable.hasSum weightedCube_summable
  simp only [one_mul] at hs
  have hx : HasSum weightedCube zetaThree := by convert! hs using 1
  have hf := hx.tsum_fiberwise (fun p : ℕ×ℕ => p.1*p.2)
  convert! hf using 1
  funext n
  exact (weightedCube_fiber n).symm

theorem tsum_multiples {q : ℕ} (hq : 0<q) (f : ℕ → ℝ) :
    (∑' m, f (q*m))=∑' n, if q∣n then f n else 0 := by
  have hi : Function.Injective (fun m : ℕ => q*m) := fun a b h => Nat.mul_left_cancel hq h
  have hh := hi.tsum_eq (f := fun n => if q∣n then f n else 0) (by
    intro n hn
    by_cases hd : q∣n
    · rcases hd with ⟨m,hm⟩
      exact ⟨m,hm.symm⟩
    · simp [Function.mem_support, hd] at hn)
  simpa only [dvd_mul_right, if_true] using hh

def harmonicSeed (q : ℕ) : ℝ := ∑' m, harmonicKernel (q*m)

theorem harmonicSeed_summable {q : ℕ} (hq : 0<q) :
    Summable (fun m => harmonicKernel (q*m)) :=
  harmonicKernel_hasSum.summable.comp_injective (fun _ _ h => Nat.mul_left_cancel hq h)

theorem harmonicSeed_positive_series {q : ℕ} (hq : 0<q) :
    harmonicSeed q=∑' m, (harmonic (q*(m+1)-1) : ℝ)/((q*(m+1) : ℕ) : ℝ)^2 := by
  have he := (harmonicSeed_summable hq).sum_add_tsum_nat_add 1
  simpa [harmonicSeed, harmonicKernel] using he.symm

theorem harmonicSeed_one : harmonicSeed 1=zetaThree := by
  simpa [harmonicSeed] using harmonicKernel_hasSum.tsum_eq

def gatedCube (q : ℕ) (p : ℕ×ℕ) : ℝ :=
  if q∣p.1*p.2 then weightedCube p else 0

theorem gatedCube_summable (q : ℕ) : Summable (gatedCube q) := by
  apply Summable.of_nonneg_of_le _ _ weightedCube_summable
  · intro p; unfold gatedCube; split_ifs <;> simp [weightedCube_nonneg]
  · intro p; unfold gatedCube; split_ifs <;> simp [weightedCube_nonneg]

theorem gatedCube_fiber (q n : ℕ) :
    (∑' p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}, gatedCube q p.val)=
      if q∣n then harmonicKernel n else 0 := by
  have he : (fun p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n} => gatedCube q p.val)=
      fun p => if q∣n then weightedCube p.val else 0 := by
    funext p
    unfold gatedCube
    rw [show p.val.1*p.val.2=n from p.property]
  rw [he]
  split_ifs <;> simp only [weightedCube_fiber, tsum_zero]

theorem harmonicSeed_eq_gatedCube {q : ℕ} (hq : 0<q) :
    harmonicSeed q=∑' p, gatedCube q p := by
  have hf := (gatedCube_summable q).hasSum.tsum_fiberwise
    (fun p : ℕ×ℕ => p.1*p.2)
  simp_rw [gatedCube_fiber] at hf
  rw [harmonicSeed, tsum_multiples hq]
  exact hf.tsum_eq

theorem cubeKernel_mul (q m : ℕ) : cubeKernel (q*m)=cubeKernel q*cubeKernel m := by
  simp [cubeKernel, Nat.cast_mul, mul_pow, one_div, mul_inv_rev, mul_comm]

theorem cubeKernel_multiples {q : ℕ} (hq : 0<q) :
    (∑' m, if q∣m then cubeKernel m else 0)=cubeKernel q*zetaThree := by
  rw [← tsum_multiples hq]
  simp_rw [cubeKernel_mul]
  exact tsum_mul_left

theorem divides_product_iff_reduced {q : ℕ} (hq : 0<q) (d m : ℕ) :
    q∣d*m ↔ q/(q.gcd d)∣m := by
  have hg := Nat.gcd_pos_of_pos_left d hq
  have hc := Nat.coprime_div_gcd_div_gcd hg
  calc
    q∣d*m ↔ q/(q.gcd d)∣(d/(q.gcd d))*m := by
      rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left q d) hg,
        ← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right q d)]
    _ ↔ _ := hc.dvd_mul_left

theorem gatedCube_row {q : ℕ} (hq : 0<q) (d : ℕ) :
    (∑' m, gatedCube q (d,m))=collisionWeight d*cubeKernel (q/(q.gcd d))*zetaThree := by
  have he (m : ℕ) : gatedCube q (d,m)=collisionWeight d*
      (if q/(q.gcd d)∣m then cubeKernel m else 0) := by
    unfold gatedCube weightedCube
    simp only [divides_product_iff_reduced hq]
    split_ifs <;> simp
  simp_rw [he]
  rw [tsum_mul_left, cubeKernel_multiples]
  · ring
  · exact Nat.div_pos (Nat.gcd_le_left d hq) (Nat.gcd_pos_of_pos_left d hq)

theorem harmonicSeed_gcd_reduced {q : ℕ} (hq : 0<q) :
    harmonicSeed q=zetaThree*∑' d, collisionWeight d*cubeKernel (q/(q.gcd d)) := by
  rw [harmonicSeed_eq_gatedCube hq, (gatedCube_summable q).tsum_prod]
  simp_rw [gatedCube_row hq]
  rw [tsum_mul_right, mul_comm]

end NField.Alignment.CollisionHarmonicSeed
