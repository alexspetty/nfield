/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeRefinement
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Primitive-pair representation of every amplitude

The coordinates are the actual positive pair addresses. Symmetry of each
finite sum gives twice the selected mass. Nonnegative partition summation
then proves the infinite representation and its absolute convergence.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimitivePairAmplitude

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionMassReadout CollisionJordanVariance
open CollisionAmplitudeArithmetic CollisionHarmonicSeed SecondaryCapacityLedger

def primitivePairMass (p : ℕ×ℕ) : ℝ :=
  if p.1.Coprime p.2 then 1/((p.1 : ℝ)*(p.2 : ℝ)*(p.1+p.2 : ℕ)) else 0

@[simp] theorem primitivePairMass_zero_left (n : ℕ) : primitivePairMass (0,n)=0 := by
  simp [primitivePairMass]

@[simp] theorem primitivePairMass_zero_right (n : ℕ) : primitivePairMass (n,0)=0 := by
  simp [primitivePairMass]

theorem primitivePairMass_nonneg (p : ℕ×ℕ) : 0≤primitivePairMass p := by
  unfold primitivePairMass
  split_ifs <;> positivity

theorem reduced_reflected_harmonic (n : ℕ) :
    (∑ a ∈ Finset.Ico 1 n, if a.Coprime n then (((n-a : ℕ) : ℝ))⁻¹ else 0)=
      reducedHarmonicStar n := by
  unfold reducedHarmonicStar
  rw [Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => n-a)
  · intro a ha
    simp only [Finset.mem_Ico] at ha ⊢
    omega
  · intro a ha b hb h
    simp only [Finset.mem_Ico] at ha hb
    omega
  · intro b hb
    refine ⟨n-b, ?_, ?_⟩
    · simp only [Finset.mem_Ico] at hb ⊢; omega
    · have := Finset.mem_Ico.mp hb; omega
  · intro a ha
    have hal := (Finset.mem_Ico.mp ha).2.le
    have he : (n-a).Coprime n ↔ a.Coprime n := by
      exact Nat.coprime_self_sub_left hal
    simp only [he]

theorem primitivePairMass_split {n a : ℕ} (ha : a∈Finset.Ico 1 n) :
    primitivePairMass (a,n-a)=
      ((if a.Coprime n then (a : ℝ)⁻¹ else 0)+
       (if a.Coprime n then (((n-a : ℕ) : ℝ))⁻¹ else 0))/(n : ℝ)^2 := by
  have ha' := Finset.mem_Ico.mp ha
  have haR : (a : ℝ)≠0 := by exact_mod_cast (by omega : a≠0)
  have hnR : (n : ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hbR : (((n-a : ℕ) : ℝ))≠0 := by exact_mod_cast (by omega : n-a≠0)
  have he : (a : ℝ)+(((n-a : ℕ) : ℝ))=(n : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le ha'.2.le
  unfold primitivePairMass
  simp only [Nat.coprime_sub_self_right ha'.2.le, Nat.add_sub_of_le ha'.2.le]
  split_ifs
  · field_simp
    nlinarith
  · simp

theorem primitivePairMass_antidiagonal (n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, primitivePairMass p)=2*collisionWeight n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have he : (∑ a ∈ Finset.Ico 1 n, primitivePairMass (a,n-a))=
      ∑ a ∈ Finset.range n.succ, primitivePairMass (a,n-a) := by
    apply Finset.sum_subset
    · intro a ha
      have := Finset.mem_Ico.mp ha
      exact Finset.mem_range.mpr (by omega)
    · intro a ha hn
      have ha' := Finset.mem_range.mp ha
      have he : a=0 ∨ a=n := by
        simp only [Finset.mem_Ico] at hn
        omega
      rcases he with he|he <;> simp [he]
  rw [← he]
  calc
    _ = (∑ a ∈ Finset.Ico 1 n, (
        (if a.Coprime n then (a : ℝ)⁻¹ else 0)+
        (if a.Coprime n then (((n-a : ℕ) : ℝ))⁻¹ else 0)))/(n : ℝ)^2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun a ha => primitivePairMass_split ha)
    _ = _ := by
      rw [Finset.sum_add_distrib, reduced_reflected_harmonic,
        ← Finset.sum_filter]
      change (reducedHarmonicStar n+reducedHarmonicStar n)/(n : ℝ)^2=
        2*(reducedHarmonicStar n/(n : ℝ)^2)
      ring

theorem addition_fiber_sum (f : ℕ×ℕ → ℝ) (n : ℕ) :
    (∑' p : (fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n}, f p.val)=
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p := by
  rw [tsum_subtype ((fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n}) f]
  rw [tsum_eq_sum (s := Finset.HasAntidiagonal.antidiagonal n) (fun p hp =>
    Set.indicator_of_notMem (show p∉(fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n} from
      fun h => hp (Finset.HasAntidiagonal.mem_antidiagonal.mpr h)) f)]
  apply Finset.sum_congr rfl
  intro p hp
  exact Set.indicator_of_mem
    (show p∈(fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n} from Finset.HasAntidiagonal.mem_antidiagonal.mp hp) f

theorem addition_fiber_summable (f : ℕ×ℕ → ℝ) (n : ℕ) :
    Summable (fun p : (fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n} => f p.val) := by
  have hf : ((fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n}).Finite := by
    convert! (Finset.HasAntidiagonal.antidiagonal n).finite_toSet using 1
    ext p
    simp
  letI := hf.fintype
  exact summable_of_hasFiniteSupport (Set.toFinite _)

theorem primitivePairMass_summable : Summable primitivePairMass := by
  apply (summable_partition primitivePairMass_nonneg
    (s := fun n => (fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n})
    (fun p => ⟨p.1+p.2,rfl,fun _ h => h.symm⟩)).mpr
  refine ⟨addition_fiber_summable primitivePairMass, ?_⟩
  simpa only [addition_fiber_sum, primitivePairMass_antidiagonal] using
    collisionWeight_summable.mul_left 2

def primitivePairGate (q : ℕ) (p : ℕ×ℕ) : ℝ :=
  if q∣p.1+p.2 then primitivePairMass p else 0

theorem primitivePairGate_summable (q : ℕ) : Summable (primitivePairGate q) := by
  apply Summable.of_nonneg_of_le _ _ primitivePairMass_summable
  · intro p; unfold primitivePairGate; split_ifs <;> simp [primitivePairMass_nonneg]
  · intro p; unfold primitivePairGate; split_ifs <;> simp [primitivePairMass_nonneg]

theorem primitivePairGate_fiber (q n : ℕ) :
    (∑' p : (fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n}, primitivePairGate q p.val)=
      2*(if q∣n then collisionWeight n else 0) := by
  have he : (fun p : (fun p : ℕ×ℕ => p.1+p.2) ⁻¹' {n} => primitivePairGate q p.val)=
      fun p => if q∣n then primitivePairMass p.val else 0 := by
    funext p
    unfold primitivePairGate
    rw [show p.val.1+p.val.2=n from p.property]
  rw [he]
  split_ifs
  · rw [addition_fiber_sum, primitivePairMass_antidiagonal]
  · simp only [tsum_zero, mul_zero]

theorem amplitude_primitive_pair (q : ℕ) :
    amplitude q=(1/2 : ℝ)*∑' p, primitivePairGate q p := by
  have hf := (primitivePairGate_summable q).hasSum.tsum_fiberwise
    (fun p : ℕ×ℕ => p.1+p.2)
  simp_rw [primitivePairGate_fiber] at hf
  have he := hf.tsum_eq
  rw [tsum_mul_left] at he
  change 2*amplitude q=∑' p, primitivePairGate q p at he
  linarith

theorem primitivePairGate_positive_series (q : ℕ) :
    (∑' p : ℕ×ℕ, primitivePairGate q (p.1+1,p.2+1))=∑' p, primitivePairGate q p := by
  apply (show Function.Injective (fun p : ℕ×ℕ => (p.1+1,p.2+1)) from by
    intro a b h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp at h1 h2
    exact Prod.ext (by omega) (by omega)).tsum_eq
  intro p hp
  have hp1 : 0<p.1 := by
    by_contra h
    have : p.1=0 := by omega
    simp [Function.mem_support, primitivePairGate, primitivePairMass, this] at hp
  have hp2 : 0<p.2 := by
    by_contra h
    have : p.2=0 := by omega
    simp [Function.mem_support, primitivePairGate, primitivePairMass, this] at hp
  exact ⟨(p.1-1,p.2-1), Prod.ext (by dsimp; omega) (by dsimp; omega)⟩

theorem amplitude_positive_primitive_pair (q : ℕ) :
    amplitude q=(1/2 : ℝ)*∑' p : ℕ×ℕ,
      if (p.1+1).Coprime (p.2+1) ∧ q∣(p.1+1)+(p.2+1) then
        1/(((p.1+1 : ℕ) : ℝ)*((p.2+1 : ℕ) : ℝ)*((p.1+1+p.2+1 : ℕ) : ℝ)) else 0 := by
  rw [amplitude_primitive_pair, ← primitivePairGate_positive_series]
  congr 1
  apply tsum_congr
  intro p
  unfold primitivePairGate primitivePairMass
  by_cases hc : (p.1+1).Coprime (p.2+1) <;>
    by_cases hd : q∣(p.1+1)+(p.2+1) <;> simp only [hc,hd,ite_true,ite_false,and_true,and_false]
  simp only [Nat.add_assoc]

end NField.Alignment.CollisionPrimitivePairAmplitude
