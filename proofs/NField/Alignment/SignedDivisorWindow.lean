/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.DivisorWindowCount

/-! # The literal signed-displacement divisor count -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SignedDivisorWindow
open scoped BigOperators Classical
open DivisorWindowCount

def signedDisplacements (C : ℕ) : Finset ℤ := (Finset.Icc (-(C:ℤ)) (C:ℤ)).erase 0

def signedDivisorCount (p C : ℕ) : ℝ :=
  ∑ c ∈ signedDisplacements C, ((((p:ℤ)^2-c).toNat).divisors.card : ℝ)

theorem signed_displacement_mem {C : ℕ} {c : ℤ} :
    c∈signedDisplacements C ↔ 1≤c.natAbs ∧ c.natAbs≤C := by
  simp only [signedDisplacements,Finset.mem_erase,Finset.mem_Icc]
  have h := Int.natCast_natAbs c
  have hzero := @Int.natAbs_eq_zero c
  have habs := abs_le (a := c) (b := (C:ℤ))
  omega

theorem signed_divisor_count_le_window {p C : ℕ} (hp : 2≤p) (hhalf : 2*C≤p) :
    signedDivisorCount p C ≤
      ∑ n ∈ Finset.Icc (p^2-C) (p^2+C), (n.divisors.card : ℝ) := by
  let f : ℤ→ℕ := fun c => ((p:ℤ)^2-c).toNat
  have hCsq : C<p^2 := by nlinarith
  have hmap (c : ℤ) (hc : c∈signedDisplacements C) :
      f c∈Finset.Icc (p^2-C) (p^2+C) := by
    have hi := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hc)
    have hpcast : (p:ℤ)^2=(p^2:ℕ) := by norm_cast
    have hnonneg : 0≤(p:ℤ)^2-c := by omega
    have he := Int.toNat_of_nonneg hnonneg
    simp only [f,Finset.mem_Icc]
    omega
  have hinj : Set.InjOn f (signedDisplacements C) := by
    intro c hc d hd he
    have hcI := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hc)
    have hdI := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hd)
    have hpcast : (p:ℤ)^2=(p^2:ℕ) := by norm_cast
    have hc0 : 0≤(p:ℤ)^2-c := by omega
    have hd0 : 0≤(p:ℤ)^2-d := by omega
    have hcE := Int.toNat_of_nonneg hc0
    have hdE := Int.toNat_of_nonneg hd0
    dsimp [f] at he
    omega
  unfold signedDivisorCount
  change (∑ c ∈ signedDisplacements C, ((f c).divisors.card : ℝ))≤_
  have he : (∑ c ∈ signedDisplacements C, ((f c).divisors.card : ℝ)) =
      ∑ n ∈ (signedDisplacements C).image f, (n.divisors.card : ℝ) :=
    (Finset.sum_image (f := fun n : ℕ => (n.divisors.card : ℝ)) hinj).symm
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hn
    exact hmap c hc
  · intro n hn hn'
    positivity

/-- Title: `Signed-displacement divisor count`. -/
theorem signed_divisor_window_bound {p C : ℕ} (hp : p.Prime) (hC : 1≤C)
    (hhalf : 2*C≤p) :
    signedDivisorCount p C ≤
      5000*((C:ℝ)*Real.log (2*p)+Real.rpow p (2/3:ℝ)*Real.log (2*p)) :=
  (signed_divisor_count_le_window hp.two_le hhalf).trans
    (prime_square_divisor_window_bound hp hC hhalf)

end NField.Alignment.SignedDivisorWindow
