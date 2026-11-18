/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Fibre
/-! # Continuous reconstruction from the complete fibre path

The affine cells cover the whole unit interval. Products are integrated
before any source specialization, so every mixed term remains present.
-/

noncomputable section

namespace NField.ResetForests.FibreReconstruction

open scoped BigOperators
open Filter MeasureTheory
open NField.Alignment CommonResetGram CollisionRampEnergy

theorem weighted_product_expansion (N : ℕ) (c e : ℕ → ℝ) (x : ℝ) :
    weightedProfile N c x*weightedProfile N e x=
      4*∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (c j*e k)*(midpointRow j x*midpointRow k x) := by
  unfold weightedProfile
  rw [show (2*(∑ j ∈ Finset.Icc 1 N, c j*midpointRow j x))*
      (2*(∑ k ∈ Finset.Icc 1 N, e k*midpointRow k x))=
      4*((∑ j ∈ Finset.Icc 1 N, c j*midpointRow j x)*
        (∑ k ∈ Finset.Icc 1 N, e k*midpointRow k x)) by ring]
  congr 1
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem weighted_product_interval_integrable (N : ℕ) (c e : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => weightedProfile N c x*weightedProfile N e x) volume a b := by
  have hint (j k : ℕ) (hj : j ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
      IntervalIntegrable (fun x => (c j*e k)*(midpointRow j x*midpointRow k x)) volume a b :=
    (midpointProduct_intervalIntegrable (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1 a b).const_mul _
  simp_rw [weighted_product_expansion]
  exact ⟨(integrable_finsetSum _ (fun j hj =>
      integrable_finsetSum _ (fun k hk => (hint j k hj hk).1))).const_mul 4,
    (integrable_finsetSum _ (fun j hj =>
      integrable_finsetSum _ (fun k hk => (hint j k hj hk).2))).const_mul 4⟩

theorem affine_cell_integrable {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) (v : ℝ) :
    IntervalIntegrable (fun u => f ((v+u)/(p : ℝ))) volume 0 1 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hs : IntervalIntegrable (fun u => f (u/(p : ℝ))) volume v (v+1) := by
    simpa [div_eq_mul_inv, hpR] using
      (hf (v/(p : ℝ)) ((v+1)/(p : ℝ))).comp_mul_right (c := (p : ℝ)⁻¹)
  simpa using hs.comp_add_left v

theorem affine_cell_integral {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ) (v : ℝ) :
    (∫ u in (0 : ℝ)..1, f ((v+u)/(p : ℝ)))=
      (p : ℝ)*(∫ x in v/(p : ℝ)..(v+1)/(p : ℝ), f x) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  calc
    _ = ∫ u in v..v+1, f (u/(p : ℝ)) := by
      simpa using intervalIntegral.integral_comp_add_left
        (fun u => f (u/(p : ℝ))) (a := (0 : ℝ)) (b := 1) v
    _ = _ := by rw [intervalIntegral.integral_comp_div f hpR]; rfl

theorem affine_fibre_sum_integrable {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun u => ∑ v : Fin p, f (((v.val : ℝ)+u)/(p : ℝ))) volume 0 1 :=
  ⟨integrable_finsetSum _ (fun v _ => (affine_cell_integrable hp f hf (v.val : ℝ)).1),
    integrable_finsetSum _ (fun v _ => (affine_cell_integrable hp f hf (v.val : ℝ)).2)⟩

theorem affine_fibre_sum_integral {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    (∫ u in (0 : ℝ)..1, ∑ v : Fin p, f (((v.val : ℝ)+u)/(p : ℝ)))=
      (p : ℝ)*(∫ x in (0 : ℝ)..1, f x) := by
  rw [intervalIntegral.integral_finsetSum (fun v _ => affine_cell_integrable hp f hf (v.val : ℝ))]
  simp_rw [affine_cell_integral hp]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun v : ℕ => ∫ x in (v : ℝ)/(p : ℝ)..((v : ℝ)+1)/(p : ℝ), f x) p]
  have hi := intervalIntegral.sum_integral_adjacent_intervals (n := p)
    (a := fun k : ℕ => (k : ℝ)/(p : ℝ)) (fun k _ => hf _ _)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Nat.cast_zero, zero_div, div_self hpR, Nat.cast_add, Nat.cast_one] at hi
  rw [hi]

theorem fibre_pair_interval_integrable {p : ℕ} (hp : p.Prime) (c e : ℕ → ℝ) :
    IntervalIntegrable (fibrePair p c e) volume 0 1 := by
  have hf := weighted_product_interval_integrable (p-1) c e
  have hs := affine_fibre_sum_integrable hp.pos
    (fun x => weightedProfile (p-1) c x*weightedProfile (p-1) e x) hf
  change IntervalIntegrable (fun u => fibrePair p c e u) volume 0 1
  simp_rw [fibre_pair_identity hp]
  exact hs.sub ((hf 0 1).div_const (p : ℝ))

theorem continuous_fibre_reconstruction {p : ℕ} (hp : p.Prime) (c e : ℕ → ℝ) :
    (∫ u in (0 : ℝ)..1, fibrePair p c e u)=
      ((p : ℝ)-(p : ℝ)⁻¹)*continuousWork (p-1) c e := by
  have hf := weighted_product_interval_integrable (p-1) c e
  have hs := affine_fibre_sum_integrable hp.pos
    (fun x => weightedProfile (p-1) c x*weightedProfile (p-1) e x) hf
  simp_rw [fibre_pair_identity hp]
  rw [intervalIntegral.integral_sub hs ((hf 0 1).div_const (p : ℝ)),
    affine_fibre_sum_integral hp.pos _ hf, intervalIntegral.integral_div]
  unfold continuousWork
  ring

end NField.ResetForests.FibreReconstruction
