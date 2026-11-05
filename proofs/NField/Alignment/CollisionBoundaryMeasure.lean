/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionRampEnergy
import NField.Alignment.CollisionReciprocalBudget

/-!
# Boundary source and weak derivative

Finite sums of actual Dirac measures retain every rational jump address.
The response derivative is tested against periodic continuously
differentiable functions on the unit interval.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionBoundaryMeasure

open scoped BigOperators Classical
open MeasureTheory CollisionRampEnergy CollisionRemainderDynamics

def sourceRow (r : ℕ) : Measure ℝ :=
  ∑ j ∈ Finset.range r, Measure.dirac ((j : ℝ)/(r : ℝ))

def boundaryMeasure (N : ℕ) : Measure ℝ :=
  ∑ r ∈ Finset.Icc 1 N, sourceRow r

theorem sourceRow_integrable (r : ℕ) (φ : ℝ → ℝ) : Integrable φ (sourceRow r) := by
  apply integrable_finsetSum_measure.mpr
  intro j _
  exact integrable_dirac (by simp)

theorem sourceRow_integral (r : ℕ) (φ : ℝ → ℝ) :
    (∫ x, φ x ∂sourceRow r) = ∑ j ∈ Finset.range r, φ ((j : ℝ)/(r : ℝ)) := by
  rw [sourceRow, integral_finsetSum_measure (fun j _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem boundaryMeasure_integral (N : ℕ) (φ : ℝ → ℝ) :
    (∫ x, φ x ∂boundaryMeasure N) =
      ∑ r ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range r, φ ((j : ℝ)/(r : ℝ)) := by
  rw [boundaryMeasure, integral_finsetSum_measure (fun r _ => sourceRow_integrable r φ)]
  simp only [sourceRow_integral]

theorem affine_test_cell {r : ℕ} (_hr : 0 < r) (j : ℕ)
    (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hc : Continuous φ') :
    (1/(r : ℝ)) * (∫ t in (0 : ℝ)..1, (t-1/2)*φ' (((j : ℝ)+t)/(r : ℝ))) =
      (φ (((j : ℝ)+1)/(r : ℝ))+φ ((j : ℝ)/(r : ℝ)))/2 -
        ∫ t in (0 : ℝ)..1, φ (((j : ℝ)+t)/(r : ℝ)) := by
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  let ψ : ℝ → ℝ := fun t => φ (((j : ℝ)+t)/(r : ℝ))
  let ψ' : ℝ → ℝ := fun t => φ' (((j : ℝ)+t)/(r : ℝ))/(r : ℝ)
  have hdψ (t : ℝ) : HasDerivAt ψ (ψ' t) t := by
    convert! (hφ (((j : ℝ)+t)/(r : ℝ))).comp t
      (((hasDerivAt_id t).const_add (j : ℝ)).div_const (r : ℝ)) using 1
    simp [ψ', div_eq_mul_inv]
  have hcψ : Continuous ψ := by dsimp [ψ]; fun_prop
  have hcψ' : Continuous ψ' := by dsimp [ψ']; fun_prop
  have hd (t : ℝ) : HasDerivAt (fun t => (t-1/2)*ψ t)
      (ψ t+(t-1/2)*ψ' t) t := by
    convert! ((hasDerivAt_id t).sub_const (1/2 : ℝ)).mul (hdψ t) using 1
    simp
  have hiψ : IntervalIntegrable ψ volume 0 1 := hcψ.intervalIntegrable 0 1
  have hiprod : IntervalIntegrable (fun t => (t-1/2)*ψ' t) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hiψ.add hiprod)
  rw [intervalIntegral.integral_add hiψ hiprod] at hftc
  have hfactor : (∫ t in (0 : ℝ)..1, (t-1/2)*ψ' t) =
      (1/(r : ℝ))*(∫ t in (0 : ℝ)..1, (t-1/2)*φ' (((j : ℝ)+t)/(r : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [ψ']
    ring
  rw [hfactor] at hftc
  dsimp [ψ] at hftc ⊢
  simp only [add_zero] at hftc
  linarith

theorem cyclic_address_sum {r : ℕ} (hr : 0 < r) (φ : ℝ → ℝ)
    (hper : φ 1 = φ 0) :
    (∑ j ∈ Finset.range r, φ (((j : ℝ)+1)/(r : ℝ))) =
      ∑ j ∈ Finset.range r, φ ((j : ℝ)/(r : ℝ)) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he := Finset.sum_range_succ (fun j : ℕ => φ ((j : ℝ)/(r : ℝ))) r
  rw [Finset.sum_range_succ'] at he
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hrR, hper] at he
  linarith

theorem affineRow_weak_derivative {r : ℕ} (hr : 0 < r)
    (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hc : Continuous φ') (hper : φ 1 = φ 0) :
    (∫ x in (0 : ℝ)..1, affineRow r x*φ' x) =
      (∫ x, φ x ∂sourceRow r) - (r : ℝ)*(∫ x in (0 : ℝ)..1, φ x) := by
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  have hcell (j : ℕ) :
      (∫ t in (0 : ℝ)..1, affineRow r (((j : ℝ)+t)/(r : ℝ))*
        φ' (((j : ℝ)+t)/(r : ℝ))) =
      ∫ t in (0 : ℝ)..1, (t-1/2)*φ' (((j : ℝ)+t)/(r : ℝ)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have he := affineRow_on_cell hr (by norm_num : 0 < 1) j ht.1.le ht.2
    simpa [centeredRemainder, Nat.mod_one] using congrArg
      (fun z : ℝ => z*φ' (((j : ℝ)+t)/(r : ℝ))) he
  rw [integral_uniform_cells hr _
    (fun a b => (affineRow_intervalIntegrable r a b).mul_continuousOn hc.continuousOn)]
  simp only [hcell, Finset.mul_sum, affine_test_cell hr _ φ φ' hφ hc]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [cyclic_address_sum hr φ hper, sourceRow_integral]
  have hsum := integral_uniform_cells hr φ (fun a b => hcont.intervalIntegrable a b)
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : (r : ℝ)*(∫ x in (0 : ℝ)..1, φ x) =
      ∑ j ∈ Finset.range r, ∫ t in (0 : ℝ)..1, φ (((j : ℝ)+t)/(r : ℝ)) := by
    rw [hsum]
    field_simp
  rw [he]
  ring

theorem midpointRow_weak_derivative {r : ℕ} (hr : 0 < r)
    (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hc : Continuous φ') (hper : φ 1 = φ 0) :
    (∫ x in (0 : ℝ)..1, midpointRow r x*φ' x) =
      (∫ x, φ x ∂sourceRow r) - (r : ℝ)*(∫ x in (0 : ℝ)..1, φ x) := by
  calc
    _ = ∫ x in (0 : ℝ)..1, affineRow r x*φ' x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [midpointRow_ae_affineRow hr] with x hx
      exact fun _ => congrArg (fun y => y*φ' x) hx
    _ = _ := affineRow_weak_derivative hr φ φ' hφ hc hper

theorem sum_positive_indices (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 N, (r : ℝ)) = (N : ℝ)*((N : ℝ)+1)/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1), ih]
    push_cast
    ring

theorem boundaryResponse_weak_derivative (N : ℕ)
    (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hc : Continuous φ') (hper : φ 1 = φ 0) :
    -(∫ x in (0 : ℝ)..1, boundaryResponse N x*φ' x) =
      (N : ℝ)*((N : ℝ)+1)*(∫ x in (0 : ℝ)..1, φ x) -
        2*(∫ x, φ x ∂boundaryMeasure N) := by
  have hi (r : ℕ) (hr : r ∈ Finset.Icc 1 N) :
      IntervalIntegrable (fun x => midpointRow r x*φ' x) volume 0 1 :=
    (midpointRow_intervalIntegrable (Finset.mem_Icc.mp hr).1 0 1).mul_continuousOn hc.continuousOn
  simp only [boundaryResponse, mul_assoc, Finset.sum_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hi]
  have he : (∑ r ∈ Finset.Icc 1 N, ∫ x in (0 : ℝ)..1, midpointRow r x*φ' x) =
      (∫ x, φ x ∂boundaryMeasure N) -
        ((N : ℝ)*((N : ℝ)+1)/2)*(∫ x in (0 : ℝ)..1, φ x) := by
    calc
      _ = ∑ r ∈ Finset.Icc 1 N,
          ((∫ x, φ x ∂sourceRow r) - (r : ℝ)*(∫ x in (0 : ℝ)..1, φ x)) :=
        Finset.sum_congr rfl (fun r hr =>
          midpointRow_weak_derivative (Finset.mem_Icc.mp hr).1 φ φ' hφ hc hper)
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_positive_indices,
          boundaryMeasure, integral_finsetSum_measure (fun r _ => sourceRow_integrable r φ)]
  rw [he]
  ring

def positivePrimitiveRow (k : ℕ) : Measure ℝ :=
  ∑ a ∈ (Finset.Ico 1 k).filter (fun a => a.Coprime k),
    Measure.dirac ((a : ℝ)/(k : ℝ))

def primitiveSourceRow (k : ℕ) : Measure ℝ :=
  ∑ a ∈ (Finset.range k).filter (fun a => a.Coprime k),
    Measure.dirac ((a : ℝ)/(k : ℝ))

theorem primitiveSourceRow_split (k : ℕ) :
    primitiveSourceRow k =
      (if k=1 then Measure.dirac 0 else 0) + positivePrimitiveRow k := by
  by_cases hk : k=1
  · subst k
    simp [primitiveSourceRow, positivePrimitiveRow]
  · have hf : (Finset.range k).filter (fun a => a.Coprime k) =
        (Finset.Ico 1 k).filter (fun a => a.Coprime k) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · intro ha
        have hap : 0 < a := by
          by_contra h
          have haz : a=0 := by omega
          simpa [haz, hk] using ha.2
        exact ⟨⟨hap, ha.1⟩, ha.2⟩
      · exact fun ha => ⟨ha.1.2, ha.2⟩
    simp only [primitiveSourceRow, hf, positivePrimitiveRow, hk, if_false, zero_add]

theorem sourceRow_primitive_divisors {r : ℕ} (hr : 0 < r) :
    sourceRow r = ∑ k ∈ r.divisors, primitiveSourceRow k := by
  open CollisionReciprocalBudget in
  have hpos : (∑ a ∈ Finset.Ico 1 r, Measure.dirac ((a : ℝ)/(r : ℝ))) =
      ∑ p ∈ primitiveAddresses r, Measure.dirac ((p.2 : ℝ)/(p.1 : ℝ)) := by
    apply Finset.sum_bij (fun a _ => reducedAddress r a)
    · intro a ha; exact reducedAddress_mem ha
    · intro a ha b hb he
      have hh := congrArg (fun p : Σ _ : ℕ, ℕ => (r/p.1)*p.2) he
      simpa only [reducedAddress_restore ha, reducedAddress_restore hb] using hh
    · intro p hp
      exact ⟨(r/p.1)*p.2, (primitiveAddress_restore p hp).1, (primitiveAddress_restore p hp).2⟩
    · intro a ha
      have hap := (Finset.mem_Ico.mp ha).1
      have hg : 0 < a.gcd r := Nat.gcd_pos_of_pos_left r hap
      have hgR : (a.gcd r : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
      congr 1
      simp only [reducedAddress]
      rw [Nat.cast_div (Nat.gcd_dvd_left a r) hgR,
        Nat.cast_div (Nat.gcd_dvd_right a r) hgR]
      field_simp
  have hsplit : Finset.range r = insert 0 (Finset.Ico 1 r) := by
    ext a
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hone : (1 : ℕ) ∈ r.divisors := Nat.mem_divisors.mpr ⟨one_dvd r, hr.ne'⟩
  rw [sourceRow, hsplit, Finset.sum_insert (by simp), Nat.cast_zero, zero_div, hpos]
  simp only [primitiveSourceRow_split, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' r.divisors 1]
  simp only [hone, if_true]
  congr 1
  simp only [CollisionReciprocalBudget.primitiveAddresses, Finset.sum_sigma, positivePrimitiveRow]

theorem multiples_Icc_card (N k : ℕ) :
    ((Finset.Icc 1 N).filter (fun r => k ∣ r)).card = N/k := by
  have hs : (Finset.Icc 1 N).filter (fun r => k ∣ r) =
      (Finset.range (N+1)).filter (fun r => r ≠ 0 ∧ k ∣ r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hs]
  exact Nat.card_multiples' N k

theorem boundaryMeasure_primitive (N : ℕ) :
    boundaryMeasure N =
      ∑ k ∈ Finset.Icc 1 N, (N/k) • primitiveSourceRow k := by
  have hrow (r : ℕ) (hr : r ∈ Finset.Icc 1 N) :
      sourceRow r = ∑ k ∈ Finset.Icc 1 N, if k ∣ r then primitiveSourceRow k else 0 := by
    rw [sourceRow_primitive_divisors (Finset.mem_Icc.mp hr).1]
    have he : r.divisors = (Finset.Icc 1 N).filter (fun k => k ∣ r) := by
      ext k
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro hk
        exact ⟨⟨Nat.pos_of_dvd_of_pos hk.1 (Finset.mem_Icc.mp hr).1,
          (Nat.le_of_dvd (Finset.mem_Icc.mp hr).1 hk.1).trans (Finset.mem_Icc.mp hr).2⟩, hk.1⟩
      · exact fun hk => ⟨hk.2, by have := (Finset.mem_Icc.mp hr).1; omega⟩
    rw [he, Finset.sum_filter]
  rw [boundaryMeasure, Finset.sum_congr rfl hrow, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_filter, Finset.sum_const, multiples_Icc_card]

theorem boundary_energy_completed (N : ℕ) :
    (∫ x in (0 : ℝ)..1, boundaryResponse N x^2) = (N : ℝ)/3 + (2/3 : ℝ)*
      ∑' k, collisionWeight k*(k : ℝ)*((N/k : ℕ) : ℝ) :=
  (boundaryResponse_energy N).trans (CollisionResolutionLaw.completedCapacity_tsum N)

theorem boundary_energy_readout (N : ℕ) :
    (N : ℝ)-(∫ x in (0 : ℝ)..1, boundaryResponse N x^2) =
      (2/3 : ℝ)*∑' k, collisionWeight k*((N%k : ℕ) : ℝ) := by
  rw [boundaryResponse_energy]
  exact (CollisionMassReadout.deficit_eq_capacity N).symm

theorem boundary_energy_increment {N : ℕ} (hN : 0 < N) :
    ((N : ℝ)-(∫ x in (0 : ℝ)..1, boundaryResponse N x^2)) -
        (((N-1 : ℕ) : ℝ)-(∫ x in (0 : ℝ)..1, boundaryResponse (N-1) x^2)) =
      (2/3 : ℝ)*(1-∑ k ∈ N.divisors, (k : ℝ)*collisionWeight k) := by
  simp only [boundaryResponse_energy, ← CollisionMassReadout.deficit_eq_capacity]
  simpa only [Nat.sub_add_cancel hN] using CollisionResolutionLaw.deficit_reset (N-1)

theorem boundary_energy_coefficients_unique (v : ℕ → ℝ) (hv1 : v 1 = 0)
    (hv : ∀ N, CollisionResolutionLaw.completedCapacity v N =
      ∫ x in (0 : ℝ)..1, boundaryResponse N x^2) :
    ∀ k, 1 ≤ k → v k=collisionWeight k := by
  apply CollisionResolutionLaw.completedCapacity_injective v hv1
  exact fun N => (hv N).trans (boundaryResponse_energy N)

/-- The complete positive-mass/readout result, with the actual continuous
response and its primitive rational source retained in the statement. -/
theorem boundary_selection_and_readout :
    (∀ k, 2 ≤ k → 0 < collisionWeight k) ∧
    HasSum collisionWeight 1 ∧
    Asymptotics.IsBigO Filter.atTop collisionWeight
      (fun k : ℕ => Real.log (2*(k : ℝ))/(k : ℝ)^2) ∧
    (∀ N : ℕ, boundaryMeasure N = ∑ k ∈ Finset.Icc 1 N, (N/k) • primitiveSourceRow k) ∧
    (∀ N : ℕ, (∫ x in (0 : ℝ)..1, boundaryResponse N x) = 0) ∧
    (∀ (N : ℕ) (φ φ' : ℝ → ℝ), (∀ x, HasDerivAt φ (φ' x) x) →
      Continuous φ' → φ 1=φ 0 →
      -(∫ x in (0 : ℝ)..1, boundaryResponse N x*φ' x) =
        (N : ℝ)*((N : ℝ)+1)*(∫ x in (0 : ℝ)..1, φ x) -
          2*(∫ x, φ x ∂boundaryMeasure N)) ∧
    (∀ N : ℕ, (∫ x in (0 : ℝ)..1, boundaryResponse N x^2) = (N : ℝ)/3+(2/3 : ℝ)*
      ∑' k, collisionWeight k*(k : ℝ)*((N/k : ℕ) : ℝ)) ∧
    (∀ N : ℕ, (N : ℝ)-(∫ x in (0 : ℝ)..1, boundaryResponse N x^2) =
      (2/3 : ℝ)*∑' k, collisionWeight k*((N%k : ℕ) : ℝ)) ∧
    (∀ N : ℕ, 0 < N →
      ((N : ℝ)-(∫ x in (0 : ℝ)..1, boundaryResponse N x^2)) -
        (((N-1 : ℕ) : ℝ)-(∫ x in (0 : ℝ)..1, boundaryResponse (N-1) x^2)) =
      (2/3 : ℝ)*(1-∑ k ∈ N.divisors, (k : ℝ)*collisionWeight k)) ∧
    (∀ v : ℕ → ℝ, v 1=0 →
      (∀ N, CollisionResolutionLaw.completedCapacity v N =
        ∫ x in (0 : ℝ)..1, boundaryResponse N x^2) →
      ∀ k, 1 ≤ k → v k=collisionWeight k) :=
  ⟨fun _ hk => collisionWeight_pos hk, CollisionMassReadout.collisionWeight_hasSum,
    CollisionMassReadout.collisionWeight_isBigO_log_div_sq, boundaryMeasure_primitive,
    boundaryResponse_mean_zero, boundaryResponse_weak_derivative, boundary_energy_completed,
    boundary_energy_readout, fun _ hN => boundary_energy_increment hN,
    boundary_energy_coefficients_unique⟩

end NField.Alignment.CollisionBoundaryMeasure
