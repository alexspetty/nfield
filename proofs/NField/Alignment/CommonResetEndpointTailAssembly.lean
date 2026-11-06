/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetEndpointTailRows
import NField.Alignment.CommonResetTailGrowth

/-! # All three endpoint tails with complete modulus multiplicity -/

noncomputable section

namespace NField.Alignment.CommonResetEndpointTailAssembly

open scoped BigOperators
open CommonResetEndpointTailRows CommonResetShiftedDeterminants CommonResetShiftedFibers
open CommonResetDivisorFibers CommonResetSmallConductors CommonResetTailGrowth

theorem fixed_phase_tail_bound {p u v : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hup : 2*u < p) (hv : 0 < v) (hvp : 2*v < p)
    (η : ℤ) (hη : η = 0 ∨ η = 1 ∨ η = -1)
    (S : Finset ℕ) (hS : ∀ t ∈ S, 2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*v < t ∧ u.Coprime t)
    (start : ℕ) (hs : 0 < start) (length : ℕ → ℕ) :
    |∑ t ∈ S, (harmonic ((p-1)/t) : ℝ)*phaseTail p t u v η start (length t)| ≤
      (p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/
        ((start : ℝ)*(u : ℝ)*(v : ℝ)) := by
  have hterm (t : ℕ) (htS : t ∈ S) :
      |(harmonic ((p-1)/t) : ℝ)*phaseTail p t u v η start (length t)| ≤
      ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(v : ℝ)))*
        centeredReciprocal (centeredEndpointPhase p v u t η) := by
    have htd := hS t htS
    have hb := phase_tail_bound hp htd.1 htd.2.1 hu htd.2.2.1 hv htd.2.2.2.1
      htd.2.2.2.2 η hη start (length t) hs
    have hH : (harmonic ((p-1)/t) : ℝ) ≤ (harmonic p : ℝ) :=
      harmonic_monotone ((Nat.div_le_self (p-1) t).trans (Nat.sub_le p 1))
    have htR : (t : ℝ)^2 ≤ (p : ℝ)^2 := by
      exact_mod_cast Nat.pow_le_pow_left htd.2.1.le 2
    rw [abs_mul, abs_of_nonneg (harmonic_nonneg _)]
    calc
      _ ≤ (harmonic p : ℝ)*(((t : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(v : ℝ)))*
          centeredReciprocal (centeredEndpointPhase p v u t η)) :=
        mul_le_mul hH hb (abs_nonneg _) (harmonic_nonneg _)
      _ ≤ (harmonic p : ℝ)*(((p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(v : ℝ)))*
          centeredReciprocal (centeredEndpointPhase p v u t η)) := by
        apply mul_le_mul_of_nonneg_left _ (harmonic_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (centeredReciprocal_nonneg _)
        exact div_le_div_of_nonneg_right htR (by positivity)
      _ = _ := by ring
  have hηabs : |η| ≤ 1 := by rcases hη with rfl|rfl|rfl <;> norm_num
  calc
    _ ≤ ∑ t ∈ S, |(harmonic ((p-1)/t) : ℝ)*phaseTail p t u v η start (length t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ S, ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(v : ℝ)))*
        centeredReciprocal (centeredEndpointPhase p v u t η) := Finset.sum_le_sum hterm
    _ = ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(v : ℝ)))*
        ∑ t ∈ S, centeredReciprocal (centeredEndpointPhase p v u t η) := by rw [Finset.mul_sum]
    _ ≤ ((harmonic p : ℝ)*(p : ℝ)^2/(2*(start : ℝ)*(u : ℝ)*(v : ℝ)))*
        (2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact shifted_fiber_bound hp.two_le hv hvp hup η hηabs S (fun t ht => by
          have hh := hS t ht
          exact ⟨by omega, hh.2.1, hh.2.2.2.2⟩)
      · exact div_nonneg (mul_nonneg (harmonic_nonneg _) (sq_nonneg _)) (by positivity)
    _ = _ := by ring

theorem rectangular_harmonic_bound (U V : ℕ) (f : ℕ → ℕ → ℝ) (C : ℝ)
    (hf : ∀ u ∈ Finset.Icc 1 U, ∀ v ∈ Finset.Icc 1 V,
      |f u v| ≤ C/((u : ℝ)*(v : ℝ))) :
    |∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V, f u v| ≤
      C*((harmonic U : ℝ)*(harmonic V : ℝ)) := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 U, |∑ v ∈ Finset.Icc 1 V, f u v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V, C/((u : ℝ)*(v : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v hv => hf u hu v hv))
    _ = _ := by
      rw [harmonic_eq_sum_Icc (n := U), harmonic_eq_sum_Icc (n := V)]
      push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring

def selectedPhaseTail (p U V start : ℕ) (η : ℤ) (S : ℕ → ℕ → Finset ℕ)
    (length : ℕ → ℕ → ℕ → ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V, ∑ t ∈ S u v,
    (harmonic ((p-1)/t) : ℝ)*phaseTail p t u v η start (length u v t)

theorem selected_phase_tail_bound {p : ℕ} (hp : p.Prime)
    (U V start : ℕ) (hU : 2*U < p) (hV : 2*V < p) (hs : 0 < start)
    (η : ℤ) (hη : η = 0 ∨ η = 1 ∨ η = -1)
    (S : ℕ → ℕ → Finset ℕ) (length : ℕ → ℕ → ℕ → ℕ)
    (hS : ∀ u ∈ Finset.Icc 1 U, ∀ v ∈ Finset.Icc 1 V, ∀ t ∈ S u v,
      2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*v < t ∧ u.Coprime t) :
    |selectedPhaseTail p U V start η S length| ≤
      (p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^4/(start : ℝ) := by
  have hb := rectangular_harmonic_bound U V
    (fun u v => ∑ t ∈ S u v, (harmonic ((p-1)/t) : ℝ)*phaseTail p t u v η start (length u v t))
    ((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/(start : ℝ))
    (fun u hu v hv => by
      have hud := Finset.mem_Icc.mp hu
      have hvd := Finset.mem_Icc.mp hv
      have hh := fixed_phase_tail_bound hp hud.1 (by omega) hvd.1 (by omega) η hη
        (S u v) (hS u hu v hv) start hs (length u v)
      convert hh using 1 <;> ring)
  have hH : (harmonic U : ℝ)*(harmonic V : ℝ) ≤ (harmonic p : ℝ)^2 := by
    simpa only [pow_two] using mul_le_mul (harmonic_monotone (by omega : U ≤ p))
      (harmonic_monotone (by omega : V ≤ p)) (harmonic_nonneg V) (harmonic_nonneg p)
  calc
    _ ≤ ((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/(start : ℝ))*
        ((harmonic U : ℝ)*(harmonic V : ℝ)) := hb
    _ ≤ ((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^2/(start : ℝ))*
        (harmonic p : ℝ)^2 := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = _ := by ring

def naturalEndpointTail (p t u v start length : ℕ) : ℝ :=
  if ht : 0 < t then
    letI : NeZero t := ⟨ht.ne'⟩
    if hu : u.Coprime t then
      endpointTail (p-1) (p^2) (ZMod.unitOfCoprime u hu) (v : ZMod t) start length
    else 0
  else 0

theorem naturalEndpointTail_three_phases {p t u v : ℕ} (hp : 2 ≤ p) (ht : 0 < t)
    (hut : u < t) (hvt : v < t) (hcop : u.Coprime t) (start length : ℕ) (hs : 0 < start) :
    naturalEndpointTail p t u v start length =
      phaseTail p t u v 0 start length+phaseTail p t u v 1 start length+
        phaseTail p t u v (-1) start length := by
  letI : NeZero t := ⟨ht.ne'⟩
  rw [naturalEndpointTail, dif_pos ht, dif_pos hcop,
    endpointTail_three_phases hp _ _ start length hs]
  simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hut, Nat.mod_eq_of_lt hvt]

def selectedEndpointTail (p U V start : ℕ) (S : ℕ → ℕ → Finset ℕ)
    (length : ℕ → ℕ → ℕ → ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V, ∑ t ∈ S u v,
    (harmonic ((p-1)/t) : ℝ)*naturalEndpointTail p t u v start (length u v t)

theorem selectedEndpointTail_three_phases {p : ℕ} (hp : 2 ≤ p)
    (U V start : ℕ) (hs : 0 < start)
    (S : ℕ → ℕ → Finset ℕ) (length : ℕ → ℕ → ℕ → ℕ)
    (hS : ∀ u ∈ Finset.Icc 1 U, ∀ v ∈ Finset.Icc 1 V, ∀ t ∈ S u v,
      2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*v < t ∧ u.Coprime t) :
    selectedEndpointTail p U V start S length =
      selectedPhaseTail p U V start 0 S length+selectedPhaseTail p U V start 1 S length+
        selectedPhaseTail p U V start (-1) S length := by
  unfold selectedEndpointTail selectedPhaseTail
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have htd := hS u hu v hv t ht
  rw [naturalEndpointTail_three_phases hp (by omega) (by omega) (by omega)
    htd.2.2.2.2 start (length u v t) hs]
  ring

/-- Title: `The whole endpoint-frequency tail retains all three phases and every selected modulus`. -/
theorem endpoint_frequency_tail_finite_bound {p : ℕ} (hp : p.Prime)
    (U V J : ℕ) (hU : 2*U < p) (hV : 2*V < p) (hJ : 0 < J)
    (S : ℕ → ℕ → Finset ℕ) (length : ℕ → ℕ → ℕ → ℕ)
    (hS : ∀ u ∈ Finset.Icc 1 U, ∀ v ∈ Finset.Icc 1 V, ∀ t ∈ S u v,
      2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*v < t ∧ u.Coprime t) :
    |selectedEndpointTail p U V (J+1) S length| ≤
      3*(p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^4/(J : ℝ) := by
  rw [selectedEndpointTail_three_phases hp.two_le U V (J+1) (by omega) S length hS]
  have hzero := selected_phase_tail_bound hp U V (J+1) hU hV (by omega) 0
    (Or.inl rfl) S length hS
  have hone := selected_phase_tail_bound hp U V (J+1) hU hV (by omega) 1
    (Or.inr (Or.inl rfl)) S length hS
  have hneg := selected_phase_tail_bound hp U V (J+1) hU hV (by omega) (-1)
    (Or.inr (Or.inr rfl)) S length hS
  calc
    _ ≤ |selectedPhaseTail p U V (J+1) 0 S length|+
        |selectedPhaseTail p U V (J+1) 1 S length|+
        |selectedPhaseTail p U V (J+1) (-1) S length| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3*((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^4/((J+1 : ℕ) : ℝ)) := by linarith
    _ ≤ 3*((p : ℝ)^2*(divisorMaximum p : ℝ)*(harmonic p : ℝ)^4/(J : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hJ)
      exact_mod_cast Nat.le_succ J
    _ = _ := by ring

/-- Title: `The full endpoint-frequency tail has the published two-plus-epsilon bound`. -/
theorem endpoint_frequency_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∀ U V J : ℕ,
      2*U < p → 2*V < p → 0 < J → ∀ (S : ℕ → ℕ → Finset ℕ) (length : ℕ → ℕ → ℕ → ℕ),
      (∀ u ∈ Finset.Icc 1 U, ∀ v ∈ Finset.Icc 1 V, ∀ t ∈ S u v,
        2 ≤ t ∧ t < p ∧ 2*u < t ∧ 2*v < t ∧ u.Coprime t) →
      |selectedEndpointTail p U V (J+1) S length| ≤ C*(p : ℝ)^(2+ε)/(J : ℝ) := by
  obtain ⟨C, hC, hc⟩ := tail_arithmetic_small_power ε hε
  refine ⟨3*C, by positivity, ?_⟩
  intro p hp U V J hU hV hJ S length hS
  have htail := endpoint_frequency_tail_finite_bound hp U V J hU hV hJ S length hS
  have hcost := hc p hp.one_le
  calc
    _ ≤ 3*(p : ℝ)^2*tailArithmeticCost p/(J : ℝ) := by
      simpa only [tailArithmeticCost, mul_assoc] using htail
    _ ≤ 3*(p : ℝ)^2*(C*(p : ℝ)^ε)/(J : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg J)
      exact mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast hp.pos : (0 : ℝ) < p), Real.rpow_two]
      ring

end NField.Alignment.CommonResetEndpointTailAssembly
