/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreReset
import NField.ResetForests.Words
/-! # The coherent one-sided traces and their exact work -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.FibreTraces

open scoped BigOperators Topology
open Filter NField.Alignment CommonResetGram CollisionRampEnergy
open CommonResetSampling CarrierJumpData DedekindReciprocity SourceMetrics FibreReconstruction

theorem coherent_prime_grid_zero {p : ℕ} (hp : p.Prime) (a : ℕ) :
    weightedProfile (p-1) (fun _ => 1) ((a : ℝ)/(p : ℝ))=0 := by
  rw [unit_weights, boundaryResponse_rational hp.pos]
  have hfull := Core.full_word_period_zero hp.two_le a
  rw [← Nat.sub_add_cancel hp.one_le, Finset.sum_range_succ] at hfull
  simp only [Nat.sub_add_cancel hp.one_le] at hfull
  have hlast : rationalSawtooth (p*a) p=0 := by
    simp [rationalSawtooth]
  rw [hlast, add_zero] at hfull
  simp only [boundaryMidpoint, hfull, mul_zero, Rat.cast_zero]

theorem contact_mass_prime_grid {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) (a : ℕ) :
    contactMass (p-1) c ((a : ℝ)/(p : ℝ))=
      if p ∣ a then sourceTotal (p-1) c else 0 := by
  have hcontact (j : ℕ) (hj : j ∈ Finset.Icc 1 (p-1)) :
      Int.fract ((j : ℝ)*((a : ℝ)/(p : ℝ)))=0 ↔ p ∣ a := by
    rw [← mul_div_assoc, ← Nat.cast_mul, fract_nat_ratio_zero_iff _ hp.pos]
    have hjB := Finset.mem_Icc.mp hj
    exact (hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hjB.1 (by have := hp.two_le; omega))).dvd_mul_left
  unfold contactMass sourceTotal
  by_cases ha : p ∣ a
  · rw [if_pos ha]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos ((hcontact j hj).mpr ha)]
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by simpa only [hcontact j hj] using ha)]

theorem coherent_source_total (N : ℕ) : sourceTotal N (fun _ => 1)=(N : ℝ) := by
  simp [sourceTotal]

theorem coherent_fibre_right_trace {p : ℕ} (hp : p.Prime) (v : Fin p) :
    fibreRight p (fun _ => 1) 0 v=-((p-1 : ℕ) : ℝ)*resetDirection p ⟨0,hp.pos⟩ v := by
  have hgrid : p ∣ v.val ↔ v=⟨0,hp.pos⟩ := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt v.isLt]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  unfold fibreRight profileRight
  simp only [add_zero, coherent_prime_grid_zero hp]
  have horigin : weightedProfile (p-1) (fun _ => (1 : ℝ)) 0=0 := by
    simp [weightedProfile, midpointRow]
  have hm0 : contactMass (p-1) (fun _ => (1 : ℝ)) 0=(p-1 : ℕ) := by
    simp [contactMass]
  rw [contact_mass_prime_grid hp, horigin, hm0, coherent_source_total]
  unfold resetDirection
  split_ifs <;> first | tauto | ring

theorem coherent_fibre_left_trace {p : ℕ} (hp : p.Prime) (v : Fin p) :
    fibreLeft p (fun _ => 1) 1 v=
      (p-1 : ℕ)*resetDirection p ⟨p-1,by have := hp.two_le; omega⟩ v := by
  have hcast : (v.val : ℝ)+1=((v.val+1 : ℕ) : ℝ) := by push_cast; rfl
  have hlast : p ∣ v.val+1 ↔ v=⟨p-1,by have := hp.two_le; omega⟩ := by
    constructor
    · intro hd
      have hle := Nat.le_of_dvd (by omega : 0 < v.val+1) hd
      apply Fin.ext
      change v.val=p-1
      omega
    · intro he
      have he' := congrArg Fin.val he
      rw [he', Nat.sub_add_cancel hp.one_le]
  unfold fibreLeft profileLeft
  rw [hcast, coherent_prime_grid_zero hp]
  have hone : weightedProfile (p-1) (fun _ => (1 : ℝ)) 1=0 := by
    simp [weightedProfile, midpointRow]
  have hm1 : contactMass (p-1) (fun _ => (1 : ℝ)) 1=(p-1 : ℕ) := by
    simp [contactMass]
  rw [contact_mass_prime_grid hp, hone, hm1, coherent_source_total]
  unfold resetDirection
  split_ifs <;> first | tauto | ring

theorem coherent_fibre_origin_work {p : ℕ} (hp : p.Prime) :
    (∑ v : Fin p, (fibreRight p (fun _ => 1) 0 v)^2)=((p-1 : ℕ) : ℝ)^3/(p : ℝ) := by
  simp_rw [coherent_fibre_right_trace hp, mul_pow]
  rw [← Finset.mul_sum, reset_direction_square_work hp.pos]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [hN]
  field_simp

theorem coherent_fibre_endpoint_limits {p : ℕ} (hp : p.Prime) (v : Fin p) :
    Tendsto (fun x => fibrePath p (fun _ => 1) x v) (𝓝[>] 0)
        (𝓝 (-((p-1 : ℕ) : ℝ)*resetDirection p ⟨0,hp.pos⟩ v)) ∧
    Tendsto (fun x => fibrePath p (fun _ => 1) x v) (𝓝[<] 1)
        (𝓝 ((p-1 : ℕ)*resetDirection p ⟨p-1,by have := hp.two_le; omega⟩ v)) := by
  constructor
  · simpa only [coherent_fibre_right_trace hp] using fibre_path_right_limit hp.pos (fun _ => 1) 0 v
  · simpa only [coherent_fibre_left_trace hp] using fibre_path_left_limit hp.pos (fun _ => 1) 1 v

end NField.ResetForests.FibreTraces
