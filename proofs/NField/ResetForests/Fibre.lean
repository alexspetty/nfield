/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.EnergyMatrices
import NField.Alignment.RealSawtoothDistribution
import NField.Alignment.DedekindFourierMoment
/-! # The actual zero-sum fibre path

The midpoint distribution includes integer contacts. The source is the
same complete cutoff field before and after removing the mean direction.
-/

noncomputable section

namespace NField.ResetForests.FibreReconstruction

open scoped BigOperators
open NField.Alignment CommonResetGram CollisionRampEnergy
open CollisionDedekindPairing RealSawtoothDistribution DedekindFourierMoment

theorem midpoint_row_periodic_saw (j : ℕ) (x : ℝ) :
    midpointRow j x=periodicSawtooth ((j : ℝ)*x) := rfl

theorem coprime_midpoint_distribution {p j : ℕ} (hp : 0 < p) (hj : j.Coprime p) (u : ℝ) :
    (∑ v ∈ Finset.range p, midpointRow j (((v : ℝ)+u)/(p : ℝ)))=midpointRow j u := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpoint (v : ℕ) :
      periodicSawtooth ((j : ℝ)*(((v : ℝ)+u)/(p : ℝ)))=
        periodicSawtooth (((j : ℝ)*u+((j*v%p : ℕ) : ℝ))/(p : ℝ)) := by
    have hr : ((j*v%p : ℕ) : ℝ)+(p : ℝ)*((j*v/p : ℕ) : ℝ)=(j : ℝ)*(v : ℝ) := by
      exact_mod_cast Nat.mod_add_div (j*v) p
    have he : (j : ℝ)*(((v : ℝ)+u)/(p : ℝ)) =
        ((j : ℝ)*u+((j*v%p : ℕ) : ℝ))/(p : ℝ)+((j*v/p : ℕ) : ℝ) := by
      field_simp
      nlinarith
    rw [he, sawtooth_add_nat]
  simp only [midpoint_row_periodic_saw]
  simp_rw [hpoint]
  rw [sum_mul_mod_coprime hp hj
    (fun v : ℕ => periodicSawtooth (((j : ℝ)*u+(v : ℝ))/(p : ℝ)))]
  simp_rw [add_div]
  rw [sawtooth_distribution hp]
  congr 1
  field_simp

theorem weighted_midpoint_distribution {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) (u : ℝ) :
    (∑ v : Fin p, weightedProfile (p-1) c (((v.val : ℝ)+u)/(p : ℝ)))=
      weightedProfile (p-1) c u := by
  rw [Fin.sum_univ_eq_sum_range
    (fun v : ℕ => weightedProfile (p-1) c (((v : ℝ)+u)/(p : ℝ))) p]
  unfold weightedProfile
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  have hjI := Finset.mem_Icc.mp hj
  have hcop : j.Coprime p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hjI.1 (by have := hp.two_le; omega))).symm
  rw [coprime_midpoint_distribution hp.pos hcop]

def fibrePath (p : ℕ) (c : ℕ → ℝ) (u : ℝ) (v : Fin p) : ℝ :=
  weightedProfile (p-1) c (((v.val : ℝ)+u)/(p : ℝ))-
    weightedProfile (p-1) c u/(p : ℝ)

def fibrePair (p : ℕ) (c e : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ v : Fin p, fibrePath p c u v*fibrePath p e u v

def continuousWork (N : ℕ) (c e : ℕ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, weightedProfile N c x*weightedProfile N e x

def sampledWork (N Q : ℕ) (c e : ℕ → ℝ) : ℝ :=
  (1/(Q : ℝ))*∑ a ∈ Finset.range Q,
    weightedProfile N c ((a : ℝ)/(Q : ℝ))*weightedProfile N e ((a : ℝ)/(Q : ℝ))

theorem fibre_path_zero_sum {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) (u : ℝ) :
    (∑ v : Fin p, fibrePath p c u v)=0 := by
  simp only [fibrePath, Finset.sum_sub_distrib, weighted_midpoint_distribution hp,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem fibre_pair_identity {p : ℕ} (hp : p.Prime) (c e : ℕ → ℝ) (u : ℝ) :
    fibrePair p c e u =
      (∑ v : Fin p, weightedProfile (p-1) c (((v.val : ℝ)+u)/(p : ℝ))*
        weightedProfile (p-1) e (((v.val : ℝ)+u)/(p : ℝ)))-
          weightedProfile (p-1) c u*weightedProfile (p-1) e u/(p : ℝ) := by
  have hpoint (v : Fin p) : fibrePath p c u v*fibrePath p e u v=
      weightedProfile (p-1) c (((v.val : ℝ)+u)/(p : ℝ))*
        weightedProfile (p-1) e (((v.val : ℝ)+u)/(p : ℝ))-
      (weightedProfile (p-1) e u/(p : ℝ))*weightedProfile (p-1) c (((v.val : ℝ)+u)/(p : ℝ))-
      (weightedProfile (p-1) c u/(p : ℝ))*weightedProfile (p-1) e (((v.val : ℝ)+u)/(p : ℝ))+
        weightedProfile (p-1) c u*weightedProfile (p-1) e u/(p : ℝ)^2 := by
    unfold fibrePath
    ring
  unfold fibrePair
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    weighted_midpoint_distribution hp, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem weighted_profile_sub (N : ℕ) (c e : ℕ → ℝ) (x : ℝ) :
    weightedProfile N (c-e) x=weightedProfile N c x-weightedProfile N e x := by
  simp only [weightedProfile, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem fibre_path_sub (p : ℕ) (c e : ℕ → ℝ) (u : ℝ) (v : Fin p) :
    fibrePath p (c-e) u v=fibrePath p c u v-fibrePath p e u v := by
  simp only [fibrePath, weighted_profile_sub]
  ring

end NField.ResetForests.FibreReconstruction
