/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionReciprocalBudget

/-!
# Literal split bounds and completion for general unit masses

The logarithmic estimate controls the actual split upper bound, not only
the deficit below it. The general completion retains the full convergent
floor sum, and its leading law is proved by dominated convergence.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionMassDisplays

open scoped BigOperators
open Filter Asymptotics
open CollisionRemainderDynamics CollisionMassReadout CollisionReciprocalBudget
open SecondaryCapacityLedger

def splitUpper (N : ℕ) : ℝ := (2/3 : ℝ)*
  ((∑ k ∈ Finset.Icc 2 N, (k : ℝ)*collisionWeight k)+
    (N : ℝ)*∑' j : ℕ, collisionWeight (j+(N+1)))

theorem weight_tail_literal (N : ℕ) :
    (∑' j : ℕ, collisionWeight (j+(N+1)))=reducedEulerTailMass N := by
  have h := collisionWeight_summable.sum_add_tsum_nat_add (N+1)
  rw [collisionWeight_tsum,sum_range_weights] at h
  change _=1-∑ k ∈ Finset.Icc 2 N, collisionWeight k
  linarith

theorem fractionalFloorTerm_le_firstMoment (N : ℕ) :
    fractionalFloorTerm N ≤ ∑ k ∈ Finset.Icc 2 N, (k : ℝ)*collisionWeight k := by
  unfold fractionalFloorTerm
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
  calc
    _ = ((N%k : ℕ) : ℝ)*collisionWeight k := by unfold collisionWeight; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.mod_lt N hk0).le) (collisionWeight_nonneg k)

theorem deficit_le_splitUpper (N : ℕ) : deficit N ≤ splitUpper N := by
  rw [deficit,remainder_age_tsum,splitUpper,weight_tail_literal]
  nlinarith [fractionalFloorTerm_le_firstMoment N]

theorem firstMoment_le_harmonic_sq (N : ℕ) :
    (∑ k ∈ Finset.Icc 2 N, (k : ℝ)*collisionWeight k) ≤ (harmonic N : ℝ)^2 := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 N, (harmonic N : ℝ)*(k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      calc
        (k : ℝ)*collisionWeight k = reducedHarmonicStar k*(k : ℝ)⁻¹ := by
          unfold collisionWeight
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (reducedHarmonicStar_le_harmonic hkI.2)
          (inv_nonneg.mpr hk0.le)
    _ = (harmonic N : ℝ)*∑ k ∈ Finset.Icc 2 N, (k : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (harmonic N : ℝ)*∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (harmonic_nonneg N)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hk).1; omega,
          (Finset.mem_Icc.mp hk).2⟩
      · intro k _ _; positivity
    _ = (harmonic N : ℝ)^2 := by rw [← harmonic_real_sum]; ring

theorem splitUpper_nonneg (N : ℕ) : 0 ≤ splitUpper N := by
  unfold splitUpper
  apply mul_nonneg (by norm_num)
  exact add_nonneg
    (Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (collisionWeight_nonneg k)))
    (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun j => collisionWeight_nonneg _)))

theorem splitUpper_harmonic_bound {N : ℕ} (hN : 2 ≤ N) :
    splitUpper N ≤ (2/3 : ℝ)*((harmonic N : ℝ)^2+2*(harmonic N : ℝ)+4) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht := CoprimeEulerMass.eulerFrontierPotential_le hN
  rw [← reducedEulerTailMass_eq_frontier hN] at ht
  have hm := mul_le_mul_of_nonneg_left ht hNR.le
  have he : (N : ℝ)*(4/(N : ℝ)+2*(harmonic N : ℝ)/(N : ℝ))=
      4+2*(harmonic N : ℝ) := by field_simp
  rw [he] at hm
  rw [splitUpper,weight_tail_literal]
  nlinarith [firstMoment_le_harmonic_sq N]

theorem splitUpper_log_bound {N : ℕ} (hN : 2 ≤ N) :
    splitUpper N ≤ 6*(1+Real.log N)^2 := by
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hH := harmonic_nonneg N
  have hHlog := harmonic_le_one_add_log N
  have hs : (harmonic N : ℝ)^2 ≤ (1+Real.log N)^2 := by nlinarith
  nlinarith [splitUpper_harmonic_bound hN,sq_nonneg (Real.log (N : ℝ))]

theorem splitUpper_isBigO_log_sq :
    IsBigO atTop splitUpper (fun N : ℕ => (Real.log (2*(N : ℝ)))^2) := by
  apply isBigO_iff.mpr
  refine ⟨24,?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 2,hl] with N hN hlN
  rw [Real.norm_of_nonneg (splitUpper_nonneg N),Real.norm_of_nonneg (sq_nonneg _)]
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : Real.log (N : ℝ) ≤ Real.log (2*(N : ℝ)) := Real.log_le_log hNR (by linarith)
  have hs : (1+Real.log (N : ℝ))^2 ≤ 4*(Real.log (2*(N : ℝ)))^2 := by
    nlinarith [mul_nonneg
      (show 0 ≤ 2*Real.log (2*(N : ℝ))-(1+Real.log (N : ℝ)) by linarith)
      (show 0 ≤ 2*Real.log (2*(N : ℝ))+(1+Real.log (N : ℝ)) by linarith)]
  nlinarith [splitUpper_log_bound hN]

theorem literal_deficit_split :
    (∀ N : ℕ, deficit N ≤ (2/3 : ℝ)*
      ((∑ k ∈ Finset.Icc 2 N, (k : ℝ)*collisionWeight k)+
        (N : ℝ)*∑' j : ℕ, collisionWeight (j+(N+1)))) ∧
    IsBigO atTop splitUpper (fun N : ℕ => (Real.log (2*(N : ℝ)))^2) :=
  ⟨deficit_le_splitUpper,splitUpper_isBigO_log_sq⟩

theorem general_floor_summable (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hs : Summable v) (N : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)*v k*((N/k : ℕ) : ℝ)) := by
  apply Summable.of_nonneg_of_le (f := fun k => v k*(N : ℝ))
  · intro k
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hv k)) (Nat.cast_nonneg _)
  · intro k
    have h : ((k*(N/k) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N k
    calc
      _ = v k*((k*(N/k) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (hv k)
  · exact hs.mul_right _

theorem general_floor_balance (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hs : HasSum v 1) (N : ℕ) :
    (∑' k, v k*((N%k : ℕ) : ℝ))+
      (∑' k : ℕ, (k : ℝ)*v k*((N/k : ℕ) : ℝ))=(N : ℝ) := by
  rw [← (general_age_summable v hv hs.summable N).tsum_add
    (general_floor_summable v hv hs.summable N)]
  have ht (k : ℕ) : v k*((N%k : ℕ) : ℝ)+(k : ℝ)*v k*((N/k : ℕ) : ℝ)=v k*(N : ℝ) := by
    have h : ((N%k : ℕ) : ℝ)+(k : ℝ)*((N/k : ℕ) : ℝ)=N := by
      exact_mod_cast Nat.mod_add_div N k
    calc
      _ = v k*(((N%k : ℕ) : ℝ)+(k : ℝ)*((N/k : ℕ) : ℝ)) := by ring
      _ = _ := congrArg (fun x : ℝ => v k*x) h
  simp_rw [ht]
  rw [tsum_mul_right,hs.tsum_eq,one_mul]

theorem general_completion (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hs : HasSum v 1) (N : ℕ) :
    (N : ℝ)-ageDeficit v N=(N : ℝ)/3+(2/3 : ℝ)*
      ∑' k : ℕ, (k : ℝ)*v k*((N/k : ℕ) : ℝ) := by
  have h := general_floor_balance v hv hs N
  unfold ageDeficit
  linarith

theorem general_completion_from_two (v : ℕ → ℝ) (hv1 : v 1=0)
    (hv : ∀ k, 0 ≤ v k) (hs : HasSum v 1) (N : ℕ) :
    (N : ℝ)-ageDeficit v N=(N : ℝ)/3+(2/3 : ℝ)*
      ∑' j : ℕ, ((j+2 : ℕ) : ℝ)*v (j+2)*((N/(j+2) : ℕ) : ℝ) := by
  have h := (general_floor_summable v hv hs.summable N).sum_add_tsum_nat_add 2
  simp [Finset.sum_range_succ,hv1] at h
  rw [general_completion v hv hs N,← h]
  simp only [Nat.cast_add,Nat.cast_ofNat]

theorem general_age_ratio_zero (v : ℕ → ℝ) (hv0 : v 0=0)
    (hv : ∀ k, 0 ≤ v k) (hs : Summable v) :
    Tendsto (fun N : ℕ => ageDeficit v N/(N : ℝ)) atTop (nhds 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hp (k : ℕ) : Tendsto
      (fun N : ℕ => v k*((N%k : ℕ) : ℝ)/(N : ℝ)) atTop (nhds 0) := by
    by_cases hk : k=0
    · subst k; simp [hv0]
    · apply squeeze_zero' (g := fun N : ℕ => v k*(k : ℝ)/(N : ℝ))
      · exact Eventually.of_forall (fun N => div_nonneg
          (mul_nonneg (hv k) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      · exact Eventually.of_forall (fun N => div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt N (Nat.pos_of_ne_zero hk)).le)
            (hv k)) (Nat.cast_nonneg _))
      · simpa [div_eq_mul_inv] using hi.const_mul (v k*(k : ℝ))
  have hb : ∀ᶠ N : ℕ in atTop, ∀ k, ‖v k*((N%k : ℕ) : ℝ)/(N : ℝ)‖ ≤ v k := by
    filter_upwards [eventually_ge_atTop 1] with N hN k
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg (hv k) (Nat.cast_nonneg _)) hNR.le)]
    apply (div_le_iff₀ hNR).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N k) (hv k)
  have ht := tendsto_tsum_of_dominated_convergence hs hp hb
  simp only [tsum_zero] at ht
  have he : (fun N : ℕ => ageDeficit v N/(N : ℝ))=
      (fun N : ℕ => (2/3 : ℝ)*∑' k, v k*((N%k : ℕ) : ℝ)/(N : ℝ)) := by
    funext N
    rw [ageDeficit,tsum_div_const]
    ring
  rw [he]
  simpa using ht.const_mul (2/3 : ℝ)

theorem literal_general_completion_and_leading (v : ℕ → ℝ) (hv0 : v 0=0) (hv1 : v 1=0)
    (hv : ∀ k, 0 ≤ v k) (hs : HasSum v 1) :
    (∀ N : ℕ, (N : ℝ)-ageDeficit v N=(N : ℝ)/3+(2/3 : ℝ)*
      ∑' j : ℕ, ((j+2 : ℕ) : ℝ)*v (j+2)*((N/(j+2) : ℕ) : ℝ)) ∧
    Tendsto (fun N : ℕ => ageDeficit v N/(N : ℝ)) atTop (nhds 0) :=
  ⟨general_completion_from_two v hv1 hv hs,general_age_ratio_zero v hv0 hv hs.summable⟩

end NField.Alignment.CollisionMassDisplays
