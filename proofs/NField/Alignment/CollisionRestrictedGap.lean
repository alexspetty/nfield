/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionConductorExtrema

/-!
# The actual restricted gap for a full-amplitude conductor cutoff

The minimum is taken over the finite residue classes after both endpoint
classes have been removed. Reflection proves the corresponding maximum.
No asymptotic classification is assumed in these finite assertions.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionRestrictedGap

open scoped BigOperators Classical
open CollisionRemainderDynamics CollisionFiniteRegrouping CollisionConductorOne
open CollisionConductorExtrema CollisionOdometerRecurrence CollisionCylinderOne

def interiorResidues (Q : ℕ) : Finset ℕ := Finset.Ioo 0 (cutoffPeriod Q-1)
def conductorGap (Q a : ℕ) : ℝ := fixedConductorValue Q a+conductorEndpoint Q
def reflectedResidue (Q a : ℕ) : ℕ := cutoffPeriod Q-1-a
def restrictedGap (Q : ℕ) : ℝ :=
  if h : (interiorResidues Q).Nonempty then
    (interiorResidues Q).inf' h (conductorGap Q) else 0

theorem cutoffPeriod_ge_three {Q : ℕ} (hQ : 3 ≤ Q) : 3 ≤ cutoffPeriod Q :=
  Nat.le_of_dvd (cutoffPeriod_pos Q) (dvd_cutoffPeriod (by norm_num) hQ)

theorem interiorResidues_mem {Q a : ℕ} :
    a ∈ interiorResidues Q ↔ 0 < a ∧ a < cutoffPeriod Q-1 := by
  simp only [interiorResidues,Finset.mem_Ioo]

theorem interiorResidues_nonempty {Q : ℕ} (hQ : 3 ≤ Q) :
    (interiorResidues Q).Nonempty := by
  refine ⟨1,interiorResidues_mem.mpr ⟨by norm_num,?_⟩⟩
  have := cutoffPeriod_ge_three hQ
  omega

theorem conductorGap_formula (Q a : ℕ) :
    conductorGap Q a=(2/3 : ℝ)*∑ d ∈ Finset.Icc 2 Q, beta d Q*((a%d : ℕ) : ℝ) :=
  fixedConductor_beta_gap Q a

theorem conductorGap_pos {Q a : ℕ} (ha : a ∈ interiorResidues Q) :
    0 < conductorGap Q a := by
  have hm := interiorResidues_mem.mp ha
  have hal : a < cutoffPeriod Q := by omega
  have hne : fixedConductorValue Q a ≠ -conductorEndpoint Q := by
    intro he
    have := (fixedConductor_unique_min hal).mp he
    omega
  have hle := fixedConductor_lower Q a
  have hlt : -conductorEndpoint Q < fixedConductorValue Q a :=
    (lt_iff_le_and_ne).mpr ⟨hle,hne.symm⟩
  unfold conductorGap
  linarith

theorem conductorGap_lt_twice_endpoint {Q a : ℕ} (ha : a ∈ interiorResidues Q) :
    conductorGap Q a < 2*conductorEndpoint Q := by
  have hm := interiorResidues_mem.mp ha
  have hal : a < cutoffPeriod Q := by omega
  have hne : fixedConductorValue Q a ≠ conductorEndpoint Q := by
    intro he
    have := (fixedConductor_unique_max hal).mp he
    omega
  have hle := fixedConductor_upper Q a
  have hlt : fixedConductorValue Q a < conductorEndpoint Q :=
    (lt_iff_le_and_ne).mpr ⟨hle,hne⟩
  unfold conductorGap
  linarith

theorem reflectedResidue_mem {Q a : ℕ} (ha : a ∈ interiorResidues Q) :
    reflectedResidue Q a ∈ interiorResidues Q := by
  rw [interiorResidues_mem] at ha ⊢
  unfold reflectedResidue
  omega

theorem reflectedResidue_involutive {Q a : ℕ} (ha : a < cutoffPeriod Q) :
    reflectedResidue Q (reflectedResidue Q a)=a := by
  unfold reflectedResidue
  omega

theorem remainder_reflection {L d a : ℕ} (hd : 0 < d) (hdL : d ∣ L) (ha : a < L) :
    a%d+(L-1-a)%d=d-1 := by
  have he : a+(L-1-a)+1=L := by omega
  have hm : (a%d+(L-1-a)%d+1)%d=0 := by
    have h := congrArg (fun n : ℕ => n%d) he
    simpa only [Nat.add_mod,Nat.mod_mod,Nat.mod_eq_zero_of_dvd hdL] using h
  have hdiv := Nat.dvd_of_mod_eq_zero hm
  have hlt1 := Nat.mod_lt a hd
  have hlt2 := Nat.mod_lt (L-1-a) hd
  obtain ⟨k,hk⟩ := hdiv
  have hk0 : k ≠ 0 := by intro h; rw [h,Nat.mul_zero] at hk; omega
  have hk1 : k=1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    nlinarith
  rw [hk1,Nat.mul_one] at hk
  omega

theorem fixedConductor_reflection {Q a : ℕ} (ha : a < cutoffPeriod Q) :
    fixedConductorValue Q (reflectedResidue Q a) = -fixedConductorValue Q a := by
  rw [fixedConductor_regrouping,fixedConductor_regrouping]
  have hsum : (∑ d ∈ Finset.Icc 2 Q, beta d Q*centeredRemainder d (reflectedResidue Q a)) =
      -(∑ d ∈ Finset.Icc 2 Q, beta d Q*centeredRemainder d a) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hm := Finset.mem_Icc.mp hd
    have hr := remainder_reflection (by omega : 0 < d)
      (dvd_cutoffPeriod (by omega) hm.2) ha
    have he : ((a%d : ℕ) : ℝ)+(((cutoffPeriod Q-1-a)%d : ℕ) : ℝ)=(d : ℝ)-1 := by
      have hc : ((a%d : ℕ) : ℝ)+(((cutoffPeriod Q-1-a)%d : ℕ) : ℝ)+1=(d : ℝ) := by
        exact_mod_cast (show a%d+(cutoffPeriod Q-1-a)%d+1=d by omega)
      linarith
    have he' : centeredRemainder d (reflectedResidue Q a) = -centeredRemainder d a := by
      unfold centeredRemainder reflectedResidue
      linarith
    rw [he']
    ring
  rw [hsum]
  ring

theorem conductorGap_reflection {Q a : ℕ} (ha : a < cutoffPeriod Q) :
    conductorGap Q (reflectedResidue Q a)=2*conductorEndpoint Q-conductorGap Q a := by
  unfold conductorGap
  rw [fixedConductor_reflection ha]
  ring

theorem restrictedGap_eq_inf {Q : ℕ} (hQ : 3 ≤ Q) :
    restrictedGap Q=(interiorResidues Q).inf' (interiorResidues_nonempty hQ) (conductorGap Q) := by
  simp only [restrictedGap,dif_pos (interiorResidues_nonempty hQ)]

theorem restrictedGap_pos {Q : ℕ} (hQ : 3 ≤ Q) : 0 < restrictedGap Q := by
  rw [restrictedGap_eq_inf hQ,Finset.lt_inf'_iff]
  exact fun _ ha => conductorGap_pos ha

theorem restrictedGap_le {Q a : ℕ} (hQ : 3 ≤ Q) (ha : a ∈ interiorResidues Q) :
    restrictedGap Q ≤ conductorGap Q a := by
  rw [restrictedGap_eq_inf hQ]
  exact Finset.inf'_le _ ha

theorem restrictedGap_attained {Q : ℕ} (hQ : 3 ≤ Q) :
    ∃ a ∈ interiorResidues Q, conductorGap Q a=restrictedGap Q := by
  obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_inf' (interiorResidues_nonempty hQ) (conductorGap Q)
  exact ⟨a,ha,by rw [restrictedGap_eq_inf hQ,he]⟩

theorem restricted_value_bounds {Q a : ℕ} (hQ : 3 ≤ Q) (ha : a ∈ interiorResidues Q) :
    -conductorEndpoint Q+restrictedGap Q ≤ fixedConductorValue Q a ∧
      fixedConductorValue Q a ≤ conductorEndpoint Q-restrictedGap Q := by
  have hl := restrictedGap_le hQ ha
  have hu := restrictedGap_le hQ (reflectedResidue_mem ha)
  have hm := interiorResidues_mem.mp ha
  rw [conductorGap_reflection (by omega : a < cutoffPeriod Q)] at hu
  unfold conductorGap at hl hu
  constructor <;> linarith

theorem restricted_extrema_attained {Q : ℕ} (hQ : 3 ≤ Q) :
    (∃ a ∈ interiorResidues Q,
      fixedConductorValue Q a = -conductorEndpoint Q+restrictedGap Q) ∧
    (∃ a ∈ interiorResidues Q,
      fixedConductorValue Q a = conductorEndpoint Q-restrictedGap Q) := by
  obtain ⟨a,ha,he⟩ := restrictedGap_attained hQ
  have hm := interiorResidues_mem.mp ha
  have hr := fixedConductor_reflection (by omega : a < cutoffPeriod Q)
  unfold conductorGap at he
  exact ⟨⟨a,ha,by linarith⟩,⟨reflectedResidue Q a,reflectedResidue_mem ha,by linarith⟩⟩

theorem restricted_finite_extrema {Q : ℕ} (hQ : 3 ≤ Q) :
    0 < restrictedGap Q ∧
    (∀ a ∈ interiorResidues Q,
      -conductorEndpoint Q+restrictedGap Q ≤ fixedConductorValue Q a ∧
      fixedConductorValue Q a ≤ conductorEndpoint Q-restrictedGap Q) ∧
    (∃ a ∈ interiorResidues Q,
      fixedConductorValue Q a = -conductorEndpoint Q+restrictedGap Q) ∧
    (∃ a ∈ interiorResidues Q,
      fixedConductorValue Q a = conductorEndpoint Q-restrictedGap Q) := by
  exact ⟨restrictedGap_pos hQ,fun _ ha => restricted_value_bounds hQ ha,
    restricted_extrema_attained hQ⟩

end NField.Alignment.CollisionRestrictedGap
