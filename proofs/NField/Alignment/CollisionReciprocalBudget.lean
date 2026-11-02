/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResolutionLaw

/-!
# Reciprocal address budgets

Reducing each fraction a/n by its gcd partitions the finite reciprocal
budget into primitive denominator rows. The resulting triangular system
determines every positive-index collision weight.
-/

noncomputable section

namespace NField.Alignment.CollisionReciprocalBudget

open scoped BigOperators
open CollisionRemainderDynamics CollisionMassReadout CollisionResolutionLaw SecondaryCapacityLedger

def primitiveAddresses (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  n.divisors.sigma (fun k => (Finset.Ico 1 k).filter (fun a => a.Coprime k))

def reducedAddress (n a : ℕ) : Σ _ : ℕ, ℕ := ⟨n / a.gcd n, a / a.gcd n⟩

theorem reducedAddress_mem {n a : ℕ} (ha : a ∈ Finset.Ico 1 n) :
    reducedAddress n a ∈ primitiveAddresses n := by
  have hap := (Finset.mem_Ico.mp ha).1
  have han := (Finset.mem_Ico.mp ha).2
  have hn : 0 < n := by omega
  have hg : 0 < a.gcd n := Nat.gcd_pos_of_pos_left n hap
  have hga : a.gcd n ∣ a := Nat.gcd_dvd_left a n
  have hgn : a.gcd n ∣ n := Nat.gcd_dvd_right a n
  have had : 0 < a / a.gcd n := Nat.div_pos (Nat.gcd_le_left n hap) hg
  have hlt : a / a.gcd n < n / a.gcd n := by
    apply (Nat.mul_lt_mul_left hg).mp
    simpa only [Nat.mul_div_cancel' hga, Nat.mul_div_cancel' hgn] using han
  simp only [primitiveAddresses, reducedAddress, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_Ico]
  exact ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hgn, hn.ne'⟩,
    ⟨had, hlt⟩, Nat.coprime_div_gcd_div_gcd hg⟩

theorem reducedAddress_restore {n a : ℕ} (ha : a ∈ Finset.Ico 1 n) :
    (n / (reducedAddress n a).1) * (reducedAddress n a).2 = a := by
  have hap := (Finset.mem_Ico.mp ha).1
  have hn : 0 < n := by have := (Finset.mem_Ico.mp ha).2; omega
  have hg : 0 < a.gcd n := Nat.gcd_pos_of_pos_left n hap
  have hgn := Nat.gcd_dvd_right a n
  simp only [reducedAddress]
  rw [Nat.div_div_self hgn hn.ne', Nat.mul_div_cancel' (Nat.gcd_dvd_left a n)]

theorem primitiveAddress_restore {n : ℕ} (p : Σ _ : ℕ, ℕ)
    (hp : p ∈ primitiveAddresses n) :
    (n/p.1)*p.2 ∈ Finset.Ico 1 n ∧ reducedAddress n ((n/p.1)*p.2) = p := by
  rcases p with ⟨k,a⟩
  have hp' := Finset.mem_sigma.mp hp
  have hkdiv := Nat.dvd_of_mem_divisors hp'.1
  have hkp := Nat.pos_of_mem_divisors hp'.1
  have hn : 0 < n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hp'.1)
  have ha' := Finset.mem_filter.mp hp'.2
  have ha := Finset.mem_Ico.mp ha'.1
  have hd : 0 < n/k := Nat.div_pos (Nat.le_of_dvd hn hkdiv) hkp
  have hdk : (n/k)*k = n := Nat.div_mul_cancel hkdiv
  have hg : ((n/k)*a).gcd n = n/k := by
    calc
      _ = ((n/k)*a).gcd ((n/k)*k) := congrArg (Nat.gcd ((n/k)*a)) hdk.symm
      _ = _ := by rw [Nat.gcd_mul_left, ha'.2.gcd_eq_one, mul_one]
  constructor
  · exact Finset.mem_Ico.mpr ⟨Nat.mul_pos hd ha.1,
      by simpa only [hdk] using Nat.mul_lt_mul_of_pos_left ha.2 hd⟩
  · simp only [reducedAddress, hg]
    have hk : n / (n/k) = k := Nat.div_div_self hkdiv hn.ne'
    rw [hk, Nat.mul_div_right _ hd]

theorem reciprocal_budget {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ n.divisors, (k : ℝ)^3 * collisionWeight k) =
      (n : ℝ) * (harmonic (n-1) : ℝ) := by
  have hrows : (∑ k ∈ n.divisors, (k : ℝ)^3 * collisionWeight k) =
      ∑ p ∈ primitiveAddresses n, (p.1 : ℝ)/(p.2 : ℝ) := by
    rw [primitiveAddresses, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
    unfold collisionWeight reducedHarmonicStar
    simp only [div_eq_mul_inv]
    rw [← Finset.mul_sum]
    field_simp
  rw [hrows, harmonic_real_sum, Finset.mul_sum]
  have hI : Finset.Icc 1 (n-1) = Finset.Ico 1 n := by ext a; simp; omega
  rw [hI]
  symm
  apply Finset.sum_bij (fun a _ => reducedAddress n a)
  · intro a ha; exact reducedAddress_mem ha
  · intro a ha b hb he
    have hr := congrArg (fun p : Σ _ : ℕ, ℕ => (n/p.1)*p.2) he
    simpa only [reducedAddress_restore ha, reducedAddress_restore hb] using hr
  · intro p hp
    exact ⟨(n/p.1)*p.2, (primitiveAddress_restore p hp).1, (primitiveAddress_restore p hp).2⟩
  · intro a ha
    have hap := (Finset.mem_Ico.mp ha).1
    have hg : 0 < a.gcd n := Nat.gcd_pos_of_pos_left n hap
    have hga := Nat.gcd_dvd_left a n
    have hgn := Nat.gcd_dvd_right a n
    have hgR : (a.gcd n : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    simp only [reducedAddress]
    rw [Nat.cast_div hgn hgR, Nat.cast_div hga hgR]
    field_simp

theorem divisor_sums_injective (f g : ℕ → ℝ)
    (he : ∀ n, 0 < n → (∑ k ∈ n.divisors, f k) = ∑ k ∈ n.divisors, g k) :
    ∀ n, 0 < n → f n = g n := by
  have hf := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := f) (g := fun n => ∑ k ∈ n.divisors, g k)).mp he
  have hg := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := g) (g := fun n => ∑ k ∈ n.divisors, g k)).mp (fun _ _ => rfl)
  intro n hn
  exact (hf n hn).symm.trans (hg n hn)

theorem reciprocal_budget_injective (v : ℕ → ℝ) (hv1 : v 1 = 0)
    (hb : ∀ n : ℕ, 2 ≤ n → (∑ k ∈ n.divisors, (k : ℝ)^3 * v k) =
      (n : ℝ) * (harmonic (n-1) : ℝ)) :
    ∀ k, 0 < k → v k = collisionWeight k := by
  have he : ∀ n : ℕ, 0 < n → (∑ k ∈ n.divisors, (k : ℝ)^3 * v k) =
      ∑ k ∈ n.divisors, (k : ℝ)^3 * collisionWeight k := by
    intro n hn
    by_cases hn1 : n = 1
    · simp [hn1, hv1]
    · rw [hb n (by omega), reciprocal_budget hn]
  have hi := divisor_sums_injective (fun k => (k : ℝ)^3 * v k)
    (fun k => (k : ℝ)^3 * collisionWeight k) he
  intro k hk
  exact mul_left_cancel₀ (pow_ne_zero 3 (by exact_mod_cast hk.ne')) (hi k hk)

theorem collisionWeight_moebius_budget {n : ℕ} (hn : 0 < n) :
    collisionWeight n = (1 / (n : ℝ)^3) *
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d) : ℝ) *
        (d : ℝ) * (harmonic (d-1) : ℝ) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun k => (k : ℝ)^3 * collisionWeight k)
    (g := fun n => (n : ℝ) * (harmonic (n-1) : ℝ))).mp
      (fun _ hn => reciprocal_budget hn) n hn
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun x y => (ArithmeticFunction.moebius x : ℝ) *
      ((y : ℝ) * (harmonic (y-1) : ℝ)))] at h
  simp only [← mul_assoc] at h
  rw [h]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

def ageDeficit (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  (2/3 : ℝ) * ∑' k, v k * ((N%k : ℕ) : ℝ)

theorem general_age_summable (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hs : Summable v) (N : ℕ) : Summable (fun k => v k * ((N%k : ℕ) : ℝ)) := by
  apply Summable.of_nonneg_of_le (f := fun k => v k * (N : ℝ))
    (fun k => mul_nonneg (hv k) (Nat.cast_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N k) (hv k))
  exact hs.mul_right (N : ℝ)

def resetRow (v : ℕ → ℝ) (n k : ℕ) : ℝ := if k ∣ n then (k : ℝ)*v k else 0

theorem resetRow_hasSum (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    HasSum (resetRow v n) (∑ k ∈ n.divisors, (k : ℝ)*v k) := by
  have h : HasSum (resetRow v n) (∑ k ∈ n.divisors, resetRow v n k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    unfold resetRow
    rw [if_neg]
    intro h
    exact hk (Nat.mem_divisors.mpr ⟨h, hn.ne'⟩)
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (if_pos (Nat.dvd_of_mem_divisors hk)).symm

theorem general_age_reset (v : ℕ → ℝ) (hv0 : v 0 = 0) (hv : ∀ k, 0 ≤ v k)
    (hs : HasSum v 1) (N : ℕ) :
    ageDeficit v (N+1) - ageDeficit v N =
      (2/3 : ℝ) * (1 - ∑ k ∈ (N+1).divisors, (k : ℝ)*v k) := by
  have hterm (k : ℕ) : v k * (((N+1)%k : ℕ) : ℝ) - v k * ((N%k : ℕ) : ℝ) =
      v k - resetRow v (N+1) k := by
    by_cases hk : k = 0
    · simp [hk, hv0, resetRow]
    rw [← mul_sub, remainder_step (Nat.pos_of_ne_zero hk) N]
    unfold resetRow
    split_ifs <;> ring
  unfold ageDeficit
  rw [← mul_sub, ← (general_age_summable v hv hs.summable (N+1)).tsum_sub
    (general_age_summable v hv hs.summable N)]
  simp_rw [hterm]
  rw [hs.summable.tsum_sub (resetRow_hasSum v (Nat.succ_pos N)).summable,
    hs.tsum_eq, (resetRow_hasSum v (Nat.succ_pos N)).tsum_eq]

theorem divisor_reset_injective (v : ℕ → ℝ)
    (he : ∀ n : ℕ, 0 < n → (∑ k ∈ n.divisors, (k : ℝ)*v k) =
      ∑ k ∈ n.divisors, (k : ℝ)*collisionWeight k) :
    ∀ k, 0 < k → v k = collisionWeight k := by
  have h := divisor_sums_injective (fun k => (k : ℝ)*v k)
    (fun k => (k : ℝ)*collisionWeight k) he
  intro k hk
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') (h k hk)

theorem age_reset_injective (v : ℕ → ℝ) (hv0 : v 0 = 0) (hv : ∀ k, 0 ≤ v k)
    (hs : HasSum v 1)
    (hr : ∀ N, ageDeficit v (N+1) - ageDeficit v N = deficit (N+1) - deficit N) :
    ∀ k, 0 < k → v k = collisionWeight k := by
  apply divisor_reset_injective v
  intro n hn
  have h := hr (n-1)
  rw [general_age_reset v hv0 hv hs, deficit_reset, Nat.sub_add_cancel hn] at h
  linarith

theorem age_readout_injective (v : ℕ → ℝ) (hv0 : v 0 = 0) (hv : ∀ k, 0 ≤ v k)
    (hs : HasSum v 1) (hr : ∀ N, ageDeficit v N = deficit N) :
    ∀ k, 0 < k → v k = collisionWeight k := by
  apply age_reset_injective v hv0 hv hs
  intro N
  rw [hr, hr]

theorem reciprocal_characterization (v : ℕ → ℝ) (hv1 : v 1 = 0) :
    (∀ n : ℕ, 2 ≤ n → (∑ k ∈ n.divisors, (k : ℝ)^3*v k) =
      (n : ℝ)*(harmonic (n-1) : ℝ)) ↔
      ∀ k, 0 < k → v k = collisionWeight k := by
  constructor
  · exact reciprocal_budget_injective v hv1
  · intro he n hn
    rw [← reciprocal_budget (by omega : 0 < n)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [he k (Nat.pos_of_mem_divisors hk)]

theorem age_characterization (v : ℕ → ℝ) (hv0 : v 0 = 0) (hv : ∀ k, 0 ≤ v k)
    (hs : HasSum v 1) :
    (∀ N, ageDeficit v N = deficit N) ↔ ∀ k, 0 < k → v k = collisionWeight k := by
  constructor
  · exact age_readout_injective v hv0 hv hs
  · intro he N
    unfold ageDeficit deficit
    congr 1
    apply tsum_congr
    intro k
    by_cases hk : k = 0
    · simp [hk, hv0]
    · rw [he k (Nat.pos_of_ne_zero hk)]

theorem reset_characterization (v : ℕ → ℝ) (hv0 : v 0 = 0) (hv : ∀ k, 0 ≤ v k)
    (hs : HasSum v 1) :
    (∀ N, ageDeficit v (N+1) - ageDeficit v N = deficit (N+1) - deficit N) ↔
      ∀ k, 0 < k → v k = collisionWeight k := by
  constructor
  · exact age_reset_injective v hv0 hv hs
  · intro he N
    have hr := (age_characterization v hv0 hv hs).mpr he
    rw [hr, hr]

end NField.Alignment.CollisionReciprocalBudget
