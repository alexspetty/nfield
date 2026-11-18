/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Words
import Mathlib
/-! # Centering the prime phase

The two branches retain their actual source words, reset loads and sampling
phase. Mathlib's prime, gcd and lcm identities supply the joint-clock law.
-/

noncomputable section

namespace NField.ResetForests.CenteredPhase

open NField.Alignment
open CollisionRampEnergy CommonResetSampling

def centeredPhase (p k : ℕ) : ℕ := min (p%k) (k-p%k)

theorem prime_remainder_pos {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    0 < p%k := by
  have hn : ¬k ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  exact Nat.pos_of_ne_zero (fun h => hn (Nat.dvd_of_mod_eq_zero h))

theorem centered_phase_range {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    1 ≤ centeredPhase p k ∧ centeredPhase p k ≤ p/3 := by
  have hr := prime_remainder_pos hp hk hkp
  have hrl := Nat.mod_lt p (by omega : 0 < k)
  have hfirst : centeredPhase p k ≤ p%k := min_le_left _ _
  have hsecond : centeredPhase p k ≤ k-p%k := min_le_right _ _
  have hload : 1 ≤ p/k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by omega)
  have hprod : k ≤ p/k*k := by nlinarith
  have hdecomp : p/k*k+p%k=p := by simpa [mul_comm] using Nat.div_add_mod p k
  constructor
  · unfold centeredPhase
    omega
  · omega

theorem predecessor_remainder {p k : ℕ} (hk : 0 < k) (hr : 0 < p%k) :
    (p-1)%k=p%k-1 ∧ (p-1)/k=p/k := by
  have hdecomp : k*(p/k)+p%k=p := Nat.div_add_mod p k
  have he : p-1 = p%k-1 + k*(p/k) := by omega
  have hsmall : p%k-1 < k := by have := Nat.mod_lt p hk; omega
  rw [he]
  simp [Nat.add_mul_mod_self_left, Nat.add_mul_div_left, hk,
    Nat.mod_eq_of_lt hsmall, Nat.div_eq_of_lt hsmall]

theorem centered_lower_branch {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (hbranch : p%k ≤ k-p%k) :
    k ∣ p-centeredPhase p k ∧ 2*centeredPhase p k ≤ k ∧
      (p-centeredPhase p k)/k=(p-1)/k ∧
      (∀ a : ℕ, boundaryResponse (p-1) ((a : ℝ)/(k : ℝ)) =
        boundaryResponse (centeredPhase p k-1) ((a : ℝ)/(k : ℝ))) ∧
      p^2%k=(centeredPhase p k)^2%k := by
  have hh : centeredPhase p k=p%k := min_eq_left hbranch
  have hr := prime_remainder_pos hp hk hkp
  obtain ⟨hmod, hdiv⟩ := predecessor_remainder (by omega : 0 < k) hr
  have hdecomp : p/k*k+p%k=p := by simpa [mul_comm] using Nat.div_add_mod p k
  have he : p-centeredPhase p k=(p/k)*k := by rw [hh]; omega
  refine ⟨?_, by rw [hh]; omega, ?_, ?_, ?_⟩
  · rw [he]; exact dvd_mul_left _ _
  · rw [he, Nat.mul_div_cancel _ (by omega : 0 < k), hdiv]
  · intro a
    simp_rw [boundaryResponse_rational (by omega : 0 < k)]
    rw [Core.cutoff_word_remainder hk, hmod, hh]
  · rw [hh, Nat.pow_mod]

theorem centered_upper_branch {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (hbranch : k-p%k < p%k) :
    k ∣ p+centeredPhase p k ∧ 2*centeredPhase p k < k ∧
      (p+centeredPhase p k)/k-1=(p-1)/k ∧
      (∀ a : ℕ, boundaryResponse (p-1) ((a : ℝ)/(k : ℝ)) =
        boundaryResponse (centeredPhase p k) ((a : ℝ)/(k : ℝ))) ∧
      p^2%k=(centeredPhase p k)^2%k := by
  letI : NeZero k := ⟨by omega⟩
  have hh : centeredPhase p k=k-p%k := min_eq_right hbranch.le
  have hr := prime_remainder_pos hp hk hkp
  have hrl := Nat.mod_lt p (by omega : 0 < k)
  obtain ⟨hmod, hdiv⟩ := predecessor_remainder (by omega : 0 < k) hr
  have hdecomp : p/k*k+p%k=p := by simpa [mul_comm] using Nat.div_add_mod p k
  have he : p+centeredPhase p k=(p/k+1)*k := by rw [hh]; nlinarith [Nat.sub_add_cancel hrl.le]
  refine ⟨?_, by rw [hh]; omega, ?_, ?_, ?_⟩
  · rw [he]; exact dvd_mul_left _ _
  · rw [he, Nat.mul_div_cancel _ (by omega : 0 < k), Nat.add_sub_cancel, hdiv]
  · intro a
    simp_rw [boundaryResponse_rational (by omega : 0 < k)]
    rw [Core.cutoff_word_remainder hk, hmod,
      Core.prefix_word_reflection hk (by omega : p%k-1 < k)]
    have hs : k-1-(p%k-1)=centeredPhase p k := by rw [hh]; omega
    rw [hs]
  · have hz : (p : ZMod k)+(centeredPhase p k : ZMod k)=0 := by
      have hc := congrArg (fun n : ℕ => (n : ZMod k)) he
      simpa using hc
    have hs : ((p^2 : ℕ) : ZMod k)=(((centeredPhase p k)^2 : ℕ) : ZMod k) := by
      push_cast
      rw [eq_neg_iff_add_eq_zero.mpr hz, neg_sq]
    have hv := congrArg ZMod.val hs
    simpa only [ZMod.val_natCast] using hv

theorem joint_clock {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    (p-h).gcd (p+h)=1 ∨ (p-h).gcd (p+h)=2 := by
  let g := (p-h).gcd (p+h)
  have hA : g ∣ p-h := Nat.gcd_dvd_left _ _
  have hB : g ∣ p+h := Nat.gcd_dvd_right _ _
  have ha : g ∣ 2*p := by
    have ht := Nat.dvd_add hA hB
    convert ht using 1
    omega
  have hb : g ∣ 2*h := by
    have ht := Nat.dvd_sub hB hA
    convert ht using 1
    omega
  have hcop : p.Coprime h := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hh hhp)
  have hd := Nat.dvd_gcd ha hb
  rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one] at hd
  exact (Nat.dvd_prime Nat.prime_two).mp hd

theorem joint_clock_product {p h : ℕ} (hh : h ≤ p) :
    (p-h).gcd (p+h)*((p-h).lcm (p+h))+h^2=p^2 := by
  rw [Nat.gcd_mul_lcm]
  have he := Nat.sub_add_cancel hh
  nlinarith

theorem centered_lower_source_integer {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hkp : k < p) (hbranch : p%k ≤ k-p%k) (a : ℤ) :
    boundaryResponse (p-1) ((a : ℝ)/(k : ℝ)) =
      boundaryResponse (centeredPhase p k-1) ((a : ℝ)/(k : ℝ)) := by
  rw [Core.integer_address_reduction (by omega : 0 < k) (p-1) a,
    Core.integer_address_reduction (by omega : 0 < k) (centeredPhase p k-1) a]
  exact (centered_lower_branch hp hk hkp hbranch).2.2.2.1 _

theorem centered_upper_source_integer {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hkp : k < p) (hbranch : k-p%k < p%k) (a : ℤ) :
    boundaryResponse (p-1) ((a : ℝ)/(k : ℝ)) =
      boundaryResponse (centeredPhase p k) ((a : ℝ)/(k : ℝ)) := by
  rw [Core.integer_address_reduction (by omega : 0 < k) (p-1) a,
    Core.integer_address_reduction (by omega : 0 < k) (centeredPhase p k) a]
  exact (centered_upper_branch hp hk hkp hbranch).2.2.2.1 _

theorem centered_joint_clock {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hkp : k < p) :
    ((p-centeredPhase p k).gcd (p+centeredPhase p k)=1 ∨
      (p-centeredPhase p k).gcd (p+centeredPhase p k)=2) ∧
    (p-centeredPhase p k).gcd (p+centeredPhase p k)*
      ((p-centeredPhase p k).lcm (p+centeredPhase p k))+(centeredPhase p k)^2=p^2 := by
  obtain ⟨hh, hH⟩ := centered_phase_range hp hk hkp
  have hlt : centeredPhase p k < p :=
    hH.trans_lt (Nat.div_lt_self hp.pos (by decide : 1 < 3))
  exact ⟨joint_clock hp (by omega) hlt, joint_clock_product hlt.le⟩

end NField.ResetForests.CenteredPhase
