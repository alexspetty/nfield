/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.PacketOrbit
import Mathlib.Data.Int.CardIntervalMod
/-! # Full word periods, exact populations and the unique common anchor

These are periods of the two labelled word congruences. No periodicity of
the changing physical clock weights or of the full cutoff field is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PacketCycles

def wordPeriodLower (p m : ℕ) (s : ℤ) : Finset ℤ :=
  (Finset.Ico s (s + (m : ℤ) * ((m : ℤ) + 1))).filter
    (fun v => Int.ModEq (m : ℤ) v ((p : ℤ) - 1))
def wordPeriodUpper (p m : ℕ) (s : ℤ) : Finset ℤ :=
  (Finset.Ico s (s + (m : ℤ) * ((m : ℤ) + 1))).filter
    (fun v => Int.ModEq ((m : ℤ) + 1) v (-(p : ℤ)))
def commonWordAnchor (p m : ℕ) : ℤ := (2 * (m : ℤ) + 1) * p - ((m : ℤ) + 1)

theorem residue_count_integer_period (s r : ℤ) {d : ℤ} (hd : 0 < d) (n : ℕ) :
    ((Finset.Ico s (s + d * (n : ℤ))).filter (fun v => Int.ModEq d v r)).card = n := by
  have hq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ((s + d * (n : ℤ) - r : ℤ) : ℚ) / (d : ℚ) =
      ((s - r : ℤ) : ℚ) / (d : ℚ) + (n : ℚ) := by
    push_cast
    field_simp
    ring
  have hc := Int.Ico_filter_modEq_card s (s + d * (n : ℤ)) hd r
  push_cast at he hc
  rw [he, Int.ceil_add_natCast] at hc
  apply Int.ofNat_inj.mp
  simpa using hc

theorem word_period_lower_card (p : ℕ) {m : ℕ} (hm : 0 < m) (s : ℤ) :
    (wordPeriodLower p m s).card = m + 1 := by
  have h := residue_count_integer_period s ((p : ℤ) - 1)
    (show (0 : ℤ) < m by exact_mod_cast hm) (m + 1)
  simpa only [wordPeriodLower, Int.natCast_add, Int.natCast_one] using h

theorem word_period_upper_card (p : ℕ) (m : ℕ) (s : ℤ) :
    (wordPeriodUpper p m s).card = m := by
  have h := residue_count_integer_period s (-(p : ℤ))
    (show (0 : ℤ) < (m : ℤ) + 1 by omega) m
  simpa only [wordPeriodUpper, mul_comm] using h

theorem consecutive_moduli_coprime (m : ℕ) :
    (m : ℤ).natAbs.Coprime ((m : ℤ) + 1).natAbs := by
  norm_cast
  simp

theorem common_word_anchor_lower (p m : ℕ) :
    Int.ModEq (m : ℤ) (commonWordAnchor p m) ((p : ℤ) - 1) := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨1 - 2 * (p : ℤ), by unfold commonWordAnchor; ring⟩

theorem common_word_anchor_upper (p m : ℕ) :
    Int.ModEq ((m : ℤ) + 1) (commonWordAnchor p m) (-(p : ℤ)) := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨1 - 2 * (p : ℤ), by unfold commonWordAnchor; ring⟩

theorem common_word_anchor_iff (p m : ℕ) (v : ℤ) :
    (Int.ModEq (m : ℤ) v ((p : ℤ) - 1) ∧
      Int.ModEq ((m : ℤ) + 1) v (-(p : ℤ))) ↔
    Int.ModEq ((m : ℤ) * ((m : ℤ) + 1)) v (commonWordAnchor p m) := by
  have hcrt := Int.modEq_and_modEq_iff_modEq_mul (consecutive_moduli_coprime m)
    (a := v) (b := commonWordAnchor p m)
  constructor
  · rintro ⟨hlo, hup⟩
    exact hcrt.mp ⟨hlo.trans (common_word_anchor_lower p m).symm,
      hup.trans (common_word_anchor_upper p m).symm⟩
  · intro h
    obtain ⟨hlo, hup⟩ := hcrt.mpr h
    exact ⟨hlo.trans (common_word_anchor_lower p m), hup.trans (common_word_anchor_upper p m)⟩

theorem labelled_word_period_iff (m : ℕ) (v T : ℤ) :
    (Int.ModEq (m : ℤ) (v + T) v ∧ Int.ModEq ((m : ℤ) + 1) (v + T) v) ↔
      (m : ℤ) * ((m : ℤ) + 1) ∣ T := by
  rw [Int.modEq_and_modEq_iff_modEq_mul (consecutive_moduli_coprime m), Int.modEq_iff_dvd]
  have he : v - (v + T) = -T := by ring
  rw [he, Int.dvd_neg]

theorem labelled_full_word_period (m : ℕ) (v : ℤ) :
    Int.ModEq (m : ℤ) (v + (m : ℤ) * ((m : ℤ) + 1)) v ∧
      Int.ModEq ((m : ℤ) + 1) (v + (m : ℤ) * ((m : ℤ) + 1)) v :=
  (labelled_word_period_iff m v _).mpr dvd_rfl

theorem word_class_period_iff (p m : ℕ) (T : ℤ) :
    ((∀ v : ℤ, Int.ModEq (m : ℤ) (v + T) ((p : ℤ) - 1) ↔
        Int.ModEq (m : ℤ) v ((p : ℤ) - 1)) ∧
      (∀ v : ℤ, Int.ModEq ((m : ℤ) + 1) (v + T) (-(p : ℤ)) ↔
        Int.ModEq ((m : ℤ) + 1) v (-(p : ℤ)))) ↔
      (m : ℤ) * ((m : ℤ) + 1) ∣ T := by
  constructor
  · rintro ⟨hlo, hup⟩
    have hl := (hlo (commonWordAnchor p m)).mpr (common_word_anchor_lower p m)
    have hu := (hup (commonWordAnchor p m)).mpr (common_word_anchor_upper p m)
    apply (labelled_word_period_iff m (commonWordAnchor p m) T).mp
    exact ⟨hl.trans (common_word_anchor_lower p m).symm,
      hu.trans (common_word_anchor_upper p m).symm⟩
  · intro hd
    constructor
    · intro v
      have h := ((labelled_word_period_iff m v T).mpr hd).1
      exact ⟨fun hv => h.symm.trans hv, fun hv => h.trans hv⟩
    · intro v
      have h := ((labelled_word_period_iff m v T).mpr hd).2
      exact ⟨fun hv => h.symm.trans hv, fun hv => h.trans hv⟩

theorem labelled_word_period_first {m : ℕ} {T : ℤ} (hT : 0 < T)
    (hTm : T < (m : ℤ) * ((m : ℤ) + 1)) (v : ℤ) :
    ¬(Int.ModEq (m : ℤ) (v + T) v ∧ Int.ModEq ((m : ℤ) + 1) (v + T) v) := by
  intro h
  have hd := (labelled_word_period_iff m v T).mp h
  have hz := Int.dvd_iff_emod_eq_zero.mp hd
  rw [Int.emod_eq_of_lt hT.le hTm] at hz
  omega

end NField.ResetForests.PacketCycles
