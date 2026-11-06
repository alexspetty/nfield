/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TerminalSupportSource

/-! # Every interval of the terminal digit support is a singleton -/

namespace NField.Alignment.TerminalSingletonSupport
open TerminalCarrySource TerminalSupportSource

/-- Title: `Adjacent cells cannot both belong to the terminal digit support`. -/
theorem terminal_support_no_adjacent {p N n : ℕ} (hp : 2 ≤ p) (hN : 2 ≤ N)
    (hn : n ∈ terminalDigitSupport p N) : n + 1 ∉ terminalDigitSupport p N := by
  intro hn'
  simp only [terminalDigitSupport, Finset.mem_filter, Finset.mem_range] at hn hn'
  have hp0 : 0 < p := by omega
  have hP : 0 < p ^ (N - 1) := pow_pos hp0 _
  have hpow : p ^ N = p * p ^ (N - 1) := by
    calc
      p ^ N = p ^ ((N - 1) + 1) := by congr 1; omega
      _ = _ := pow_succ' _ _
  have ha : n / p ^ (N - 1) < p := by
    rw [Nat.div_lt_iff_lt_mul hP]
    simpa only [hpow] using hn.1
  have hmono : n / p ^ (N - 1) ≤ (n + 1) / p ^ (N - 1) :=
    Nat.div_le_div_right (by omega)
  have hnext : (n + 1) % p = (n % p + 1) % p := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < p)]
  have hb : (n + 1) / p ^ (N - 1) = (n / p ^ (N - 1) + 1) % p := by
    rw [hn'.2, hnext, hn.2]
  have hstep : (n + 1) / p ^ (N - 1) = n / p ^ (N - 1) + 1 := by
    by_cases hlt : n / p ^ (N - 1) + 1 < p
    · simpa only [Nat.mod_eq_of_lt hlt] using hb
    · have he : n / p ^ (N - 1) + 1 = p := by omega
      rw [he, Nat.mod_self] at hb
      omega
  have h₁ := Nat.div_add_mod n (p ^ (N - 1))
  have h₂ := Nat.div_add_mod (n + 1) (p ^ (N - 1))
  have hr := Nat.mod_lt n hP
  have hzero : (n + 1) % p ^ (N - 1) = 0 := by
    rw [hstep] at h₂
    have hnonneg : 0 ≤ (n + 1) % p ^ (N - 1) := Nat.zero_le _
    nlinarith
  have hdiv : p ∣ p ^ (N - 1) := by
    rw [terminal_top_power hN]
    exact dvd_mul_right _ _
  have hlast : (n + 1) % p = 0 := by
    rw [← Nat.mod_mod_of_dvd _ hdiv, hzero, Nat.zero_mod]
  rw [hlast] at hn'
  omega

end NField.Alignment.TerminalSingletonSupport
