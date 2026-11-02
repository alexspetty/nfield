/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialConvergence

/-!
# Quantitative cutoff for the actual Haar collision potential

The Gram-box capacity estimate, applied on each dyadic block with the
logarithmic collision weight bound, gives the manuscript's sharp cutoff order.
-/

noncomputable section

namespace NField.Alignment.CollisionPotentialCutoff

open scoped BigOperators
open Filter CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialConvergence

theorem block_norm_log_bound {L : ℕ} (hL : 1 ≤ L) :
    ‖potentialOn (Finset.Ioc L (2 * L)) collisionWeight‖ ≤
      (1 + Real.log (2 * (L : ℝ))) * (L : ℝ)^(-(1 / 2 : ℝ)) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hlog : 0 ≤ 1 + Real.log (2 * (L : ℝ)) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (L : ℝ) by exact_mod_cast (by omega : 1 ≤ 2 * L))
    linarith
  have h := potentialOn_norm_sq_bound (Finset.Ioc L (2 * L)) collisionWeight (2 * L)
    ((1 + Real.log (2 * (L : ℝ))) / (L : ℝ))
    (by intro k hk; have hk' := Finset.mem_Ioc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩)
    (fun k _ => collisionWeight_nonneg k) (div_nonneg hlog hLR.le)
    (by
      intro k hk
      obtain ⟨hkL, hk2L⟩ := Finset.mem_Ioc.mp hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      calc
        _ ≤ (k : ℝ) * ((1 + Real.log (k : ℝ)) / (k : ℝ)^2) :=
          mul_le_mul_of_nonneg_left (collisionWeight_log_bound (by omega)) hkR.le
        _ = (1 + Real.log (k : ℝ)) / (k : ℝ) := by field_simp
        _ ≤ (1 + Real.log (2 * (L : ℝ))) / (k : ℝ) :=
          div_le_div_of_nonneg_right
            (add_le_add_right (Real.log_le_log hkR (show (k : ℝ) ≤ 2 * (L : ℝ) by exact_mod_cast hk2L)) 1) hkR.le
        _ ≤ _ := div_le_div_of_nonneg_left hlog hLR (by exact_mod_cast hkL.le))
  have he : ((1 + Real.log (2 * (L : ℝ))) * (L : ℝ)^(-(1 / 2 : ℝ)))^2 =
      (1 + Real.log (2 * (L : ℝ)))^2 / (L : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hLR.le]
    norm_num only [show (-(1 / 2 : ℝ)) * 2 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hsq : ‖potentialOn (Finset.Ioc L (2 * L)) collisionWeight‖^2 ≤
      ((1 + Real.log (2 * (L : ℝ))) * (L : ℝ)^(-(1 / 2 : ℝ)))^2 := by
    rw [he]
    apply h.trans
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have : 0 ≤ (1 + Real.log (2 * (L : ℝ)))^2 / (L : ℝ) := by positivity
    field_simp
    nlinarith [sq_nonneg (1 + Real.log (2 * (L : ℝ)))]
  have hn : 0 ≤ (1 + Real.log (2 * (L : ℝ))) * (L : ℝ)^(-(1 / 2 : ℝ)) := by positivity
  nlinarith [norm_nonneg (potentialOn (Finset.Ioc L (2 * L)) collisionWeight)]

def cutoffRatio : ℝ := (2 : ℝ)^(-(1 / 2 : ℝ))

theorem cutoffRatio_pos : 0 < cutoffRatio := Real.rpow_pos_of_pos (by norm_num) _

theorem cutoffRatio_lt_one : cutoffRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem cutoff_series_summable : Summable (fun i : ℕ => ((i : ℝ) + 1) * cutoffRatio^i) := by
  have hr : ‖cutoffRatio‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos cutoffRatio_pos]; exact cutoffRatio_lt_one
  have h := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
    (summable_geometric_of_norm_lt_one hr)
  simpa only [pow_one, add_mul, one_mul] using h

def cutoffConstant : ℝ := ∑' i : ℕ, ((i : ℝ) + 1) * cutoffRatio^i

theorem cutoffConstant_nonneg : 0 ≤ cutoffConstant := by
  apply tsum_nonneg
  intro i
  have := cutoffRatio_pos
  positivity

theorem scaled_block_bound {M : ℕ} (hM : 1 ≤ M) (i : ℕ) :
    ‖potentialOn (Finset.Ioc (2^i * M) (2 * (2^i * M))) collisionWeight‖ ≤
      (((i : ℝ) + 1) * cutoffRatio^i) *
        ((1 + Real.log (2 * (M : ℝ))) * (M : ℝ)^(-(1 / 2 : ℝ))) := by
  have hr := cutoffRatio_pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : 1 ≤ 2^i * M := Nat.mul_pos (by positivity) hM
  have h := block_norm_log_bound hp
  have he : ((2^i * M : ℕ) : ℝ)^(-(1 / 2 : ℝ)) =
      cutoffRatio^i * (M : ℝ)^(-(1 / 2 : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_two, Real.mul_rpow (by positivity) hMR.le]
    congr 1
    rw [← Real.rpow_natCast_mul (by norm_num)]
    unfold cutoffRatio
    rw [← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  have heLog : 1 + Real.log (2 * ((2^i * M : ℕ) : ℝ)) =
      1 + Real.log (2 * (M : ℝ)) + (i : ℝ) * Real.log 2 := by
    push_cast
    rw [show (2 : ℝ) * (2^i * M) = (2 * M) * 2^i by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  have hl : Real.log 2 ≤ 1 + Real.log (2 * (M : ℝ)) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ 2 * M by exact_mod_cast (by omega : 2 ≤ 2 * M))
    linarith
  rw [he, heLog] at h
  apply h.trans
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hiL := mul_le_mul_of_nonneg_left hl hi
  have hnon : 0 ≤ cutoffRatio^i * (M : ℝ)^(-(1 / 2 : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hiL hnon]

theorem dyadic_cutoff_bound {M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    ‖finitePotential collisionWeight (2^j * M) - finitePotential collisionWeight M‖ ≤
      (∑ i ∈ Finset.range j, ((i : ℝ) + 1) * cutoffRatio^i) *
        ((1 + Real.log (2 * (M : ℝ))) * (M : ℝ)^(-(1 / 2 : ℝ))) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hp : 1 ≤ 2^j * M := Nat.mul_pos (by positivity) hM
      rw [show 2^(j+1) * M = 2 * (2^j * M) by ring,
        finitePotential_double hp, Finset.sum_range_succ, add_mul]
      rw [show finitePotential collisionWeight (2^j * M) +
          potentialOn (Finset.Ioc (2^j * M) (2 * (2^j * M))) collisionWeight -
          finitePotential collisionWeight M =
          (finitePotential collisionWeight (2^j * M) - finitePotential collisionWeight M) +
          potentialOn (Finset.Ioc (2^j * M) (2 * (2^j * M))) collisionWeight by abel]
      exact (norm_add_le _ _).trans (add_le_add ih (scaled_block_bound hM j))

theorem collisionPotential_cutoff_bound {M : ℕ} (hM : 1 ≤ M) :
    ‖collisionPotential - finitePotential collisionWeight M‖ ≤
      cutoffConstant * (1 + Real.log (2 * (M : ℝ))) / Real.sqrt (M : ℝ) := by
  have hindex : Tendsto (fun j : ℕ => 2^j * M) atTop atTop := by
    apply tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right (2^j) hM)
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim := ((tendsto_collisionPotential.comp hindex).sub
    (tendsto_const_nhds (x := finitePotential collisionWeight M))).norm
  have hb : ∀ j : ℕ,
      ‖finitePotential collisionWeight (2^j * M) - finitePotential collisionWeight M‖ ≤
        cutoffConstant * ((1 + Real.log (2 * (M : ℝ))) * (M : ℝ)^(-(1/2 : ℝ))) := by
    intro j
    apply (dyadic_cutoff_bound hM j).trans
    have hr := cutoffRatio_pos
    apply mul_le_mul_of_nonneg_right
      (cutoff_series_summable.sum_le_tsum (Finset.range j) (fun i _ => by positivity))
    have : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * M))
    positivity
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hb)
  rw [Real.rpow_neg (Nat.cast_nonneg M), ← Real.sqrt_eq_rpow] at h
  simpa only [div_eq_mul_inv, mul_assoc] using h

theorem collisionPotential_cutoff_isBigO :
    (fun M : ℕ => collisionPotential - finitePotential collisionWeight M) =O[atTop]
      (fun M : ℕ => Real.log (2 * (M : ℝ)) / Real.sqrt (M : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (cutoffConstant * (1 + 1 / Real.log 2))
  filter_upwards [eventually_ge_atTop 1] with M hM
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ 2 * M))
  have hs : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (le_trans h2.le hl) hs.le)]
  apply (collisionPotential_cutoff_bound hM).trans
  have hratio : 1 ≤ Real.log (2 * (M : ℝ)) / Real.log 2 := (le_div_iff₀ h2).mpr (by simpa using hl)
  have hlog : 1 + Real.log (2 * (M : ℝ)) ≤
      (1 + 1 / Real.log 2) * Real.log (2 * (M : ℝ)) := by
    calc
      _ ≤ Real.log (2 * (M : ℝ)) / Real.log 2 + Real.log (2 * (M : ℝ)) := add_le_add_left hratio _
      _ = _ := by ring
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog cutoffConstant_nonneg) hs.le
  convert h using 1
  ring

end NField.Alignment.CollisionPotentialCutoff
