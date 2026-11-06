/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.CotangentGrid
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The complete cotangent mass and its nonunit multiplicative orbits -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CotangentOrbitBound
open scoped BigOperators Classical
open CotangentGrid DedekindFourierMoment

def cotMass (m : ℕ) : ℝ := ∑ n ∈ Finset.Ico 1 m,|cotGrid m n|

theorem cot_mass_range {m : ℕ} (hm : 0 < m) :
    cotMass m=∑ n ∈ Finset.range m,|cotGrid m n| := by
  have hset : Finset.range m=insert 0 (Finset.Ico 1 m) := by
    ext n
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Ico]
    omega
  rw [hset,Finset.sum_insert (by simp),cot_grid_zero,abs_zero,zero_add]
  rfl

theorem cot_mass_harmonic {m : ℕ} (hm : 0 < m) :
    cotMass m ≤ (m : ℝ)*(harmonic m : ℝ) := by
  have he : sawtoothFourierNormMass m=cotMass m/2 := by
    rw [cot_mass_range hm,Finset.sum_div]
    unfold sawtoothFourierNormMass
    apply Finset.sum_congr rfl
    intro n hn
    exact norm_sawtooth_fourier_real_cot hm (Finset.mem_range.mp hn)
  have hb := sawtoothFourierNormMass_le hm
  rw [he] at hb
  linarith

/-- Title: `The real cotangent mass has the harmonic logarithmic bound`. -/
theorem cot_mass_logarithmic {m : ℕ} (hm : 0 < m) :
    cotMass m ≤ 3*(m : ℝ)*Real.log (2*(m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hl : (1/2 : ℝ) ≤ Real.log (2*(m : ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hlog : Real.log (m : ℝ) ≤ Real.log (2*(m : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  calc
    _ ≤ (m : ℝ)*(harmonic m : ℝ) := cot_mass_harmonic hm
    _ ≤ (m : ℝ)*(1+Real.log (m : ℝ)) := by
      gcongr
      exact harmonic_le_one_add_log m
    _ ≤ _ := by nlinarith

theorem full_cotangent_orbit {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∑ j ∈ Finset.range m,|cotGrid m (n*j)|)=
      (n.gcd m : ℝ)*cotMass (m/n.gcd m) := by
  let d := n.gcd m
  let q := m/d
  let h := n/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left m hn
  have hmfac : m=d*q := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)).symm
  have hnfac : n=d*h := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm
  have hq : 0 < q := Nat.div_pos (Nat.gcd_le_right n hm) hd
  have hcop : h.Coprime q := Nat.coprime_div_gcd_div_gcd hd
  have he := sum_mul_mod_of_factorization hd hq hmfac hnfac hcop
    (fun r => |cotGrid m r|)
  simp_rw [cot_grid_mod hm] at he
  rw [hmfac] at he
  simp_rw [cot_grid_mul_scale hd hq] at he
  rw [nsmul_eq_mul,← cot_mass_range hq] at he
  simpa only [← hmfac] using he

theorem unit_cotangent_orbit_le_full {m : ℕ} [NeZero m] (n : ℕ) :
    (∑ u : (ZMod m)ˣ,|cotGrid m (n*u.val.val)|) ≤
      ∑ j ∈ Finset.range m,|cotGrid m (n*j)| := by
  let φ := fun u : (ZMod m)ˣ => u.val.val
  have hφ : Function.Injective φ := by
    intro u v huv
    apply Units.val_injective
    exact ZMod.val_injective m huv
  have hsub : Finset.univ.image φ ⊆ Finset.range m := by
    intro j hj
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr u.val.val_lt
  calc
    _ = ∑ j ∈ Finset.univ.image φ,|cotGrid m (n*j)| := by
      rw [Finset.sum_image hφ.injOn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro j hj hnot; positivity)

/-- Title: `Cotangent orbits retain their exact common-divisor multiplicity`. -/
theorem unit_cotangent_orbit_bound {m n : ℕ} [NeZero m] (hn : 0 < n) :
    (∑ u : (ZMod m)ˣ,|cotGrid m (n*u.val.val)|) ≤
      (n.gcd m : ℝ)*cotMass (m/n.gcd m) := by
  rw [← full_cotangent_orbit (Nat.pos_of_ne_zero (NeZero.ne m)) hn]
  exact unit_cotangent_orbit_le_full n

theorem unit_cotangent_orbit_logarithmic {m n : ℕ} [NeZero m] (hn : 0 < n) :
    (∑ u : (ZMod m)ˣ,|cotGrid m (n*u.val.val)|) ≤
      3*(m : ℝ)*Real.log (2*(m : ℝ)) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hd : 0 < n.gcd m := Nat.gcd_pos_of_pos_left m hn
  have hq : 0 < m/n.gcd m := Nat.div_pos (Nat.gcd_le_right n hm) hd
  have hmfac : (n.gcd m : ℝ)*(m/n.gcd m : ℕ)=(m : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)
  calc
    _ ≤ (n.gcd m : ℝ)*cotMass (m/n.gcd m) := unit_cotangent_orbit_bound hn
    _ ≤ (n.gcd m : ℝ)*(3*(m/n.gcd m : ℕ)*Real.log (2*(m/n.gcd m : ℕ))) := by
      gcongr
      exact cot_mass_logarithmic hq
    _ ≤ (n.gcd m : ℝ)*(3*(m/n.gcd m : ℕ)*Real.log (2*(m : ℝ))) := by
      gcongr
      exact_mod_cast Nat.div_le_self m (n.gcd m)
    _ = 3*((n.gcd m : ℝ)*(m/n.gcd m : ℕ))*Real.log (2*(m : ℝ)) := by ring
    _ = _ := by rw [hmfac]

end NField.Alignment.CotangentOrbitBound
