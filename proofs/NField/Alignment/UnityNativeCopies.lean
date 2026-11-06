/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeHilbert

/-!
# Exact integer copies in the reciprocal-weight Hilbert space

The zero extension at the origin is retained throughout. Complete blocks
are regrouped with `Nat.divModEquiv`; their weights telescope exactly.
-/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.UnityNativeCopies
open scoped BigOperators
open UnityNativeWeights UnityNativeHilbert

/-- The actual block sum, including the otherwise exceptional initial block. -/
theorem copy_weighted_row (b : ℕ) (hb : 0<b) (F : ℕ → ℝ) (hF0 : F 0=0) (m : ℕ) :
    (∑ i : Fin b, weight (m*b+i) * F ((m*b+i)/b)) = weight m * F m / b := by
  have hd (i : Fin b) : (m*b+i)/b=m := by
    rw [Nat.add_div hb, Nat.mul_div_cancel _ hb, Nat.div_eq_of_lt i.is_lt, add_zero]
    simp [Nat.mod_eq_of_lt i.is_lt, Nat.not_le.mpr i.is_lt]
  simp_rw [hd]
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i : ℕ => weight (m*b+i))]
  by_cases hm : m=0
  · simp [hm, hF0]
  · rw [Nat.mul_comm m b, copy_block_weight b m hb (Nat.pos_of_ne_zero hm)]
    ring

/-- Regrouping a nonnegative native series under integer dilation. -/
theorem copied_weighted_summable (b : ℕ) (hb : 0<b) (F : ℕ → ℝ)
    (hF0 : F 0=0) (hF : ∀ m, 0≤F m) (hs : Summable (fun m => weight m * F m)) :
    Summable (fun n => weight n * F (n/b)) := by
  letI : NeZero b := ⟨hb.ne'⟩
  have hp : Summable (fun p : ℕ × Fin b => weight (p.1*b+p.2) * F ((p.1*b+p.2)/b)) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (weight_nonneg _) (hF _))).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype, copy_weighted_row b hb F hF0] using hs.div_const (b : ℝ)
  apply (Nat.divModEquiv b).symm.summable_iff.mp
  exact hp

/-- The corresponding infinite sum retains the exact factor `1 / b`. -/
theorem copied_weighted_tsum (b : ℕ) (hb : 0<b) (F : ℕ → ℝ)
    (hF0 : F 0=0) (hF : ∀ m, 0≤F m) (hs : Summable (fun m => weight m * F m)) :
    (∑' n, weight n * F (n/b)) = (∑' m, weight m * F m) / b := by
  letI : NeZero b := ⟨hb.ne'⟩
  have hc := copied_weighted_summable b hb F hF0 hF hs
  have hp : Summable (fun p : ℕ × Fin b => weight (p.1*b+p.2) * F ((p.1*b+p.2)/b)) :=
    (Nat.divModEquiv b).symm.summable_iff.mpr hc
  rw [← (Nat.divModEquiv b).symm.tsum_eq (fun n => weight n * F (n/b))]
  change (∑' p : ℕ × Fin b, weight (p.1*b+p.2) * F ((p.1*b+p.2)/b)) = _
  rw [hp.tsum_prod]
  simp only [tsum_fintype, copy_weighted_row b hb F hF0]
  exact tsum_div_const

/-- Every Hilbert vector has its actual native square sum, with zero origin. -/
theorem native_square_summable (f : NativeHilbert) :
    Summable (fun m : ℕ => weight m * value f m^2) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [pow_two, mul_assoc] using weighted_inner_summable f f

theorem weighted_square_tsum (f : NativeHilbert) :
    (∑' m : ℕ, weight m * value f m^2) = ‖f‖^2 := by
  have h := (native_square_summable f).sum_add_tsum_nat_add 1
  simpa [norm_sq_eq_weighted, weight_zero] using h.symm

/-- Dilation of the actual native sequence with the paper's zero boundary. -/
def copy (b : ℕ) (hb : 0<b) (f : NativeHilbert) : NativeHilbert :=
  ofFunction (fun n => value f (n/b))
    ((summable_nat_add_iff 1).mpr
      (copied_weighted_summable b hb (fun m => value f m^2) (by simp)
        (fun m => sq_nonneg _) (native_square_summable f)))

@[simp] theorem copy_value (b : ℕ) (hb : 0<b) (f : NativeHilbert) (n : ℕ) :
    value (copy b hb f) n = value f (n/b) := by
  by_cases hn : n=0
  · simp [hn]
  · exact value_ofFunction _ _ (Nat.pos_of_ne_zero hn)

/-- Title: `Integer copies scale native energy exactly`.

 The exact native norm scaling, for every Hilbert vector. -/
theorem copy_norm_sq (b : ℕ) (hb : 0<b) (f : NativeHilbert) :
    ‖copy b hb f‖^2 = ‖f‖^2 / b := by
  rw [← weighted_square_tsum]
  simp_rw [copy_value]
  rw [copied_weighted_tsum b hb (fun m => value f m^2) (by simp)
    (fun m => sq_nonneg _) (native_square_summable f), weighted_square_tsum]

theorem copy_add (b : ℕ) (hb : 0<b) (f g : NativeHilbert) :
    copy b hb (f+g) = copy b hb f + copy b hb g := by
  apply ext_value
  intro n hn
  simp [copy_value, value_add]

theorem copy_smul (b : ℕ) (hb : 0<b) (c : ℝ) (f : NativeHilbert) :
    copy b hb (c • f) = c • copy b hb f := by
  apply ext_value
  intro n hn
  simp [copy_value, value_smul]

/-- The copy operation is linear in the actual native Hilbert space. -/
def copyLinear (b : ℕ) (hb : 0<b) : NativeHilbert →ₗ[ℝ] NativeHilbert where
  toFun := copy b hb
  map_add' := copy_add b hb
  map_smul' c f := copy_smul b hb c f

/-- Title: `Integer copies preserve signed inner products up to scale`. -/
theorem copy_inner (b : ℕ) (hb : 0<b) (f g : NativeHilbert) :
    inner ℝ (copy b hb f) (copy b hb g) = inner ℝ f g / b := by
  have he := copy_norm_sq b hb (f+g)
  rw [copy_add, norm_add_sq_real, norm_add_sq_real, copy_norm_sq, copy_norm_sq] at he
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp at he ⊢
  linarith

/-- Title: `Native integer copies compose exactly`.

 Integer copies compose without boundary corrections. -/
theorem copy_copy (a b : ℕ) (ha : 0<a) (hb : 0<b) (f : NativeHilbert) :
    copy a ha (copy b hb f) = copy (a*b) (Nat.mul_pos ha hb) f := by
  apply ext_value
  intro n hn
  simp only [copy_value, Nat.div_div_eq_div_mul]

theorem copy_one (f : NativeHilbert) : copy 1 (by omega) f = f := by
  apply ext_value
  intro n hn
  simp only [copy_value, Nat.div_one]

end NField.Alignment.UnityNativeCopies
