/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionResetIntegrability

/-!
# The infinite collision coboundary and compensation over blocks

Translation acts on the actual profinite Haar space. Absolute L² summability
of the reset series passes the finite carry law to the infinite potential.
-/

noncomputable section

namespace NField.Alignment.CollisionPotentialCoboundary

open scoped BigOperators ENNReal
open Filter MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionPotentialHilbert CollisionPotentialConvergence CollisionResetIntegrability

def translate (z : ℤ) (x : Phase) : Phase := integerPhase z * x

@[simp] theorem integerPhase_zero : integerPhase 0 = 1 := rfl

theorem integerPhase_add (a b : ℤ) : integerPhase (a+b) = integerPhase a * integerPhase b := by
  rfl

@[simp] theorem translate_zero (x : Phase) : translate 0 x = x := by
  simp [translate]

theorem translate_add (a b : ℤ) (x : Phase) :
    translate (a+b) x = translate a (translate b x) := by
  simp only [translate, integerPhase_add, mul_assoc]

theorem translate_measurePreserving (z : ℤ) :
    MeasurePreserving (translate z) phaseHaar phaseHaar :=
  measurePreserving_mul_left phaseHaar (integerPhase z)

theorem residue_translate (k : ℕ) [NeZero k] (z : ℤ) (x : Phase) :
    (residueHom k (translate z x)).toAdd = (z : ZMod k) + (residueHom k x).toAdd := by
  unfold translate
  rw [map_mul]
  change (residueHom k (integerPhase z)).toAdd + (residueHom k x).toAdd = _
  rw [residue_integer]

theorem centered_backward_step {k : ℕ} (hk : 0 < k) (x : Phase) :
    centered k x - centered k (translate (-1) x) =
      1 - (resetSet k).indicator (fun _ => (k : ℝ)) x := by
  letI : NeZero k := ⟨hk.ne'⟩
  let u := (residueHom k x).toAdd
  have hres : (residueHom k (translate (-1) x)).toAdd = u - 1 := by
    rw [residue_translate]
    dsimp [u]
    push_cast
    ring
  rw [centered_eq, centered_eq, hres]
  simp only [resetSet, dif_pos hk, Set.indicator_apply, Set.mem_setOf_eq]
  change ((u.val : ℝ) - ((k : ℝ)-1)/2) -
      (((u-1).val : ℝ) - ((k : ℝ)-1)/2) = 1 - if u = 0 then (k : ℝ) else 0
  by_cases hu : u = 0
  · rw [hu, if_pos rfl]
    have hn : (-1 : ZMod k).val = k - 1 := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simp only [ZMod.val_neg_one, Nat.succ_sub_one]
    simp only [zero_sub, ZMod.val_zero, Nat.cast_zero, hn]
    rw [Nat.cast_sub hk]
    ring
  · have huk : k ≠ 1 := by
      intro h
      subst k
      exact hu (Subsingleton.elim _ _)
    have huval : 1 ≤ u.val := by
      have hn : u.val ≠ 0 := by intro h; exact hu ((ZMod.val_eq_zero u).mp h)
      omega
    have hsub : (1 : ZMod k).val ≤ u.val := by simpa [ZMod.val_one'' huk] using huval
    rw [ZMod.val_sub hsub, ZMod.val_one'' huk, Nat.cast_sub huval]
    rw [if_neg hu]
    ring

def shift (z : ℤ) : HaarL2 →ₗᵢ[ℝ] HaarL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (translate z) (translate_measurePreserving z)

theorem shift_coe (z : ℤ) (f : HaarL2) :
    (fun x => shift z f x) =ᵐ[phaseHaar] (fun x => f (translate z x)) :=
  Lp.coeFn_compMeasurePreserving f (translate_measurePreserving z)

@[simp] theorem shift_zero (f : HaarL2) : shift 0 f = f := by
  change Lp.compMeasurePreserving (translate 0) _ f = f
  have h : translate 0 = id := funext translate_zero
  simp [h]

theorem shift_add (a b : ℤ) (f : HaarL2) : shift (a+b) f = shift a (shift b f) := by
  have h : translate (a+b) = translate b ∘ translate a := by
    funext x
    rw [add_comm a b, translate_add]
    rfl
  change Lp.compMeasurePreserving (translate (a+b)) _ f =
    Lp.compMeasurePreserving (translate a) _ (Lp.compMeasurePreserving (translate b) _ f)
  simpa only [← h] using
    (Lp.compMeasurePreserving_comp_apply f (translate_measurePreserving b)
      (translate_measurePreserving a))

theorem weighted_remainder_step {k : ℕ} (hk : 0 < k) :
    collisionWeight k • (remainderVector k - shift (-1) (remainderVector k)) =
      collisionWeight k • oneVector - resetVector 2 k := by
  apply Lp.ext
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (remainderMap k)
  have hp := (translate_measurePreserving (-1)).quasiMeasurePreserving.ae hr
  have ho := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase, ℝ))
  filter_upwards [Lp.coeFn_smul (collisionWeight k)
      (remainderVector k - shift (-1) (remainderVector k)),
    Lp.coeFn_sub (remainderVector k) (shift (-1) (remainderVector k)),
    shift_coe (-1) (remainderVector k), hr, hp,
    Lp.coeFn_sub (collisionWeight k • oneVector) (resetVector 2 k),
    Lp.coeFn_smul (collisionWeight k) oneVector, ho, resetVector_coe 2 k]
    with x hsm hsub hsh hrx hpx hsub' hsm' hox hreset
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hsm hsub hsub' hsm'
  rw [hsm, hsub, hsub', hsm', hreset]
  change collisionWeight k * (remainderVector k x - shift (-1) (remainderVector k) x) =
    collisionWeight k * oneVector x - resetTerm k x
  rw [hsh, show remainderVector k x = centered k x from hrx,
    show remainderVector k (translate (-1) x) = centered k (translate (-1) x) from hpx,
    show oneVector x = 1 from hox, centered_backward_step hk]
  unfold resetTerm
  by_cases hx : x ∈ resetSet k
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    ring

theorem finitePotential_backward_step (M : ℕ) :
    finitePotential collisionWeight M - shift (-1) (finitePotential collisionWeight M) =
      (2/3 : ℝ) • ((∑ k ∈ Finset.Icc 2 M, collisionWeight k) • oneVector -
        ∑ k ∈ Finset.Icc 2 M, resetVector 2 k) := by
  simp only [finitePotential, map_smul, map_sum, ← smul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact weighted_remainder_step (by have := (Finset.mem_Icc.mp hk).1; omega)

theorem reset_partial_tendsto :
    Tendsto (fun M => ∑ k ∈ Finset.Icc 2 M, resetVector 2 k) atTop
      (nhds (∑' k, resetVector 2 k)) := by
  have hs : Summable (resetVector 2) :=
    (resetVector_norm_summable 2 (by norm_num) (by norm_num)).of_norm
  have he (M : ℕ) : (∑ k ∈ Finset.range (M+1), resetVector 2 k) =
      ∑ k ∈ Finset.Icc 2 M, resetVector 2 k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk hnot
      have hkN := Finset.mem_range.mp hk
      have hk2 : k < 2 := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
        omega
      interval_cases k <;> simp
  simpa only [Function.comp_def, he] using hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem collisionPotential_coboundary :
    collisionPotential - shift (-1) collisionPotential =
      (2/3 : ℝ) • (oneVector - ∑' k, resetVector 2 k) := by
  have hw : Tendsto (fun M => ∑ k ∈ Finset.Icc 2 M, collisionWeight k)
      atTop (nhds (1 : ℝ)) := by
    simpa only [Function.comp_def, sum_range_zero_one collisionWeight (by simp) (by simp)] using
      collisionWeight_hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hleft := tendsto_collisionPotential.sub
    ((shift (-1)).continuous.tendsto collisionPotential |>.comp tendsto_collisionPotential)
  have hright := ((hw.smul (tendsto_const_nhds (x := oneVector))).sub
    reset_partial_tendsto).const_smul (2/3 : ℝ)
  simp only [one_smul] at hright
  change Tendsto (fun M => finitePotential collisionWeight M -
    shift (-1) (finitePotential collisionWeight M)) _ _ at hleft
  simp only [finitePotential_backward_step] at hleft
  exact tendsto_nhds_unique hleft hright

def increment (x : Phase) : ℝ := (2/3 : ℝ) * (1-resetFunction x)

def incrementVector : HaarL2 := collisionPotential - shift (-1) collisionPotential

theorem incrementVector_coe : (fun x => incrementVector x) =ᵐ[phaseHaar] increment := by
  unfold incrementVector
  rw [collisionPotential_coboundary]
  have ho := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (1 : C(Phase, ℝ))
  filter_upwards [Lp.coeFn_smul (2/3 : ℝ) (oneVector - ∑' k, resetVector 2 k),
    Lp.coeFn_sub oneVector (∑' k, resetVector 2 k), ho,
    resetVector_tsum_coe 2 (by norm_num)] with x hsm hsub hone hrs
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hsm hsub
  rw [hsm, hsub, hrs, show oneVector x = 1 from hone]
  rfl

theorem increment_coboundary_ae :
    increment =ᵐ[phaseHaar] (fun x => collisionPotential x - collisionPotential (translate (-1) x)) := by
  filter_upwards [incrementVector_coe,
    Lp.coeFn_sub collisionPotential (shift (-1) collisionPotential),
    shift_coe (-1) collisionPotential] with x hx hsub hshift
  simp only [Pi.sub_apply] at hsub
  exact hx.symm.trans (hsub.trans (by rw [hshift]))

theorem block_telescope (H : ℕ) :
    (∑ j ∈ Finset.Icc 1 H, shift (j : ℤ) incrementVector) =
      shift (H : ℤ) collisionPotential - collisionPotential := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H+1), ih]
      simp only [incrementVector, map_sub, ← shift_add]
      rw [show ((H+1 : ℕ) : ℤ) + (-1) = (H : ℤ) by omega]
      abel

theorem block_norm_bound (H : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 H, shift (j : ℤ) incrementVector‖ ≤ 2 * ‖collisionPotential‖ := by
  rw [block_telescope]
  calc
    _ ≤ ‖shift (H : ℤ) collisionPotential‖ + ‖collisionPotential‖ := norm_sub_le _ _
    _ = _ := by rw [(shift (H : ℤ)).norm_map]; ring

def blockFunction (H : ℕ) (x : Phase) : ℝ :=
  ∑ j ∈ Finset.Icc 1 H, increment (translate (j : ℤ) x)

theorem block_coe (H : ℕ) :
    (fun x => (∑ j ∈ Finset.Icc 1 H, shift (j : ℤ) incrementVector) x) =ᵐ[phaseHaar]
      blockFunction H := by
  have hs : ∀ᵐ x ∂phaseHaar, ∀ j : ℕ,
      shift (j : ℤ) incrementVector x = increment (translate (j : ℤ) x) := by
    apply ae_all_iff.mpr
    intro j
    have hj : ∀ᵐ x ∂phaseHaar, incrementVector (translate (j : ℤ) x) =
        increment (translate (j : ℤ) x) :=
      (translate_measurePreserving (j : ℤ)).quasiMeasurePreserving.ae
        (p := fun y => incrementVector y = increment y) incrementVector_coe
    filter_upwards [shift_coe (j : ℤ) incrementVector, hj] with x hx hy
    exact hx.trans hy
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.Icc 1 H)
    (fun j => shift (j : ℤ) incrementVector), hs] with x hx hsx
  exact hx.trans (Finset.sum_congr rfl (fun j _ => hsx j))

theorem block_telescope_ae (H : ℕ) :
    blockFunction H =ᵐ[phaseHaar]
      (fun x => collisionPotential (translate (H : ℤ) x) - collisionPotential x) := by
  have hc := block_coe H
  rw [block_telescope] at hc
  filter_upwards [hc, Lp.coeFn_sub (shift (H : ℤ) collisionPotential) collisionPotential,
    shift_coe (H : ℤ) collisionPotential] with x hx hsub hshift
  simp only [Pi.sub_apply] at hsub
  exact hx.symm.trans (hsub.trans (by rw [hshift]))

theorem block_second_moment (H : ℕ) :
    (∫ x, |blockFunction H x|^2 ∂phaseHaar) ≤ 4 * ‖collisionPotential‖^2 := by
  let F : HaarL2 := ∑ j ∈ Finset.Icc 1 H, shift (j : ℤ) incrementVector
  have he : (∫ x, |blockFunction H x|^2 ∂phaseHaar) = ‖F‖^2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [block_coe H] with x hx
    change |blockFunction H x|^2 = inner ℝ (F x) (F x)
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, show F x = blockFunction H x from hx]
  rw [he]
  have h := block_norm_bound H
  change ‖F‖ ≤ 2 * ‖collisionPotential‖ at h
  nlinarith [norm_nonneg F, norm_nonneg collisionPotential]

/-- All clauses of the manuscript's exact-compensation theorem. -/
theorem exact_compensation :
    (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → MemLp resetFunction p phaseHaar) ∧
    (∫ x, resetFunction x ∂phaseHaar) = 1 ∧
    increment =ᵐ[phaseHaar]
      (fun x => collisionPotential x - collisionPotential (translate (-1) x)) ∧
    (∀ H : ℕ, blockFunction H =ᵐ[phaseHaar]
      (fun x => collisionPotential (translate (H : ℤ) x) - collisionPotential x)) ∧
    (∀ H : ℕ, (∫ x, |blockFunction H x|^2 ∂phaseHaar) ≤ 4 * ‖collisionPotential‖^2) := by
  exact ⟨resetFunction_memLp, resetFunction_mean, increment_coboundary_ae,
    block_telescope_ae, block_second_moment⟩

end NField.Alignment.CollisionPotentialCoboundary
