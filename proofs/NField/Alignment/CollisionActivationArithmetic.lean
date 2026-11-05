/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionHitConditioning
import NField.Alignment.CollisionConductorCosts

/-!
# Arithmetic monotonicity of prime activation

Changing a prime coordinate from an inactive block to a hit preserves
every divisor term prime to that coordinate, and only adds other positive
terms. The infinite assertion is stated on the proved summability domain.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionActivationArithmetic

open scoped BigOperators Classical ENNReal
open MeasureTheory
open ProfiniteRemainderMeasure CollisionRemainderDynamics CollisionMassReadout
open CollisionResetIntegrability CollisionPotentialCoboundary
open CollisionPrimeHit CollisionHitConditioning

def agreesAway (p : ℕ) (x y : Phase) : Prop :=
  ∀ k : ℕ, ∀ hk : 0<k,
    letI : NeZero k := ⟨hk.ne'⟩
    ¬p∣k → (residueHom k x).toAdd=(residueHom k y).toAdd

def forcingTermBlock (h k : ℕ) (x : Phase) : ℝ :=
  ∑ j : Fin h, resetTerm k (translate ((j.val : ℤ)+1) x)

def forcingBlock (h : ℕ) (x : Phase) : ℝ :=
  ∑ j : Fin h, resetFunction (translate ((j.val : ℤ)+1) x)

def blockResetSummable (h : ℕ) (x : Phase) : Prop :=
  ∀ j : Fin h, Summable (fun k : ℕ => resetTerm k (translate ((j.val : ℤ)+1) x))

def agreesAwayBelow (p M : ℕ) (x y : Phase) : Prop :=
  ∀ k : ℕ, k≤M → ∀ hk : 0<k,
    letI : NeZero k := ⟨hk.ne'⟩
    ¬p∣k → (residueHom k x).toAdd=(residueHom k y).toAdd

def forcingCutoff (h M : ℕ) (x : Phase) : ℝ :=
  ∑ k∈Finset.range (M+1), forcingTermBlock h k x

theorem ae_resetTerm_summable : ∀ᵐ x ∂phaseHaar, Summable (fun k : ℕ => resetTerm k x) := by
  letI : Fact (1≤(1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hn : ∑' k, ‖resetVector 1 k‖ₑ≠∞ := by
    simpa only [ofReal_norm] using (resetVector_norm_summable 1 le_rfl (by norm_num)).tsum_ofReal_ne_top
  have hs : ∀ᵐ x ∂phaseHaar, Summable (fun k : ℕ => ‖resetVector 1 k x‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top le_rfl (fun k => Lp.aestronglyMeasurable (resetVector 1 k))
    simpa only [Lp.enorm_def] using hn
  have he : ∀ᵐ x ∂phaseHaar, ∀ k : ℕ, resetVector 1 k x=resetTerm k x :=
    ae_all_iff.mpr (resetVector_coe 1)
  filter_upwards [hs,he] with x hx he
  exact (hx.congr (fun k => congrArg norm (he k))).of_norm

theorem blockResetSummable_ae (h : ℕ) : ∀ᵐ x ∂phaseHaar, blockResetSummable h x := by
  change ∀ᵐ x ∂phaseHaar, ∀ j : Fin h,
    Summable (fun k : ℕ => resetTerm k (translate ((j.val : ℤ)+1) x))
  apply ae_all_iff.mpr
  intro j
  exact (translate_measurePreserving ((j.val : ℤ)+1)).quasiMeasurePreserving.ae
    (p := fun x : Phase => Summable (fun k : ℕ => resetTerm k x)) ae_resetTerm_summable

theorem forcingTermBlock_nonneg (h k : ℕ) (x : Phase) : 0≤forcingTermBlock h k x :=
  Finset.sum_nonneg (fun _ _ => resetTerm_nonneg k _)

theorem forcingTermBlock_summable (h : ℕ) (x : Phase) (hx : blockResetSummable h x) :
    Summable (fun k : ℕ => forcingTermBlock h k x) := by
  have hs (s : Finset (Fin h)) : Summable
      (fun k : ℕ => ∑ j∈s, resetTerm k (translate ((j.val : ℤ)+1) x)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hx i).add ih
  exact hs Finset.univ

theorem forcingBlock_tsum (h : ℕ) (x : Phase) (hx : blockResetSummable h x) :
    forcingBlock h x=∑' k : ℕ, forcingTermBlock h k x := by
  unfold forcingBlock forcingTermBlock resetFunction
  rw [Summable.tsum_finsetSum (fun j _ => hx j)]

theorem resetTerm_eq_away {p k : ℕ} {x y : Phase} (hxy : agreesAway p x y)
    (hk : ¬p∣k) (j : ℕ) :
    resetTerm k (translate ((j : ℤ)+1) x)=resetTerm k (translate ((j : ℤ)+1) y) := by
  have hk0 : 0<k := Nat.pos_of_ne_zero (fun he => hk (he ▸ dvd_zero p))
  letI : NeZero k := ⟨hk0.ne'⟩
  have he := hxy k hk0 hk
  simp only [resetTerm,Set.indicator_apply,resetSet,dif_pos hk0,Set.mem_setOf_eq,
    residue_translate,he]

theorem inactive_multiple_zero {p h k j : ℕ} [NeZero p] {x : Phase}
    (hx : hitCoordinate p h x=false) (hj : j<h) (hpk : p∣k) :
    resetTerm k (translate ((j : ℤ)+1) x)=0 := by
  by_cases hk : k=0
  · simp [hk]
  have hk0 := Nat.pos_of_ne_zero hk
  have hp0 := Nat.pos_of_ne_zero (NeZero.ne p)
  apply Set.indicator_of_notMem
  intro hmem
  have hloc : x∈locationSet p j := locationSet_subset_of_dvd hp0 hk0 hpk j hmem
  have ht := (hitCoordinate_locations x).mpr ⟨j,hj,hloc⟩
  rw [hx] at ht
  cases ht

theorem forcingTermBlock_activation_mono {p h : ℕ} [NeZero p] {x y : Phase}
    (hx : hitCoordinate p h x=false) (hxy : agreesAway p x y) (k : ℕ) :
    forcingTermBlock h k x≤forcingTermBlock h k y := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hpk : p∣k
  · rw [inactive_multiple_zero hx j.isLt hpk]
    exact resetTerm_nonneg k _
  · exact le_of_eq (resetTerm_eq_away hxy hpk j.val)

theorem forcingTermBlock_prime_increment {p h : ℕ} [NeZero p] {x y : Phase}
    (hx : hitCoordinate p h x=false) (hy : hitCoordinate p h y=true) :
    (p : ℝ)*collisionWeight p ≤ forcingTermBlock h p y-forcingTermBlock h p x := by
  have hz : forcingTermBlock h p x=0 :=
    Finset.sum_eq_zero (fun j _ => inactive_multiple_zero hx j.isLt (dvd_refl p))
  obtain ⟨j,hj,hmem⟩ := (hitCoordinate_locations y).mp hy
  change translate ((j : ℤ)+1) y∈resetSet p at hmem
  have he : resetTerm p (translate ((j : ℤ)+1) y)=(p : ℝ)*collisionWeight p :=
    Set.indicator_of_mem hmem _
  rw [hz,sub_zero]
  have ht := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin h => resetTerm p (translate ((j.val : ℤ)+1) y))
    (fun i _ => resetTerm_nonneg p _) (Finset.mem_univ (⟨j,hj⟩ : Fin h))
  exact he.symm.trans_le ht

theorem forcingBlock_prime_activation {p h : ℕ} [NeZero p] {x y : Phase}
    (hx : hitCoordinate p h x=false) (hy : hitCoordinate p h y=true)
    (hxy : agreesAway p x y) (hsx : blockResetSummable h x) (hsy : blockResetSummable h y) :
    forcingBlock h x+(p : ℝ)*collisionWeight p ≤ forcingBlock h y := by
  have hs := (forcingTermBlock_summable h y hsy).sub (forcingTermBlock_summable h x hsx)
  have ht := hs.le_tsum p (fun k _ => sub_nonneg.mpr (forcingTermBlock_activation_mono hx hxy k))
  have hh := (forcingTermBlock_prime_increment hx hy).trans ht
  rw [Summable.tsum_sub (forcingTermBlock_summable h y hsy) (forcingTermBlock_summable h x hsx),
    ← forcingBlock_tsum h y hsy,← forcingBlock_tsum h x hsx] at hh
  linarith

theorem forcingBlock_Icc (h : ℕ) (x : Phase) :
    forcingBlock h x=∑ j∈Finset.Icc 1 h, resetFunction (translate (j : ℤ) x) := by
  induction h with
  | zero => simp [forcingBlock]
  | succ h ih =>
    rw [forcingBlock,Fin.sum_univ_castSucc]
    change forcingBlock h x+resetFunction (translate ((h : ℤ)+1) x)=_
    rw [ih,Finset.sum_Icc_succ_top (by omega : 1≤h+1)]
    simp only [Nat.cast_add,Nat.cast_one]

theorem blockFunction_forcingBlock (h : ℕ) (x : Phase) :
    blockFunction h x=(2/3 : ℝ)*((h : ℝ)-forcingBlock h x) := by
  rw [forcingBlock_Icc]
  unfold blockFunction increment
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  simp

theorem prime_increment_positive {p : ℕ} (hp : p.Prime) :
    0<(p : ℝ)*collisionWeight p :=
  mul_pos (by exact_mod_cast hp.pos) (collisionWeight_pos hp.two_le)

theorem prime_increment_formula {p : ℕ} (hp : p.Prime) :
    (p : ℝ)*collisionWeight p=(harmonic (p-1) : ℝ)/(p : ℝ) := by
  rw [CollisionConductorCosts.collisionWeight_prime_formula hp]
  have hp0 : (p : ℝ)≠0 := by exact_mod_cast hp.ne_zero
  field_simp

theorem prime_increment_log_lower {p : ℕ} (hp : p.Prime) :
    Real.log p/(p : ℝ)≤(p : ℝ)*collisionWeight p := by
  rw [prime_increment_formula hp]
  exact div_le_div_of_nonneg_right
    (CollisionConductorCosts.log_le_harmonic_predecessor (by have := hp.two_le; omega))
    (Nat.cast_nonneg p)

theorem prime_increment_window_lower {P p : ℕ} (hP : 2≤P) (hp : p.Prime)
    (hlo : (P : ℝ)/2<(p : ℝ)) (hhi : p≤P) :
    Real.log ((P : ℝ)/2)/(P : ℝ)≤(p : ℝ)*collisionWeight p := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hhalf : (1 : ℝ)≤(P : ℝ)/2 := by
    have ht : (2 : ℝ)≤P := by exact_mod_cast hP
    linarith
  have hlog : 0≤Real.log ((P : ℝ)/2) := Real.log_nonneg hhalf
  calc
    _ ≤ Real.log ((P : ℝ)/2)/(p : ℝ) :=
      div_le_div_of_nonneg_left hlog hp0 (by exact_mod_cast hhi)
    _ ≤ Real.log p/(p : ℝ) := div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith) hlo.le) hp0.le
    _ ≤ _ := prime_increment_log_lower hp

theorem resetTerm_eq_of_residue {k : ℕ} [NeZero k] {x y : Phase}
    (he : (residueHom k x).toAdd=(residueHom k y).toAdd) (j : ℕ) :
    resetTerm k (translate ((j : ℤ)+1) x)=resetTerm k (translate ((j : ℤ)+1) y) := by
  have hk0 := Nat.pos_of_ne_zero (NeZero.ne k)
  simp only [resetTerm,Set.indicator_apply,resetSet,dif_pos hk0,Set.mem_setOf_eq,
    residue_translate,he]

theorem forcingTermBlock_activation_mono_below {p h M : ℕ} [NeZero p] {x y : Phase}
    (hx : hitCoordinate p h x=false) (hxy : agreesAwayBelow p M x y)
    {k : ℕ} (hk : k≤M) : forcingTermBlock h k x≤forcingTermBlock h k y := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hpk : p∣k
  · rw [inactive_multiple_zero hx j.isLt hpk]
    exact resetTerm_nonneg k _
  · have hk0 : 0<k := Nat.pos_of_ne_zero (fun he => hpk (he ▸ dvd_zero p))
    letI : NeZero k := ⟨hk0.ne'⟩
    exact le_of_eq (resetTerm_eq_of_residue (hxy k hk hk0 hpk) j.val)

theorem forcingCutoff_prime_activation {p h M : ℕ} [NeZero p] {x y : Phase}
    (hp : p≤M) (hx : hitCoordinate p h x=false) (hy : hitCoordinate p h y=true)
    (hxy : agreesAwayBelow p M x y) :
    forcingCutoff h M x+(p : ℝ)*collisionWeight p≤forcingCutoff h M y := by
  have ht := Finset.single_le_sum (s := Finset.range (M+1))
    (f := fun k => forcingTermBlock h k y-forcingTermBlock h k x)
    (fun k hk => sub_nonneg.mpr (forcingTermBlock_activation_mono_below hx hxy
      (by have := Finset.mem_range.mp hk; omega)))
    (Finset.mem_range.mpr (by omega : p<M+1))
  have hh := (forcingTermBlock_prime_increment hx hy).trans ht
  rw [Finset.sum_sub_distrib] at hh
  change (p : ℝ)*collisionWeight p≤forcingCutoff h M y-forcingCutoff h M x at hh
  linarith

theorem forcingCutoff_tendsto (h : ℕ) (x : Phase) (hx : blockResetSummable h x) :
    Filter.Tendsto (fun M : ℕ => forcingCutoff h M x) Filter.atTop (nhds (forcingBlock h x)) := by
  have ht := (forcingTermBlock_summable h x hx).hasSum.tendsto_sum_nat
  have hn : Filter.Tendsto (fun M : ℕ => M+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_add_atTop_nat 1
  simpa only [forcingCutoff,Function.comp_def,← forcingBlock_tsum h x hx] using ht.comp hn

end NField.Alignment.CollisionActivationArithmetic
