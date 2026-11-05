/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPotentialRecovery

/-!
# A finite quadratic antiderivative of a centered remainder

The test r(k-r)/2 has forward difference equal to the centered age row.
It is continuous on the actual profinite space and can therefore test
the L1 divisor forcing without assuming an L2 limit in advance.
-/

noncomputable section

namespace NField.Alignment.CollisionFiniteAntiderivative

open scoped BigOperators
open MeasureTheory
open ProfiniteRemainderMeasure CollisionPotentialHilbert CollisionPotentialCoboundary

def antiderivativeMap (k : ℕ) : C(Phase, ℝ) :=
  ⟨fun x => (centered k x + ((k : ℝ)-1)/2) * (((k : ℝ)+1)/2 - centered k x) / 2,
    by have hc := continuous_centered k; fun_prop⟩

theorem antiderivativeMap_residue (k : ℕ) [NeZero k] (x : Phase) :
    antiderivativeMap k x =
      ((residueHom k x).toAdd.val : ℝ) * ((k : ℝ) - ((residueHom k x).toAdd.val : ℝ)) / 2 := by
  change (centered k x + ((k : ℝ)-1)/2) * (((k : ℝ)+1)/2 - centered k x) / 2 = _
  rw [centered_eq]
  ring

theorem antiderivative_forward {k : ℕ} (hk : 0 < k) (x : Phase) :
    antiderivativeMap k x - antiderivativeMap k (translate 1 x) = centered k x := by
  letI : NeZero k := ⟨hk.ne'⟩
  let u := (residueHom k x).toAdd
  rw [antiderivativeMap_residue, antiderivativeMap_residue, centered_eq, residue_translate]
  simp only [Int.cast_one]
  change (u.val : ℝ)*((k : ℝ)-(u.val : ℝ))/2 -
      (((1 : ZMod k)+u).val : ℝ)*((k : ℝ)-(((1 : ZMod k)+u).val : ℝ))/2 =
        (u.val : ℝ)-((k : ℝ)-1)/2
  by_cases hk1 : k = 1
  · subst k
    have hu : u = 0 := Subsingleton.elim _ _
    simp [hu]
  have hv : u.val < k := ZMod.val_lt u
  have hs : ((1 : ZMod k)+u).val = (u.val+1)%k := by
    rw [add_comm, ZMod.val_add, ZMod.val_one'' hk1]
  rw [hs]
  by_cases ht : u.val+1 = k
  · rw [ht, Nat.mod_self]
    have he : (u.val : ℝ)+1 = (k : ℝ) := by exact_mod_cast ht
    push_cast
    nlinarith
  · have hlt : u.val+1 < k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    push_cast
    ring

def antiderivativeVector (k : ℕ) : HaarL2 :=
  ContinuousMap.toLp 2 phaseHaar ℝ (antiderivativeMap k)

theorem antiderivativeVector_step {k : ℕ} (hk : 0 < k) :
    antiderivativeVector k - shift 1 (antiderivativeVector k) = remainderVector k := by
  apply Lp.ext
  have ha := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (antiderivativeMap k)
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) phaseHaar (remainderMap k)
  have hat := (translate_measurePreserving 1).quasiMeasurePreserving.ae
    (p := fun x => antiderivativeVector k x = antiderivativeMap k x) ha
  filter_upwards [Lp.coeFn_sub (antiderivativeVector k) (shift 1 (antiderivativeVector k)),
    shift_coe 1 (antiderivativeVector k), ha, hat, hr] with x hsub hsh hx ht he
  simp only [Pi.sub_apply] at hsub
  change antiderivativeVector k x = antiderivativeMap k x at hx
  change remainderVector k x = centered k x at he
  rw [hsub, hsh, hx, ht]
  exact (antiderivative_forward hk x).trans he.symm

theorem backward_difference_pairing (Y : HaarL2) {k : ℕ} (hk : 0 < k) :
    inner ℝ (Y - shift (-1) Y) (antiderivativeVector k) = inner ℝ Y (remainderVector k) := by
  have hshift : inner ℝ (shift (-1) Y) (antiderivativeVector k) =
      inner ℝ Y (shift 1 (antiderivativeVector k)) := by
    have h := (shift 1).inner_map_map (shift (-1) Y) (antiderivativeVector k)
    rw [← shift_add, show (1 : ℤ)+(-1)=0 by norm_num, shift_zero] at h
    exact h.symm
  rw [inner_sub_left, hshift, ← inner_sub_right, antiderivativeVector_step hk]

end NField.Alignment.CollisionFiniteAntiderivative
