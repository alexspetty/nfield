/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.FibreTraces
/-! # Actual reduced return addresses and one-sided reset limits -/

noncomputable section
set_option autoImplicit false

namespace NField.ResetForests.FibreTraces

open scoped Topology
open Filter NField.Alignment CommonResetGram FibreReconstruction

theorem returned_quotient_coprime {p k a : ℕ} (ha : a.Coprime k) (v : ℕ)
    (hdiv : p ∣ v*k+a) : ((v*k+a)/p).Coprime k := by
  have hnum : (v*k+a).Coprime k := (Nat.coprime_mul_right_add_left a k v).mpr ha
  exact hnum.coprime_dvd_left ⟨p,(Nat.div_mul_cancel hdiv).symm⟩

theorem returned_root_is_reduced {p k a : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (ha : a.Coprime k)
    (haPos : 0 < a) (haLt : a < k) (v : Fin p)
    (hv : (v.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹) :
    (((a : ZMod k)*(p : ZMod k)⁻¹).val).Coprime k := by
  have hkB := Finset.mem_Icc.mp hk
  have hd := reset_fibre_divisibility hp hk a v hv
  have he := (returned_root_reduced_coordinates hp hkB.1
    (by have := hp.two_le; omega) haPos haLt v hd).2.2
  rw [← he]
  exact returned_quotient_coprime ha v.val hd

theorem inverse_reset_fibre_exists {p : ℕ} (hp : 0 < p) (k a : ℕ) :
    ∃ v : Fin p, (v.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹ := by
  letI : NeZero p := ⟨hp.ne'⟩
  exact ⟨⟨(-(a : ZMod p)*(k : ZMod p)⁻¹).val,ZMod.val_lt _⟩,
    ZMod.natCast_zmod_val _⟩

theorem reduced_reset_limits_and_jump {p k a : ℕ} (hp : p.Prime)
    (hk : k ∈ Finset.Icc 1 (p-1)) (ha : a.Coprime k) (c : ℕ → ℝ) :
    ∃ v0 : Fin p, (v0.val : ZMod p)=-(a : ZMod p)*(k : ZMod p)⁻¹ ∧
      ∀ v : Fin p,
        Tendsto (fun x => fibrePath p c x v) (𝓝[<] ((a : ℝ)/(k : ℝ)))
          (𝓝 (fibreLeft p c ((a : ℝ)/(k : ℝ)) v)) ∧
        Tendsto (fun x => fibrePath p c x v) (𝓝[>] ((a : ℝ)/(k : ℝ)))
          (𝓝 (fibreRight p c ((a : ℝ)/(k : ℝ)) v)) ∧
        fibreRight p c ((a : ℝ)/(k : ℝ)) v-fibreLeft p c ((a : ℝ)/(k : ℝ)) v=
          -2*Core.resetMass (p-1) c k*resetDirection p v0 v := by
  obtain ⟨v0,hv0⟩ := inverse_reset_fibre_exists hp.pos k a
  exact ⟨v0,hv0,fun v => ⟨fibre_path_left_limit hp.pos c _ v,
    fibre_path_right_limit hp.pos c _ v,fibre_path_jump_at_reduced hp hk ha v0 v hv0 c⟩⟩

end NField.ResetForests.FibreTraces
