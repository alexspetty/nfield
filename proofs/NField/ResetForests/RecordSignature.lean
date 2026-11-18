/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.RecordRank
/-! # Positive and negative source directions of an onto packet record -/

set_option autoImplicit false

noncomputable section

namespace NField.ResetForests.PacketQueries

open scoped BigOperators Matrix

def signedRecord (t : ℕ) (s : ℝ) : (Fin t → ℝ) →ₗ[ℝ] (RecordIndex t → ℝ) where
  toFun x i := if i.2 then s * x i.1 else x i.1
  map_add' x y := by
    ext ⟨i, b⟩
    cases b <;> simp [mul_add]
  map_smul' a x := by
    ext ⟨i, b⟩
    cases b <;> simp [mul_left_comm]

def liftedSignedRecord {N t : ℕ} (R : Matrix (Fin N) (RecordIndex t) ℝ) (s : ℝ) :
    (Fin t → ℝ) →ₗ[ℝ] (Fin N → ℝ) := R.mulVecLin.comp (signedRecord t s)

theorem sum_squares_pos {t : ℕ} (x : Fin t → ℝ) (hx : x ≠ 0) :
    0 < ∑ i : Fin t, x i ^ 2 := by
  have hi : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hi
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem signed_record_quadratic (t : ℕ) (s : ℝ) (x : Fin t → ℝ) :
    (signedRecord t s x) ⬝ᵥ (pairQuery t *ᵥ (signedRecord t s x)) =
      4 * s * ∑ i : Fin t, x i ^ 2 := by
  rw [pair_query_quadratic]
  simp only [signedRecord, LinearMap.coe_mk, AddHom.coe_mk, Bool.false_eq_true,
    if_false, if_true]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem lifted_signed_readback {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ)
    (R : Matrix (Fin N) (RecordIndex t) ℝ) (hAR : A * R = 1) (s : ℝ) (x : Fin t → ℝ) :
    A *ᵥ (liftedSignedRecord R s x) = signedRecord t s x := by
  change A *ᵥ (R *ᵥ (signedRecord t s x)) = _
  rw [Matrix.mulVec_mulVec, hAR, Matrix.one_mulVec]

theorem lifted_signed_quadratic {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ)
    (R : Matrix (Fin N) (RecordIndex t) ℝ) (hAR : A * R = 1) (s : ℝ) (x : Fin t → ℝ) :
    matrixForm (pullbackQuery A) (liftedSignedRecord R s x) =
      4 * s * ∑ i : Fin t, x i ^ 2 := by
  rw [matrix_form_apply, pullback_query_quadratic, lifted_signed_readback A R hAR,
    signed_record_quadratic]

theorem positive_embedding_signature {N t : ℕ} (Q : QuadraticForm ℝ (Fin N → ℝ))
    (f : (Fin t → ℝ) →ₗ[ℝ] (Fin N → ℝ)) (hp : (Q.comp f).PosDef) : t ≤ sigPos Q := by
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    apply hp.anisotropic x
    change Q (f x) = 0
    change f x = 0 at hx
    rw [hx, map_zero]
  have hpos : (Q.restrict (LinearMap.range f)).PosDef := by
    rintro ⟨v, ⟨x, rfl⟩⟩ hv
    change 0 < Q (f x)
    apply hp x
    intro hx
    apply hv
    apply Subtype.ext
    simp [hx]
  have hd : Module.finrank ℝ (LinearMap.range f) = t := by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  rw [← hd]
  exact le_sigPos_of_posDef Q hpos

theorem pullback_query_signature {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ)
    (hA : Function.Surjective A.mulVec) :
    sigPos (matrixForm (pullbackQuery A)) = t ∧ sigNeg (matrixForm (pullbackQuery A)) = t := by
  obtain ⟨R, hAR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hp : ((matrixForm (pullbackQuery A)).comp (liftedSignedRecord R 1)).PosDef := by
    intro x hx
    rw [QuadraticMap.comp_apply, lifted_signed_quadratic A R hAR]
    exact mul_pos (by norm_num) (sum_squares_pos x hx)
  have hn : ((-matrixForm (pullbackQuery A)).comp (liftedSignedRecord R (-1))).PosDef := by
    intro x hx
    rw [QuadraticMap.comp_apply, QuadraticMap.neg_apply, lifted_signed_quadratic A R hAR]
    have hs := sum_squares_pos x hx
    nlinarith
  have hlp := positive_embedding_signature _ _ hp
  have hln := positive_embedding_signature _ _ hn
  rw [sigPos_neg] at hln
  have hs := matrix_form_signature_rank (pullbackQuery A) (pullback_query_symmetric A)
  rw [pullback_query_rank A hA] at hs
  omega

theorem full_row_rank_surjective {N t : ℕ} (A : Matrix (RecordIndex t) (Fin N) ℝ)
    (hA : A.rank = 2 * t) : Function.Surjective A.mulVec := by
  change Function.Surjective A.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change A.rank = Module.finrank ℝ (RecordIndex t → ℝ)
  rw [hA, Module.finrank_pi, record_index_card]

theorem complete_packet_record_rank_signature {t : ℕ} (N Q : ℕ) (κ : Fin t → ℕ)
    (hA : (packetRecord N Q κ).rank = 2 * t) :
    (pullbackQuery (packetRecord N Q κ)).rank = 2 * t ∧
      sigPos (matrixForm (pullbackQuery (packetRecord N Q κ))) = t ∧
      sigNeg (matrixForm (pullbackQuery (packetRecord N Q κ))) = t := by
  have hs := full_row_rank_surjective _ hA
  exact ⟨pullback_query_rank _ hs, pullback_query_signature _ hs⟩

theorem complete_packet_record_minimal {t d : ℕ} (N Q : ℕ) (κ : Fin t → ℕ)
    (hA : (packetRecord N Q κ).rank = 2 * t)
    (T : Matrix (Fin d) (Fin N) ℝ) (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ c, packetQuery N Q κ c = f (T *ᵥ c)) : 2 * t ≤ d := by
  apply exact_packet_record_minimum_dimension (packetRecord N Q κ)
    (full_row_rank_surjective _ hA) T f
  intro c
  rw [← packet_record_quadratic]
  exact hf c

theorem complete_packet_quadratic_record_minimal {t d : ℕ} (N Q : ℕ) (κ : Fin t → ℕ)
    (hA : (packetRecord N Q κ).rank = 2 * t)
    (T : Matrix (Fin d) (Fin N) ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (hf : ∀ c, packetQuery N Q κ c = (T *ᵥ c) ⬝ᵥ (B *ᵥ (T *ᵥ c))) : 2 * t ≤ d :=
  complete_packet_record_minimal N Q κ hA T (fun y => y ⬝ᵥ (B *ᵥ y)) hf

end NField.ResetForests.PacketQueries
