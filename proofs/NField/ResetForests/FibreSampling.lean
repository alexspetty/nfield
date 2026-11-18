/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.Fibre
/-! # Complete prime-square sampling in fibre coordinates

All labels are grouped once as pv+r. In particular r=0 and v=0
remain in the identities before any source is specialized.
-/

noncomputable section

namespace NField.ResetForests.FibreReconstruction

open scoped BigOperators
open NField.Alignment CommonResetGram DedekindFourierMoment

theorem prime_square_grid_reindex {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ) :
    (∑ a ∈ Finset.range (p^2), f ((a : ℝ)/(p : ℝ)^2))=
      ∑ r ∈ Finset.range p, ∑ v : Fin p,
        f (((v.val : ℝ)+(r : ℝ)/(p : ℝ))/(p : ℝ)) := by
  rw [pow_two, sum_range_mul_blocks, Finset.sum_comm]
  have hs (r : ℕ) : (∑ v : Fin p, f (((v.val : ℝ)+(r : ℝ)/(p : ℝ))/(p : ℝ)))=
      ∑ v ∈ Finset.range p, f (((v : ℝ)+(r : ℝ)/(p : ℝ))/(p : ℝ)) :=
    Fin.sum_univ_eq_sum_range
      (fun v : ℕ => f (((v : ℝ)+(r : ℝ)/(p : ℝ))/(p : ℝ))) p
  simp_rw [hs]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

theorem sampled_fibre_reconstruction {p : ℕ} (hp : p.Prime) (c e : ℕ → ℝ) :
    sampledWork (p-1) (p^2) c e =
      sampledWork (p-1) p c e/(p : ℝ)^2+
        (1/(p : ℝ)^2)*(∑ r ∈ Finset.range p, fibrePair p c e ((r : ℝ)/(p : ℝ))) := by
  have hg := prime_square_grid_reindex hp.pos
    (fun x => weightedProfile (p-1) c x*weightedProfile (p-1) e x)
  have hr (r : ℕ) :
      (∑ v : Fin p,
        weightedProfile (p-1) c (((v.val : ℝ)+(r : ℝ)/(p : ℝ))/(p : ℝ))*
          weightedProfile (p-1) e (((v.val : ℝ)+(r : ℝ)/(p : ℝ))/(p : ℝ)))=
      fibrePair p c e ((r : ℝ)/(p : ℝ))+
        weightedProfile (p-1) c ((r : ℝ)/(p : ℝ))*
          weightedProfile (p-1) e ((r : ℝ)/(p : ℝ))/(p : ℝ) := by
    linarith [fibre_pair_identity hp c e ((r : ℝ)/(p : ℝ))]
  unfold sampledWork
  simp only [Nat.cast_pow]
  rw [hg]
  simp_rw [hr]
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  ring

end NField.ResetForests.FibreReconstruction
