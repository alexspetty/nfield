/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExponentialSpectralQuotient

/-! The positive Perron vector bounds every concrete quotient eigenvalue. -/

namespace NField.Alignment.ExponentialSpectralQuotient

open scoped BigOperators
open Matrix

theorem eigenvalue_abs_le_one_of_positive_fixed {ι : Type*} [Fintype ι] [Nonempty ι]
    (Q : Matrix ι ι ℝ) (v : ι → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hv : ∀ i, 0 < v i) (hfix : Q *ᵥ v = v)
    (μ : ℝ) (w : ι → ℝ) (hw : w ≠ 0) (heig : Q *ᵥ w = μ • w) : |μ| ≤ 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hw (funext hh)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun k => |w k| / v k) Finset.univ_nonempty
  have hwi : 0 < |w i| := by
    have hpos : 0 < |w i| / v i :=
      lt_of_lt_of_le (div_pos (abs_pos.mpr hj) (hv j)) (hi j (Finset.mem_univ j))
    exact (div_pos_iff_of_pos_right (hv i)).mp hpos
  let c := |w i| / v i
  have hbound : ∀ j, |w j| ≤ c * v j := fun j =>
    (div_le_iff₀ (hv j)).mp (hi j (Finset.mem_univ j))
  have hrow : ∑ j, Q i j * w j = μ * w i := congrFun heig i
  have hsum : ∑ j, Q i j * v j = v i := congrFun hfix i
  have hle : |μ| * |w i| ≤ |w i| := calc
    |μ| * |w i| = |∑ j, Q i j * w j| := by rw [hrow, abs_mul]
    _ ≤ ∑ j, |Q i j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, Q i j * |w j| := by simp only [abs_mul, abs_of_nonneg (hQ _ _)]
    _ ≤ ∑ j, Q i j * (c * v j) :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hbound j) (hQ i j))
    _ = c * v i := by rw [← hsum, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ = |w i| := div_mul_cancel₀ _ (ne_of_gt (hv i))
  nlinarith

/-- Title: `Every quotient eigenvalue is positive and at most one`. -/
theorem quotient_eigenvalues_bounds {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) (i : Fin (n + 1)) :
    0 < (quotient_posDef x pop hx hp hτ).isHermitian.eigenvalues i ∧
      (quotient_posDef x pop hx hp hτ).isHermitian.eigenvalues i ≤ 1 := by
  let hQ := quotient_posDef x pop hx hp hτ
  refine ⟨hQ.eigenvalues_pos i, ?_⟩
  have hn : (⇑(hQ.isHermitian.eigenvectorBasis i) : Fin (n + 1) → ℝ) ≠ 0 := by
    intro hh
    apply hQ.isHermitian.eigenvectorBasis.toBasis.ne_zero i
    apply PiLp.ext
    intro j
    exact congrFun hh j
  have h := eigenvalue_abs_le_one_of_positive_fixed (quotient x pop τ) (perron x pop τ)
    (fun i j => (quotient_pos x pop τ hp i j).le) (perron_pos x pop τ hp)
    (quotient_perron x pop τ hp) _ _ hn (hQ.isHermitian.mulVec_eigenvectorBasis i)
  exact (le_abs_self _).trans h

theorem quotient_one_mem_spectrum {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hp : ∀ i, 0 < pop i) : 1 ∈ spectrum ℝ (quotient x pop τ) := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    simpa using quotient_perron x pop τ hp
  · intro hzero
    have hh := congrFun hzero 0
    exact (ne_of_gt (perron_pos x pop τ hp 0)) hh

/-- Title: `The quotient spectrum contains one`. -/
theorem quotient_exists_eigenvalue_one {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) :
    ∃ i, (quotient_posDef x pop hx hp hτ).isHermitian.eigenvalues i = 1 := by
  have h := quotient_one_mem_spectrum x pop (τ := τ) hp
  rw [(quotient_posDef x pop hx hp hτ).isHermitian.spectrum_real_eq_range_eigenvalues] at h
  exact h

/-- Title: `Every quotient Hamiltonian mode lies below one`. -/
theorem quotient_modes_bounds {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) (i : Fin (n + 1)) :
    0 ≤ (1 - (quotient_posDef x pop hx hp hτ).isHermitian.eigenvalues i) ^ 2 ∧
      (1 - (quotient_posDef x pop hx hp hτ).isHermitian.eigenvalues i) ^ 2 < 1 := by
  obtain ⟨h0, h1⟩ := quotient_eigenvalues_bounds x pop hx hp hτ i
  constructor
  · positivity
  · nlinarith

/-- Title: `The quotient Hamiltonian modes are distinct`. -/
theorem quotient_modes_injective {n : ℕ} (x pop : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hp : ∀ i, 0 < pop i) (hτ : 0 < τ) :
    Function.Injective (fun i => (1 - (quotient_posDef x pop hx hp hτ).isHermitian.eigenvalues i) ^ 2) := by
  intro i j hij
  apply quotient_eigenvalues_injective x pop hx hp hτ
  have hi := (quotient_eigenvalues_bounds x pop hx hp hτ i).2
  have hj := (quotient_eigenvalues_bounds x pop hx hp hτ j).2
  nlinarith

end NField.Alignment.ExponentialSpectralQuotient
