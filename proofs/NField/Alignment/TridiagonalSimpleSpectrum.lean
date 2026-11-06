/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ExponentialPrecisionInverse

/-! The three-term recurrence proves simplicity without a spectral assumption. -/

namespace NField.Alignment.TridiagonalSimpleSpectrum

open scoped BigOperators
open Matrix

def Tridiagonal {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → T i j = 0

/-- Title: `The first coordinate determines a tridiagonal eigenvector`.

An eigenvector of an irreducible tridiagonal matrix is determined by its first entry. -/
theorem eigenvector_zero_of_first_zero {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hT : Tridiagonal T) (hadj : ∀ i : Fin n, T i.castSucc i.succ ≠ 0)
    (μ : ℝ) (v : Fin (n + 1) → ℝ) (hv : T *ᵥ v = μ • v) (h0 : v 0 = 0) :
    v = 0 := by
  funext i
  change v i = 0
  induction i using Fin.strong_induction_on with
  | h i ih =>
    induction i using Fin.cases with
    | zero => exact h0
    | succ i =>
      have hprev : v i.castSucc = 0 := ih i.castSucc Fin.castSucc_lt_succ
      have heq := congrFun hv i.castSucc
      have hsum : (T *ᵥ v) i.castSucc = T i.castSucc i.succ * v i.succ := by
        rw [mulVec, dotProduct, Finset.sum_eq_single i.succ]
        · intro j hj hji
          by_cases hjlt : j < i.succ
          · simp [ih j hjlt]
          · have hfar : i.castSucc.val + 1 < j.val := by
              have hn : j.val ≠ i.succ.val := fun h => hji (Fin.ext h)
              change ¬j.val < i.val + 1 at hjlt
              simp only [Fin.val_succ, Fin.val_castSucc] at *
              omega
            simp [hT _ _ (Or.inl hfar)]
        · simp
      rw [hsum] at heq
      simp only [Pi.smul_apply, smul_eq_mul, hprev, mul_zero] at heq
      exact (mul_eq_zero.mp heq).resolve_left (hadj i)

theorem hermitian_eigenvalues_injective {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian)
    (hfirst : ∀ (μ : ℝ) (v : Fin (n + 1) → ℝ),
      A *ᵥ v = μ • v → v 0 = 0 → v = 0) : Function.Injective hA.eigenvalues := by
  intro i j hij
  let u : Fin (n + 1) → ℝ := hA.eigenvectorBasis i
  let v : Fin (n + 1) → ℝ := hA.eigenvectorBasis j
  have hu : A *ᵥ u = hA.eigenvalues i • u := hA.mulVec_eigenvectorBasis i
  have hv : A *ᵥ v = hA.eigenvalues i • v := hij ▸ hA.mulVec_eigenvectorBasis j
  have hv0 : v 0 ≠ 0 := by
    intro hzero
    have hh := hfirst _ v hv hzero
    apply hA.eigenvectorBasis.toBasis.ne_zero j
    apply PiLp.ext
    intro k
    exact congrFun hh k
  have hw : A *ᵥ (v 0 • u - u 0 • v) = hA.eigenvalues i • (v 0 • u - u 0 • v) := by
    rw [mulVec_sub, mulVec_smul, mulVec_smul, hu, hv]
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hw0 : (v 0 • u - u 0 • v) 0 = 0 := by simp [mul_comm]
  have hrel := sub_eq_zero.mp (hfirst _ _ hw hw0)
  apply hA.eigenvectorBasis.toBasis.linearIndependent.eq_of_smul_apply_eq_smul_apply
    (v 0) (u 0) i j hv0
  apply PiLp.ext
  intro k
  exact congrFun hrel k

theorem inverse_eigenvector {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : IsUnit A)
    {μ : ℝ} (hμ : μ ≠ 0) (v : Fin (n + 1) → ℝ) (hv : A *ᵥ v = μ • v) :
    A⁻¹ *ᵥ v = μ⁻¹ • v := by
  letI := hA.invertible
  apply Matrix.inv_mulVec_eq_vec
  rw [mulVec_smul, hv, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem posDef_eigenvalues_injective_of_inverse {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.PosDef)
    (htri : Tridiagonal A⁻¹) (hadj : ∀ i : Fin n, A⁻¹ i.castSucc i.succ ≠ 0) :
    Function.Injective hA.isHermitian.eigenvalues := by
  apply hermitian_eigenvalues_injective hA.isHermitian
  intro μ v hv h0
  by_cases hμ : μ = 0
  · have hu : A *ᵥ v = A *ᵥ 0 := by simp [hv, hμ]
    exact Matrix.mulVec_injective_of_isUnit hA.isUnit hu
  · exact eigenvector_zero_of_first_zero A⁻¹ htri hadj μ⁻¹ v
      (inverse_eigenvector hA.isUnit hμ v hv) h0

/-- The actual exponential distance matrix has simple positive eigenvalues. -/
theorem exponential_eigenvalues_injective {n : ℕ} (x : Fin (n + 1) → ℝ) {τ : ℝ}
    (hx : StrictMono x) (hτ : 0 < τ) :
    Function.Injective (ExponentialDistanceKernel.kernel_posDef x hx hτ).isHermitian.eigenvalues := by
  apply posDef_eigenvalues_injective_of_inverse (ExponentialDistanceKernel.kernel_posDef x hx hτ)
  · intro i j hij
    rw [ExponentialDistanceKernel.kernel_inverse x hx hτ]
    exact ExponentialDistanceKernel.precision_tridiagonal _ i j hij
  · exact ExponentialDistanceKernel.kernel_inverse_adjacent_ne_zero x hx hτ

end NField.Alignment.TridiagonalSimpleSpectrum
