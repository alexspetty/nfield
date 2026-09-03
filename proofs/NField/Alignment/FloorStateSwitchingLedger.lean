/-
Author: Alexander S. Petty
-/

import Mathlib

/-!
# The floor-state switching ledger

Exact discrete summation-by-parts identities for carrier burdens, fresh
increments, and their quadratic charge/release split.
-/

namespace NField.Alignment.FloorStateSwitchingLedger

open scoped BigOperators

/-- Dwell-weighted stored burden. -/
noncomputable def dwellBurden
    (N : ℕ) (H B : ℕ → ℝ) : ℝ :=
  ∑ X ∈ Finset.Icc 3 N, (H X - H (X + 1)) * B X

/-- Lifetime-weighted fresh increment. -/
noncomputable def lifetimeFresh
    (N : ℕ) (H B : ℕ → ℝ) : ℝ :=
  ∑ X ∈ Finset.Icc 3 N, H X * (B X - B (X - 1))

/-- The boundary-term form of discrete summation by parts. -/
theorem switching_boundary_identity
    (N : ℕ) (hN : 3 ≤ N) (H B : ℕ → ℝ) :
    dwellBurden N H B - lifetimeFresh N H B =
      H 3 * B 2 - H (N + 1) * B N := by
  induction N, hN using Nat.le_induction with
  | base =>
      unfold dwellBurden lifetimeFresh
      norm_num
      ring
  | succ N hN ih =>
      unfold dwellBurden lifetimeFresh at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ N + 1),
        Finset.sum_Icc_succ_top (by omega : 3 ≤ N + 1)]
      simp only [Nat.add_sub_cancel]
      linear_combination ih

/-- Manuscript Proposition `Exact switching ledger`, in its linear form. -/
theorem exact_switching_ledger
    (N : ℕ) (hN : 3 ≤ N) (H B : ℕ → ℝ)
    (hB : B 2 = 0) (hH : H (N + 1) = 0) :
    dwellBurden N H B = lifetimeFresh N H B := by
  have h := switching_boundary_identity N hN H B
  rw [hB, hH] at h
  linarith

/-- Dwell-weighted quadratic burden. -/
noncomputable def quadraticBurden
    (N : ℕ) (H B : ℕ → ℝ) : ℝ :=
  ∑ X ∈ Finset.Icc 3 N, (H X - H (X + 1)) * B X ^ 2

/-- Exact quadratic switching identity. -/
theorem quadratic_switching_ledger
    (N : ℕ) (hN : 3 ≤ N) (H B : ℕ → ℝ)
    (hB : B 2 = 0) (hH : H (N + 1) = 0) :
    quadraticBurden N H B =
      ∑ X ∈ Finset.Icc 3 N,
        H X * ((B X - B (X - 1)) ^ 2 +
          2 * B (X - 1) * (B X - B (X - 1))) := by
  have h := exact_switching_ledger N hN H (fun X => B X ^ 2)
    (by rw [hB]; simp) hH
  unfold dwellBurden lifetimeFresh at h
  unfold quadraticBurden
  rw [h]
  apply Finset.sum_congr rfl
  intro X _
  ring

/-- The dwell increments telescope to the initial lifetime.  This is the
normalization used by the manuscript's stored-burden variance identity. -/
theorem sum_dwellDifference_eq
    (N : ℕ) (hN : 3 ≤ N) (H : ℕ → ℝ)
    (hH : H (N + 1) = 0) :
    (∑ X ∈ Finset.Icc 3 N, (H X - H (X + 1))) = H 3 := by
  have h := switching_boundary_identity N hN H (fun _ => (1 : ℝ))
  unfold dwellBurden lifetimeFresh at h
  simp only [mul_one, sub_self, mul_zero, Finset.sum_const_zero,
    sub_zero] at h
  simpa [hH] using h

/-- Exact weighted variance decomposition for the floor-state burden.  No
positivity assumption on the dwell increments is needed for this algebraic
identity. -/
theorem burden_variance_identity
    (N : ℕ) (hN : 3 ≤ N) (H B : ℕ → ℝ)
    (hH : H (N + 1) = 0) (hD : H 3 ≠ 0) :
    let total := ∑ X ∈ Finset.Icc 3 N,
      (H X - H (X + 1)) * B X
    let mean := total / H 3
    total ^ 2 / H 3 +
        ∑ X ∈ Finset.Icc 3 N,
          (H X - H (X + 1)) * (B X - mean) ^ 2 =
      quadraticBurden N H B := by
  dsimp only
  let total := ∑ X ∈ Finset.Icc 3 N,
    (H X - H (X + 1)) * B X
  let mean := total / H 3
  have hweight := sum_dwellDifference_eq N hN H hH
  have hexpand :
      (∑ X ∈ Finset.Icc 3 N,
          (H X - H (X + 1)) * (B X - mean) ^ 2) =
        (∑ X ∈ Finset.Icc 3 N,
          (H X - H (X + 1)) * B X ^ 2) -
          2 * mean * total + mean ^ 2 * H 3 := by
    calc
      (∑ X ∈ Finset.Icc 3 N,
          (H X - H (X + 1)) * (B X - mean) ^ 2) =
        ∑ X ∈ Finset.Icc 3 N,
          ((H X - H (X + 1)) * B X ^ 2 -
            2 * mean * ((H X - H (X + 1)) * B X) +
            mean ^ 2 * (H X - H (X + 1))) := by
              apply Finset.sum_congr rfl
              intro X _hX
              ring
      _ = (∑ X ∈ Finset.Icc 3 N,
          (H X - H (X + 1)) * B X ^ 2) -
          2 * mean * total + mean ^ 2 * H 3 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, hweight]
  rw [hexpand]
  unfold quadraticBurden
  dsimp [mean]
  field_simp [hD]
  ring

/-- Positive and negative parts of one switching current. -/
noncomputable def positivePart (x : ℝ) : ℝ := max x 0
noncomputable def negativePart (x : ℝ) : ℝ := max (-x) 0

theorem positivePart_sub_negativePart (x : ℝ) :
    positivePart x - negativePart x = x := by
  unfold positivePart negativePart
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by linarith)]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (by linarith)]
    ring

/-- A switching current is negative exactly when the fresh increment opposes
the stored burden without overshooting twice its magnitude. -/
theorem switchingCurrent_neg_iff (stored fresh : ℝ) :
    stored * fresh + (1 / 2 : ℝ) * fresh ^ 2 < 0 ↔
      stored * fresh < 0 ∧ |fresh| < 2 * |stored| := by
  constructor
  · intro hcurrent
    have hopposes : stored * fresh < 0 := by
      nlinarith [sq_nonneg fresh]
    refine ⟨hopposes, ?_⟩
    rcases (mul_neg_iff.mp hopposes) with hsign | hsign
    · rw [abs_of_neg hsign.2, abs_of_pos hsign.1]
      nlinarith
    · rw [abs_of_pos hsign.2, abs_of_neg hsign.1]
      nlinarith
  · rintro ⟨hopposes, hmagnitude⟩
    rcases (mul_neg_iff.mp hopposes) with hsign | hsign
    · rw [abs_of_neg hsign.2, abs_of_pos hsign.1] at hmagnitude
      nlinarith
    · rw [abs_of_pos hsign.2, abs_of_neg hsign.1] at hmagnitude
      nlinarith

/-- Exact charge/release balance. -/
theorem charge_release_balance
    (N : ℕ) (H J : ℕ → ℝ)
    (Q : ℝ)
    (hQ : Q = 2 * ∑ X ∈ Finset.Icc 3 N, H X * J X) :
    (∑ X ∈ Finset.Icc 3 N, H X * positivePart (J X)) =
      (∑ X ∈ Finset.Icc 3 N, H X * negativePart (J X)) + Q / 2 := by
  have hsplit :
      (∑ X ∈ Finset.Icc 3 N,
          H X * positivePart (J X)) -
        (∑ X ∈ Finset.Icc 3 N,
          H X * negativePart (J X)) =
        ∑ X ∈ Finset.Icc 3 N, H X * J X := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro X _
    rw [← mul_sub, positivePart_sub_negativePart]
  rw [hQ]
  linear_combination hsplit

/-- Finite Möbius inversion turns an additive convolution grouped by common
scale into its primitive part.  The inverse formula is proved here; it is not
accepted as a second hypothesis. -/
theorem primitive_additive_convolution
    (A C : ℕ → ℝ)
    (hforward : ∀ X, 0 < X → A X = ∑ d ∈ X.divisors, C d) :
    (∀ X, 0 < X → A X = ∑ d ∈ X.divisors, C d) ∧
      (∀ X, 0 < X → C X = ∑ d ∈ X.divisors,
        (ArithmeticFunction.moebius d : ℝ) * A (X / d)) := by
  refine ⟨hforward, ?_⟩
  intro X hX
  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (R := ℝ) (f := C) (g := A)).mp (by
        intro n hn
        exact (hforward n hn).symm) X hX
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun x y => (ArithmeticFunction.moebius x : ℝ) * A y)] at hinv
  exact hinv.symm

end NField.Alignment.FloorStateSwitchingLedger
