/-
Author: Alexander S. Petty
-/

import NField.Alignment.DoubleTransversality
import Mathlib.Analysis.Fourier.ZMod

/-!
# Spectral repulsion

Finite sector-factorization, relabeling-moment, additive-convolution, and
reflected-pair algebra for the Lean companion to "The Spectral Repulsion".
-/

namespace NField.Alignment.SpectralRepulsion

open scoped BigOperators ComplexConjugate ZMod
open ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.DoubleTransversality

/-! ## Sector normalization -/

/-- Primitive-sector overlap of two real mass distributions. -/
noncomputable def sectorOverlap {α : Type*} [Fintype α]
    (p q : α → ℝ) : ℝ :=
  ∑ i, p i * q i

/-- The full odd-sector overlap factors into sector occupancy and assignment
inside the eligible sector. -/
theorem sector_factorization
    {α : Type*} [Fintype α]
    (p q qFull : α → ℝ) (η primitiveCount oddCount : ℝ)
    (hq : ∀ i, qFull i = η * q i)
    (hprimitive : primitiveCount ≠ 0) :
    oddCount * sectorOverlap p qFull =
      (oddCount / primitiveCount) * η *
        (primitiveCount * sectorOverlap p q) := by
  classical
  unfold sectorOverlap
  have hoverlap : (∑ i, p i * qFull i) = η * ∑ i, p i * q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hq]
    ring
  rw [hoverlap]
  field_simp

/-! ## Exact relabeling algebra -/

/-- Uniform average over a finite nonempty sample space. -/
noncomputable def uniformAverage {Ω : Type*} [Fintype Ω]
    (z : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, z ω

/-- Uniform variance on a finite sample space. -/
noncomputable def uniformVariance {Ω : Type*} [Fintype Ω]
    (z : Ω → ℝ) : ℝ :=
  uniformAverage (fun ω => (z ω - uniformAverage z) ^ 2)

/-- Center a mass list at the uniform value `1/k`. -/
noncomputable def centeredMass {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) : ℝ :=
  x i - (Fintype.card ι : ℝ)⁻¹

/-- A probability mass list has zero centered total. -/
theorem centeredMass_sum_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (hx : ∑ i, x i = 1) :
    ∑ i, centeredMass x i = 0 := by
  classical
  unfold centeredMass
  rw [Finset.sum_sub_distrib, hx]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  field_simp
  ring

/-- Uniform averaging commutes with finite sums. -/
theorem uniformAverage_sum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (F : ι → Ω → ℝ) :
    uniformAverage (fun ω => ∑ i, F i ω) =
      ∑ i, uniformAverage (F i) := by
  classical
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Uniform averaging commutes with scalar multiplication. -/
theorem uniformAverage_mul_left
    {Ω : Type*} [Fintype Ω] (c : ℝ) (z : Ω → ℝ) :
    uniformAverage (fun ω => c * z ω) = c * uniformAverage z := by
  unfold uniformAverage
  rw [← Finset.mul_sum]
  ring

/-- Uniform averaging commutes with pointwise addition. -/
theorem uniformAverage_add
    {Ω : Type*} [Fintype Ω] (z w : Ω → ℝ) :
    uniformAverage (fun ω => z ω + w ω) =
      uniformAverage z + uniformAverage w := by
  unfold uniformAverage
  rw [Finset.sum_add_distrib]
  ring

/-- The uniform average of the constant-one signal is one. -/
theorem uniformAverage_one
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformAverage (fun _ : Ω => (1 : ℝ)) = 1 := by
  unfold uniformAverage
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_one]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  exact inv_mul_cancel₀ hcard

/-- A centered list has negative square mass across all ordered distinct
pairs. -/
theorem offDiagonal_centered_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, x i * x j) =
      -(∑ i, (x i) ^ 2) := by
  classical
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i, x i * x j) =
      ∑ i, x i * ∑ j ∈ Finset.univ.erase i, x j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ = ∑ i, x i * (-x i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := Finset.sum_erase_add (s := Finset.univ) x
        (Finset.mem_univ i)
      rw [hx] at hi
      rw [show ∑ j ∈ Finset.univ.erase i, x j = -x i by linarith]
    _ = -(∑ i, (x i) ^ 2) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Scaled centered overlap under a relabeling family. -/
noncomputable def centeredRelabelingStatistic
    {Ω ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (image : Ω → ι → ι) (ω : Ω) : ℝ :=
  (Fintype.card ι : ℝ) *
    ∑ i, centeredMass x i * centeredMass y (image ω i)

/-- The manuscript's uncentered scaled overlap under a relabeling family. -/
noncomputable def relabelingStatistic
    {Ω ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (image : Ω → ι → ι) (ω : Ω) : ℝ :=
  (Fintype.card ι : ℝ) * ∑ i, x i * y (image ω i)

/-- When every relabeling preserves total mass, the uncentered statistic is
exactly one plus the centered statistic. -/
theorem relabelingStatistic_eq_centered_add_one
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hx : ∑ i, x i = 1)
    (hmass : ∀ ω, ∑ i, y (image ω i) = 1) (ω : Ω) :
    relabelingStatistic x y image ω =
      centeredRelabelingStatistic x y image ω + 1 := by
  classical
  let k : ℝ := Fintype.card ι
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hexpand :
      (∑ i, centeredMass x i * centeredMass y (image ω i)) =
        (∑ i, x i * y (image ω i)) -
          (∑ i, x i) * k⁻¹ -
          k⁻¹ * (∑ i, y (image ω i)) +
          k * k⁻¹ * k⁻¹ := by
    calc
      (∑ i, centeredMass x i * centeredMass y (image ω i)) =
          ∑ i, (x i * y (image ω i) - x i * k⁻¹ -
            k⁻¹ * y (image ω i) + k⁻¹ * k⁻¹) := by
              apply Finset.sum_congr rfl
              intro i _
              unfold centeredMass
              dsimp [k]
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring
  unfold relabelingStatistic centeredRelabelingStatistic
  change k * ∑ i, x i * y (image ω i) =
    k * ∑ i, centeredMass x i * centeredMass y (image ω i) + 1
  rw [hexpand, hx, hmass]
  field_simp
  ring

/-- If every relabeled coordinate has zero centered first moment, the scaled
centered overlap has exact mean zero. -/
theorem centered_relabeling_mean_zero
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hfirst : ∀ i,
      uniformAverage (fun ω => centeredMass y (image ω i)) = 0) :
    uniformAverage (centeredRelabelingStatistic x y image) = 0 := by
  unfold centeredRelabelingStatistic
  rw [uniformAverage_mul_left, uniformAverage_sum]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i _
  rw [uniformAverage_mul_left, hfirst, mul_zero]

/-- Under mass preservation and the exact centered first moment, the
manuscript's uncentered overlap has mean one. -/
theorem relabelingStatistic_mean_one
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hx : ∑ i, x i = 1)
    (hmass : ∀ ω, ∑ i, y (image ω i) = 1)
    (hfirst : ∀ i,
      uniformAverage (fun ω => centeredMass y (image ω i)) = 0) :
    uniformAverage (relabelingStatistic x y image) = 1 := by
  have hcentered := centered_relabeling_mean_zero x y image hfirst
  calc
    uniformAverage (relabelingStatistic x y image) =
        uniformAverage (fun ω =>
          centeredRelabelingStatistic x y image ω + 1) := by
            apply congrArg uniformAverage
            funext ω
            exact relabelingStatistic_eq_centered_add_one
              x y image hx hmass ω
    _ = uniformAverage (centeredRelabelingStatistic x y image) +
        uniformAverage (fun _ : Ω => (1 : ℝ)) :=
      uniformAverage_add _ _
    _ = 1 := by rw [hcentered, uniformAverage_one]; ring

/-- The exact variance algebra from the one-point and two-point moments of a
uniform relabeling without replacement. -/
theorem centered_relabeling_variance
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hx : ∑ i, x i = 1) (_hy : ∑ i, y i = 1)
    (hk : 1 < Fintype.card ι)
    (hfirst : ∀ i,
      uniformAverage (fun ω => centeredMass y (image ω i)) = 0)
    (hsecond : ∀ i j,
      uniformAverage (fun ω =>
        centeredMass y (image ω i) * centeredMass y (image ω j)) =
        if i = j then
          (Fintype.card ι : ℝ)⁻¹ * ∑ r, (centeredMass y r) ^ 2
        else
          -((Fintype.card ι : ℝ) *
            (Fintype.card ι - 1 : ℝ))⁻¹ *
              ∑ r, (centeredMass y r) ^ 2) :
    uniformVariance (centeredRelabelingStatistic x y image) =
      (Fintype.card ι : ℝ) ^ 2 /
          (Fintype.card ι - 1 : ℝ) *
        (∑ r, (centeredMass x r) ^ 2) *
        (∑ r, (centeredMass y r) ^ 2) := by
  classical
  let k : ℝ := Fintype.card ι
  let X : ℝ := ∑ r, (centeredMass x r) ^ 2
  let Y : ℝ := ∑ r, (centeredMass y r) ^ 2
  have hx0 : ∑ i, centeredMass x i = 0 := centeredMass_sum_zero x hx
  have hmean : uniformAverage (centeredRelabelingStatistic x y image) = 0 :=
    centered_relabeling_mean_zero x y image hfirst
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hk1 : k - 1 ≠ 0 := by
    have : (1 : ℝ) < k := by
      dsimp [k]
      exact_mod_cast hk
    linarith
  unfold uniformVariance
  rw [hmean]
  simp only [sub_zero]
  unfold centeredRelabelingStatistic
  rw [show uniformAverage (fun ω : Ω =>
      (k * ∑ i, centeredMass x i * centeredMass y (image ω i)) ^ 2) =
      k ^ 2 * uniformAverage (fun ω : Ω =>
        (∑ i, centeredMass x i * centeredMass y (image ω i)) ^ 2) by
        calc
          uniformAverage (fun ω : Ω =>
              (k * ∑ i, centeredMass x i *
                centeredMass y (image ω i)) ^ 2) =
            uniformAverage (fun ω : Ω =>
              k ^ 2 * (∑ i, centeredMass x i *
                centeredMass y (image ω i)) ^ 2) := by
                  apply congrArg uniformAverage
                  funext ω
                  ring
          _ = _ := uniformAverage_mul_left _ _]
  rw [show uniformAverage (fun ω : Ω =>
      (∑ i, centeredMass x i * centeredMass y (image ω i)) ^ 2) =
      ∑ i, ∑ j,
        centeredMass x i * centeredMass x j *
          uniformAverage (fun ω =>
            centeredMass y (image ω i) * centeredMass y (image ω j)) by
        calc
          uniformAverage (fun ω : Ω =>
              (∑ i, centeredMass x i * centeredMass y (image ω i)) ^ 2) =
            uniformAverage (fun ω : Ω =>
              ∑ i, ∑ j,
                (centeredMass x i * centeredMass x j) *
                  (centeredMass y (image ω i) *
                    centeredMass y (image ω j))) := by
                      apply congrArg uniformAverage
                      funext ω
                      rw [pow_two, Fintype.sum_mul_sum]
                      apply Finset.sum_congr rfl
                      intro i _
                      apply Finset.sum_congr rfl
                      intro j _
                      ring
          _ = _ := by
            rw [uniformAverage_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [uniformAverage_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [uniformAverage_mul_left]]
  simp_rw [hsecond]
  change k ^ 2 * (∑ i : ι, ∑ j : ι,
      centeredMass x i * centeredMass x j *
        (if i = j then k⁻¹ * Y
          else -(k * (k - 1))⁻¹ * Y)) =
    k ^ 2 / (k - 1) * X * Y
  rw [show (∑ i : ι, ∑ j : ι,
      centeredMass x i * centeredMass x j *
        (if i = j then k⁻¹ * Y else -(k * (k - 1))⁻¹ * Y)) =
      k⁻¹ * X * Y + (-(k * (k - 1))⁻¹) * (-X) * Y by
        calc
          (∑ i : ι, ∑ j : ι,
              centeredMass x i * centeredMass x j *
                (if i = j then k⁻¹ * Y
                  else -(k * (k - 1))⁻¹ * Y)) =
            (∑ i : ι, (centeredMass x i) ^ 2 * (k⁻¹ * Y)) +
              ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
                centeredMass x i * centeredMass x j *
                  (-(k * (k - 1))⁻¹ * Y) := by
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [← Finset.add_sum_erase Finset.univ
                      (fun j => centeredMass x i * centeredMass x j *
                        (if i = j then k⁻¹ * Y
                          else -(k * (k - 1))⁻¹ * Y))
                      (Finset.mem_univ i)]
                    simp only [if_pos]
                    congr 1
                    · ring
                    · apply Finset.sum_congr rfl
                      intro j hj
                      rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
          _ = k⁻¹ * X * Y + (-(k * (k - 1))⁻¹) * (-X) * Y := by
            rw [← Finset.sum_mul]
            congr 1
            · dsimp [X]
              ring
            · have hfactor (i : ι) :
                  (∑ j ∈ Finset.univ.erase i,
                    centeredMass x i * centeredMass x j *
                      (-(k * (k - 1))⁻¹ * Y)) =
                    (∑ j ∈ Finset.univ.erase i,
                      centeredMass x i * centeredMass x j) *
                        (-(k * (k - 1))⁻¹ * Y) := by
                    exact (Finset.sum_mul _ _ _).symm
              simp_rw [hfactor]
              rw [← Finset.sum_mul]
              rw [offDiagonal_centered_mass (centeredMass x) hx0]
              dsimp [X]
              ring]
  field_simp [hk0, hk1]
  ring

/-- The same exact variance formula for the manuscript's uncentered overlap,
once each relabeling preserves total mass. -/
theorem relabelingStatistic_variance
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (image : Ω → ι → ι)
    (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hmass : ∀ ω, ∑ i, y (image ω i) = 1)
    (hk : 1 < Fintype.card ι)
    (hfirst : ∀ i,
      uniformAverage (fun ω => centeredMass y (image ω i)) = 0)
    (hsecond : ∀ i j,
      uniformAverage (fun ω =>
        centeredMass y (image ω i) * centeredMass y (image ω j)) =
        if i = j then
          (Fintype.card ι : ℝ)⁻¹ * ∑ r, (centeredMass y r) ^ 2
        else
          -((Fintype.card ι : ℝ) *
            (Fintype.card ι - 1 : ℝ))⁻¹ *
              ∑ r, (centeredMass y r) ^ 2) :
    uniformVariance (relabelingStatistic x y image) =
      (Fintype.card ι : ℝ) ^ 2 /
          (Fintype.card ι - 1 : ℝ) *
        (∑ r, (centeredMass x r) ^ 2) *
        (∑ r, (centeredMass y r) ^ 2) := by
  have hmean := centered_relabeling_mean_zero x y image hfirst
  have hmeanUncentered :=
    relabelingStatistic_mean_one x y image hx hmass hfirst
  calc
    uniformVariance (relabelingStatistic x y image) =
        uniformVariance (centeredRelabelingStatistic x y image) := by
      unfold uniformVariance
      rw [hmeanUncentered, hmean]
      apply congrArg uniformAverage
      funext ω
      rw [relabelingStatistic_eq_centered_add_one x y image hx hmass ω]
      ring
    _ = _ := centered_relabeling_variance
      x y image hx hy hk hfirst hsecond

/-! ## Uniform permutation moments -/

/-- Summing one coordinate over the full permutation group does not depend on
the chosen input coordinate. -/
theorem sum_perm_apply_invariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (i j : ι) :
    (∑ σ : Equiv.Perm ι, z (σ i)) =
      ∑ σ : Equiv.Perm ι, z (σ j) := by
  have h := Equiv.sum_comp
    (Equiv.mulRight (Equiv.swap i j))
    (fun σ : Equiv.Perm ι => z (σ i))
  simpa [Equiv.Perm.mul_def] using h.symm

/-- The corresponding uniform averages are coordinate independent. -/
theorem uniformAverage_perm_apply_invariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (i j : ι) :
    uniformAverage (fun σ : Equiv.Perm ι => z (σ i)) =
      uniformAverage (fun σ : Equiv.Perm ι => z (σ j)) := by
  unfold uniformAverage
  rw [sum_perm_apply_invariant z i j]

/-- Every coordinate of a centered probability mass has zero mean under the
uniform permutation group. -/
theorem uniform_perm_centered_first
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (y : ι → ℝ) (hy : ∑ i, y i = 1) (i : ι) :
    uniformAverage (fun σ : Equiv.Perm ι => centeredMass y (σ i)) = 0 := by
  let A : ι → ℝ := fun j =>
    uniformAverage (fun σ : Equiv.Perm ι => centeredMass y (σ j))
  have hA (j : ι) : A j = A i := by
    exact uniformAverage_perm_apply_invariant (centeredMass y) j i
  have hpoint (σ : Equiv.Perm ι) :
      ∑ j, centeredMass y (σ j) = 0 := by
    rw [Equiv.sum_comp σ]
    exact centeredMass_sum_zero y hy
  have hsum : ∑ j, A j = 0 := by
    rw [show (∑ j, A j) =
        uniformAverage (fun σ : Equiv.Perm ι =>
          ∑ j, centeredMass y (σ j)) by
      symm
      exact uniformAverage_sum
        (fun j (σ : Equiv.Perm ι) => centeredMass y (σ j))]
    rw [show (fun σ : Equiv.Perm ι =>
        ∑ j, centeredMass y (σ j)) = (fun _ => 0) by
      funext σ
      exact hpoint σ]
    simp [uniformAverage]
  rw [show (∑ j, A j) = ∑ _j : ι, A i by
    apply Finset.sum_congr rfl
    intro j _
    exact hA j] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hsum
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hAi : A i = 0 := (mul_eq_zero.mp hsum).resolve_left hk
  exact hAi

/-- The diagonal centered second moment under uniform permutation is the
average centered square mass. -/
theorem uniform_perm_centered_square
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (y : ι → ℝ) (i : ι) :
    uniformAverage (fun σ : Equiv.Perm ι =>
      (centeredMass y (σ i)) ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ r, (centeredMass y r) ^ 2 := by
  let Y : ℝ := ∑ r, (centeredMass y r) ^ 2
  let A : ι → ℝ := fun j =>
    uniformAverage (fun σ : Equiv.Perm ι =>
      (centeredMass y (σ j)) ^ 2)
  have hA (j : ι) : A j = A i := by
    exact uniformAverage_perm_apply_invariant
      (fun r => (centeredMass y r) ^ 2) j i
  have hpoint (σ : Equiv.Perm ι) :
      ∑ j, (centeredMass y (σ j)) ^ 2 = Y := by
    dsimp [Y]
    exact Equiv.sum_comp σ (fun r => (centeredMass y r) ^ 2)
  have hsum : ∑ j, A j = Y := by
    rw [show (∑ j, A j) =
        uniformAverage (fun σ : Equiv.Perm ι =>
          ∑ j, (centeredMass y (σ j)) ^ 2) by
      symm
      exact uniformAverage_sum
        (fun j (σ : Equiv.Perm ι) => (centeredMass y (σ j)) ^ 2)]
    rw [show (fun σ : Equiv.Perm ι =>
        ∑ j, (centeredMass y (σ j)) ^ 2) = (fun _ => Y) by
      funext σ
      exact hpoint σ]
    calc
      uniformAverage (fun _ : Equiv.Perm ι => Y) =
          Y * uniformAverage (fun _ : Equiv.Perm ι => (1 : ℝ)) := by
            rw [← uniformAverage_mul_left]
            congr 1
            funext σ
            ring
      _ = Y := by rw [uniformAverage_one]; ring
  rw [show (∑ j, A j) = ∑ _j : ι, A i by
    apply Finset.sum_congr rfl
    intro j _
    exact hA j] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hsum
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  change A i = (Fintype.card ι : ℝ)⁻¹ * Y
  field_simp
  simpa [mul_comm] using hsum

/-- Two distinct input coordinates can be sent to any two distinct output
coordinates by a permutation. -/
theorem exists_perm_apply_pair
    {ι : Type*} [DecidableEq ι]
    {i j u v : ι} (hij : i ≠ j) (huv : u ≠ v) :
    ∃ τ : Equiv.Perm ι, τ i = u ∧ τ j = v := by
  let τ₁ : Equiv.Perm ι := Equiv.swap i u
  let j₁ : ι := τ₁ j
  have hτ₁i : τ₁ i = u := by simp [τ₁]
  have hj₁u : j₁ ≠ u := by
    intro h
    apply hij
    apply τ₁.injective
    rw [hτ₁i]
    change u = j₁
    exact h.symm
  let τ₂ : Equiv.Perm ι := Equiv.swap j₁ v
  have hτ₂u : τ₂ u = u := by
    exact Equiv.swap_apply_of_ne_of_ne hj₁u.symm huv
  refine ⟨τ₁.trans τ₂, ?_, ?_⟩
  · simp only [Equiv.trans_apply, hτ₁i, hτ₂u]
  · simp only [Equiv.trans_apply]
    change τ₂ j₁ = v
    exact Equiv.swap_apply_left j₁ v

/-- Summing an ordered pair of distinct coordinates over the full permutation
group does not depend on the chosen ordered pair. -/
theorem sum_perm_pair_invariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ι → ℝ) {i j u v : ι}
    (hij : i ≠ j) (huv : u ≠ v) :
    (∑ σ : Equiv.Perm ι, z (σ i) (σ j)) =
      ∑ σ : Equiv.Perm ι, z (σ u) (σ v) := by
  obtain ⟨τ, hτi, hτj⟩ := exists_perm_apply_pair hij huv
  have h := Equiv.sum_comp (Equiv.mulRight τ)
    (fun σ : Equiv.Perm ι => z (σ i) (σ j))
  simpa [Equiv.Perm.mul_def, hτi, hτj] using h.symm

/-- The corresponding ordered-pair uniform averages are invariant. -/
theorem uniformAverage_perm_pair_invariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ι → ℝ) {i j u v : ι}
    (hij : i ≠ j) (huv : u ≠ v) :
    uniformAverage (fun σ : Equiv.Perm ι => z (σ i) (σ j)) =
      uniformAverage (fun σ : Equiv.Perm ι => z (σ u) (σ v)) := by
  unfold uniformAverage
  rw [sum_perm_pair_invariant z hij huv]

/-- Uniform averaging commutes with a finite sum over a specified finset. -/
theorem uniformAverage_finset_sum
    {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (F : ι → Ω → ℝ) :
    uniformAverage (fun ω => ∑ i ∈ s, F i ω) =
      ∑ i ∈ s, uniformAverage (F i) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The off-diagonal centered second moment under uniform permutation has the
exact sampling-without-replacement value. -/
theorem uniform_perm_centered_offdiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (y : ι → ℝ) (hy : ∑ i, y i = 1)
    {i j : ι} (hij : i ≠ j) :
    uniformAverage (fun σ : Equiv.Perm ι =>
      centeredMass y (σ i) * centeredMass y (σ j)) =
      -((Fintype.card ι : ℝ) *
        (Fintype.card ι - 1 : ℝ))⁻¹ *
          ∑ r, (centeredMass y r) ^ 2 := by
  let Y : ℝ := ∑ r, (centeredMass y r) ^ 2
  let A : ι → ι → ℝ := fun u v =>
    uniformAverage (fun σ : Equiv.Perm ι =>
      centeredMass y (σ u) * centeredMass y (σ v))
  have hA {u v : ι} (huv : u ≠ v) : A u v = A i j := by
    exact uniformAverage_perm_pair_invariant
      (fun a b => centeredMass y a * centeredMass y b) huv hij
  have hpoint (σ : Equiv.Perm ι) :
      (∑ u, ∑ v ∈ Finset.univ.erase u,
        centeredMass y (σ u) * centeredMass y (σ v)) = -Y := by
    have hzero : ∑ u, centeredMass y (σ u) = 0 := by
      rw [Equiv.sum_comp σ]
      exact centeredMass_sum_zero y hy
    have hsquare : ∑ u, (centeredMass y (σ u)) ^ 2 = Y := by
      dsimp [Y]
      exact Equiv.sum_comp σ (fun r => (centeredMass y r) ^ 2)
    rw [offDiagonal_centered_mass
      (fun u => centeredMass y (σ u)) hzero, hsquare]
  have hsum :
      (∑ u, ∑ v ∈ Finset.univ.erase u, A u v) = -Y := by
    calc
      (∑ u, ∑ v ∈ Finset.univ.erase u, A u v) =
          ∑ u, uniformAverage (fun σ : Equiv.Perm ι =>
            ∑ v ∈ Finset.univ.erase u,
              centeredMass y (σ u) * centeredMass y (σ v)) := by
            apply Finset.sum_congr rfl
            intro u _
            symm
            exact uniformAverage_finset_sum (Finset.univ.erase u)
              (fun v (σ : Equiv.Perm ι) =>
                centeredMass y (σ u) * centeredMass y (σ v))
      _ = uniformAverage (fun σ : Equiv.Perm ι =>
          ∑ u, ∑ v ∈ Finset.univ.erase u,
            centeredMass y (σ u) * centeredMass y (σ v)) := by
            symm
            exact uniformAverage_sum
              (fun u (σ : Equiv.Perm ι) =>
                ∑ v ∈ Finset.univ.erase u,
                  centeredMass y (σ u) * centeredMass y (σ v))
      _ = -Y := by
        rw [show (fun σ : Equiv.Perm ι =>
            ∑ u, ∑ v ∈ Finset.univ.erase u,
              centeredMass y (σ u) * centeredMass y (σ v)) =
            (fun _ => -Y) by
          funext σ
          exact hpoint σ]
        calc
          uniformAverage (fun _ : Equiv.Perm ι => -Y) =
              (-Y) * uniformAverage (fun _ : Equiv.Perm ι => (1 : ℝ)) := by
                rw [← uniformAverage_mul_left]
                congr 1
                funext σ
                ring
          _ = -Y := by rw [uniformAverage_one]; ring
  rw [show (∑ u, ∑ v ∈ Finset.univ.erase u, A u v) =
      ∑ u, ∑ _v ∈ Finset.univ.erase u, A i j by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v hv
    exact hA (Ne.symm (Finset.ne_of_mem_erase hv))] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem, Finset.mem_univ, Finset.card_univ] at hsum
  have hkNat : 1 < Fintype.card ι :=
    Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) =
      (Fintype.card ι : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
      (Fintype.card_ne_zero))]
    norm_num
  rw [hcast] at hsum
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hk1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hkNat))
  change A i j = -((Fintype.card ι : ℝ) *
    (Fintype.card ι - 1 : ℝ))⁻¹ * Y
  field_simp
  simpa [mul_assoc, mul_left_comm, mul_comm] using hsum

/-- The scaled overlap has exact mean one under the actual uniform permutation
group, with no moment law supplied as a hypothesis. -/
theorem permutation_relabeling_mean_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1) :
    uniformAverage (fun π : Equiv.Perm ι =>
      relabelingStatistic x y (fun σ i => σ i) π) = 1 := by
  let image : Equiv.Perm ι → ι → ι := fun σ i => σ i
  change uniformAverage (relabelingStatistic x y image) = 1
  exact relabelingStatistic_mean_one x y image hx
    (fun π => by
      dsimp [image]
      rw [Equiv.sum_comp π y, hy])
    (fun i => by
      simpa [image] using uniform_perm_centered_first y hy i)

/- The scaled overlap has the manuscript's exact variance under the actual
uniform permutation group. -/
set_option maxHeartbeats 800000 in
theorem permutation_relabeling_variance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hk : 1 < Fintype.card ι) :
    uniformVariance (fun π : Equiv.Perm ι =>
      relabelingStatistic x y (fun σ i => σ i) π) =
      (Fintype.card ι : ℝ) ^ 2 /
      (Fintype.card ι - 1 : ℝ) *
        (∑ r, (centeredMass x r) ^ 2) *
        (∑ r, (centeredMass y r) ^ 2) := by
  let image : Equiv.Perm ι → ι → ι := fun σ i => σ i
  change uniformVariance (relabelingStatistic x y image) = _
  apply relabelingStatistic_variance x y image hx hy
  · intro π
    dsimp [image]
    rw [Equiv.sum_comp π y, hy]
  · exact hk
  · intro i
    exact uniform_perm_centered_first y hy i
  · intro i j
    split_ifs with hij
    · subst j
      simpa [image, pow_two] using uniform_perm_centered_square y i
    · simpa [image] using uniform_perm_centered_offdiagonal y hy hij

/-- With one label, every relabeling statistic is identically one. -/
theorem permutation_relabeling_eq_one_of_card_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hk : Fintype.card ι = 1) (π : Equiv.Perm ι) :
    relabelingStatistic x y (fun σ i => σ i) π = 1 := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hk
  have hxi : x i = 1 := by
    have hsum : (∑ j, x j) = x i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact False.elim (hji (hi j))
      · simp
    rw [← hsum, hx]
  have hyi : y i = 1 := by
    have hsum : (∑ j, y j) = y i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact False.elim (hji (hi j))
      · simp
    rw [← hsum, hy]
  unfold relabelingStatistic
  rw [show (∑ j, x j * y (π j)) = x i * y (π i) by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact False.elim (hji (hi j))
    · simp]
  rw [hi (π i), hxi, hyi, hk]
  norm_num

/-! ## Zero extension from the unit group -/

/-- Extend a real function on the units by zero to the full residue ring. -/
noncomputable def unitZeroExtension
    {N : ℕ} [NeZero N] (f : UnitClass N → ℝ) (a : ZMod N) : ℝ :=
  if h : IsUnit a then f h.unit else 0

/-- Zero extension agrees with the original function on every unit. -/
theorem unitZeroExtension_unit
    {N : ℕ} [NeZero N] (f : UnitClass N → ℝ) (u : UnitClass N) :
    unitZeroExtension f u.val = f u := by
  classical
  unfold unitZeroExtension
  rw [dif_pos u.isUnit]
  congr 1
  apply Units.ext
  exact u.isUnit.unit_spec

/-- Zero extension vanishes on every nonunit residue. -/
theorem unitZeroExtension_nonunit
    {N : ℕ} [NeZero N] (f : UnitClass N → ℝ) (a : ZMod N)
    (ha : ¬IsUnit a) :
    unitZeroExtension f a = 0 := by
  simp [unitZeroExtension, ha]

/-- Zero extension preserves oddness. -/
theorem unitZeroExtension_odd
    {N : ℕ} [NeZero N] (f : UnitClass N → ℝ)
    (hodd : ∀ u, f (-u) = -f u) (a : ZMod N) :
    unitZeroExtension f (-a) = -unitZeroExtension f a := by
  classical
  by_cases ha : IsUnit a
  · let u : UnitClass N := ha.unit
    have hua : u.val = a := ha.unit_spec
    calc
      unitZeroExtension f (-a) = unitZeroExtension f (-u).val := by
        apply congrArg (unitZeroExtension f)
        rw [← hua]
        rfl
      _ = f (-u) := unitZeroExtension_unit f (-u)
      _ = -f u := hodd u
      _ = -unitZeroExtension f u.val := by rw [unitZeroExtension_unit]
      _ = -unitZeroExtension f a := by rw [hua]
  · have hna : ¬IsUnit (-a) := by
      intro h
      apply ha
      simpa using h.neg
    rw [unitZeroExtension_nonunit f a ha,
      unitZeroExtension_nonunit f (-a) hna]
    simp

/-- Canonical equivalence between the unit group and residues equipped with an
`IsUnit` certificate. -/
noncomputable def unitClassEquivIsUnit
    {N : ℕ} [NeZero N] :
    UnitClass N ≃ {a : ZMod N // IsUnit a} where
  toFun u := ⟨u.val, u.isUnit⟩
  invFun a := a.property.unit
  left_inv u := by
    apply Units.ext
    exact u.isUnit.unit_spec
  right_inv a := by
    apply Subtype.ext
    exact a.property.unit_spec

/-- Summing a zero extension over the residue ring is the same as summing the
original function over the unit group. -/
theorem sum_unitZeroExtension
    {N : ℕ} [NeZero N] (f : UnitClass N → ℝ) :
    (∑ a : ZMod N, unitZeroExtension f a) = ∑ u : UnitClass N, f u := by
  classical
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod N)) IsUnit (unitZeroExtension f)
  have hnonunit :
      (∑ a ∈ (Finset.univ : Finset (ZMod N)) with ¬IsUnit a,
        unitZeroExtension f a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : ¬IsUnit a := by simpa using (Finset.mem_filter.mp ha).2
    exact unitZeroExtension_nonunit f a hnot
  calc
    (∑ a : ZMod N, unitZeroExtension f a) =
        ∑ a ∈ (Finset.univ : Finset (ZMod N)) with IsUnit a,
          unitZeroExtension f a := by
            rw [← hpartition, hnonunit, add_zero]
    _ = ∑ a : {a : ZMod N // IsUnit a}, unitZeroExtension f a.val := by
          exact Finset.sum_subtype
            ((Finset.univ : Finset (ZMod N)).filter IsUnit)
            (by intro a; simp) (unitZeroExtension f)
    _ = ∑ u : UnitClass N, f u := by
          symm
          apply Fintype.sum_equiv unitClassEquivIsUnit
          intro u
          simpa [unitClassEquivIsUnit] using
            (unitZeroExtension_unit f u).symm

/-! ## The additive reflection well -/

/-- Finite additive self-convolution. -/
def additiveSelfConvolution {G : Type*} [Fintype G] [AddCommGroup G]
    (f : G → ℝ) (t : G) : ℝ :=
  ∑ a, f a * f (t - a)

/-- Odd input gives an even self-convolution. -/
theorem additiveSelfConvolution_even
    {G : Type*} [Fintype G] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a) (t : G) :
    additiveSelfConvolution f (-t) = additiveSelfConvolution f t := by
  classical
  unfold additiveSelfConvolution
  calc
    (∑ a, f a * f (-t - a)) =
        ∑ a, f (-a) * f (-t - (-a)) := by
      simpa using (Equiv.sum_comp (Equiv.neg G)
        (fun a => f a * f (-t - a))).symm
    _ = ∑ a, f a * f (t - a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hodd, show -t - -a = -(t - a) by abel, hodd]
      ring

/-- Summing every additive shift factors as the square of the total mass. -/
theorem additiveSelfConvolution_total
    {G : Type*} [Fintype G] [AddCommGroup G]
    (f : G → ℝ) :
    ∑ t, additiveSelfConvolution f t = (∑ a, f a) ^ 2 := by
  classical
  unfold additiveSelfConvolution
  rw [Finset.sum_comm, pow_two, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ x, f a * f (x - a) = f a * ∑ x, f (x - a) := by
      rw [Finset.mul_sum]
    _ = f a * ∑ j, f j := by
      congr 1
      exact Equiv.sum_comp (Equiv.subRight a) f
    _ = ∑ j, f a * f j := by
      rw [Finset.mul_sum]

/-- A zero-total signal has zero-total self-convolution. -/
theorem additiveSelfConvolution_total_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (f : G → ℝ) (hsum : ∑ a, f a = 0) :
    ∑ t, additiveSelfConvolution f t = 0 := by
  rw [additiveSelfConvolution_total, hsum, zero_pow]
  norm_num

/-- The reflection shift is exactly the negative square energy. -/
theorem additiveSelfConvolution_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a) :
    additiveSelfConvolution f 0 = -(∑ a, (f a) ^ 2) := by
  classical
  unfold additiveSelfConvolution
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [zero_sub, hodd]
  ring

/-- Nonzero shifts collectively compensate for the negative reflection well. -/
theorem additiveSelfConvolution_nonzero_compensation
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a)
    (hsum : ∑ a, f a = 0) :
    ∑ t ∈ Finset.univ.erase 0, additiveSelfConvolution f t =
      ∑ a, (f a) ^ 2 := by
  have htotal := additiveSelfConvolution_total_zero f hsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G)),
    additiveSelfConvolution_zero f hodd] at htotal
  linarith

/-! ## Additive Fourier square -/

/-- The complex additive transform of a real signal. -/
noncomputable def realAdditiveTransform {N : ℕ} [NeZero N]
    (f : ZMod N → ℝ) (j : ZMod N) : ℂ :=
  ∑ a : ZMod N, (f a : ℂ) * stdAddChar (-(a * j))

/-- The transform of a real odd signal is purely imaginary. -/
theorem realAdditiveTransform_star_eq_neg
    {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (j : ZMod N) :
    star (realAdditiveTransform f j) = -realAdditiveTransform f j := by
  classical
  unfold realAdditiveTransform
  rw [star_sum]
  calc
    (∑ a : ZMod N,
        star ((f a : ℂ) * stdAddChar (-(a * j)))) =
      ∑ a : ZMod N, (f a : ℂ) * stdAddChar (a * j) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [star_mul]
        have hreal : star (f a : ℂ) = (f a : ℂ) := by simp
        rw [hreal]
        have hchar : star (stdAddChar (-(a * j))) =
            stdAddChar (a * j) := by
          have h :=
            AddChar.map_neg_eq_conj (stdAddChar (N := N)) (-(a * j))
          simpa using h.symm
        rw [hchar]
        ring
    _ = ∑ a : ZMod N, (f (-a) : ℂ) * stdAddChar ((-a) * j) := by
      simpa using (Equiv.sum_comp (Equiv.neg (ZMod N))
        (fun a : ZMod N => (f a : ℂ) * stdAddChar (a * j))).symm
    _ = -∑ a : ZMod N, (f a : ℂ) * stdAddChar (-(a * j)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [hodd]
      push_cast
      rw [show (-a) * j = -(a * j) by ring]
      ring

/-- Fourier transform takes the finite additive self-convolution to a square. -/
theorem additiveSelfConvolution_transform
    {N : ℕ} [NeZero N] (f : ZMod N → ℝ) (j : ZMod N) :
    realAdditiveTransform (additiveSelfConvolution f) j =
      (realAdditiveTransform f j) ^ 2 := by
  classical
  unfold realAdditiveTransform additiveSelfConvolution
  simp_rw [Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [Finset.sum_mul]
  rw [pow_two, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Fintype.sum_equiv (Equiv.subRight a)
  intro t
  simp only [Equiv.subRight_apply]
  have hphase : stdAddChar (-(a * j)) *
      stdAddChar (-((t - a) * j)) = stdAddChar (-(t * j)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [← hphase]
  ring

/-- The additive spectrum of an odd real signal is a negative norm square. -/
theorem additive_reflection_spectrum_nonpositive
    {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hodd : ∀ a, f (-a) = -f a) (j : ZMod N) :
    (realAdditiveTransform f j) ^ 2 =
        -(Complex.normSq (realAdditiveTransform f j) : ℂ) ∧
      ((realAdditiveTransform f j) ^ 2).re ≤ 0 := by
  have hstar := realAdditiveTransform_star_eq_neg f hodd j
  constructor
  · rw [Complex.normSq_eq_conj_mul_self]
    change _ = -(star (realAdditiveTransform f j) * realAdditiveTransform f j)
    rw [hstar]
    ring
  · rw [show (realAdditiveTransform f j) ^ 2 =
        -(Complex.normSq (realAdditiveTransform f j) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]
      change _ = -(star (realAdditiveTransform f j) *
        realAdditiveTransform f j)
      rw [hstar]
      ring]
    change -Complex.normSq (realAdditiveTransform f j) ≤ 0
    exact neg_nonpos.mpr (Complex.normSq_nonneg _)

/-! ## Reflected pair obstruction -/

/-- Every finite family of reflected additive pairs contributes the negative
square energy. -/
theorem reflected_pair_sum
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a)
    (p q : ι → G) (hpq : ∀ i, q i = -p i) :
    (∑ i, f (p i) * f (q i)) = -(∑ i, (f (p i)) ^ 2) := by
  classical
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hpq, hodd]
  ring

/-- Consequently every reflected-pair sum is nonpositive. -/
theorem reflected_pair_sum_nonpositive
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (f : G → ℝ) (hodd : ∀ a, f (-a) = -f a)
    (p q : ι → G) (hpq : ∀ i, q i = -p i) :
    (∑ i, f (p i) * f (q i)) ≤ 0 := by
  rw [reflected_pair_sum f hodd p q hpq]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end NField.Alignment.SpectralRepulsion
