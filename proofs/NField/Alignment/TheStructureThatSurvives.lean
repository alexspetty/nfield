/-
Author: Alexander S. Petty
-/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import NField.Alignment.CollisionInvariant
import NField.Alignment.CenteredCollisionClosure

/-!
# The structure that survives

Exact all-size slice periodicity, reflection parity, and finite block-quotient
algebra for the Lean companion to "The Structure That Survives".
-/

namespace NField.Alignment.TheStructureThatSurvives

open scoped BigOperators ComplexConjugate
open Filter
open NField.CollisionDefinition
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.CollisionInvariant
open NField.Alignment.CenteredCollisionClosure

/-! ## The all-size finite slice table -/

/-- The lower-size restriction is unnecessary after the diagonal-slice
reduction.  Every positive integer coprime to the base reduces to its least
positive residue modulo `b^(ell+1)`, including quotient zero. -/
theorem allLagSliceDeviation_eq_table_mod
    {b ell N : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hcop : Nat.Coprime N b) :
    allLagSliceDeviation b ell N =
      allLagTable b ell (N % allLagModulus b ell) := by
  let m := allLagModulus b ell
  let a := N % m
  have hcopPow : Nat.Coprime N m := by
    simpa [m, allLagModulus] using hcop.pow_right (ell + 1)
  have hcopA : Nat.Coprime a m := by
    simpa [a] using (ZMod.coprime_mod_iff_coprime N m).2 hcopPow
  have ha : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha0
    have hmOne : m = 1 := by
      rw [ha0] at hcopA
      simpa using hcopA
    have hmLower : 2 ≤ m := by
      dsimp [m, allLagModulus]
      exact le_trans hb2 (Nat.le_pow (by omega))
    omega
  have hdecomp : m * (N / m) + a = N := by
    calc
      m * (N / m) + a = a + m * (N / m) := by omega
      _ = N := by simpa [a] using Nat.mod_add_div N m
  change allLagSliceDeviation b ell N = allLagTable b ell a
  rw [← hdecomp]
  exact allLagSliceDeviation_eq_table hb2 hell ha hcopA

/-- Direct digit collisions reduce to the same finite table for every integer
coprime to the base, including the quotient-zero case. -/
theorem directAllLagDeviation_eq_table_mod
    {b ell N : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hcop : Nat.Coprime N b) :
    directAllLagDeviation b ell N =
      allLagTable b ell (N % allLagModulus b ell) := by
  let m := allLagModulus b ell
  let a := N % m
  have hcopPow : Nat.Coprime N m := by
    simpa [m, allLagModulus] using hcop.pow_right (ell + 1)
  have hcopA : Nat.Coprime a m := by
    simpa [a] using (ZMod.coprime_mod_iff_coprime N m).2 hcopPow
  have ha : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha0
    have hmOne : m = 1 := by
      rw [ha0] at hcopA
      simpa using hcopA
    have hmLower : 2 ≤ m := by
      dsimp [m, allLagModulus]
      exact le_trans hb2 (Nat.le_pow (by omega))
    omega
  have hmPos : 0 < m := by
    dsimp [m, allLagModulus]
    exact pow_pos (by omega) _
  have halt : a < m := by
    exact Nat.mod_lt N hmPos
  have hdecomp : m * (N / m) + a = N := by
    calc
      m * (N / m) + a = a + m * (N / m) := by omega
      _ = N := by simpa [a] using Nat.mod_add_div N m
  change directAllLagDeviation b ell N = allLagTable b ell a
  rw [← hdecomp]
  exact directAllLagDeviation_eq_allLagTable hb2 hell ha halt hcopA

/-- A prime divisor of the base has exact direct collision deviation zero at
every positive lag. -/
theorem primeDividingBase_directDeviation_zero
    {b ell p : ℕ} (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (hp : Nat.Prime p) (hpb : p ∣ b) :
    directAllLagDeviation b ell p = 0 := by
  have hp0 : 0 < p := hp.pos
  have hple : p ≤ b := Nat.le_of_dvd (by omega) hpb
  have hpPow : p ∣ b ^ ell :=
    dvd_trans hpb (dvd_pow_self b (by omega))
  have hcount : directAllLagCollisionCount b ell p = 0 := by
    unfold directAllLagCollisionCount
    apply Finset.sum_eq_zero
    intro r hr
    have hrange := Finset.mem_Ico.mp hr
    have htransport : (b ^ ell * r) % p = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_left hpPow r)
    have hbinPos : 0 < digitBin b p r := by
      unfold digitBin
      apply Nat.div_pos
      · calc
          p ≤ b := hple
          _ ≤ b * r := Nat.le_mul_of_pos_right b hrange.1
      · exact hp0
    have hzero : digitBin b p 0 = 0 := by simp [digitBin]
    have hne : digitBin b p r ≠ digitBin b p 0 := by
      rw [hzero]
      exact hbinPos.ne'
    simp [htransport, hne]
  have hfloor : (p - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
  unfold directAllLagDeviation
  rw [hcount, hfloor]
  simp

/-! ## Reflection and the parity gate -/

/-- The half-centered finite unit table. -/
noncomputable def halfCenteredUnitTable
    (b ell : ℕ) [NeZero (allLagModulus b ell)]
    (a : UnitClass (allLagModulus b ell)) : ℂ :=
  allLagUnitTable b ell a + 1 / 2

/-- Reflection makes the half-centered table exactly odd. -/
theorem halfCenteredUnitTable_odd
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    halfCenteredUnitTable b ell (-a) = -halfCenteredUnitTable b ell a := by
  have hreflect := allLagUnitTable_reflection hb2 hell a
  unfold halfCenteredUnitTable
  linear_combination hreflect

/-- Every even character is killed by the actual half-centered unit table. -/
theorem halfCenteredUnitTable_evenCoefficient_zero
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell)) (heven : χ.Even) :
    collisionCoefficient (halfCenteredUnitTable b ell) χ = 0 :=
  collisionCoefficient_even_zero (halfCenteredUnitTable b ell) χ
    (halfCenteredUnitTable_odd hb2 hell)
    (even_character_invariant_under_negation χ heven)

/-! ## Exact block compression -/

/-- A fiber of a finite label map. -/
abbrev LabelFiber {ι κ : Type*} (label : ι → κ) (α : κ) :=
  {i : ι // label i = α}

/-- The population of one label state. -/
def labelPopulation
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (α : κ) : ℕ :=
  Fintype.card (LabelFiber label α)

/-- Sum a particle vector over one label block. -/
def labelBlockSum
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (v : ι → ℝ) (α : κ) : ℝ :=
  ∑ i : LabelFiber label α, v i

/-- Orthonormal block coordinate with an abstract nonzero square-root scale. -/
noncomputable def normalizedBlockCoordinate
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (v : ι → ℝ) (α : κ) : ℝ :=
  labelBlockSum label v α / scale α

/-- Lift quotient coordinates back to a block-constant particle vector. -/
noncomputable def normalizedBlockLift
    {ι κ : Type*} (label : ι → κ) (scale : κ → ℝ)
    (y : κ → ℝ) (i : ι) : ℝ :=
  y (label i) / scale (label i)

/-- The particle kernel obtained from a normalized quotient matrix. -/
noncomputable def normalizedBlockKernel
    {ι κ : Type*} (label : ι → κ) (scale : κ → ℝ)
    (Q : Matrix κ κ ℝ) : Matrix ι ι ℝ :=
  fun i j => Q (label i) (label j) /
    (scale (label i) * scale (label j))

/-- A normalized block kernel acts only through the finitely many block
coordinates. -/
theorem normalizedBlockKernel_mulVec
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (Q : Matrix κ κ ℝ)
    (hscale : ∀ α, scale α ≠ 0) (v : ι → ℝ) (i : ι) :
    Matrix.mulVec (normalizedBlockKernel label scale Q) v i =
      Matrix.mulVec Q (normalizedBlockCoordinate label scale v) (label i) /
        scale (label i) := by
  classical
  unfold normalizedBlockKernel Matrix.mulVec dotProduct
  rw [← Fintype.sum_fiberwise label
    (fun j =>
      Q (label i) (label j) /
        (scale (label i) * scale (label j)) * v j)]
  unfold normalizedBlockCoordinate labelBlockSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro α _
  have hpoint (j : LabelFiber label α) :
      Q (label i) (label j) /
          (scale (label i) * scale (label j)) * v j =
        Q (label i) α / (scale (label i) * scale α) * v j := by
    rw [j.property]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  field_simp [hscale α, hscale (label i)]

/-- The normalized block coordinate of a normalized lift is exactly the
original quotient vector. -/
theorem normalizedBlockCoordinate_lift
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ)
    (hscale : ∀ α, scale α ≠ 0)
    (hscaleSq : ∀ α, scale α ^ 2 = labelPopulation label α)
    (y : κ → ℝ) (α : κ) :
    normalizedBlockCoordinate label scale
      (normalizedBlockLift label scale y) α = y α := by
  classical
  unfold normalizedBlockCoordinate labelBlockSum normalizedBlockLift
  have hpoint (i : LabelFiber label α) :
      y (label i) / scale (label i) = y α / scale α := by
    rw [i.property]
  simp_rw [hpoint]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  have hsquare : scale α * scale α = labelPopulation label α := by
    simpa [pow_two] using hscaleSq α
  rw [show (Fintype.card (LabelFiber label α) : ℝ) =
      labelPopulation label α by rfl]
  rw [← hsquare]
  field_simp [hscale α]

/-- The block-constant subspace is invariant and its matrix is exactly `Q` in
the normalized block coordinates. -/
theorem normalizedBlockKernel_mulVec_lift
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (Q : Matrix κ κ ℝ)
    (hscale : ∀ α, scale α ≠ 0)
    (hscaleSq : ∀ α, scale α ^ 2 = labelPopulation label α)
    (y : κ → ℝ) :
    Matrix.mulVec (normalizedBlockKernel label scale Q)
        (normalizedBlockLift label scale y) =
      normalizedBlockLift label scale (Matrix.mulVec Q y) := by
  have hcoordinate :
      normalizedBlockCoordinate label scale
          (normalizedBlockLift label scale y) = y := by
    funext α
    exact normalizedBlockCoordinate_lift label scale hscale hscaleSq y α
  funext i
  rw [normalizedBlockKernel_mulVec label scale Q hscale]
  rw [hcoordinate]
  unfold normalizedBlockLift
  rfl

/-- Vectors with zero sum on every label block are annihilated by the
normalized kernel. -/
theorem normalizedBlockKernel_annihilates_zeroBlockCoordinates
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (Q : Matrix κ κ ℝ)
    (hscale : ∀ α, scale α ≠ 0) (v : ι → ℝ)
    (hzero : normalizedBlockCoordinate label scale v = 0) :
    Matrix.mulVec (normalizedBlockKernel label scale Q) v = 0 := by
  funext i
  rw [normalizedBlockKernel_mulVec label scale Q hscale]
  rw [hzero]
  simp

/-- The squared normalized Laplacian action. -/
noncomputable def squaredNormalizedLaplacianAction
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ :=
  let L := fun w : ι → ℝ => w - Matrix.mulVec A w
  L (L v)

/-- Every within-block zero-sum vector is an exact eigenvector with eigenvalue
one of the squared normalized Laplacian. -/
theorem squaredNormalizedLaplacianAction_eq_self_of_kernel
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℝ)
    (hzero : Matrix.mulVec A v = 0) :
    squaredNormalizedLaplacianAction A v = v := by
  simp [squaredNormalizedLaplacianAction, hzero]

/-- The block-coordinate map as a linear map. -/
noncomputable def normalizedBlockCoordinateLinear
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (κ → ℝ) where
  toFun := normalizedBlockCoordinate label scale
  map_add' x y := by
    funext α
    simp [normalizedBlockCoordinate, labelBlockSum,
      Finset.sum_add_distrib, add_div]
  map_smul' c x := by
    funext α
    change (∑ i : LabelFiber label α, c * x i) / scale α =
      c * ((∑ i : LabelFiber label α, x i) / scale α)
    rw [← Finset.mul_sum]
    ring

/-- Nonempty label blocks make the normalized block-coordinate map
surjective. -/
theorem normalizedBlockCoordinateLinear_surjective
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ)
    (hscale : ∀ α, scale α ≠ 0)
    (hscaleSq : ∀ α, scale α ^ 2 = labelPopulation label α) :
    Function.Surjective (normalizedBlockCoordinateLinear label scale) := by
  intro y
  refine ⟨normalizedBlockLift label scale y, ?_⟩
  funext α
  exact normalizedBlockCoordinate_lift label scale hscale hscaleSq y α

/-- The exact dimension of the within-block zero-sum space is `N-q`. -/
theorem normalizedBlockCoordinate_ker_finrank
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ)
    (hscale : ∀ α, scale α ≠ 0)
    (hscaleSq : ∀ α, scale α ^ 2 = labelPopulation label α) :
    Module.finrank ℝ (normalizedBlockCoordinateLinear label scale).ker =
      Fintype.card ι - Fintype.card κ := by
  have hrange : (normalizedBlockCoordinateLinear label scale).range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (normalizedBlockCoordinateLinear_surjective label scale hscale hscaleSq)
  have h := LinearMap.finrank_range_add_finrank_ker
    (normalizedBlockCoordinateLinear label scale)
  rw [hrange, finrank_top, Module.finrank_pi, Module.finrank_pi] at h
  omega

/-- Combining the previous results gives an exact `N-q`-dimensional
eigenvalue-one subspace. -/
theorem surviving_bulk_subspace
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (scale : κ → ℝ) (Q : Matrix κ κ ℝ)
    (hscale : ∀ α, scale α ≠ 0)
    (hscaleSq : ∀ α, scale α ^ 2 = labelPopulation label α) :
    Module.finrank ℝ (normalizedBlockCoordinateLinear label scale).ker =
        Fintype.card ι - Fintype.card κ ∧
      ∀ v ∈ (normalizedBlockCoordinateLinear label scale).ker,
        squaredNormalizedLaplacianAction
          (normalizedBlockKernel label scale Q) v = v := by
  constructor
  · exact normalizedBlockCoordinate_ker_finrank label scale hscale hscaleSq
  · intro v hv
    apply squaredNormalizedLaplacianAction_eq_self_of_kernel
    apply normalizedBlockKernel_annihilates_zeroBlockCoordinates
      label scale Q hscale v
    exact LinearMap.mem_ker.mp hv

/-! ## Fixed complexity and prime coverage -/

/-- Every finite unit class contains arbitrarily large primes. -/
theorem unitClass_contains_arbitrarily_large_primes
    {m : ℕ} [NeZero m] (a : UnitClass m) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod m) = a.val :=
  Nat.forall_exists_prime_gt_and_eq_mod a.isUnit n

/-- Any fixed finite number of surviving modes has asymptotic proportion
zero in a growing ambient list. -/
theorem fixedModeProportion_tendsto_zero (q : ℕ) :
    Tendsto (fun N : ℕ => (q : ℝ) / N) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-! ## Heat bounds and exact displayed tables -/

/-- Every quotient heat term whose squared-Laplacian eigenvalue lies in
`[0,1]` lies between the bulk heat term and one. -/
theorem quotientHeatTerms_bounds
    {κ : Type*} [Fintype κ] (mode : κ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hmode : ∀ i, 0 ≤ mode i ∧ mode i ≤ 1) :
    (Fintype.card κ : ℝ) * Real.exp (-t) ≤
        ∑ i, Real.exp (-t * mode i) ∧
      (∑ i, Real.exp (-t * mode i)) ≤ Fintype.card κ := by
  constructor
  · calc
      (Fintype.card κ : ℝ) * Real.exp (-t) =
          ∑ _i : κ, Real.exp (-t) := by simp
      _ ≤ ∑ i, Real.exp (-t * mode i) := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.exp_le_exp.mpr
        nlinarith [(hmode i).2]
  · calc
      (∑ i, Real.exp (-t * mode i)) ≤ ∑ _i : κ, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [(hmode i).1]
      _ = Fintype.card κ := by simp

/-- Exact set of labels in the lag-one finite unit table. -/
def finiteUnitLabelSet (b : ℕ) : Finset ℤ :=
  (reducedResidues (allLagModulus b 1)).image (allLagTable b 1)

theorem baseSeven_finiteUnitLabelSet :
    finiteUnitLabelSet 7 = {-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} := by
  decide

theorem baseTen_finiteUnitLabelSet :
    finiteUnitLabelSet 10 = {-9, -7, -4, -3, -2, -1, 0, 1, 2, 3, 6, 8} := by
  decide

theorem baseTwelve_finiteUnitLabelSet :
    finiteUnitLabelSet 12 = {-11, -7, -5, -3, -2, -1, 0, 1, 2, 4, 6, 10} := by
  decide

theorem displayed_finiteUnitLabelSet_cardinalities :
    (finiteUnitLabelSet 7).card = 12 ∧
      (finiteUnitLabelSet 10).card = 12 ∧
      (finiteUnitLabelSet 12).card = 12 := by
  decide

end NField.Alignment.TheStructureThatSurvives
