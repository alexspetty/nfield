/-
Author: Alexander S. Petty
-/

import NField.Alignment.GeneralNeutrality

/-!
# Double transversality

Finite product-space orthogonality, energy splitting, coordinate recovery,
and common-quotient algebra for the Lean companion to
"The Double Transversality".
-/

namespace NField.Alignment.DoubleTransversality

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.GeneralNeutrality

/-! ## Normalized finite geometry -/

/-- Uniform finite inner product in the manuscript's convention. -/
noncomputable def finiteInner {α : Type*} [Fintype α]
    (f g : α → ℂ) : ℂ :=
  (Fintype.card α : ℂ)⁻¹ * ∑ x, f x * star (g x)

/-- Uniform finite square energy. -/
noncomputable def finiteEnergy {α : Type*} [Fintype α]
    (f : α → ℂ) : ℂ :=
  finiteInner f f

/-- Normalized finite inner products are invariant under reindexing. -/
theorem finiteInner_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f g : β → ℂ) :
    finiteInner (fun x => f (e x)) (fun x => g (e x)) = finiteInner f g := by
  classical
  unfold finiteInner
  rw [Fintype.card_congr e]
  congr 1
  simpa using Equiv.sum_comp e (fun y : β => f y * star (g y))

/-- Square energy is likewise invariant under finite reindexing. -/
theorem finiteEnergy_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℂ) :
    finiteEnergy (fun x => f (e x)) = finiteEnergy f :=
  finiteInner_equiv e f f

/-- Lift a signal from the left coordinate of a product. -/
def leftLift {α β : Type*} (f : α → ℂ) : α × β → ℂ :=
  fun x => f x.1

/-- Lift a signal from the right coordinate of a product. -/
def rightLift {α β : Type*} (g : β → ℂ) : α × β → ℂ :=
  fun x => g x.2

/-- Two zero-sum coordinate lifts are exactly orthogonal on the complete
product space. -/
theorem product_lifts_orthogonal
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ)
    (hf : ∑ x, f x = 0) (_hg : ∑ y, g y = 0) :
    finiteInner (leftLift (β := β) f) (rightLift (α := α) g) = 0 := by
  classical
  unfold finiteInner leftLift rightLift
  rw [Fintype.sum_prod_type]
  calc
    (↑(Fintype.card (α × β)))⁻¹ *
        ∑ x : α, ∑ y : β, f x * star (g y) =
      (↑(Fintype.card (α × β)))⁻¹ *
        ((∑ x : α, f x) * ∑ y : β, star (g y)) := by
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = 0 := by rw [hf]; simp

/-- The reverse cross term also vanishes. -/
theorem product_lifts_orthogonal_rev
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ)
    (_hf : ∑ x, f x = 0) (hg : ∑ y, g y = 0) :
    finiteInner (rightLift (α := α) g) (leftLift (β := β) f) = 0 := by
  classical
  unfold finiteInner leftLift rightLift
  rw [Fintype.sum_prod_type]
  calc
    (↑(Fintype.card (α × β)))⁻¹ *
        ∑ x : α, ∑ y : β, g y * star (f x) =
      (↑(Fintype.card (α × β)))⁻¹ *
        ((∑ y : β, g y) * ∑ x : α, star (f x)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
    _ = 0 := by rw [hg]; simp

/-- Lifting through one product coordinate preserves normalized energy. -/
theorem leftLift_energy
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℂ) :
    finiteEnergy (leftLift (β := β) f) = finiteEnergy f := by
  classical
  unfold finiteEnergy finiteInner leftLift
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Nat.cast_mul]
  have hα : (Fintype.card α : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hβ : (Fintype.card β : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The symmetric right-coordinate lift also preserves normalized energy. -/
theorem rightLift_energy
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (g : β → ℂ) :
    finiteEnergy (rightLift (α := α) g) = finiteEnergy g := by
  classical
  unfold finiteEnergy finiteInner rightLift
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Nat.cast_mul]
  have hα : (Fintype.card α : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hβ : (Fintype.card β : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  field_simp

/-- Exact two-coordinate Pythagorean identity for arbitrary complex weights. -/
theorem weighted_product_energy
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β]
    (f : α → ℂ) (g : β → ℂ)
    (hf : ∑ x, f x = 0) (hg : ∑ y, g y = 0)
    (w v : ℂ) :
    finiteEnergy (fun x : α × β =>
        w * leftLift (β := β) f x + v * rightLift (α := α) g x) =
      (w * star w) * finiteEnergy f +
        (v * star v) * finiteEnergy g := by
  classical
  have hcross := product_lifts_orthogonal f g hf hg
  have hcross' := product_lifts_orthogonal_rev f g hf hg
  have hleft := leftLift_energy (β := β) f
  have hright := rightLift_energy (α := α) g
  unfold finiteEnergy finiteInner at *
  have hexpand :
      (∑ x : α × β,
          (w * leftLift f x + v * rightLift g x) *
            star (w * leftLift f x + v * rightLift g x)) =
        (w * star w) *
            ∑ x : α × β, leftLift f x * star (leftLift f x) +
          (w * star v) *
            ∑ x : α × β, leftLift f x * star (rightLift g x) +
          (v * star w) *
            ∑ x : α × β, rightLift g x * star (leftLift f x) +
          (v * star v) *
            ∑ x : α × β, rightLift g x * star (rightLift g x) := by
    calc
      (∑ x : α × β,
          (w * leftLift f x + v * rightLift g x) *
            star (w * leftLift f x + v * rightLift g x)) =
        ∑ x : α × β,
          ((w * star w) * (leftLift f x * star (leftLift f x)) +
            (w * star v) * (leftLift f x * star (rightLift g x)) +
            (v * star w) * (rightLift g x * star (leftLift f x)) +
            (v * star v) * (rightLift g x * star (rightLift g x))) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [star_add, star_mul, star_mul]
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
        simp_rw [← Finset.mul_sum]
  rw [hexpand]
  calc
    (↑(Fintype.card (α × β)))⁻¹ *
          ((w * star w) * ∑ x, leftLift f x * star (leftLift f x) +
            (w * star v) * ∑ x, leftLift f x * star (rightLift g x) +
            (v * star w) * ∑ x, rightLift g x * star (leftLift f x) +
            (v * star v) * ∑ x, rightLift g x * star (rightLift g x)) =
        (w * star w) *
            ((↑(Fintype.card (α × β)))⁻¹ *
              ∑ x, leftLift f x * star (leftLift f x)) +
          (w * star v) *
            ((↑(Fintype.card (α × β)))⁻¹ *
              ∑ x, leftLift f x * star (rightLift g x)) +
          (v * star w) *
            ((↑(Fintype.card (α × β)))⁻¹ *
              ∑ x, rightLift g x * star (leftLift f x)) +
          (v * star v) *
            ((↑(Fintype.card (α × β)))⁻¹ *
              ∑ x, rightLift g x * star (rightLift g x)) := by ring
    _ = _ := by rw [hleft, hcross, hcross', hright]; simp

/-- Averaging a weighted two-coordinate signal over the right coordinate
recovers the left component exactly. -/
theorem recover_left_coordinate
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → ℂ) (g : β → ℂ) (hg : ∑ y, g y = 0)
    (w v : ℂ) (x : α) :
    (Fintype.card β : ℂ)⁻¹ *
        ∑ y : β, (w * f x + v * g y) = w * f x := by
  classical
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hg, mul_zero,
    add_zero, Finset.card_univ]
  have hβ : (Fintype.card β : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  field_simp

/-! ## Coordinate-axis Fourier support -/

/-- A left-coordinate lift has zero coefficient against every product
channel whose right factor has zero total. -/
theorem leftLift_product_channel_zero
    {α β : Type*} [Fintype α] [Fintype β]
    (f χ : α → ℂ) (ψ : β → ℂ) (hψ : ∑ y, ψ y = 0) :
    finiteCoefficient (leftLift (β := β) f)
      (fun x : α × β => χ x.1 * ψ x.2) = 0 := by
  classical
  unfold finiteCoefficient leftLift
  rw [Fintype.sum_prod_type]
  have hstar : (∑ y : β, star (ψ y)) = 0 := by
    calc
      (∑ y : β, star (ψ y)) = star (∑ y : β, ψ y) := by
        simp
      _ = 0 := by rw [hψ, star_zero]
  have hmul (a b : ℂ) : star (a * b) = star a * star b :=
    (star_mul a b).trans (mul_comm _ _)
  calc
    (↑(Fintype.card (α × β)))⁻¹ *
        ∑ x : α, ∑ y : β, f x * star (χ x * ψ y) =
      (↑(Fintype.card (α × β)))⁻¹ *
        ∑ x : α, (f x * star (χ x)) * ∑ y : β, star (ψ y) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          rw [hmul]
          ring
    _ = 0 := by rw [hstar]; simp

/-- A right-coordinate lift has zero coefficient against every product
channel whose left factor has zero total. -/
theorem rightLift_product_channel_zero
    {α β : Type*} [Fintype α] [Fintype β]
    (g : β → ℂ) (χ : α → ℂ) (ψ : β → ℂ)
    (hχ : ∑ x, χ x = 0) :
    finiteCoefficient (rightLift (α := α) g)
      (fun x : α × β => χ x.1 * ψ x.2) = 0 := by
  classical
  unfold finiteCoefficient rightLift
  rw [Fintype.sum_prod_type]
  have hstar : (∑ x : α, star (χ x)) = 0 := by
    calc
      (∑ x : α, star (χ x)) = star (∑ x : α, χ x) := by
        simp
      _ = 0 := by rw [hχ, star_zero]
  have hmul (a b : ℂ) : star (a * b) = star a * star b :=
    (star_mul a b).trans (mul_comm _ _)
  calc
    (↑(Fintype.card (α × β)))⁻¹ *
        ∑ x : α, ∑ y : β, g y * star (χ x * ψ y) =
      (↑(Fintype.card (α × β)))⁻¹ *
        ((∑ y : β, g y * star (ψ y)) * ∑ x : α, star (χ x)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _
          rw [hmul]
          ring
    _ = 0 := by rw [hstar]; simp

/-! ## Actual unit-group Chinese-remainder lifts -/

/-- A centered signal lifted to the left CRT coordinate. -/
noncomputable def crtLeftLift {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (f : UnitClass m → ℂ) :
    UnitClass (m * n) → ℂ :=
  fun a => f ((generalCrtUnitEquiv h a).1)

/-- A centered signal lifted to the right CRT coordinate. -/
noncomputable def crtRightLift {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (g : UnitClass n → ℂ) :
    UnitClass (m * n) → ℂ :=
  fun a => g ((generalCrtUnitEquiv h a).2)

/-- Exact orthogonality of two zero-sum signals after the actual unit-group
Chinese-remainder lift. -/
theorem crt_lifts_orthogonal
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n)
    (f : UnitClass m → ℂ) (g : UnitClass n → ℂ)
    (hf : ∑ x, f x = 0) (_hg : ∑ y, g y = 0) :
    finiteInner (crtLeftLift h f) (crtRightLift h g) = 0 := by
  classical
  unfold finiteInner crtLeftLift crtRightLift
  apply mul_eq_zero_of_right
  calc
    (∑ a : UnitClass (m * n),
        f ((generalCrtUnitEquiv h a).1) *
          star (g ((generalCrtUnitEquiv h a).2))) =
      ∑ x : UnitClass m × UnitClass n, f x.1 * star (g x.2) := by
        simpa using Equiv.sum_comp (generalCrtUnitEquiv h)
          (fun x : UnitClass m × UnitClass n => f x.1 * star (g x.2))
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ x : UnitClass m, ∑ y : UnitClass n, f x * star (g y)) =
            (∑ x : UnitClass m, f x) *
              ∑ y : UnitClass n, star (g y) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro x _
                rw [Finset.mul_sum]
        _ = 0 := by rw [hf]; simp

/-- A CRT coordinate lift preserves its normalized energy. -/
theorem crtLeftLift_energy
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (f : UnitClass m → ℂ) :
    finiteEnergy (crtLeftLift h f) = finiteEnergy f := by
  calc
    finiteEnergy (crtLeftLift h f) =
      finiteEnergy (leftLift (β := UnitClass n) f) := by
        unfold crtLeftLift
        exact finiteEnergy_equiv (generalCrtUnitEquiv h)
          (leftLift (β := UnitClass n) f)
    _ = finiteEnergy f := leftLift_energy (β := UnitClass n) f

/-- The symmetric CRT coordinate lift preserves normalized energy. -/
theorem crtRightLift_energy
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (g : UnitClass n → ℂ) :
    finiteEnergy (crtRightLift h g) = finiteEnergy g := by
  calc
    finiteEnergy (crtRightLift h g) =
      finiteEnergy (rightLift (α := UnitClass m) g) := by
        unfold crtRightLift
        exact finiteEnergy_equiv (generalCrtUnitEquiv h)
          (rightLift (α := UnitClass m) g)
    _ = finiteEnergy g := rightLift_energy (α := UnitClass m) g

/-- The exact weighted energy splitting transported to the actual joint unit
group by the Chinese remainder equivalence. -/
theorem weighted_crt_energy
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n)
    (f : UnitClass m → ℂ) (g : UnitClass n → ℂ)
    (hf : ∑ x, f x = 0) (hg : ∑ y, g y = 0)
    (w v : ℂ) :
    finiteEnergy (fun a : UnitClass (m * n) =>
        w * crtLeftLift h f a + v * crtRightLift h g a) =
      (w * star w) * finiteEnergy f +
        (v * star v) * finiteEnergy g := by
  let e := generalCrtUnitEquiv h
  calc
    finiteEnergy (fun a : UnitClass (m * n) =>
        w * crtLeftLift h f a + v * crtRightLift h g a) =
      finiteEnergy (fun x : UnitClass m × UnitClass n =>
        w * leftLift (β := UnitClass n) f x +
          v * rightLift (α := UnitClass m) g x) := by
            simpa [e, crtLeftLift, crtRightLift, leftLift, rightLift] using
              finiteEnergy_equiv e
                (fun x : UnitClass m × UnitClass n =>
                  w * leftLift (β := UnitClass n) f x +
                    v * rightLift (α := UnitClass m) g x)
    _ = _ := weighted_product_energy f g hf hg w v

/-! ## The common quotient -/

/-- The fiber product of two finite maps over their common quotient, written
intrinsically as a shared label together with one point from each fiber. -/
abbrev CompatiblePair {α β γ : Type*} (ρ : α → γ) (σ : β → γ) :=
  Σ u : γ, Fiber ρ u × Fiber σ u

/-- The usual unit-group fiber product over the common divisor. -/
abbrev UnitFiberProduct (m n : ℕ) [NeZero m] [NeZero n]
    [NeZero (Nat.gcd m n)] :=
  {x : UnitClass m × UnitClass n //
    unitReduction (Nat.gcd_dvd_left m n) x.1 =
      unitReduction (Nat.gcd_dvd_right m n) x.2}

/-- Regroup a compatible unit pair by its common residue. -/
def unitFiberProductToCompatiblePair
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (Nat.gcd m n)] :
    UnitFiberProduct m n →
      CompatiblePair
        (unitReduction (Nat.gcd_dvd_left m n))
        (unitReduction (Nat.gcd_dvd_right m n)) :=
  fun x =>
    ⟨unitReduction (Nat.gcd_dvd_left m n) x.1.1,
      ⟨⟨x.1.1, rfl⟩, ⟨x.1.2, x.2.symm⟩⟩⟩

/-- Forget the displayed common residue and retain the compatible pair. -/
def compatiblePairToUnitFiberProduct
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (Nat.gcd m n)] :
    CompatiblePair
        (unitReduction (Nat.gcd_dvd_left m n))
        (unitReduction (Nat.gcd_dvd_right m n)) →
      UnitFiberProduct m n :=
  fun z => ⟨⟨z.2.1.1, z.2.2.1⟩, z.2.1.2.trans z.2.2.2.symm⟩

/-- The subtype and displayed-fiber forms of the compatible unit pairs are
equivalent. -/
noncomputable def unitFiberProductCompatiblePairEquiv
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (Nat.gcd m n)] :
    UnitFiberProduct m n ≃
      CompatiblePair
        (unitReduction (Nat.gcd_dvd_left m n))
        (unitReduction (Nat.gcd_dvd_right m n)) where
  toFun := unitFiberProductToCompatiblePair
  invFun := compatiblePairToUnitFiberProduct
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv z := by
    rcases z with ⟨u, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩
    subst u
    rfl

/-- Reduction from units modulo the lcm lands in the exact compatible pair. -/
def lcmUnitToFiberProduct
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)] :
    UnitClass (Nat.lcm m n) → UnitFiberProduct m n :=
  fun A =>
    ⟨⟨unitReduction (Nat.dvd_lcm_left m n) A,
        unitReduction (Nat.dvd_lcm_right m n) A⟩, by
      calc
        unitReduction (Nat.gcd_dvd_left m n)
            (unitReduction (Nat.dvd_lcm_left m n) A) =
          unitReduction
            (dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)) A :=
              (unitReduction_comp _ _ A).symm
        _ = unitReduction
            (dvd_trans (Nat.gcd_dvd_right m n) (Nat.dvd_lcm_right m n)) A := by
              congr 1
        _ = unitReduction (Nat.gcd_dvd_right m n)
            (unitReduction (Nat.dvd_lcm_right m n) A) :=
              unitReduction_comp _ _ A⟩

theorem lcmUnitToFiberProduct_injective
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)] :
    Function.Injective (lcmUnitToFiberProduct (m := m) (n := n)) := by
  intro A B hAB
  have hmUnit : unitReduction (Nat.dvd_lcm_left m n) A =
      unitReduction (Nat.dvd_lcm_left m n) B :=
    congrArg (fun x => x.1.1) hAB
  have hnUnit : unitReduction (Nat.dvd_lcm_right m n) A =
      unitReduction (Nat.dvd_lcm_right m n) B :=
    congrArg (fun x => x.1.2) hAB
  have hm := (unitReduction_eq_iff_modEq
    (Nat.dvd_lcm_left m n) A
    (unitReduction (Nat.dvd_lcm_left m n) B)).1 hmUnit
  have hm' : A.val.val ≡ B.val.val [MOD m] := by
    exact hm.trans ((unitReduction_eq_iff_modEq
      (Nat.dvd_lcm_left m n) B
      (unitReduction (Nat.dvd_lcm_left m n) B)).1 rfl).symm
  have hn := (unitReduction_eq_iff_modEq
    (Nat.dvd_lcm_right m n) A
    (unitReduction (Nat.dvd_lcm_right m n) B)).1 hnUnit
  have hn' : A.val.val ≡ B.val.val [MOD n] := by
    exact hn.trans ((unitReduction_eq_iff_modEq
      (Nat.dvd_lcm_right m n) B
      (unitReduction (Nat.dvd_lcm_right m n) B)).1 rfl).symm
  have hself := (unitReduction_eq_iff_modEq
    (dvd_refl (Nat.lcm m n)) A B).2 (Nat.mod_lcm hm' hn')
  simpa [unitReduction] using hself

theorem lcmUnitToFiberProduct_surjective
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)] :
    Function.Surjective (lcmUnitToFiberProduct (m := m) (n := n)) := by
  rintro ⟨⟨a, b⟩, hab⟩
  have hcompat := (unitReduction_eq_iff_modEq
    (Nat.gcd_dvd_left m n) a
    (unitReduction (Nat.gcd_dvd_right m n) b)).1 hab
  have hbreduce := (unitReduction_eq_iff_modEq
    (Nat.gcd_dvd_right m n) b
    (unitReduction (Nat.gcd_dvd_right m n) b)).1 rfl
  have habmod : a.val.val ≡ b.val.val [MOD Nat.gcd m n] :=
    hcompat.trans hbreduce.symm
  let z := Nat.chineseRemainder' habmod
  have hzlt : z.1 < Nat.lcm m n :=
    Nat.chineseRemainder'_lt_lcm habmod (NeZero.ne m) (NeZero.ne n)
  have hzm : Nat.Coprime z.1 m := by
    rw [Nat.coprime_iff_gcd_eq_one, z.property.1.gcd_eq]
    exact (ZMod.val_coe_unit_coprime a).gcd_eq_one
  have hzn : Nat.Coprime z.1 n := by
    rw [Nat.coprime_iff_gcd_eq_one, z.property.2.gcd_eq]
    exact (ZMod.val_coe_unit_coprime b).gcd_eq_one
  have hzL : Nat.Coprime z.1 (Nat.lcm m n) := by
    apply Nat.Coprime.of_dvd_right
      (Nat.lcm_dvd (Nat.dvd_mul_right m n) (Nat.dvd_mul_left n m))
    exact hzm.mul_right hzn
  let A : UnitClass (Nat.lcm m n) := ZMod.unitOfCoprime z.1 hzL
  have hAval : A.val.val = z.1 := by
    exact ZMod.val_natCast_of_lt hzlt
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply (unitReduction_eq_iff_modEq (Nat.dvd_lcm_left m n) A a).2
    simpa [hAval] using z.property.1
  · apply (unitReduction_eq_iff_modEq (Nat.dvd_lcm_right m n) A b).2
    simpa [hAval] using z.property.2

/-- Generalized CRT identifies the actual lcm unit group with the compatible
unit-group fiber product. -/
noncomputable def lcmUnitFiberProductEquiv
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)] :
    UnitClass (Nat.lcm m n) ≃ UnitFiberProduct m n :=
  Equiv.ofBijective (lcmUnitToFiberProduct (m := m) (n := n))
    ⟨lcmUnitToFiberProduct_injective (m := m) (n := n),
      lcmUnitToFiberProduct_surjective (m := m) (n := n)⟩

/-- Generalized CRT in the displayed common-residue coordinates used by the
common-quotient identity. -/
noncomputable def lcmUnitCompatiblePairEquiv
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)] :
    UnitClass (Nat.lcm m n) ≃
      CompatiblePair
        (unitReduction (Nat.gcd_dvd_left m n))
        (unitReduction (Nat.gcd_dvd_right m n)) :=
  lcmUnitFiberProductEquiv.trans unitFiberProductCompatiblePairEquiv

/-- Exact cleared common-quotient identity.  Every cross term is a sum of
products of the two conditional fiber sums. -/
theorem compatiblePair_sum
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ]
    (ρ : α → γ) (σ : β → γ) (f : α → ℂ) (g : β → ℂ) :
    (∑ z : CompatiblePair ρ σ, f z.2.1 * star (g z.2.2)) =
      ∑ u : γ,
        (∑ a : Fiber ρ u, f a) * star (∑ b : Fiber σ u, g b) := by
  classical
  calc
    (∑ z : CompatiblePair ρ σ, f z.2.1 * star (g z.2.2)) =
      ∑ u : γ, ∑ z : Fiber ρ u × Fiber σ u,
          f z.1 * star (g z.2) := by rw [Fintype.sum_sigma]
    _ = ∑ u : γ,
        (∑ a : Fiber ρ u, f a) * star (∑ b : Fiber σ u, g b) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Fintype.sum_prod_type, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          change (∑ y : Fiber σ u, f a * star (g y)) =
            f a * star (∑ b : Fiber σ u, g b)
          have hmap : star (∑ b : Fiber σ u, g b) =
              ∑ b : Fiber σ u, star (g b) := by
            simp
          rw [hmap, Finset.mul_sum]

/-- Cardinality of a common-quotient fiber product with uniform fibers. -/
theorem compatiblePair_card
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ]
    (ρ : α → γ) (σ : β → γ) (r s : ℕ)
    (hρ : ∀ u, Fintype.card (Fiber ρ u) = r)
    (hσ : ∀ u, Fintype.card (Fiber σ u) = s) :
    Fintype.card (CompatiblePair ρ σ) = Fintype.card γ * r * s := by
  classical
  simp only [CompatiblePair, Fintype.card_sigma, Fintype.card_prod, hρ, hσ]
  simp [mul_assoc]

/-- Normalized common-quotient identity for surjections with uniform positive
fibers.  This is the exact conditional-average form of the manuscript's
shared-factor proposition. -/
theorem common_quotient_inner
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ] [Nonempty γ]
    (ρ : α → γ) (σ : β → γ) (f : α → ℂ) (g : β → ℂ)
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hρ : ∀ u, Fintype.card (Fiber ρ u) = r)
    (hσ : ∀ u, Fintype.card (Fiber σ u) = s) :
    (Fintype.card (CompatiblePair ρ σ) : ℂ)⁻¹ *
        ∑ z : CompatiblePair ρ σ, f z.2.1 * star (g z.2.2) =
      finiteInner (fun u => fiberMean ρ f u)
        (fun u => fiberMean σ g u) := by
  classical
  rw [compatiblePair_sum]
  unfold finiteInner fiberMean
  rw [compatiblePair_card ρ σ r s hρ hσ]
  simp_rw [hρ, hσ]
  have hγ : (Fintype.card γ : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Nat.cast_mul, star_mul, star_inv₀, star_natCast]
  let S : ℂ := ∑ u : γ,
    (∑ a : Fiber ρ u, f a) * star (∑ b : Fiber σ u, g b)
  have hsum :
      (∑ u : γ,
        ((r : ℂ)⁻¹ * ∑ a : Fiber ρ u, f a) *
          (star (∑ b : Fiber σ u, g b) * (s : ℂ)⁻¹)) =
        (r : ℂ)⁻¹ * (s : ℂ)⁻¹ * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hsum]
  dsimp [S]
  field_simp

end NField.Alignment.DoubleTransversality
