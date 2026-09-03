/-
Author: Alexander S. Petty
-/

import NField.Alignment.DoubleTransversality

/-!
# The Double Transversality

Reader-facing theorem map for the Lean companion to
`papers/double_transversality.tex`.

## Checked here

* The exact all-lag collision table, its reflection law, coarse-fiber
  centering, centered oddness, even-character gate, and base-factored
  character gate are inherited and exported for this title.
* Every finite weighted packet has the exact character pairing used by the
  manuscript.  It is a finite identity and assumes no infinite prime sum.
* Centered collision tables have global sum zero.
* Powers of coprime bases remain coprime.  The actual unit-group Chinese
  remainder equivalence then makes two centered base signals exactly
  orthogonal on their complete joint unit group.
* Their normalized energies are preserved, arbitrary complex weights satisfy
  the exact two-coordinate Pythagorean identity, and averaging over the other
  coordinate recovers either weighted component.
* Product-character coefficients of a coordinate lift vanish off that
  coordinate axis whenever the other character factor has zero total.
* For two surjective finite reductions with uniform fibers, the normalized
  cross term is exactly the inner product of their conditional fiber means.
  This is specialized below to the actual unit group modulo `lcm(m,n)` through
  its exact generalized Chinese-remainder equivalence.

## Boundary

The fourteen higher-lag prime-cutoff rows, Pearson coefficients, five-cutoff
monotonicity table, and ten-base implementation audit are finite software
evidence and are not recomputed in Lean.  Independence of all coordinate
random variables and the arbitrary finite-family Fourier factorization are
not separately encoded; the companion proves the exact two-coordinate
orthogonality, support, energy, and recovery statements from which the finite
pairwise claims follow.  Cutoff-uniform assignment control and convergence
below one remain open.  No unchecked declaration is used.
-/

namespace NField.Papers.DoubleTransversality

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.GeneralNeutrality
open NField.Alignment.DoubleTransversality

/-- The manuscript's centered collision table on the intrinsic unit group. -/
noncomputable def centeredCollisionTable (b ell : ℕ)
    [NeZero b] [NeZero (allLagModulus b ell)] :
    UnitClass (allLagModulus b ell) → ℂ :=
  centeredSignal (coarseUnitReduction b ell) (allLagUnitTable b ell)

/-- Natural unit reduction commutes with negation. -/
theorem coarseUnitReduction_neg
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (a : UnitClass (allLagModulus b ell)) :
    coarseUnitReduction b ell (-a) = -coarseUnitReduction b ell a := by
  unfold coarseUnitReduction
  apply Units.ext
  rw [ZMod.unitsMap_val]
  change ((-(a : ZMod (allLagModulus b ell))).cast : ZMod b) =
    -((a : ZMod (allLagModulus b ell)).cast : ZMod b)
  exact ZMod.cast_neg
    (show b ∣ allLagModulus b ell by
      unfold allLagModulus
      exact dvd_pow_self b (by omega))
    (a : ZMod (allLagModulus b ell))

/-- Every centered collision table has exactly zero global sum. -/
theorem centered_collision_table_sum_zero
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)] :
    ∑ a, centeredCollisionTable b ell a = 0 :=
  centeredSignal_sum_zero (coarseUnitReduction b ell)
    (allLagUnitTable b ell) (coarseUnitReduction_surjective b ell)

/-- Exact raw reflection law for the table used in this title. -/
theorem exact_raw_reflection
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    allLagUnitTable b ell a + allLagUnitTable b ell (-a) = -1 :=
  allLagUnitTable_reflection hb2 hell a

/-- Fiber centering turns raw reflection into exact oddness. -/
theorem exact_centered_reflection
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTable b ell (-a) = -centeredCollisionTable b ell a := by
  exact centered_allLagUnitTable_odd hb2 hell
    (coarseUnitReduction b ell) (fun u : UnitClass b => -u)
    (fun _ => neg_neg _) coarseUnitReduction_neg
    (coarseUnitReduction_surjective b ell) a

/-- Every even Dirichlet-character channel is absent. -/
theorem even_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (χ : Character (allLagModulus b ell))
    (heven : χ (-1 : ZMod (allLagModulus b ell)) = 1) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  centered_allLag_even_character_zero hb2 hell
    (coarseUnitReduction b ell) (fun u : UnitClass b => -u)
    (fun _ => neg_neg _) coarseUnitReduction_neg
    (coarseUnitReduction_surjective b ell) χ heven

/-- Every character channel factored through reduction to the base is absent. -/
theorem base_factored_character_gate
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    (ψ : UnitClass b → ℂ) (χ : Character (allLagModulus b ell))
    (hfactor : ∀ a, χ a.val = ψ (coarseUnitReduction b ell a)) :
    collisionCoefficient (centeredCollisionTable b ell) χ = 0 :=
  centered_allLag_factored_character_zero
    (coarseUnitReduction b ell) (coarseUnitReduction_surjective b ell)
    ψ χ hfactor

/-- Exact finite character pairing for every declared finite packet. -/
theorem exact_finite_pairing
    {b ell : ℕ} [NeZero b] [NeZero (allLagModulus b ell)]
    {ι : Type*} [Fintype ι]
    (residue : ι → UnitClass (allLagModulus b ell))
    (weight : ι → ℂ) :
    ∑ i, centeredCollisionTable b ell (residue i) * weight i =
      ∑ χ : Character (allLagModulus b ell),
        collisionCoefficient (centeredCollisionTable b ell) χ *
          ∑ i, χ (residue i).val * weight i :=
  finite_prime_packet_decomposition
    (centeredCollisionTable b ell) residue weight

/-- The table moduli attached to coprime bases are coprime at arbitrary
independently chosen lags. -/
theorem table_moduli_coprime
    {b c ell k : ℕ} (hbc : Nat.Coprime b c) :
    Nat.Coprime (allLagModulus b ell) (allLagModulus c k) := by
  unfold allLagModulus
  exact Nat.Coprime.pow (ell + 1) (k + 1) hbc

/-- Exact cross-base orthogonality on the actual joint CRT unit group. -/
theorem coprime_base_orthogonality
    {b c ell k : ℕ} [NeZero b] [NeZero c]
    [NeZero (allLagModulus b ell)] [NeZero (allLagModulus c k)]
    (hbc : Nat.Coprime b c) :
    finiteInner
      (crtLeftLift (table_moduli_coprime hbc)
        (centeredCollisionTable b ell))
      (crtRightLift (table_moduli_coprime hbc)
        (centeredCollisionTable c k)) = 0 :=
  crt_lifts_orthogonal (table_moduli_coprime hbc)
    (centeredCollisionTable b ell) (centeredCollisionTable c k)
    centered_collision_table_sum_zero centered_collision_table_sum_zero

/-- Lifting a centered table to a coprime joint unit group preserves its
normalized energy. -/
theorem coprime_base_energy_preserved
    {b c ell k : ℕ} [NeZero b] [NeZero c]
    [NeZero (allLagModulus b ell)] [NeZero (allLagModulus c k)]
    (hbc : Nat.Coprime b c) :
    finiteEnergy
        (crtLeftLift
          (m := allLagModulus b ell) (n := allLagModulus c k)
          (table_moduli_coprime (ell := ell) (k := k) hbc)
          (centeredCollisionTable b ell)) =
      finiteEnergy (centeredCollisionTable b ell) :=
  crtLeftLift_energy
    (m := allLagModulus b ell) (n := allLagModulus c k)
    (table_moduli_coprime (ell := ell) (k := k) hbc)
    (centeredCollisionTable b ell)

/-- Exact weighted Pythagorean identity for two coprime base signals. -/
theorem coprime_base_weighted_energy
    {b c ell k : ℕ} [NeZero b] [NeZero c]
    [NeZero (allLagModulus b ell)] [NeZero (allLagModulus c k)]
    (hbc : Nat.Coprime b c) (w v : ℂ) :
    finiteEnergy (fun a : UnitClass
        (allLagModulus b ell * allLagModulus c k) =>
      w * crtLeftLift (table_moduli_coprime hbc)
          (centeredCollisionTable b ell) a +
        v * crtRightLift (table_moduli_coprime hbc)
          (centeredCollisionTable c k) a) =
      (w * star w) * finiteEnergy (centeredCollisionTable b ell) +
        (v * star v) * finiteEnergy (centeredCollisionTable c k) :=
  weighted_crt_energy (table_moduli_coprime hbc)
    (centeredCollisionTable b ell) (centeredCollisionTable c k)
    centered_collision_table_sum_zero centered_collision_table_sum_zero w v

/-- Averaging over the complete second CRT coordinate recovers the first
weighted centered table exactly. -/
theorem recover_coprime_base_coordinate
    {b c ell k : ℕ} [NeZero b] [NeZero c]
    [NeZero (allLagModulus b ell)] [NeZero (allLagModulus c k)]
    (w v : ℂ) (x : UnitClass (allLagModulus b ell)) :
    (Fintype.card (UnitClass (allLagModulus c k)) : ℂ)⁻¹ *
        ∑ y : UnitClass (allLagModulus c k),
          (w * centeredCollisionTable b ell x +
            v * centeredCollisionTable c k y) =
      w * centeredCollisionTable b ell x :=
  recover_left_coordinate (centeredCollisionTable b ell)
    (centeredCollisionTable c k) centered_collision_table_sum_zero w v x

/-- A lifted left signal has no product-character component away from its
coordinate axis. -/
theorem left_coordinate_support
    {α β : Type*} [Fintype α] [Fintype β]
    (f χ : α → ℂ) (ψ : β → ℂ) (hψ : ∑ y, ψ y = 0) :
    finiteCoefficient (leftLift (β := β) f)
      (fun x : α × β => χ x.1 * ψ x.2) = 0 :=
  leftLift_product_channel_zero f χ ψ hψ

/-- The normalized cross term for natural unit reductions passes exactly
through their common quotient. -/
theorem unit_reduction_common_quotient
    {d m n : ℕ} [NeZero d] [NeZero m] [NeZero n]
    (hdm : d ∣ m) (hdn : d ∣ n)
    (f : UnitClass m → ℂ) (g : UnitClass n → ℂ) :
    (Fintype.card
        (CompatiblePair (unitReduction hdm) (unitReduction hdn)) : ℂ)⁻¹ *
      ∑ z : CompatiblePair (unitReduction hdm) (unitReduction hdn),
        f z.2.1 * star (g z.2.2) =
      finiteInner
        (fun u => fiberMean (unitReduction hdm) f u)
        (fun u => fiberMean (unitReduction hdn) g u) := by
  have hr : 0 < m.totient / d.totient := by
    obtain ⟨a, ha⟩ := unitReduction_surjective hdm (1 : UnitClass d)
    have hpos : 0 < Fintype.card
        (Fiber (unitReduction hdm) (1 : UnitClass d)) :=
      Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
    simpa [unitReduction_fiber_card hdm] using hpos
  have hs : 0 < n.totient / d.totient := by
    obtain ⟨a, ha⟩ := unitReduction_surjective hdn (1 : UnitClass d)
    have hpos : 0 < Fintype.card
        (Fiber (unitReduction hdn) (1 : UnitClass d)) :=
      Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
    simpa [unitReduction_fiber_card hdn] using hpos
  exact common_quotient_inner (unitReduction hdm) (unitReduction hdn) f g
    (m.totient / d.totient) (n.totient / d.totient) hr hs
    (unitReduction_fiber_card hdm) (unitReduction_fiber_card hdn)

/-- The manuscript's common-quotient formula on the actual unit group modulo
`lcm(m,n)`. -/
theorem lcm_unit_reduction_common_quotient
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)]
    (f : UnitClass m → ℂ) (g : UnitClass n → ℂ) :
    finiteInner
        (fun A : UnitClass (Nat.lcm m n) =>
          f (unitReduction (Nat.dvd_lcm_left m n) A))
        (fun A : UnitClass (Nat.lcm m n) =>
          g (unitReduction (Nat.dvd_lcm_right m n) A)) =
      finiteInner
        (fun u => fiberMean (unitReduction (Nat.gcd_dvd_left m n)) f u)
        (fun u => fiberMean (unitReduction (Nat.gcd_dvd_right m n)) g u) := by
  let e := lcmUnitCompatiblePairEquiv (m := m) (n := n)
  calc
    finiteInner
        (fun A : UnitClass (Nat.lcm m n) =>
          f (unitReduction (Nat.dvd_lcm_left m n) A))
        (fun A : UnitClass (Nat.lcm m n) =>
          g (unitReduction (Nat.dvd_lcm_right m n) A)) =
      finiteInner
        (fun z : CompatiblePair
            (unitReduction (Nat.gcd_dvd_left m n))
            (unitReduction (Nat.gcd_dvd_right m n)) => f z.2.1)
        (fun z : CompatiblePair
            (unitReduction (Nat.gcd_dvd_left m n))
            (unitReduction (Nat.gcd_dvd_right m n)) => g z.2.2) := by
              simpa [e, lcmUnitCompatiblePairEquiv,
                lcmUnitFiberProductEquiv, unitFiberProductCompatiblePairEquiv,
                unitFiberProductToCompatiblePair, lcmUnitToFiberProduct] using
                finiteInner_equiv e
                  (fun z : CompatiblePair
                    (unitReduction (Nat.gcd_dvd_left m n))
                    (unitReduction (Nat.gcd_dvd_right m n)) => f z.2.1)
                  (fun z : CompatiblePair
                    (unitReduction (Nat.gcd_dvd_left m n))
                    (unitReduction (Nat.gcd_dvd_right m n)) => g z.2.2)
    _ = _ := by
      simpa [finiteInner] using
        unit_reduction_common_quotient
          (Nat.gcd_dvd_left m n) (Nat.gcd_dvd_right m n) f g

/-- A zero conditional mean on the left removes the complete lcm-level cross
term. -/
theorem lcm_common_quotient_orthogonal_of_left
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)]
    (f : UnitClass m → ℂ) (g : UnitClass n → ℂ)
    (hzero : ∀ u,
      fiberMean (unitReduction (Nat.gcd_dvd_left m n)) f u = 0) :
    finiteInner
        (fun A : UnitClass (Nat.lcm m n) =>
          f (unitReduction (Nat.dvd_lcm_left m n) A))
        (fun A : UnitClass (Nat.lcm m n) =>
          g (unitReduction (Nat.dvd_lcm_right m n) A)) = 0 := by
  rw [lcm_unit_reduction_common_quotient]
  unfold finiteInner
  simp [hzero]

/-- A zero conditional mean on the right removes the complete lcm-level cross
term. -/
theorem lcm_common_quotient_orthogonal_of_right
    {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (Nat.lcm m n)] [NeZero (Nat.gcd m n)]
    (f : UnitClass m → ℂ) (g : UnitClass n → ℂ)
    (hzero : ∀ u,
      fiberMean (unitReduction (Nat.gcd_dvd_right m n)) g u = 0) :
    finiteInner
        (fun A : UnitClass (Nat.lcm m n) =>
          f (unitReduction (Nat.dvd_lcm_left m n) A))
        (fun A : UnitClass (Nat.lcm m n) =>
          g (unitReduction (Nat.dvd_lcm_right m n) A)) = 0 := by
  rw [lcm_unit_reduction_common_quotient]
  unfold finiteInner
  simp [hzero]

#check centered_collision_table_sum_zero
#check exact_raw_reflection
#check exact_centered_reflection
#check even_character_gate
#check base_factored_character_gate
#check exact_finite_pairing
#check table_moduli_coprime
#check coprime_base_orthogonality
#check coprime_base_energy_preserved
#check coprime_base_weighted_energy
#check recover_coprime_base_coordinate
#check left_coordinate_support
#check unit_reduction_common_quotient
#check lcm_unit_reduction_common_quotient
#check lcm_common_quotient_orthogonal_of_left
#check lcm_common_quotient_orthogonal_of_right

end NField.Papers.DoubleTransversality
