/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.DoubleTransversality
import NField.Alignment.FiniteFamilyCRT
import NField.Alignment.FiniteFamilyNorm
import NField.Alignment.CenteredPowerFibers

/-!
# The Double Transversality

## Coverage

Centered collision signals for coprime bases are orthogonal on the joint unit
group, with weighted energy and recovery formulas. For general bases, the
cross term is the inner product of conditional fiber means. The finite-family
results retain their finite scope; cutoff-uniform assignment control and
convergence below one remain open.

## Scope and assumptions

The orthogonality and independence results concern finite unit groups and
retain the coprimality or compatible-fiber conditions stated in each theorem.
The character decomposition of a weighted packet is finite and assumes no
infinite prime sum. Prime-cutoff rows, Pearson coefficients and observed
monotonicity are finite software evidence, not Lean interval or asymptotic
results. Cutoff-uniform assignment control and convergence below one remain
open.
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

/-- Every base-reduction fiber has the exact size used in the manuscript's mean. -/
theorem exact_reduction_fiber_card (b ell : ℕ) [NeZero b]
    [NeZero (allLagModulus b ell)] (u : UnitClass b) :
    Fintype.card (Fiber (coarseUnitReduction b ell) u) = b ^ ell :=
  NField.Alignment.CenteredPowerFibers.coarseUnitReduction_fiber_card b ell u

/-- The centered signal uses exactly the printed denominator `b^ell`. -/
theorem exact_centering_denominator (b ell : ℕ) [NeZero b]
    [NeZero (allLagModulus b ell)] (a : UnitClass (allLagModulus b ell)) :
    centeredCollisionTable b ell a = allLagUnitTable b ell a -
      (b ^ ell : ℂ)⁻¹ *
        ∑ t : Fiber (coarseUnitReduction b ell) (coarseUnitReduction b ell a),
          allLagUnitTable b ell t := by
  unfold centeredCollisionTable centeredSignal
  rw [NField.Alignment.CenteredPowerFibers.coarse_fiberMean]

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

section FiniteFamily

open NField.Alignment.FiniteFamilyTransversality NField.Alignment.FiniteFamilyCRT
open NField.Alignment.FiniteFamilyProbability
open NField.Alignment.FiniteFamilyNorm
open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b ell : ι → ℕ)
    [∀ i, NeZero (b i)] [∀ i, NeZero (allLagModulus (b i) (ell i))]
    [NeZero (∏ i, allLagModulus (b i) (ell i))]
    (hb : Pairwise fun i j => Nat.Coprime (b i) (b j))

/-- The finite CRT coordinates are reductions modulo the independently chosen power moduli. -/
noncomputable def familyUnitEquiv :
    UnitClass (∏ i, allLagModulus (b i) (ell i)) ≃*
      ∀ i, UnitClass (allLagModulus (b i) (ell i)) :=
  unitPiEquiv (fun i => allLagModulus (b i) (ell i))
    (fun _ _ hij => table_moduli_coprime (hb hij))

noncomputable def familyLift (i : ι)
    (a : UnitClass (∏ i, allLagModulus (b i) (ell i))) : ℂ :=
  centeredCollisionTable (b i) (ell i) (familyUnitEquiv b ell hb a i)

theorem finite_family_zero_mean (i : ι) : ∑ a, familyLift b ell hb i a = 0 :=
  crt_sum_zero _ _ (fun i => centeredCollisionTable (b i) (ell i))
    (fun _ => centered_collision_table_sum_zero) i

theorem finite_family_orthogonality {i j : ι} (hij : i ≠ j) :
    finiteInner (familyLift b ell hb i) (familyLift b ell hb j) = 0 :=
  crt_orthogonal _ _ (fun i => centeredCollisionTable (b i) (ell i))
    (fun _ => centered_collision_table_sum_zero) hij

theorem finite_family_energy_preserved (i : ι) :
    finiteEnergy (familyLift b ell hb i) = finiteEnergy (centeredCollisionTable (b i) (ell i)) :=
  crt_energy _ _ (fun i => centeredCollisionTable (b i) (ell i)) i

theorem finite_family_weighted_energy (w : ι → ℂ) :
    finiteEnergy (fun a => ∑ i, w i * familyLift b ell hb i a) =
      ∑ i, (w i * star (w i)) * finiteEnergy (centeredCollisionTable (b i) (ell i)) :=
  crt_weighted_energy _ _ (fun i => centeredCollisionTable (b i) (ell i))
    (fun _ => centered_collision_table_sum_zero) w

omit [∀ i, NeZero (b i)] [∀ i, NeZero (allLagModulus (b i) (ell i))]
  [NeZero (∏ i, allLagModulus (b i) (ell i))] in
theorem finite_family_character_factorization
    (χ : UnitClass (∏ i, allLagModulus (b i) (ell i)) →* ℂ) :
    ∃! ψ : ∀ i, UnitClass (allLagModulus (b i) (ell i)) →* ℂ,
      ∀ a, χ a = ∏ i, ψ i (familyUnitEquiv b ell hb a i) :=
  crt_character_factorization _ _ χ

theorem finite_family_coefficient (i : ι)
    (χ : ∀ i, UnitClass (allLagModulus (b i) (ell i)) →* ℂ) :
    finiteCoefficient (familyLift b ell hb i) (fun a => ∏ j, χ j (familyUnitEquiv b ell hb a j)) =
      finiteCoefficient (centeredCollisionTable (b i) (ell i)) (χ i) *
        ∏ j : {j // j ≠ i}, finiteMean (fun a => star (χ j a)) :=
  crt_coefficient _ _ (fun i => centeredCollisionTable (b i) (ell i)) i χ

theorem finite_family_disjoint_support {i j : ι} (hij : i ≠ j)
    (χ : ∀ i, UnitClass (allLagModulus (b i) (ell i)) →* ℂ) :
    finiteCoefficient (familyLift b ell hb i) (fun a => ∏ k, χ k (familyUnitEquiv b ell hb a k)) = 0 ∨
      finiteCoefficient (familyLift b ell hb j) (fun a => ∏ k, χ k (familyUnitEquiv b ell hb a k)) = 0 :=
  crt_disjoint_support _ _ (fun i => centeredCollisionTable (b i) (ell i))
    (fun _ => centered_collision_table_sum_zero) hij χ

omit [NeZero (∏ i, allLagModulus (b i) (ell i))] in
theorem finite_family_coordinate_recovery (w : ι → ℂ) (i : ι)
    (a : UnitClass (allLagModulus (b i) (ell i))) :
    finiteMean (fun y : ∀ j : {j // j ≠ i}, UnitClass (allLagModulus (b j) (ell j)) =>
      ∑ j, w j * familyLift b ell hb j ((familyUnitEquiv b ell hb).symm
        ((Equiv.piSplitAt i (fun j => UnitClass (allLagModulus (b j) (ell j)))).symm (a, y)))) =
      w i * centeredCollisionTable (b i) (ell i) a :=
  crt_recover_coordinate _ _ (fun i => centeredCollisionTable (b i) (ell i))
    (fun _ => centered_collision_table_sum_zero) w i a

/-- The printed equality of normalized real norms. -/
theorem finite_family_norm_preserved (i : ι) :
    finiteNorm (familyLift b ell hb i) = finiteNorm (centeredCollisionTable (b i) (ell i)) :=
  finiteNorm_of_energy_eq _ _ (finite_family_energy_preserved b ell hb i)

/-- The printed Pythagorean identity with real squared absolute values of arbitrary complex weights. -/
theorem finite_family_pythagorean (w : ι → ℂ) :
    finiteNorm (fun a => ∑ i, w i * familyLift b ell hb i a) ^ 2 =
      ∑ i, ‖w i‖ ^ 2 * finiteNorm (centeredCollisionTable (b i) (ell i)) ^ 2 := by
  rw [weighted_norm_square (familyLift b ell hb) w
    (fun _ _ hij => finite_family_orthogonality b ell hb hij)]
  simp only [finite_family_norm_preserved]

local instance unitMeasurableSpace (n : ℕ) : MeasurableSpace (UnitClass n) := ⊤
local instance unitMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (UnitClass n) :=
  ⟨fun _ => trivial⟩

omit [∀ i, NeZero (b i)] in
theorem finite_family_uniform_coordinates :
    (uniformMeasure (UnitClass (∏ i, allLagModulus (b i) (ell i)))).map
      (familyUnitEquiv b ell hb) =
        Measure.pi (fun i => uniformMeasure (UnitClass (allLagModulus (b i) (ell i)))) :=
  crt_uniform_coordinates _ _

theorem finite_family_independence :
    iIndepFun (familyLift b ell hb)
      (uniformMeasure (UnitClass (∏ i, allLagModulus (b i) (ell i)))) :=
  crt_independent_signals _ _ (fun i => centeredCollisionTable (b i) (ell i))

end FiniteFamily

#check finite_family_zero_mean
#check finite_family_orthogonality
#check finite_family_energy_preserved
#check finite_family_weighted_energy
#check finite_family_character_factorization
#check finite_family_coefficient
#check finite_family_disjoint_support
#check finite_family_coordinate_recovery
#check finite_family_uniform_coordinates
#check finite_family_independence
#check finite_family_norm_preserved
#check finite_family_pythagorean
#check centered_collision_table_sum_zero
#check exact_reduction_fiber_card
#check exact_centering_denominator
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
