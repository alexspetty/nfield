/-
Author: Alexander S. Petty
-/

import NField.Alignment.EndpointReservoirAlias
import NField.Alignment.LiveCarrierDamping
import NField.Alignment.DedekindInverseResidueTransform

/-!
# Endpoint reciprocity bridge

The endpoint jump coordinate and the lower-modulus Rademacher coordinate are
two finite presentations of the same rational mass.  This module proves that
identification by reducing every point of the finite coefficient triangle to
lowest terms.  It also identifies the elementary Rademacher correction with
the Bernoulli-curvature correction.  No Fourier or Abel identity is assumed.
-/

namespace NField.Alignment.EndpointReciprocityBridge

open scoped BigOperators ZMod
open NField.Alignment.BernoulliCurvature
open NField.Alignment.CarrierJumpData
open NField.Alignment.CarrierStateSwitching
open NField.Alignment.CollisionBernoulliStraightening
open NField.Alignment.ComplementaryPartition
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.DedekindReciprocity
open NField.Alignment.EndpointReservoirAlias
open NField.Alignment.ExactSamplingReservoirBridge
open NField.Alignment.LiveCarrierDamping
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareReducedRatio
open NField.Alignment.RademacherThreeTerm
open NField.Alignment.SecondaryCapacityLedger

/-- A unit in the first coefficient converts a symmetric coefficient term to
the ordinary one-coefficient Dedekind sum.  The second coefficient need not be
a unit. -/
theorem arithmeticCoefficientDedekindTerm_unit_left
    {c y m : ℕ} (hm : 0 < m) (hcm : c.Coprime m) :
    arithmeticCoefficientDedekindTerm c y m =
      arithmeticDedekindSum
        ((ZMod.unitOfCoprime c hcm)⁻¹.val.val * y) m := by
  letI : NeZero m := ⟨hm.ne'⟩
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime c hcm
  let e : Fin m ≃ Fin m := (coprimeResidueEquiv hcm).symm
  unfold arithmeticCoefficientDedekindTerm arithmeticDedekindSum
  rw [← Fin.sum_univ_eq_sum_range
      (fun t : ℕ ↦ rationalSawtooth (c * t) m * rationalSawtooth (y * t) m) m,
    ← Fin.sum_univ_eq_sum_range
      (fun t : ℕ ↦ rationalSawtooth t m *
        rationalSawtooth (((u⁻¹.val.val * y) * t)) m) m]
  have hreindex := e.sum_comp (fun t : Fin m ↦
    rationalSawtooth (c * t.val) m * rationalSawtooth (y * t.val) m)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro t _ht
  have hforward : (c * (e t).val) % m = t.val := by
    calc
      (c * (e t).val) % m =
          ((coprimeResidueEquiv hcm) (e t)).val := by
            symm
            exact coprimeResidueEquiv_val hcm (e t)
      _ = t.val := by
            exact congrArg Fin.val
              ((coprimeResidueEquiv hcm).apply_symm_apply t)
  have heval : (e t).val = (u⁻¹.val.val * t.val) % m := by
    have hleft : ((e t).val : ZMod m) =
        u⁻¹.val * (t.val : ZMod m) := by
      calc
        ((e t).val : ZMod m) =
            u⁻¹.val * (u.val * ((e t).val : ZMod m)) := by
              rw [← mul_assoc, ← Units.val_mul]
              simp
        _ = u⁻¹.val * (t.val : ZMod m) := by
              congr 1
              apply ZMod.val_injective m
              simpa [u, ZMod.coe_unitOfCoprime, ZMod.val_mul,
                ZMod.val_natCast, Nat.mod_eq_of_lt (e t).isLt,
                Nat.mod_eq_of_lt t.isLt] using hforward
    have hv := congrArg ZMod.val hleft
    simpa [ZMod.val_mul, ZMod.val_natCast,
      Nat.mod_eq_of_lt (e t).isLt,
      Nat.mod_eq_of_lt t.isLt] using hv
  rw [show rationalSawtooth (c * (e t).val) m =
      rationalSawtooth t.val m by
    apply rationalSawtooth_eq_of_mod_eq
    rw [hforward, Nat.mod_eq_of_lt t.isLt]]
  rw [show rationalSawtooth (y * (e t).val) m =
      rationalSawtooth (((u⁻¹.val.val * y) * t.val)) m by
    apply rationalSawtooth_eq_of_mod_eq
    have hemod : (e t).val ≡ u⁻¹.val.val * t.val [MOD m] := by
      change (e t).val % m = (u⁻¹.val.val * t.val) % m
      rw [Nat.mod_eq_of_lt (e t).isLt, heval]
    simpa only [Nat.ModEq, mul_assoc, mul_left_comm, mul_comm] using
      hemod.mul_left y]

/-- The inverse of a unit modulo a multiple reduces to the inverse of the
same unit modulo the divisor. -/
theorem inverseUnitVal_mod_divisor
    {c d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hcm : c.Coprime (d * k)) :
    (ZMod.unitOfCoprime c hcm)⁻¹.val.val % k =
    (ZMod.unitOfCoprime c (hcm.of_dvd_right (dvd_mul_left k d)))⁻¹.val.val := by
  letI : NeZero k := ⟨hk.ne'⟩
  letI : NeZero (d * k) := ⟨(Nat.mul_pos hd hk).ne'⟩
  let ubig : (ZMod (d * k))ˣ := ZMod.unitOfCoprime c hcm
  let hck : c.Coprime k := hcm.of_dvd_right (dvd_mul_left k d)
  let usmall : (ZMod k)ˣ := ZMod.unitOfCoprime c hck
  have hbigInv : ((c : ZMod k) * (ubig⁻¹.val.val : ZMod k)) = 1 := by
    have hz : ((c : ZMod (d * k)) * ubig⁻¹.val) = 1 := by
      change ubig.val * ubig⁻¹.val = 1
      simp
    have hsmall := congrArg
      (ZMod.castHom (dvd_mul_left k d) (ZMod k)) hz
    simp only [map_mul, map_one, ZMod.castHom_apply] at hsmall
    rw [show (ZMod.cast (c : ZMod (d * k)) : ZMod k) = c by
      exact ZMod.cast_natCast (dvd_mul_left k d) c] at hsmall
    rw [show (ZMod.cast ubig⁻¹.val : ZMod k) = ubig⁻¹.val.val by
      exact ZMod.cast_eq_val ubig⁻¹.val] at hsmall
    exact hsmall
  have heq : (ubig⁻¹.val.val : ZMod k) = usmall⁻¹.val := by
    calc
      (ubig⁻¹.val.val : ZMod k) =
          1 * (ubig⁻¹.val.val : ZMod k) := by rw [one_mul]
      _ = (usmall⁻¹.val * usmall.val) *
          (ubig⁻¹.val.val : ZMod k) := by simp
      _ = usmall⁻¹.val *
          (usmall.val * (ubig⁻¹.val.val : ZMod k)) := by ring
      _ = usmall⁻¹.val := by
        rw [show usmall.val = (c : ZMod k) by
          simp [usmall, ZMod.coe_unitOfCoprime], hbigInv, mul_one]
  have hval := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast] using hval

/-- Scaling the second coefficient and the modulus by the same positive
factor leaves the coefficient term unchanged when the first coefficient is a
unit on the large modulus. -/
theorem arithmeticCoefficientDedekindTerm_scale_second
    {c d X k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hcm : c.Coprime (d * k)) :
    arithmeticCoefficientDedekindTerm c (d * X) (d * k) =
      arithmeticCoefficientDedekindTerm c X k := by
  letI : NeZero k := ⟨hk.ne'⟩
  let u := (ZMod.unitOfCoprime c hcm)⁻¹.val.val
  let hck : c.Coprime k := hcm.of_dvd_right (dvd_mul_left k d)
  let v := (ZMod.unitOfCoprime c hck)⁻¹.val.val
  rw [arithmeticCoefficientDedekindTerm_unit_left (Nat.mul_pos hd hk) hcm]
  rw [show u * (d * X) = d * (u * X) by ring]
  rw [arithmeticDedekindSum_scale hd hk]
  rw [arithmeticCoefficientDedekindTerm_unit_left hk hck]
  apply Finset.sum_congr rfl
  intro t _ht
  congr 1
  apply rationalSawtooth_eq_of_mod_eq
  have huv : u % k = v := by
    exact inverseUnitVal_mod_divisor hd hk hcm
  have huvEq : u ≡ v [MOD k] := by
    change u % k = v % k
    rw [huv]
    exact (Nat.mod_eq_of_lt
      (ZMod.unitOfCoprime c hck)⁻¹.val.val_lt).symm
  exact (huvEq.mul_right X).mul_right t

/-- The primitive part of a coefficient correlation at denominator `k`. -/
noncomputable def primitiveCoefficientCorrelation (c y k : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range k).filter fun a ↦ a.Coprime k,
    rationalSawtooth (c * a) k * rationalSawtooth (y * a) k

/-- Reducing one grid point to lowest terms preserves both sawtooth factors. -/
theorem coefficientCorrelation_reduceGridPoint
    {c y m t : ℕ} (hm : 0 < m) (_ht : t ∈ Finset.range m) :
    rationalSawtooth (c * t) m * rationalSawtooth (y * t) m =
      rationalSawtooth (c * (reduceGridPoint m t).2)
          (reduceGridPoint m t).1 *
        rationalSawtooth (y * (reduceGridPoint m t).2)
          (reduceGridPoint m t).1 := by
  let g := t.gcd m
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right t hm
  have hgt : g ∣ t := Nat.gcd_dvd_left t m
  have hgm : g ∣ m := Nat.gcd_dvd_right t m
  have ht : g * (t / g) = t := Nat.mul_div_cancel' hgt
  have hmm : g * (m / g) = m := Nat.mul_div_cancel' hgm
  unfold reduceGridPoint
  dsimp only
  change rationalSawtooth (c * t) m * rationalSawtooth (y * t) m =
    rationalSawtooth (c * (t / g)) (m / g) *
      rationalSawtooth (y * (t / g)) (m / g)
  calc
    rationalSawtooth (c * t) m * rationalSawtooth (y * t) m =
        rationalSawtooth (c * (g * (t / g))) (g * (m / g)) *
          rationalSawtooth (y * (g * (t / g))) (g * (m / g)) := by
            rw [ht, hmm]
    _ = _ := by
      rw [show c * (g * (t / g)) = g * (c * (t / g)) by ring,
        show y * (g * (t / g)) = g * (y * (t / g)) by ring,
        rationalSawtooth_scale hgpos (Nat.div_pos
          (Nat.le_of_dvd hm hgm) hgpos),
        rationalSawtooth_scale hgpos (Nat.div_pos
          (Nat.le_of_dvd hm hgm) hgpos)]

/-- Every coefficient correlation is the disjoint sum of its primitive
denominator correlations. -/
theorem arithmeticCoefficientDedekindTerm_eq_primitiveDivisorSum
    {c y m : ℕ} (hm : 0 < m) :
    arithmeticCoefficientDedekindTerm c y m =
      ∑ k ∈ m.divisors, primitiveCoefficientCorrelation c y k := by
  unfold arithmeticCoefficientDedekindTerm
  calc
    (∑ t ∈ Finset.range m,
        rationalSawtooth (c * t) m * rationalSawtooth (y * t) m) =
        ∑ ka ∈ reducedFractionPairs m,
          rationalSawtooth (c * ka.2) ka.1 *
            rationalSawtooth (y * ka.2) ka.1 := by
              apply Finset.sum_bij (fun t _ ↦ reduceGridPoint m t)
              · exact fun t ht ↦ reduceGridPoint_mem hm ht
              · intro t ht u hu
                exact reduceGridPoint_injective hm ht hu
              · exact reduceGridPoint_surjective hm
              · intro t ht
                exact coefficientCorrelation_reduceGridPoint hm ht
    _ = _ := by
      unfold reducedFractionPairs primitiveCoefficientCorrelation
      rw [Finset.sum_filter]
      rw [show
        (∑ ka ∈ m.divisors.product (Finset.range m),
          if ka.2 < ka.1 ∧ ka.2.Coprime ka.1 then
            rationalSawtooth (c * ka.2) ka.1 *
              rationalSawtooth (y * ka.2) ka.1 else 0) =
          ∑ k ∈ m.divisors, ∑ a ∈ Finset.range m,
            if a < k ∧ a.Coprime k then
              rationalSawtooth (c * a) k *
                rationalSawtooth (y * a) k else 0 by
                  exact Finset.sum_product _ _ _]
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ∣ m := (Nat.mem_divisors.mp hk).1
      have hkle : k ≤ m := Nat.le_of_dvd hm hkm
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext a
        simp
        omega
      · intro a _ha
        rfl

/-- The literal strict upper triangle of coefficient correlations on the
positive window `1, ..., p - 1`. -/
noncomputable def coefficientCorrelationUpperTriangle (c p : ℕ) : ℚ :=
  ∑ ij ∈ upperIndexPairs p,
    arithmeticCoefficientDedekindTerm c
      (firstWindowNat ij.2) (firstWindowNat ij.1)

/-- Dividing each increasing pair by its gcd carries the coefficient
correlation to the corresponding primitive denominator. -/
theorem coefficientCorrelationUpperTriangle_eq_scaledReducedRatios
    {c p : ℕ} (hp2 : 2 ≤ p)
    (hunit : ∀ n, 0 < n → n < p → c.Coprime n) :
    coefficientCorrelationUpperTriangle c p =
      ∑ r ∈ scaledReducedRatios p,
        arithmeticCoefficientDedekindTerm c r.1 r.2.1 := by
  classical
  unfold coefficientCorrelationUpperTriangle
  apply Finset.sum_bij (fun ij _ ↦ reducedTripleOfPair ij)
  · exact reducedTripleOfPair_mem hp2
  · intro ij hij uv huv
    exact reducedTripleOfPair_injective_on hp2 hij huv
  · exact reducedTripleOfPair_surjective_on hp2
  · intro ij hij
    have hlt : ij.1 < ij.2 := by simpa [upperIndexPairs] using hij
    let x := firstWindowNat ij.1
    let y := firstWindowNat ij.2
    let g := x.gcd y
    have hxpos : 0 < x := firstWindowNat_pos ij.1
    have hypos : 0 < y := firstWindowNat_pos ij.2
    have hxlt : x < p := firstWindowNat_lt hp2 ij.1
    have hylt : y < p := firstWindowNat_lt hp2 ij.2
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left y hxpos
    have hgx : g ∣ x := Nat.gcd_dvd_left x y
    have hgy : g ∣ y := Nat.gcd_dvd_right x y
    have hkpos : 0 < x / g :=
      Nat.div_pos (Nat.gcd_le_left y hxpos) hgpos
    have hcm : c.Coprime (g * (x / g)) := by
      rw [Nat.mul_div_cancel' hgx]
      exact hunit x hxpos hxlt
    unfold reducedTripleOfPair
    change arithmeticCoefficientDedekindTerm c y x =
      arithmeticCoefficientDedekindTerm c (y / g) (x / g)
    calc
      arithmeticCoefficientDedekindTerm c y x =
          arithmeticCoefficientDedekindTerm c
            (g * (y / g)) (g * (x / g)) := by
              rw [Nat.mul_div_cancel' hgy, Nat.mul_div_cancel' hgx]
      _ = _ := arithmeticCoefficientDedekindTerm_scale_second
        hgpos hkpos hcm

/-- Summing the scale coordinate gives the floor multiplicity attached to
each primitive ratio. -/
theorem scaledReducedRatios_coefficient_sum_eq_floor
    {c p : ℕ} :
    (∑ r ∈ scaledReducedRatios p,
        arithmeticCoefficientDedekindTerm c r.1 r.2.1) =
      ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℚ) *
          arithmeticCoefficientDedekindTerm c ak.1 ak.2 := by
  classical
  let K := fun a k : ℕ ↦ arithmeticCoefficientDedekindTerm c a k
  have hinner (a k : ℕ) :
      (∑ t ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p then K a k else 0) =
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℚ) * K a k else 0 := by
    by_cases hpair : 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a
    · rw [if_pos hpair]
      have hpred (t : ℕ) :
          (0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p) ↔ (0 < t ∧ t * a < p) := by
        tauto
      simp_rw [hpred]
      rw [← Finset.sum_filter]
      change (∑ _t ∈ admissibleScales p a, K a k) = _
      simp [admissibleScales_card hpair.1]
    · rw [if_neg hpair]
      apply Finset.sum_eq_zero
      intro t _ht
      rw [if_neg]
      intro h
      exact hpair ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  calc
    (∑ r ∈ scaledReducedRatios p,
        arithmeticCoefficientDedekindTerm c r.1 r.2.1) =
      ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        ∑ t ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p then K a k else 0 := by
        unfold scaledReducedRatios K
        rw [Finset.sum_filter]
        calc
          _ = ∑ a ∈ Finset.range p,
              ∑ kt ∈ (Finset.range p).product (Finset.range p),
                if 0 < a ∧ 0 < kt.1 ∧ kt.1 < a ∧ kt.1.Coprime a ∧
                    0 < kt.2 ∧ kt.2 * a < p then
                  arithmeticCoefficientDedekindTerm c a kt.1 else 0 :=
              Finset.sum_product _ _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro a _ha
            exact Finset.sum_product _ _ _
    _ = ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℚ) * K a k else 0 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro k _hk
            exact hinner a k
    _ = ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℚ) * K ak.1 ak.2 := by
          unfold reducedRatioPairs
          rw [Finset.sum_filter]
          exact (Finset.sum_product (Finset.range p) (Finset.range p)
            (fun ak : ℕ × ℕ ↦
              if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧
                  ak.2.Coprime ak.1 then
                (((p - 1) / ak.1 : ℕ) : ℚ) * K ak.1 ak.2
              else 0)).symm
    _ = _ := rfl

/-- The primitive-ratio floor sum is exactly the full carrier weighted pair
sum; the omitted denominator-one boundary contributes zero. -/
theorem reducedRatioCoefficientFloorSum_eq_fullCarrierWeightedPairSum
    {p : ℕ} (hp2 : 2 ≤ p) :
    (∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℚ) *
          arithmeticCoefficientDedekindTerm (p ^ 2) ak.1 ak.2) =
      fullCarrierWeightedPairSum p := by
  classical
  unfold reducedRatioPairs fullCarrierWeightedPairSum fullCarrierSet
  rw [Finset.sum_filter]
  have hproduct :
      (∑ ak ∈ (Finset.range p).product (Finset.range p),
        if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧ ak.2.Coprime ak.1 then
          (((p - 1) / ak.1 : ℕ) : ℚ) *
            arithmeticCoefficientDedekindTerm (p ^ 2) ak.1 ak.2
        else 0) =
      ∑ X ∈ Finset.range p, ∑ k ∈ Finset.range p,
        if 0 < X ∧ 0 < k ∧ k < X ∧ k.Coprime X then
          (((p - 1) / X : ℕ) : ℚ) *
            arithmeticCoefficientDedekindTerm (p ^ 2) X k
        else 0 := Finset.sum_product _ _ _
  rw [hproduct]
  rw [show Finset.Icc 3 (p - 1) =
      (Finset.range p).filter fun X ↦ 3 ≤ X by
    ext X
    simp
    omega]
  rw [Finset.sum_filter]
  rw [show Finset.Icc 2 (p - 2) =
      (Finset.range p).filter fun k ↦ 2 ≤ k ∧ k < p - 1 by
    ext k
    simp
    omega]
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro X hX
  have hXp : X < p := Finset.mem_range.mp hX
  have hXN : X ≤ p - 1 := by omega
  by_cases hX3 : 3 ≤ X
  · rw [if_pos hX3, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hpair : 0 < X ∧ 0 < k ∧ k < X ∧ k.Coprime X
    · by_cases hk2 : 2 ≤ k
      · have hkp : k < p - 1 := by
          omega
        simp [hpair, hk2, hkp]
      · have hk1 : k = 1 := by omega
        subst k
        simp [arithmeticCoefficientDedekindTerm, rationalSawtooth]
    · by_cases hk2 : 2 ≤ k
      · have hcarrier : ¬(2 ≤ k ∧ k < X ∧ k.Coprime X) := by
          intro h
          exact hpair ⟨by omega, by omega, h.2.1, h.2.2⟩
        rw [if_neg hpair]
        simp [hcarrier]
      · simp [hpair, hk2]
  · rw [if_neg hX3]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hpair : 0 < X ∧ 0 < k ∧ k < X ∧ k.Coprime X
    · have hk1 : k = 1 := by omega
      subst k
      simp [arithmeticCoefficientDedekindTerm, rationalSawtooth]
    · simp [hpair]

/-- The literal coefficient upper triangle is the carrier weighted pair sum. -/
theorem coefficientCorrelationUpperTriangle_eq_fullCarrierWeightedPairSum
    {p : ℕ} (hp : p.Prime) :
    coefficientCorrelationUpperTriangle (p ^ 2) p =
      fullCarrierWeightedPairSum p := by
  rw [coefficientCorrelationUpperTriangle_eq_scaledReducedRatios hp.two_le
      (fun n hn hnp ↦
        (smallNatUnit_coprime hp hn hnp).symm),
    scaledReducedRatios_coefficient_sum_eq_floor,
    reducedRatioCoefficientFloorSum_eq_fullCarrierWeightedPairSum hp.two_le]

/-- Strictly increasing pairs in the literal positive window. -/
def naturalUpperPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun ij ↦ ij.1 < ij.2

/-- The finite-index and natural-coordinate presentations of the upper
triangle agree. -/
theorem coefficientCorrelationUpperTriangle_eq_naturalUpperPairs
    {c p : ℕ} (hp2 : 2 ≤ p) :
    coefficientCorrelationUpperTriangle c p =
      ∑ ij ∈ naturalUpperPairs (p - 1),
        arithmeticCoefficientDedekindTerm c ij.2 ij.1 := by
  classical
  unfold coefficientCorrelationUpperTriangle
  apply Finset.sum_bij
    (fun ij _ ↦ (firstWindowNat ij.1, firstWindowNat ij.2))
  · intro ij hij
    have hlt : ij.1 < ij.2 := by simpa [upperIndexPairs] using hij
    have hfirst : firstWindowNat ij.1 ∈ Finset.Icc 1 (p - 1) := by
      exact Finset.mem_Icc.mpr
        ⟨firstWindowNat_pos ij.1, by
          have h := firstWindowNat_lt hp2 ij.1
          omega⟩
    have hsecond : firstWindowNat ij.2 ∈ Finset.Icc 1 (p - 1) := by
      exact Finset.mem_Icc.mpr
        ⟨firstWindowNat_pos ij.2, by
          have h := firstWindowNat_lt hp2 ij.2
          omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hfirst, hsecond⟩, by
        dsimp [firstWindowNat]
        exact Nat.add_lt_add_right hlt 1⟩
  · intro ij hij uv huv heq
    apply Prod.ext
    · apply Fin.ext
      have h := congrArg Prod.fst heq
      dsimp [firstWindowNat] at h
      omega
    · apply Fin.ext
      have h := congrArg Prod.snd heq
      dsimp [firstWindowNat] at h
      omega
  · intro xy hxy
    have hdata := Finset.mem_filter.mp hxy
    have hx := Finset.mem_Icc.mp (Finset.mem_product.mp hdata.1).1
    have hy := Finset.mem_Icc.mp (Finset.mem_product.mp hdata.1).2
    let i : FirstWindowIndex p := ⟨xy.1 - 1, by omega⟩
    let j : FirstWindowIndex p := ⟨xy.2 - 1, by omega⟩
    have hilt : i < j := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hij : (i, j) ∈ upperIndexPairs p := by
      simp [upperIndexPairs, hilt]
    refine ⟨(i, j), hij, ?_⟩
    apply Prod.ext <;> dsimp [i, j, firstWindowNat] <;> omega
  · intro ij _hij
    rfl

/-- The literal natural upper triangle, grouped by its larger coordinate. -/
theorem naturalUpperPairs_sum_eq_rows (c N : ℕ) :
    (∑ ij ∈ naturalUpperPairs N,
        arithmeticCoefficientDedekindTerm c ij.2 ij.1) =
      ∑ y ∈ Finset.Icc 2 N, ∑ x ∈ Finset.Ico 1 y,
        arithmeticCoefficientDedekindTerm c y x := by
  classical
  unfold naturalUpperPairs
  rw [Finset.sum_filter]
  have hproduct :
      (∑ ij ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        if ij.1 < ij.2 then
          arithmeticCoefficientDedekindTerm c ij.2 ij.1 else 0) =
      ∑ x ∈ Finset.Icc 1 N, ∑ y ∈ Finset.Icc 1 N,
        if x < y then arithmeticCoefficientDedekindTerm c y x else 0 :=
    Finset.sum_product _ _ _
  rw [hproduct, Finset.sum_comm]
  have hrow (y : ℕ) (hy : y ∈ Finset.Icc 1 N) :
      (∑ x ∈ Finset.Icc 1 N,
          if x < y then arithmeticCoefficientDedekindTerm c y x else 0) =
        if y ∈ Finset.Icc 2 N then
          ∑ x ∈ Finset.Ico 1 y,
            arithmeticCoefficientDedekindTerm c y x
        else 0 := by
    by_cases hy2 : y ∈ Finset.Icc 2 N
    · rw [if_pos hy2, ← Finset.sum_filter]
      have hyN := (Finset.mem_Icc.mp hy2).2
      apply Finset.sum_congr
      · ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
        omega
      · intro x _hx
        rfl
    · rw [if_neg hy2]
      apply Finset.sum_eq_zero
      intro x hx
      have hy1 := Finset.mem_Icc.mp hy
      have hyone : y = 1 := by
        have : ¬2 ≤ y := by
          intro h
          exact hy2 (Finset.mem_Icc.mpr ⟨h, hy1.2⟩)
        omega
      have hx1 := (Finset.mem_Icc.mp hx).1
      simp [hyone, show ¬x < 1 by omega]
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext y
    simp
    omega
  · intro y _hy
    rfl

/-- A row of coefficient correlations decomposes by primitive denominator;
the quotient is exactly the number of positive multiples below the row. -/
theorem coefficientCorrelationRow_eq_primitiveFloor
    {c y : ℕ} (hy : 2 ≤ y) :
    (∑ x ∈ Finset.Ico 1 y,
        arithmeticCoefficientDedekindTerm c y x) =
      ∑ k ∈ Finset.Icc 1 (y - 1),
        (((y - 1) / k : ℕ) : ℚ) *
          primitiveCoefficientCorrelation c y k := by
  classical
  calc
    (∑ x ∈ Finset.Ico 1 y,
        arithmeticCoefficientDedekindTerm c y x) =
      ∑ x ∈ Finset.Ico 1 y, ∑ k ∈ x.divisors,
        primitiveCoefficientCorrelation c y k := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxdata := Finset.mem_Ico.mp hx
          exact arithmeticCoefficientDedekindTerm_eq_primitiveDivisorSum
            (by omega : 0 < x)
    _ = ∑ x ∈ Finset.Ico 1 y, ∑ k ∈ Finset.Icc 1 (y - 1),
        if k ∣ x then primitiveCoefficientCorrelation c y k else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxdata := Finset.mem_Ico.mp hx
          have hxpos : 0 < x := by omega
          have hxle : x ≤ y - 1 := by omega
          have hset : x.divisors =
              (Finset.Icc 1 (y - 1)).filter fun k ↦ k ∣ x := by
            ext k
            simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
            constructor
            · intro h
              exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hxpos,
                (Nat.le_of_dvd hxpos h.1).trans hxle⟩, h.1⟩
            · intro h
              exact ⟨h.2, hxpos.ne'⟩
          rw [hset, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc 1 (y - 1), ∑ x ∈ Finset.Ico 1 y,
        if k ∣ x then primitiveCoefficientCorrelation c y k else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      rw [← Finset.sum_filter]
      have hinterval : Finset.Ico 1 y = Finset.Ioc 0 (y - 1) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Ioc]
        omega
      rw [hinterval]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Nat.Ioc_filter_dvd_card_eq_div]

/-- The primitive correlation is periodic in its second coefficient. -/
theorem primitiveCoefficientCorrelation_add_period (c y k : ℕ) :
    primitiveCoefficientCorrelation c (y + k) k =
      primitiveCoefficientCorrelation c y k := by
  unfold primitiveCoefficientCorrelation
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  exact rationalSawtooth_add_period a k y

/-- One complete period of the primitive coefficient correlation cancels. -/
theorem primitiveCoefficientCorrelation_complete_period
    {c k : ℕ} (hk : 0 < k) :
    (∑ r ∈ Finset.range k,
        primitiveCoefficientCorrelation c (r + 1) k) = 0 := by
  unfold primitiveCoefficientCorrelation
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have hacop : a.Coprime k := (Finset.mem_filter.mp ha).2
  rw [← Finset.mul_sum]
  have hshift := sum_range_shift_one
    (fun r ↦ rationalSawtooth (r * a) k) k
  have hzero0 : rationalSawtooth (0 * a) k = 0 := by
    simp [rationalSawtooth]
  have hzerok : rationalSawtooth (k * a) k = 0 := by
    simp [rationalSawtooth]
  have hbase := sum_rationalSawtooth_coprime_mul hk hacop
  rw [hzero0, Finset.sum_range_succ, hzerok, add_zero] at hshift
  have hsum :
      (∑ r ∈ Finset.range k,
        rationalSawtooth ((r + 1) * a) k) = 0 := by
    rw [hshift]
    simpa [Nat.mul_comm] using hbase
  rw [hsum, mul_zero]

/-- A floor-weighted zero-mean periodic sum is its final incomplete block
multiplied by the number of preceding blocks. -/
theorem floorWeightedPeriodicSum_eq_terminal
    {f : ℕ → ℚ} {k M s : ℕ} (hk : 0 < k) (hs : s ≤ k)
    (hperiod : ∀ r, f (r + k) = f r)
    (hblock : (∑ r ∈ Finset.range k, f r) = 0) :
    (∑ r ∈ Finset.range (M * k + s),
        (((r / k : ℕ) : ℚ) * f r)) =
      (M : ℚ) * ∑ r ∈ Finset.range s, f r := by
  induction M with
  | zero =>
      simp only [zero_mul, zero_add, Nat.cast_zero]
      apply Finset.sum_eq_zero
      intro r hr
      have hrs : r < s := Finset.mem_range.mp hr
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hrs hs)]
      simp
  | succ M ih =>
      have hlen : (M + 1) * k + s = k + (M * k + s) := by ring
      rw [hlen, Finset.sum_range_add]
      have hfirst :
          (∑ r ∈ Finset.range k, (((r / k : ℕ) : ℚ) * f r)) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        rw [Nat.div_eq_of_lt (Finset.mem_range.mp hr)]
        simp
      rw [hfirst, zero_add]
      have htail :
          (∑ r ∈ Finset.range (M * k + s),
              ((((k + r) / k : ℕ) : ℚ) * f (k + r))) =
            (∑ r ∈ Finset.range (M * k + s),
              ((((r / k : ℕ) : ℚ) + 1) * f r)) := by
        apply Finset.sum_congr rfl
        intro r _hr
        rw [show (k + r) / k = r / k + 1 by
          simpa [Nat.add_comm] using Nat.add_mul_div_left r 1 hk]
        rw [show f (k + r) = f r by
          simpa [Nat.add_comm] using hperiod r]
        push_cast
        rfl
      rw [htail]
      simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
      rw [ih]
      have hunweighted := sum_periodic_blocks f hperiod M s
      rw [hblock, mul_zero, zero_add] at hunweighted
      rw [hunweighted]
      push_cast
      ring

/-- Shifting `0, ..., N - 1` by one gives the literal interval `1, ..., N`. -/
theorem sum_range_shift_eq_Icc
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    (∑ r ∈ Finset.range N, f (r + 1)) =
      ∑ y ∈ Finset.Icc 1 N, f y := by
  apply Finset.sum_bij (fun r _ ↦ r + 1)
  · intro r hr
    exact Finset.mem_Icc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hr
      omega⟩
  · intro r hr s hs h
    omega
  · intro y hy
    have hdata := Finset.mem_Icc.mp hy
    refine ⟨y - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro r _hr
    rfl

/-- One primitive denominator column of the upper triangle is exactly its
terminal cyclic prefix. -/
theorem primitiveCoefficientFloorColumn_eq_terminal
    {c k N : ℕ} (hk : 0 < k) :
    (∑ y ∈ Finset.Icc 2 N,
        (((y - 1) / k : ℕ) : ℚ) *
          primitiveCoefficientCorrelation c y k) =
      ((N / k : ℕ) : ℚ) *
        ∑ r ∈ Finset.range (N % k),
          primitiveCoefficientCorrelation c (r + 1) k := by
  let f := fun r : ℕ ↦ primitiveCoefficientCorrelation c (r + 1) k
  have hperiod : ∀ r, f (r + k) = f r := by
    intro r
    unfold f
    rw [show r + k + 1 = (r + 1) + k by omega]
    exact primitiveCoefficientCorrelation_add_period c (r + 1) k
  have hblock : (∑ r ∈ Finset.range k, f r) = 0 := by
    exact primitiveCoefficientCorrelation_complete_period hk
  have hweighted := floorWeightedPeriodicSum_eq_terminal
    (f := f) (M := N / k) (s := N % k) hk
      (Nat.le_of_lt (Nat.mod_lt N hk)) hperiod hblock
  have hlen : N / k * k + N % k = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N k
  rw [hlen] at hweighted
  have hshift := sum_range_shift_eq_Icc
    (fun y ↦ (((y - 1) / k : ℕ) : ℚ) *
      primitiveCoefficientCorrelation c y k) N
  have hsource :
      (∑ r ∈ Finset.range N, (((r / k : ℕ) : ℚ) * f r)) =
        ∑ y ∈ Finset.Icc 1 N,
          (((y - 1) / k : ℕ) : ℚ) *
            primitiveCoefficientCorrelation c y k := by
    simpa [f] using hshift
  rw [hsource] at hweighted
  have hdropOne :
      (∑ y ∈ Finset.Icc 1 N,
          (((y - 1) / k : ℕ) : ℚ) *
            primitiveCoefficientCorrelation c y k) =
        ∑ y ∈ Finset.Icc 2 N,
          (((y - 1) / k : ℕ) : ℚ) *
            primitiveCoefficientCorrelation c y k := by
    symm
    apply Finset.sum_subset
    · intro y hy
      have h := Finset.mem_Icc.mp hy
      exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
    · intro y hy hnot
      have hdata := Finset.mem_Icc.mp hy
      have hyone : y = 1 := by
        by_contra hne
        apply hnot
        exact Finset.mem_Icc.mpr ⟨by omega, hdata.2⟩
      subst y
      simp
  rw [hdropOne] at hweighted
  exact hweighted

/-- The whole upper triangle is the quotient-weighted sum of terminal
primitive correlation prefixes. -/
theorem coefficientCorrelationUpperTriangle_eq_terminalColumns
    {c p : ℕ} (hp2 : 2 ≤ p) :
    coefficientCorrelationUpperTriangle c p =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        (((p - 1) / k : ℕ) : ℚ) *
          ∑ r ∈ Finset.range ((p - 1) % k),
            primitiveCoefficientCorrelation c (r + 1) k := by
  rw [coefficientCorrelationUpperTriangle_eq_naturalUpperPairs hp2,
    naturalUpperPairs_sum_eq_rows]
  have hextend :
      (∑ y ∈ Finset.Icc 2 (p - 1), ∑ k ∈ Finset.Icc 1 (y - 1),
          (((y - 1) / k : ℕ) : ℚ) *
            primitiveCoefficientCorrelation c y k) =
        ∑ y ∈ Finset.Icc 2 (p - 1), ∑ k ∈ Finset.Icc 1 (p - 1),
          (((y - 1) / k : ℕ) : ℚ) *
            primitiveCoefficientCorrelation c y k := by
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_subset
    · intro k hk
      have hkdata := Finset.mem_Icc.mp hk
      have hydata := Finset.mem_Icc.mp hy
      exact Finset.mem_Icc.mpr ⟨hkdata.1, hkdata.2.trans (by omega)⟩
    · intro k hk hnot
      have hkdata := Finset.mem_Icc.mp hk
      have hydata := Finset.mem_Icc.mp hy
      have hkle : y ≤ k := by
        by_contra h
        apply hnot
        exact Finset.mem_Icc.mpr ⟨hkdata.1, by omega⟩
      rw [Nat.div_eq_of_lt (by omega : y - 1 < k)]
      simp
  have hrows :
      (∑ y ∈ Finset.Icc 2 (p - 1), ∑ x ∈ Finset.Ico 1 y,
          arithmeticCoefficientDedekindTerm c y x) =
        ∑ y ∈ Finset.Icc 2 (p - 1), ∑ k ∈ Finset.Icc 1 (y - 1),
          (((y - 1) / k : ℕ) : ℚ) *
            primitiveCoefficientCorrelation c y k := by
    apply Finset.sum_congr rfl
    intro y hy
    exact coefficientCorrelationRow_eq_primitiveFloor
      (Finset.mem_Icc.mp hy).1
  rw [hrows, hextend, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact primitiveCoefficientFloorColumn_eq_terminal
    (Finset.mem_Icc.mp hk).1

/-- The cyclic prefix at one denominator is twice the corresponding prefix of
primitive coefficient correlations. -/
theorem cyclicPrefixCorrelation_eq_primitivePrefix
    (c k s : ℕ) (hk2 : 2 ≤ k) :
    (∑ a ∈ (Finset.Ico 1 k).filter fun a ↦ a.Coprime k,
        cyclicPrefixResponse a k s * rationalSawtooth (c * a) k) =
      2 * ∑ r ∈ Finset.range s,
        primitiveCoefficientCorrelation c (r + 1) k := by
  unfold cyclicPrefixResponse primitiveCoefficientCorrelation
  have hresidues :
      (Finset.Ico 1 k).filter (fun a ↦ a.Coprime k) =
        (Finset.range k).filter (fun a ↦ a.Coprime k) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
    constructor
    · intro h
      exact ⟨h.1.2, h.2⟩
    · intro h
      have ha0 : 0 < a := by
        by_contra hzero
        have ha : a = 0 := by omega
        subst a
        have hkone : k = 1 := by simpa using h.2
        omega
      exact ⟨⟨ha0, h.1⟩, h.2⟩
  rw [hresidues]
  calc
    (∑ a ∈ (Finset.range k).filter fun a ↦ a.Coprime k,
        (2 * ∑ r ∈ Finset.range s,
          rationalSawtooth ((r + 1) * a) k) *
            rationalSawtooth (c * a) k) =
      2 * ∑ a ∈ (Finset.range k).filter (fun a ↦ a.Coprime k),
        ∑ r ∈ Finset.range s,
          rationalSawtooth (c * a) k *
            rationalSawtooth ((r + 1) * a) k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _ha
              calc
                (2 * ∑ r ∈ Finset.range s,
                    rationalSawtooth ((r + 1) * a) k) *
                    rationalSawtooth (c * a) k =
                  2 * ((∑ r ∈ Finset.range s,
                    rationalSawtooth ((r + 1) * a) k) *
                      rationalSawtooth (c * a) k) := by ring
                _ =
                  2 * ∑ r ∈ Finset.range s,
                    rationalSawtooth ((r + 1) * a) k *
                      rationalSawtooth (c * a) k := by
                        rw [Finset.sum_mul]
                _ = 2 * ∑ r ∈ Finset.range s,
                    rationalSawtooth (c * a) k *
                      rationalSawtooth ((r + 1) * a) k := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro r _hr
                        ring
    _ = 2 * ∑ r ∈ Finset.range s,
        ∑ a ∈ (Finset.range k).filter (fun a ↦ a.Coprime k),
          rationalSawtooth (c * a) k *
            rationalSawtooth ((r + 1) * a) k := by
              rw [Finset.sum_comm]
    _ = _ := rfl

/-- The jump-phase reservoir is twice the literal coefficient upper triangle. -/
theorem jumpPhaseReservoir_eq_two_upperTriangle
    {p : ℕ} (hp : p.Prime) :
    jumpPhaseReservoir p =
      2 * coefficientCorrelationUpperTriangle (p ^ 2) p := by
  let N := p - 1
  have hcolumns := coefficientCorrelationUpperTriangle_eq_terminalColumns
    (c := p ^ 2) hp.two_le
  unfold jumpPhaseReservoir
  dsimp only
  have hinner :
      (∑ k ∈ Finset.Icc 2 N,
          (((N / k : ℕ) : ℚ) *
            ∑ a ∈ (Finset.Ico 1 k).filter fun a ↦ a.Coprime k,
              cyclicPrefixResponse a k (N % k) *
                rationalSawtooth (p ^ 2 * a) k)) =
        2 * ∑ k ∈ Finset.Icc 2 N,
          (((N / k : ℕ) : ℚ) *
            ∑ r ∈ Finset.range (N % k),
              primitiveCoefficientCorrelation (p ^ 2) (r + 1) k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [cyclicPrefixCorrelation_eq_primitivePrefix _ _ _
      (Finset.mem_Icc.mp _hk).1]
    ring
  rw [hinner]
  congr 1
  rw [hcolumns]
  change
    (∑ k ∈ Finset.Icc 2 N,
        (((N / k : ℕ) : ℚ) *
          ∑ r ∈ Finset.range (N % k),
            primitiveCoefficientCorrelation (p ^ 2) (r + 1) k)) =
      ∑ k ∈ Finset.Icc 1 N,
        (((N / k : ℕ) : ℚ) *
          ∑ r ∈ Finset.range (N % k),
            primitiveCoefficientCorrelation (p ^ 2) (r + 1) k)
  apply Finset.sum_subset
  · intro k hk
    have h := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  · intro k hk hnot
    have hdata := Finset.mem_Icc.mp hk
    have hkone : k = 1 := by
      by_contra hne
      apply hnot
      exact Finset.mem_Icc.mpr ⟨by omega, hdata.2⟩
    subst k
    simp [primitiveCoefficientCorrelation, rationalSawtooth]

/-- The endpoint jump coordinate and lower-modulus carrier mass are the same
finite upper triangle. -/
theorem jumpPhaseReservoir_eq_two_fullCarrierFreshMass
    {p : ℕ} (hp : p.Prime) :
    (jumpPhaseReservoir p : ℝ) =
      2 * carrierFamilyFreshMass p (fullCarrierSet p) := by
  rw [jumpPhaseReservoir_eq_two_upperTriangle hp,
    coefficientCorrelationUpperTriangle_eq_fullCarrierWeightedPairSum hp,
    fullCarrierFreshMass_eq_weightedPairSum]
  push_cast
  rfl

/-- Curvature before the prime-square multiplier permutes each reduced residue
system. -/
noncomputable def unmultipliedCarrierBernoulliCurvature (N : ℕ) : ℚ :=
  (N : ℚ) / 6 +
    ∑ k ∈ Finset.Icc 2 N,
      (((N / k : ℕ) : ℚ) * reducedBernoulliTwoSum k)

/-- Restoring the denominator-one term writes curvature as one uniform
floor-weighted reduced-residue sum. -/
theorem unmultipliedCarrierBernoulliCurvature_eq_fullFloorSum
    {N : ℕ} (hN : 1 ≤ N) :
    unmultipliedCarrierBernoulliCurvature N =
      ∑ k ∈ Finset.Icc 1 N,
        (((N / k : ℕ) : ℚ) * reducedBernoulliTwoSum k) := by
  have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp
    omega
  rw [hset, Finset.sum_insert (by simp)]
  unfold unmultipliedCarrierBernoulliCurvature
  have hone : reducedBernoulliTwoSum 1 = 1 / 6 := by
    norm_num [reducedBernoulliTwoSum, rationalBernoulliTwo]
  rw [hone]
  norm_num
  ring

/-- Summing complete Bernoulli grids through `N` is the same as counting each
primitive denominator once for every positive multiple. -/
theorem completeBernoulliGridSum_eq_reducedFloorSum
    {N : ℕ} (_hN : 1 ≤ N) :
    (∑ y ∈ Finset.Icc 1 N, completeBernoulliTwoSum y) =
      ∑ k ∈ Finset.Icc 1 N,
        (((N / k : ℕ) : ℚ) * reducedBernoulliTwoSum k) := by
  classical
  calc
    (∑ y ∈ Finset.Icc 1 N, completeBernoulliTwoSum y) =
      ∑ y ∈ Finset.Icc 1 N, ∑ k ∈ y.divisors,
        reducedBernoulliTwoSum k := by
          apply Finset.sum_congr rfl
          intro y hy
          exact complete_eq_reduced_divisor_sum
            (Finset.mem_Icc.mp hy).1
    _ = ∑ y ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        if k ∣ y then reducedBernoulliTwoSum k else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          have hydata := Finset.mem_Icc.mp hy
          have hset : y.divisors =
              (Finset.Icc 1 N).filter fun k ↦ k ∣ y := by
            ext k
            simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
            constructor
            · intro h
              exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hydata.1,
                (Nat.le_of_dvd hydata.1 h.1).trans hydata.2⟩, h.1⟩
            · intro h
              exact ⟨h.2, (by omega : y ≠ 0)⟩
          rw [hset, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ y ∈ Finset.Icc 1 N,
        if k ∣ y then reducedBernoulliTwoSum k else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
        ext y
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hinterval]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Nat.Ioc_filter_dvd_card_eq_div]

/-- The unmultiplied curvature is exactly one sixth of the harmonic number. -/
theorem unmultipliedCarrierBernoulliCurvature_eq_harmonic
    {N : ℕ} (hN : 1 ≤ N) :
    unmultipliedCarrierBernoulliCurvature N = harmonic N / 6 := by
  rw [unmultipliedCarrierBernoulliCurvature_eq_fullFloorSum hN,
    ← completeBernoulliGridSum_eq_reducedFloorSum hN]
  calc
    (∑ y ∈ Finset.Icc 1 N, completeBernoulliTwoSum y) =
      ∑ y ∈ Finset.Icc 1 N, 1 / (6 * (y : ℚ)) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [completeBernoulliTwoSum_closed (Finset.mem_Icc.mp hy).1]
    _ = harmonic N / 6 := by
      rw [harmonic_eq_sum_Icc, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y hy
      have hyQ : (y : ℚ) ≠ 0 := by
        have hyone := (Finset.mem_Icc.mp hy).1
        have hypos : 0 < y := by omega
        exact_mod_cast hypos.ne'
      field_simp [hyQ]

/-- For a prime carrier, multiplication by `p²` permutes every reduced
residue system below `p`, so the manuscript curvature is the harmonic one. -/
theorem carrierBernoulliCurvature_eq_harmonic
    {p : ℕ} (hp : p.Prime) :
    carrierBernoulliCurvature p = harmonic (p - 1) / 6 := by
  have hN : 1 ≤ p - 1 := by
    have hp2 := hp.two_le
    omega
  calc
    carrierBernoulliCurvature p =
        unmultipliedCarrierBernoulliCurvature (p - 1) := by
      unfold carrierBernoulliCurvature unmultipliedCarrierBernoulliCurvature
      dsimp only
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hkdata := Finset.mem_Icc.mp hk
      have hkp : k < p := by omega
      letI : NeZero k := ⟨(by omega : k ≠ 0)⟩
      have hcop : (p ^ 2).Coprime k :=
        (smallNatUnit_coprime hp (by omega) hkp).symm
      rw [multipliedReducedBernoulliTwoSum_eq hkdata.1 hcop]
    _ = harmonic (p - 1) / 6 :=
      unmultipliedCarrierBernoulliCurvature_eq_harmonic hN

/-- The symmetric reciprocal ratio attached to a positive pair. -/
noncomputable def symmetricReciprocalRatio (x y : ℕ) : ℝ :=
  (x : ℝ) / (y : ℝ) + (y : ℝ) / (x : ℝ)

theorem symmetricReciprocalRatio_scale
    {d x y : ℕ} (hd : 0 < d) (hx : 0 < x) (hy : 0 < y) :
    symmetricReciprocalRatio (d * x) (d * y) =
      symmetricReciprocalRatio x y := by
  unfold symmetricReciprocalRatio
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp [hdR, hxR, hyR]

/-- The literal upper triangle of reciprocal ratios reduces to primitive
ratios with their positive scale coordinate. -/
theorem upperReciprocalRatio_eq_scaledReducedRatios
    {p : ℕ} (hp2 : 2 ≤ p) :
    (∑ ij ∈ upperIndexPairs p,
        symmetricReciprocalRatio
          (firstWindowNat ij.1) (firstWindowNat ij.2)) =
      ∑ r ∈ scaledReducedRatios p,
        symmetricReciprocalRatio r.2.1 r.1 := by
  classical
  apply Finset.sum_bij (fun ij _ ↦ reducedTripleOfPair ij)
  · exact reducedTripleOfPair_mem hp2
  · intro ij hij uv huv
    exact reducedTripleOfPair_injective_on hp2 hij huv
  · exact reducedTripleOfPair_surjective_on hp2
  · intro ij hij
    let x := firstWindowNat ij.1
    let y := firstWindowNat ij.2
    let g := x.gcd y
    have hxpos : 0 < x := firstWindowNat_pos ij.1
    have hypos : 0 < y := firstWindowNat_pos ij.2
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left y hxpos
    have hgx : g ∣ x := Nat.gcd_dvd_left x y
    have hgy : g ∣ y := Nat.gcd_dvd_right x y
    have hxq : 0 < x / g :=
      Nat.div_pos (Nat.gcd_le_left y hxpos) hgpos
    have hyq : 0 < y / g :=
      Nat.div_pos (Nat.gcd_le_right x hypos) hgpos
    unfold reducedTripleOfPair
    change symmetricReciprocalRatio x y =
      symmetricReciprocalRatio (x / g) (y / g)
    calc
      symmetricReciprocalRatio x y =
          symmetricReciprocalRatio (g * (x / g)) (g * (y / g)) := by
            rw [Nat.mul_div_cancel' hgx, Nat.mul_div_cancel' hgy]
      _ = _ := symmetricReciprocalRatio_scale hgpos hxq hyq

/-- Summing the scale coordinate of the reciprocal ratio gives its floor
multiplicity. -/
theorem scaledReducedRatios_reciprocalRatio_eq_floor (p : ℕ) :
    (∑ r ∈ scaledReducedRatios p,
        symmetricReciprocalRatio r.2.1 r.1) =
      ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℝ) *
          symmetricReciprocalRatio ak.2 ak.1 := by
  classical
  let K := fun a k : ℕ ↦ symmetricReciprocalRatio k a
  have hinner (a k : ℕ) :
      (∑ t ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p then K a k else 0) =
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℝ) * K a k else 0 := by
    by_cases hpair : 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a
    · rw [if_pos hpair]
      have hpred (t : ℕ) :
          (0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p) ↔ (0 < t ∧ t * a < p) := by
        tauto
      simp_rw [hpred]
      rw [← Finset.sum_filter]
      change (∑ _t ∈ admissibleScales p a, K a k) = _
      simp [admissibleScales_card hpair.1]
    · rw [if_neg hpair]
      apply Finset.sum_eq_zero
      intro t _ht
      rw [if_neg]
      intro h
      exact hpair ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  calc
    (∑ r ∈ scaledReducedRatios p,
        symmetricReciprocalRatio r.2.1 r.1) =
      ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        ∑ t ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p then K a k else 0 := by
        unfold scaledReducedRatios K
        rw [Finset.sum_filter]
        calc
          _ = ∑ a ∈ Finset.range p,
              ∑ kt ∈ (Finset.range p).product (Finset.range p),
                if 0 < a ∧ 0 < kt.1 ∧ kt.1 < a ∧ kt.1.Coprime a ∧
                    0 < kt.2 ∧ kt.2 * a < p then
                  symmetricReciprocalRatio kt.1 a else 0 :=
              Finset.sum_product _ _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro a _ha
            exact Finset.sum_product _ _ _
    _ = ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℝ) * K a k else 0 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro k _hk
            exact hinner a k
    _ = ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℝ) * K ak.1 ak.2 := by
          unfold reducedRatioPairs
          rw [Finset.sum_filter]
          exact (Finset.sum_product (Finset.range p) (Finset.range p)
            (fun ak : ℕ × ℕ ↦
              if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧
                  ak.2.Coprime ak.1 then
                (((p - 1) / ak.1 : ℕ) : ℝ) * K ak.1 ak.2
              else 0)).symm
    _ = _ := rfl

theorem elementaryRatioReservoir_eq_upperReciprocalRatio
    {p : ℕ} (hp2 : 2 ≤ p) :
    elementaryRatioReservoir p =
      ∑ ij ∈ upperIndexPairs p,
        symmetricReciprocalRatio
          (firstWindowNat ij.1) (firstWindowNat ij.2) := by
  rw [upperReciprocalRatio_eq_scaledReducedRatios hp2,
    scaledReducedRatios_reciprocalRatio_eq_floor]
  unfold elementaryRatioReservoir symmetricReciprocalRatio
  apply Finset.sum_congr rfl
  intro ak _hak
  ring

noncomputable def symmetricReciprocalRatioSquare (p : ℕ) : ℝ :=
  ∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
    symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j)

theorem symmetricReciprocalRatio_comm (x y : ℕ) :
    symmetricReciprocalRatio x y = symmetricReciprocalRatio y x := by
  unfold symmetricReciprocalRatio
  ring

theorem symmetricReciprocalRatio_self {x : ℕ} (hx : 0 < x) :
    symmetricReciprocalRatio x x = 2 := by
  unfold symmetricReciprocalRatio
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp [hxR]
  norm_num

/-- A symmetric square is its diagonal plus twice its strict upper triangle. -/
theorem symmetricReciprocalRatioSquare_eq_diagonal_upper
    {p : ℕ} :
    symmetricReciprocalRatioSquare p =
      2 * ((p - 1 : ℕ) : ℝ) +
        2 * ∑ ij ∈ upperIndexPairs p,
          symmetricReciprocalRatio
            (firstWindowNat ij.1) (firstWindowNat ij.2) := by
  classical
  let I := FirstWindowIndex p
  have hsplit (i j : I) :
      symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) =
        (if i = j then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) +
        (if i < j then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) +
        (if j < i then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, ne_of_lt hij, not_lt_of_ge (le_of_lt hij)]
    · subst j
      have hnot : ¬i < i := lt_irrefl i
      rw [if_neg hnot, if_pos rfl]
      ring
    · simp [hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]
  unfold symmetricReciprocalRatioSquare
  rw [show
      (∑ i : I, ∑ j : I,
        symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j)) =
        ∑ i : I, ∑ j : I,
          ((if i = j then
            symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) +
          (if i < j then
            symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) +
          (if j < i then
            symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0)) by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        exact hsplit i j]
  simp_rw [Finset.sum_add_distrib]
  have hdiag :
      (∑ i : I, ∑ j : I,
        if i = j then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) =
        2 * ((p - 1 : ℕ) : ℝ) := by
    have hpoint (i : I) :
        (∑ j : I, if i = j then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) = 2 := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
        exact symmetricReciprocalRatio_self (firstWindowNat_pos i)
      · intro j _hj hji
        rw [if_neg (Ne.symm hji)]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    simp_rw [hpoint]
    simp
    change (Fintype.card (Fin (p - 1)) : ℝ) * 2 = _
    rw [Fintype.card_fin]
    ring
  have hupper :
      (∑ i : I, ∑ j : I,
        if i < j then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) =
        ∑ ij ∈ upperIndexPairs p,
          symmetricReciprocalRatio
            (firstWindowNat ij.1) (firstWindowNat ij.2) := by
    unfold upperIndexPairs
    rw [Finset.sum_filter]
    exact (Finset.sum_product Finset.univ Finset.univ
      (fun ij : I × I ↦ if ij.1 < ij.2 then
        symmetricReciprocalRatio
          (firstWindowNat ij.1) (firstWindowNat ij.2) else 0)).symm
  have hlower :
      (∑ i : I, ∑ j : I,
        if j < i then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) =
        ∑ ij ∈ upperIndexPairs p,
          symmetricReciprocalRatio
            (firstWindowNat ij.1) (firstWindowNat ij.2) := by
    rw [Finset.sum_comm]
    calc
      (∑ j : I, ∑ i : I,
        if j < i then
          symmetricReciprocalRatio (firstWindowNat i) (firstWindowNat j) else 0) =
        ∑ j : I, ∑ i : I,
          if j < i then
            symmetricReciprocalRatio (firstWindowNat j) (firstWindowNat i) else 0 := by
              apply Finset.sum_congr rfl
              intro j _hj
              apply Finset.sum_congr rfl
              intro i _hi
              split
              · rw [symmetricReciprocalRatio_comm]
              · rfl
      _ = _ := hupper
  rw [hdiag, hupper, hlower]
  ring

/-- The reciprocal-ratio square factors into the first moment and harmonic
moment of the positive window. -/
theorem symmetricReciprocalRatioSquare_closed
    {p : ℕ} (hp2 : 2 ≤ p) :
    symmetricReciprocalRatioSquare p =
      (p : ℝ) * ((p - 1 : ℕ) : ℝ) * (harmonic (p - 1) : ℝ) := by
  let N := p - 1
  have hsum :
      (∑ i : FirstWindowIndex p, (firstWindowNat i : ℝ)) =
        (N : ℝ) * ((N : ℝ) + 1) / 2 := by
    change (∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ)) = _
    rw [show (∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ)) =
        ∑ r ∈ Finset.range N, ((r + 1 : ℕ) : ℝ) by
      exact Fin.sum_univ_eq_sum_range
        (fun r : ℕ ↦ ((r + 1 : ℕ) : ℝ)) N]
    have hrangeQ := sum_range_cast N
    have hrange := congrArg (fun q : ℚ ↦ (q : ℝ)) hrangeQ
    push_cast at hrange
    simp_rw [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    rw [hrange]
    ring
  have hinv :
      (∑ i : FirstWindowIndex p, ((firstWindowNat i : ℕ) : ℝ)⁻¹) =
        (harmonic N : ℝ) := by
    change (∑ i : Fin N, (((i.val + 1 : ℕ) : ℝ)⁻¹)) = _
    rw [show (∑ i : Fin N, (((i.val + 1 : ℕ) : ℝ)⁻¹)) =
        ∑ r ∈ Finset.range N, (((r + 1 : ℕ) : ℝ)⁻¹) by
      exact Fin.sum_univ_eq_sum_range
        (fun r : ℕ ↦ (((r + 1 : ℕ) : ℝ)⁻¹)) N]
    rw [show (∑ r ∈ Finset.range N, (((r + 1 : ℕ) : ℝ)⁻¹)) =
        ∑ y ∈ Finset.Icc 1 N, ((y : ℝ)⁻¹) by
      exact sum_range_shift_eq_Icc (fun y : ℕ ↦ ((y : ℝ)⁻¹)) N]
    have hh := harmonic_eq_sum_Icc (n := N)
    have hhR := congrArg (fun q : ℚ ↦ (q : ℝ)) hh
    push_cast at hhR
    exact hhR.symm
  unfold symmetricReciprocalRatioSquare symmetricReciprocalRatio
  simp_rw [div_eq_mul_inv, Finset.sum_add_distrib]
  rw [show
      (∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        (firstWindowNat i : ℝ) * (firstWindowNat j : ℝ)⁻¹) =
        (∑ i : FirstWindowIndex p, (firstWindowNat i : ℝ)) *
          ∑ j : FirstWindowIndex p, (firstWindowNat j : ℝ)⁻¹ by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]]
  rw [show
      (∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        (firstWindowNat j : ℝ) * (firstWindowNat i : ℝ)⁻¹) =
        (∑ i : FirstWindowIndex p, (firstWindowNat i : ℝ)) *
          ∑ j : FirstWindowIndex p, (firstWindowNat j : ℝ)⁻¹ by
            rw [Finset.sum_comm]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]]
  rw [hsum, hinv]
  have hNp : (N : ℝ) + 1 = (p : ℝ) := by
    dsimp [N]
    exact_mod_cast (show p - 1 + 1 = p by omega)
  rw [hNp]
  ring

/-- Exact elementary correction in harmonic coordinates. -/
theorem elementaryRatioReservoir_add_eq_harmonic
    {p : ℕ} (hp2 : 2 ≤ p) :
    ((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p =
      (p : ℝ) * ((p - 1 : ℕ) : ℝ) *
        (harmonic (p - 1) : ℝ) / 2 := by
  have hsplit := symmetricReciprocalRatioSquare_eq_diagonal_upper (p := p)
  have hclosed := symmetricReciprocalRatioSquare_closed hp2
  rw [← elementaryRatioReservoir_eq_upperReciprocalRatio hp2] at hsplit
  rw [hclosed] at hsplit
  linarith

/-- The elementary Rademacher correction is exactly the Bernoulli-curvature
correction used by the endpoint formula. -/
theorem elementaryRatioReservoir_eq_curvatureCorrection
    {p : ℕ} (hp : p.Prime) :
    ((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p =
      3 * (p : ℝ) * ((p - 1 : ℕ) : ℝ) *
        (carrierBernoulliCurvature p : ℝ) := by
  rw [elementaryRatioReservoir_add_eq_harmonic hp.two_le,
    carrierBernoulliCurvature_eq_harmonic hp]
  push_cast
  ring

/-- The concrete periodic jump identity follows from the independently proved
sampling bridge and the two finite endpoint identifications above. -/
theorem periodicJumpFourierAbelIdentity_odd
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    PeriodicJumpFourierAbelIdentity hp := by
  have hbridge := exact_sampling_reservoir_bridge hp hpodd
  unfold samplingDefect at hbridge
  rw [collision_energy_eq_bernoulli_energy hp] at hbridge
  have hvalue :
      (rawValueJumpSum p : ℝ) = lowerModulusReservoir p := by
    calc
      (rawValueJumpSum p : ℝ) = -4 * (jumpPhaseReservoir p : ℝ) := by
        rw [rawValueJumpSum_eq]
        push_cast
        rfl
      _ = -8 * carrierFamilyFreshMass p (fullCarrierSet p) := by
        rw [jumpPhaseReservoir_eq_two_fullCarrierFreshMass hp]
        ring
      _ = lowerModulusReservoir p :=
        (lowerModulusReservoir_eq_fullCarrierFreshMass hp).symm
  have helem := elementaryRatioReservoir_eq_curvatureCorrection hp
  rw [← hvalue, helem] at hbridge
  unfold PeriodicJumpFourierAbelIdentity
  rw [rawSlopeJumpSum_eq]
  push_cast
  have hslope : (boundarySlope p : ℝ) =
      (p : ℝ) * ((p - 1 : ℕ) : ℝ) := by
    unfold boundarySlope
    push_cast
    ring
  rw [hslope]
  linear_combination -hbridge

/-- Periodic jump aliasing with its Fourier/Abel statement discharged from
the finite reciprocity bridge. -/
theorem periodic_jump_aliasing
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    bernoulliEnergy hp / (p : ℝ) ^ 2 - continuousCapacity (p - 1) =
      -(((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2) -
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 +
        2 * (boundarySlope p : ℝ) *
          (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4 :=
  NField.Alignment.EndpointReservoirAlias.periodic_jump_aliasing hp
    (periodicJumpFourierAbelIdentity_odd hp hpodd)

/-- Exact endpoint-reservoir alias formula with no manuscript-specific input
left as a hypothesis. -/
theorem exact_endpoint_reservoir_alias_formula
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    samplingDefect hp =
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 -
        2 * (boundarySlope p : ℝ) *
          (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4 :=
  NField.Alignment.EndpointReservoirAlias.exact_endpoint_reservoir_alias_formula
    hp (periodicJumpFourierAbelIdentity_odd hp hpodd)

end NField.Alignment.EndpointReciprocityBridge
