/-
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeSquareSawtoothEnergy
import NField.Alignment.SymmetricOffDiagonalPairing

/-!
# Reduced ratios in the prime-square collision window

This module orders prime-square units by their least representatives, pairs
the two orientations of every off-diagonal window ratio, and prepares the
gcd reduction used by the cubic estimate.
-/

namespace NField.Alignment.PrimeSquareReducedRatio

open scoped BigOperators ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionRatioCompression
open NField.Alignment.DedekindCollisionKernel
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.PrimeSquareDedekindCorrection
open NField.Alignment.PrimeSquareSawtoothEnergy
open NField.Alignment.SymmetricOffDiagonalPairing

/-- The canonical order on unit classes used here is the order of their least
nonnegative representatives. -/
@[reducible] noncomputable def unitValLinearOrder (m : ℕ) [NeZero m] :
    LinearOrder (UnitClass m) :=
  LinearOrder.lift' (fun u : UnitClass m => u.val.val) <| by
    intro u v huv
    apply Units.val_injective
    exact ZMod.val_injective m huv

theorem firstWindowUnit_lt_iff
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (i j : FirstWindowIndex p) :
    @LT.lt (UnitClass (p ^ 2)) (unitValLinearOrder (p ^ 2)).toLT
        (firstWindowUnit hp i) (firstWindowUnit hp j) ↔ i < j := by
  change (firstWindowUnit hp i).val.val <
      (firstWindowUnit hp j).val.val ↔ i.val < j.val
  rw [firstWindowUnit_val hp i, firstWindowUnit_val hp j]
  simp [firstWindowNat]

/-- Exact pairing of the two orientations in the prime-square off-diagonal
Dedekind sum. -/
theorem primeSquareCollisionOffDiagonal_eq_two_upper
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    primeSquareCollisionOffDiagonal hp =
      2 * ∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        if i < j then
          dedekindSum ((firstWindowUnit hp i)⁻¹ * firstWindowUnit hp j)
        else 0 := by
  letI : LinearOrder (UnitClass (p ^ 2)) := unitValLinearOrder (p ^ 2)
  rw [show primeSquareCollisionOffDiagonal hp =
      collisionOffDiagonal (firstCollisionWindow hp) dedekindSum by rfl,
    collisionOffDiagonal_eq_two_mul_upperTriangle _ _ dedekindSum_inv]
  congr 1
  unfold collisionUpperTriangle firstCollisionWindow
  rw [sum_image_injective (firstWindowUnit hp)
    (firstWindowUnit_injective hp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_filter]
  rw [sum_image_injective (firstWindowUnit hp)
    (firstWindowUnit_injective hp)]
  apply Finset.sum_congr rfl
  intro j _
  have hiff := firstWindowUnit_lt_iff hp i j
  by_cases hij : i < j
  · simp [hij, hiff.mpr hij]
  · have hnot : ¬firstWindowUnit hp i < firstWindowUnit hp j :=
      fun h => hij (hiff.mp h)
    simp [hij, hnot]

/-! ## Natural representatives and common-factor cancellation -/

/-- A total natural-number presentation of a prime-square unit.  On the
positive first window the coprimality branch is always the first branch. -/
noncomputable def smallNatUnit
    {p : ℕ} (_hp : p.Prime) (n : ℕ) : UnitClass (p ^ 2) :=
  if h : n.Coprime (p ^ 2) then ZMod.unitOfCoprime n h else 1

theorem smallNatUnit_eq_unitOfCoprime
    {p n : ℕ} (hp : p.Prime) (h : n.Coprime (p ^ 2)) :
    smallNatUnit hp n = ZMod.unitOfCoprime n h := by
  unfold smallNatUnit
  rw [dif_pos h]

theorem smallNatUnit_coprime
    {p n : ℕ} (hp : p.Prime) (hnpos : 0 < n) (hnlt : n < p) :
    n.Coprime (p ^ 2) := by
  rw [Nat.coprime_pow_right_iff (by omega : 0 < 2)]
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt hnpos hnlt

theorem smallNatUnit_val
    {p n : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (hnpos : 0 < n) (hnlt : n < p) :
    (smallNatUnit hp n).val.val = n := by
  rw [smallNatUnit_eq_unitOfCoprime hp
    (smallNatUnit_coprime hp hnpos hnlt), ZMod.coe_unitOfCoprime,
    ZMod.val_natCast, Nat.mod_eq_of_lt]
  nlinarith [hp.two_le]

theorem firstWindowUnit_eq_smallNatUnit
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (i : FirstWindowIndex p) :
    firstWindowUnit hp i = smallNatUnit hp (firstWindowNat i) := by
  apply Units.val_injective
  apply ZMod.val_injective (p ^ 2)
  rw [firstWindowUnit_val hp i,
    smallNatUnit_val hp (firstWindowNat_pos i)
      (firstWindowNat_lt hp.two_le i)]

/-- Natural multiplication inside the first window agrees with multiplication
of the corresponding prime-square units. -/
theorem smallNatUnit_mul
    {p g n : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (hgpos : 0 < g) (hnpos : 0 < n)
    (hglt : g < p) (hnlt : n < p) (hprod : g * n < p) :
    smallNatUnit hp (g * n) = smallNatUnit hp g * smallNatUnit hp n := by
  apply Units.val_injective
  change (smallNatUnit hp (g * n)).val =
    (smallNatUnit hp g).val * (smallNatUnit hp n).val
  apply ZMod.val_injective (p ^ 2)
  rw [smallNatUnit_val hp (Nat.mul_pos hgpos hnpos) hprod,
    ZMod.val_mul,
    smallNatUnit_val hp hgpos hglt,
    smallNatUnit_val hp hnpos hnlt]
  rw [Nat.mod_eq_of_lt]
  nlinarith [hp.two_le]

/-- Cancelling a common positive first-window factor leaves the Dedekind
argument unchanged. -/
theorem dedekindRatio_smallNatUnit_cancel
    {p g k a : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (hgpos : 0 < g) (hkpos : 0 < k) (hapos : 0 < a)
    (hglt : g < p) (hklt : k < p) (halt : a < p)
    (hgklt : g * k < p) (hgalt : g * a < p) :
    dedekindSum ((smallNatUnit hp (g * k))⁻¹ *
        smallNatUnit hp (g * a)) =
    dedekindSum ((smallNatUnit hp k)⁻¹ * smallNatUnit hp a) := by
  rw [smallNatUnit_mul hp hgpos hkpos hglt hklt hgklt,
    smallNatUnit_mul hp hgpos hapos hglt halt hgalt,
    dedekindSum_ratio_cancel]

/-! ## The gcd-fiber bijection -/

/-- Strictly increasing pairs of first-window coordinates. -/
def upperIndexPairs (p : ℕ) :
    Finset (FirstWindowIndex p × FirstWindowIndex p) :=
  (Finset.univ.product Finset.univ).filter fun ij => ij.1 < ij.2

/-- Triples `(a,k,t)` representing the pair `(t*k,t*a)`, with `k/a`
reduced and both coordinates still in the first window. -/
def scaledReducedRatios (p : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  ((Finset.range p).product
    ((Finset.range p).product (Finset.range p))).filter fun r =>
      0 < r.1 ∧ 0 < r.2.1 ∧ r.2.1 < r.1 ∧
        r.2.1.Coprime r.1 ∧ 0 < r.2.2 ∧ r.2.2 * r.1 < p

/-- Divide an increasing pair by its gcd and retain the gcd as its scale. -/
def reducedTripleOfPair {p : ℕ}
    (ij : FirstWindowIndex p × FirstWindowIndex p) : ℕ × (ℕ × ℕ) :=
  let x := firstWindowNat ij.1
  let y := firstWindowNat ij.2
  let g := x.gcd y
  (y / g, (x / g, g))

theorem reducedTripleOfPair_mem
    {p : ℕ} (hp2 : 2 ≤ p)
    (ij : FirstWindowIndex p × FirstWindowIndex p)
    (hij : ij ∈ upperIndexPairs p) :
    reducedTripleOfPair ij ∈ scaledReducedRatios p := by
  have hlt : ij.1 < ij.2 := by
    simpa [upperIndexPairs] using hij
  let x := firstWindowNat ij.1
  let y := firstWindowNat ij.2
  let g := x.gcd y
  have hxpos : 0 < x := firstWindowNat_pos ij.1
  have hypos : 0 < y := firstWindowNat_pos ij.2
  have hxlt : x < p := firstWindowNat_lt hp2 ij.1
  have hylt : y < p := firstWindowNat_lt hp2 ij.2
  have hxy : x < y := by
    dsimp [x, y, firstWindowNat]
    exact Nat.add_lt_add_right hlt 1
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left y hxpos
  have hgx : g ∣ x := Nat.gcd_dvd_left x y
  have hgy : g ∣ y := Nat.gcd_dvd_right x y
  have hglex : g ≤ x := Nat.gcd_le_left y hxpos
  have hgleY : g ≤ y := Nat.gcd_le_right x hypos
  have hkpos : 0 < x / g := Nat.div_pos hglex hgpos
  have hapos : 0 < y / g := Nat.div_pos hgleY hgpos
  have hka : x / g < y / g :=
    (Nat.div_lt_div_right hgpos.ne' hgx hgy).2 hxy
  have hcop : (x / g).Coprime (y / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hscale : g * (y / g) < p := by
    rw [Nat.mul_div_cancel' hgy]
    exact hylt
  have hglt : g < p := lt_of_le_of_lt hglex hxlt
  have hklt : x / g < p := lt_trans hka (lt_of_le_of_lt (Nat.div_le_self y g) hylt)
  have halt : y / g < p := lt_of_le_of_lt (Nat.div_le_self y g) hylt
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr halt,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hklt,
        Finset.mem_range.mpr hglt⟩⟩
  · change 0 < y / g ∧ 0 < x / g ∧ x / g < y / g ∧
      (x / g).Coprime (y / g) ∧ 0 < g ∧ g * (y / g) < p
    exact ⟨hapos, hkpos, hka, hcop, hgpos, hscale⟩

theorem reducedTripleOfPair_injective_on
    {p : ℕ} (_hp2 : 2 ≤ p) :
    Set.InjOn reducedTripleOfPair (↑(upperIndexPairs p) :
      Set (FirstWindowIndex p × FirstWindowIndex p)) := by
  intro ij hij uv huv heq
  have hijlt : ij.1 < ij.2 := by simpa [upperIndexPairs] using hij
  have huvlt : uv.1 < uv.2 := by simpa [upperIndexPairs] using huv
  let x := firstWindowNat ij.1
  let y := firstWindowNat ij.2
  let g := x.gcd y
  let x' := firstWindowNat uv.1
  let y' := firstWindowNat uv.2
  let g' := x'.gcd y'
  have hgx : g ∣ x := Nat.gcd_dvd_left x y
  have hgy : g ∣ y := Nat.gcd_dvd_right x y
  have hgx' : g' ∣ x' := Nat.gcd_dvd_left x' y'
  have hgy' : g' ∣ y' := Nat.gcd_dvd_right x' y'
  have haeq : y / g = y' / g' := congrArg Prod.fst heq
  have hkeq : x / g = x' / g' := congrArg (fun r => r.2.1) heq
  have hgeq : g = g' := congrArg (fun r => r.2.2) heq
  have hgx'' : g ∣ x' := by simpa [hgeq] using hgx'
  have hgy'' : g ∣ y' := by simpa [hgeq] using hgy'
  have hkeq' : x / g = x' / g := by simpa [hgeq] using hkeq
  have haeq' : y / g = y' / g := by simpa [hgeq] using haeq
  have hxeq : x = x' := by
    calc
      x = g * (x / g) := (Nat.mul_div_cancel' hgx).symm
      _ = g * (x' / g) := by rw [hkeq']
      _ = x' := Nat.mul_div_cancel' hgx''
  have hyeq : y = y' := by
    calc
      y = g * (y / g) := (Nat.mul_div_cancel' hgy).symm
      _ = g * (y' / g) := by rw [haeq']
      _ = y' := Nat.mul_div_cancel' hgy''
  apply Prod.ext
  · apply Fin.ext
    dsimp [x, x', firstWindowNat] at hxeq
    omega
  · apply Fin.ext
    dsimp [y, y', firstWindowNat] at hyeq
    omega

theorem reducedTripleOfPair_surjective_on
    {p : ℕ} (_hp2 : 2 ≤ p) :
    ∀ r ∈ scaledReducedRatios p,
      ∃ ij, ∃ _hij : ij ∈ upperIndexPairs p,
        reducedTripleOfPair ij = r := by
  intro r hr
  rcases r with ⟨a, k, t⟩
  have hbase := (Finset.mem_filter.mp hr).1
  have hpred := (Finset.mem_filter.mp hr).2
  have halt := Finset.mem_range.mp (Finset.mem_product.mp hbase).1
  have hrest := (Finset.mem_product.mp hbase).2
  have hklt := Finset.mem_range.mp (Finset.mem_product.mp hrest).1
  have htlt := Finset.mem_range.mp (Finset.mem_product.mp hrest).2
  rcases hpred with ⟨hapos, hkpos, hka, hcop, htpos, hta⟩
  have htkpos : 0 < t * k := Nat.mul_pos htpos hkpos
  have htklt : t * k < p :=
    lt_trans ((Nat.mul_lt_mul_left htpos).2 hka) hta
  let i : FirstWindowIndex p := ⟨t * k - 1,
    Nat.sub_lt_sub_right (Nat.one_le_iff_ne_zero.mpr htkpos.ne') htklt⟩
  let j : FirstWindowIndex p := ⟨t * a - 1,
    Nat.sub_lt_sub_right (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_pos htpos hapos).ne') hta⟩
  have hiNat : firstWindowNat i = t * k := by
    dsimp [i, firstWindowNat]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr htkpos.ne')
  have hjNat : firstWindowNat j = t * a := by
    dsimp [j, firstWindowNat]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_pos htpos hapos).ne')
  have hijlt : i < j := by
    apply Fin.mk_lt_mk.mpr
    exact Nat.sub_lt_sub_right (Nat.one_le_iff_ne_zero.mpr htkpos.ne')
      ((Nat.mul_lt_mul_left htpos).2 hka)
  have hijmem : (i, j) ∈ upperIndexPairs p := by
    simp [upperIndexPairs, hijlt]
  refine ⟨(i, j), hijmem, ?_⟩
  have hgcd : (t * k).gcd (t * a) = t := by
    rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  simp only [reducedTripleOfPair]
  rw [hiNat, hjNat, hgcd, Nat.mul_div_right a htpos,
    Nat.mul_div_right k htpos]

/-- The upper-triangle sum is exactly the sum over primitive ratios and their
admissible positive scales. -/
theorem upperTriangle_eq_scaledReducedRatios
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    (∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        if i < j then
          dedekindSum ((firstWindowUnit hp i)⁻¹ * firstWindowUnit hp j)
        else 0) =
      ∑ r ∈ scaledReducedRatios p,
        dedekindSum ((smallNatUnit hp r.2.1)⁻¹ * smallNatUnit hp r.1) := by
  classical
  let sourceTerm := fun ij : FirstWindowIndex p × FirstWindowIndex p =>
    dedekindSum ((firstWindowUnit hp ij.1)⁻¹ * firstWindowUnit hp ij.2)
  let targetTerm := fun r : ℕ × (ℕ × ℕ) =>
    dedekindSum ((smallNatUnit hp r.2.1)⁻¹ * smallNatUnit hp r.1)
  calc
    (∑ i : FirstWindowIndex p, ∑ j : FirstWindowIndex p,
        if i < j then
          dedekindSum ((firstWindowUnit hp i)⁻¹ * firstWindowUnit hp j)
        else 0) = ∑ ij ∈ upperIndexPairs p, sourceTerm ij := by
          unfold upperIndexPairs sourceTerm
          rw [Finset.sum_filter]
          exact (Finset.sum_product Finset.univ Finset.univ
            (fun ij : FirstWindowIndex p × FirstWindowIndex p =>
              if ij.1 < ij.2 then
                dedekindSum ((firstWindowUnit hp ij.1)⁻¹ *
                  firstWindowUnit hp ij.2) else 0)).symm
    _ = ∑ r ∈ scaledReducedRatios p, targetTerm r := by
          apply Finset.sum_bij (fun ij _ => reducedTripleOfPair ij)
          · exact reducedTripleOfPair_mem hp.two_le
          · intro ij hij uv huv
            exact reducedTripleOfPair_injective_on hp.two_le hij huv
          · exact reducedTripleOfPair_surjective_on hp.two_le
          · intro ij hij
            have hlt : ij.1 < ij.2 := by simpa [upperIndexPairs] using hij
            let x := firstWindowNat ij.1
            let y := firstWindowNat ij.2
            let g := x.gcd y
            have hxpos : 0 < x := firstWindowNat_pos ij.1
            have hypos : 0 < y := firstWindowNat_pos ij.2
            have hxlt : x < p := firstWindowNat_lt hp.two_le ij.1
            have hylt : y < p := firstWindowNat_lt hp.two_le ij.2
            have hgpos : 0 < g := Nat.gcd_pos_of_pos_left y hxpos
            have hgx : g ∣ x := Nat.gcd_dvd_left x y
            have hgy : g ∣ y := Nat.gcd_dvd_right x y
            have hglt : g < p := lt_of_le_of_lt
              (Nat.gcd_le_left y hxpos) hxlt
            have hkpos : 0 < x / g := Nat.div_pos
              (Nat.gcd_le_left y hxpos) hgpos
            have hapos : 0 < y / g := Nat.div_pos
              (Nat.gcd_le_right x hypos) hgpos
            have hklt : x / g < p := lt_of_le_of_lt
              (Nat.div_le_self x g) hxlt
            have halt : y / g < p := lt_of_le_of_lt
              (Nat.div_le_self y g) hylt
            have hgk : g * (x / g) = x := Nat.mul_div_cancel' hgx
            have hga : g * (y / g) = y := Nat.mul_div_cancel' hgy
            unfold sourceTerm targetTerm reducedTripleOfPair
            rw [firstWindowUnit_eq_smallNatUnit hp,
              firstWindowUnit_eq_smallNatUnit hp]
            change dedekindSum ((smallNatUnit hp x)⁻¹ * smallNatUnit hp y) =
              dedekindSum ((smallNatUnit hp (x / g))⁻¹ *
                smallNatUnit hp (y / g))
            calc
              _ = dedekindSum ((smallNatUnit hp (g * (x / g)))⁻¹ *
                    smallNatUnit hp (g * (y / g))) := by rw [hgk, hga]
              _ = _ := dedekindRatio_smallNatUnit_cancel hp hgpos hkpos hapos
                hglt hklt halt (by simpa [hgk] using hxlt)
                  (by simpa [hga] using hylt)
    _ = ∑ r ∈ scaledReducedRatios p,
        dedekindSum ((smallNatUnit hp r.2.1)⁻¹ * smallNatUnit hp r.1) := rfl

/-! ## Exact scale multiplicity -/

/-- Primitive reduced ratios `k/a` with `1 <= k < a < p`. -/
def reducedRatioPairs (p : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range p).product (Finset.range p)).filter fun ak =>
    0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧ ak.2.Coprime ak.1

/-- Positive scales which keep the numerator inside the first window. -/
def admissibleScales (p a : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun t => 0 < t ∧ t * a < p

theorem admissibleScales_eq_Icc
    {p a : ℕ} (ha : 0 < a) :
    admissibleScales p a = Finset.Icc 1 ((p - 1) / a) := by
  ext t
  simp only [admissibleScales, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Icc]
  constructor
  · intro h
    refine ⟨Nat.one_le_iff_ne_zero.mpr h.2.1.ne', ?_⟩
    rw [Nat.le_div_iff_mul_le ha]
    omega
  · intro h
    have hmul : t * a ≤ p - 1 :=
      (Nat.le_div_iff_mul_le ha).mp h.2
    have htle : t ≤ p - 1 :=
      h.2.trans (Nat.div_le_self (p - 1) a)
    exact ⟨by omega, Nat.pos_of_ne_zero (by omega), by omega⟩

theorem admissibleScales_card
    {p a : ℕ} (ha : 0 < a) :
    (admissibleScales p a).card = (p - 1) / a := by
  rw [admissibleScales_eq_Icc ha, Nat.card_Icc]
  simp

/-- Summing out the scale coordinate gives exactly the floor multiplicity
`floor ((p-1)/a)` attached to each primitive ratio. -/
theorem scaledReducedRatios_sum_eq_floor
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    (∑ r ∈ scaledReducedRatios p,
        dedekindSum ((smallNatUnit hp r.2.1)⁻¹ * smallNatUnit hp r.1)) =
      ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℂ) *
          dedekindSum ((smallNatUnit hp ak.2)⁻¹ * smallNatUnit hp ak.1) := by
  classical
  let K := fun a k : ℕ =>
    dedekindSum ((smallNatUnit hp k)⁻¹ * smallNatUnit hp a)
  have hinner (a k : ℕ) :
      (∑ t ∈ Finset.range p,
          if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p then K a k else 0) =
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℂ) * K a k else 0 := by
    by_cases hpair : 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a
    · have ha := hpair.1
      rw [if_pos hpair]
      have hpred (t : ℕ) :
          (0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p) ↔ (0 < t ∧ t * a < p) := by
        tauto
      simp_rw [hpred]
      rw [← Finset.sum_filter]
      change (∑ t ∈ admissibleScales p a, K a k) = _
      simp [admissibleScales_card ha]
    · have hfalse (t : ℕ) :
          ¬(0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a ∧
              0 < t ∧ t * a < p) := by
          intro h
          exact hpair ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      simp [hpair, hfalse]
  calc
    (∑ r ∈ scaledReducedRatios p,
        dedekindSum ((smallNatUnit hp r.2.1)⁻¹ * smallNatUnit hp r.1)) =
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
                  dedekindSum ((smallNatUnit hp kt.1)⁻¹ *
                    smallNatUnit hp a) else 0 :=
              Finset.sum_product _ _ _
          _ = _ := by
              apply Finset.sum_congr rfl
              intro a _
              exact Finset.sum_product _ _ _
    _ = ∑ a ∈ Finset.range p, ∑ k ∈ Finset.range p,
        if 0 < a ∧ 0 < k ∧ k < a ∧ k.Coprime a then
          (((p - 1) / a : ℕ) : ℂ) * K a k else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro k _
        exact hinner a k
    _ = ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℂ) * K ak.1 ak.2 := by
        unfold reducedRatioPairs
        rw [Finset.sum_filter]
        exact (Finset.sum_product (Finset.range p) (Finset.range p)
          (fun ak : ℕ × ℕ =>
            if 0 < ak.1 ∧ 0 < ak.2 ∧ ak.2 < ak.1 ∧
                ak.2.Coprime ak.1 then
              (((p - 1) / ak.1 : ℕ) : ℂ) * K ak.1 ak.2 else 0)).symm
    _ = ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℂ) *
          dedekindSum ((smallNatUnit hp ak.2)⁻¹ *
            smallNatUnit hp ak.1) := rfl

/-- The manuscript's exact reduced-ratio pole split for the off-diagonal
Dedekind sum. -/
theorem primeSquareCollisionOffDiagonal_eq_reducedRatios
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    primeSquareCollisionOffDiagonal hp =
      2 * ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℂ) *
          dedekindSum ((smallNatUnit hp ak.2)⁻¹ * smallNatUnit hp ak.1) := by
  rw [primeSquareCollisionOffDiagonal_eq_two_upper hp,
    upperTriangle_eq_scaledReducedRatios hp,
    scaledReducedRatios_sum_eq_floor hp]

/-- Multiplying by the energy normalization produces the factor eight in the
paper's off-diagonal formula. -/
theorem four_mul_primeSquareCollisionOffDiagonal_eq_reducedRatios
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    4 * primeSquareCollisionOffDiagonal hp =
      8 * ∑ ak ∈ reducedRatioPairs p,
        (((p - 1) / ak.1 : ℕ) : ℂ) *
          dedekindSum ((smallNatUnit hp ak.2)⁻¹ * smallNatUnit hp ak.1) := by
  rw [primeSquareCollisionOffDiagonal_eq_reducedRatios hp]
  ring

end NField.Alignment.PrimeSquareReducedRatio
