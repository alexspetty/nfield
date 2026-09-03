/-
Author: Alexander S. Petty
-/

import NField.Alignment.AutocorrelationFormula
import NField.Alignment.FloorDigitSpectralModel
import NField.Alignment.AlignmentLimitClassification

namespace NField.Alignment.AutocorrelationFormula

open scoped BigOperators
open ZMod
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.CollisionDefinition

/-! ## Exact ordered-bin phases -/

/-- The first nonzero residue in the `d`-th intrinsic floor-digit bin. -/
def orderedBinStart (b p d : ℕ) : ℕ :=
  max 1 (digitBinBoundary b p d)

/-- The exact length of the `d`-th intrinsic floor-digit bin. -/
def orderedBinLength (b p d : ℕ) : ℕ :=
  digitBinBoundary b p (d + 1) - orderedBinStart b p d

/-- A cast natural interval is the translate of the corresponding initial
cyclic interval by its exact left endpoint. -/
theorem boundary_image_eq_translate {p lower upper : ℕ} [NeZero p]
    (hlower : lower ≤ upper) :
    (Finset.Ico lower upper).image (fun x : ℕ => (x : ZMod p)) =
      translateSet (lower : ZMod p) (initialIntervalSet p (upper - lower)) := by
  classical
  unfold translateSet initialIntervalSet
  rw [Finset.image_image]
  ext r
  simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_range,
    Function.comp_apply]
  constructor
  · rintro ⟨x, ⟨hlx, hxu⟩, rfl⟩
    refine ⟨x - lower, ?_, ?_⟩
    · omega
    · rw [← Nat.cast_add, Nat.add_sub_of_le hlx]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨lower + j, ?_, ?_⟩
    · constructor <;> omega
    · rw [Nat.cast_add]

/-- The manuscript's ordered-bin length is the intrinsic digit population. -/
theorem orderedBinLength_eq_population {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) (d : Fin b) :
    orderedBinLength b p d.val = digitBinPopulation b p d.val := by
  exact (digitBinPopulation_eq_boundary_sub hb hp d.isLt).symm

/-- Consecutive ordered-bin starts advance by exactly the current bin
population. -/
theorem orderedBinStart_succ {b p d : ℕ}
    (hb : 0 < b) (hp : 0 < p) (hd : d < b) :
    orderedBinStart b p (d + 1) =
      orderedBinStart b p d + digitBinPopulation b p d := by
  have hboundary_pos : 0 < digitBinBoundary b p (d + 1) := by
    by_contra h
    have hz : digitBinBoundary b p (d + 1) = 0 :=
      Nat.eq_zero_of_not_pos h
    have hceil : ((d + 1) * p) ⌈/⌉ b ≤ 0 := by
      simpa [digitBinBoundary] using Nat.le_of_eq hz
    have hle : (d + 1) * p ≤ b * 0 :=
      (ceilDiv_le_iff_le_mul hb).1 hceil
    have hprod : 0 < (d + 1) * p := Nat.mul_pos (by omega) hp
    omega
  have hmono : digitBinBoundary b p d ≤
      digitBinBoundary b p (d + 1) := by
    exact (gc_mul_ceilDiv hb).monotone_l
      (Nat.mul_le_mul_right p (Nat.le_succ d))
  have hstart_le : orderedBinStart b p d ≤
      digitBinBoundary b p (d + 1) := by
    rw [orderedBinStart, max_le_iff]
    exact ⟨hboundary_pos, hmono⟩
  rw [orderedBinStart, max_eq_right hboundary_pos,
    digitBinPopulation_eq_boundary_sub hb hp hd]
  exact (Nat.add_sub_of_le hstart_le).symm

/-- The exact left endpoint is one plus the populations of all earlier bins,
which is the manuscript's cumulative-start definition. -/
theorem orderedBinStart_eq_one_add_prefix {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) (d : Fin b) :
    orderedBinStart b p d.val =
      1 + ∑ e ∈ Finset.range d.val, digitBinPopulation b p e := by
  have hprefix : ∀ n, n ≤ b →
      orderedBinStart b p n =
        1 + ∑ e ∈ Finset.range n, digitBinPopulation b p e := by
    intro n hn
    induction n with
    | zero => simp [orderedBinStart, digitBinBoundary]
    | succ n ih =>
        rw [orderedBinStart_succ hb hp (by omega), ih (by omega),
          Finset.sum_range_succ]
        omega
  exact hprefix d.val d.isLt.le

/-- Each intrinsic bin Fourier coefficient is its initial-interval transform
times the phase of the bin's exact left endpoint. -/
theorem prime_binFourier_eq_ordered_interval {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p]
    (d : Fin b) (k : ZMod p) :
    binFourier (primeDigitWord b p hb hp) d k =
      stdAddChar (-((orderedBinStart b p d.val : ZMod p) * k)) *
        intervalFourier p (orderedBinLength b p d.val) k := by
  let lower := orderedBinStart b p d.val
  let upper := digitBinBoundary b p (d.val + 1)
  have hupper_le : upper ≤ p := by
    apply (ceilDiv_le_iff_le_mul hb).2
    have hdle : d.val + 1 ≤ b := by omega
    exact Nat.mul_le_mul_right p hdle
  have hlower_le : lower ≤ upper := by
    have hmono : digitBinBoundary b p d.val ≤
        digitBinBoundary b p (d.val + 1) := by
      exact (gc_mul_ceilDiv hb).monotone_l
        (Nat.mul_le_mul_right p (Nat.le_succ d.val))
    by_cases hd0 : d.val = 0
    · have hpositive : 0 < digitBinBoundary b p (d.val + 1) := by
        by_contra h
        have hz : digitBinBoundary b p (d.val + 1) = 0 :=
          Nat.eq_zero_of_not_pos h
        have hceil : ((d.val + 1) * p) ⌈/⌉ b ≤ 0 := by
          simpa [digitBinBoundary] using Nat.le_of_eq hz
        have hle : (d.val + 1) * p ≤ b * 0 :=
          (ceilDiv_le_iff_le_mul hb).1 hceil
        have hprod : 0 < (d.val + 1) * p :=
          Nat.mul_pos (by omega) hp
        omega
      dsimp [lower, orderedBinStart, upper]
      rw [show digitBinBoundary b p d.val = 0 by
        simp [digitBinBoundary, hd0], max_eq_left (by decide : 1 ≥ 0)]
      exact hpositive
    · have hpositive : 1 ≤ digitBinBoundary b p d.val := by
        have hpos : 0 < digitBinBoundary b p d.val := by
          by_contra h
          have hz : digitBinBoundary b p d.val = 0 :=
            Nat.eq_zero_of_not_pos h
          have hceil : (d.val * p) ⌈/⌉ b ≤ 0 := by
            simpa [digitBinBoundary] using Nat.le_of_eq hz
          have hle : d.val * p ≤ b * 0 :=
            (ceilDiv_le_iff_le_mul hb).1 hceil
          have hprod : 0 < d.val * p :=
            Nat.mul_pos (Nat.pos_of_ne_zero hd0) hp
          omega
        omega
      dsimp [lower, orderedBinStart, upper]
      rw [max_eq_right hpositive]
      exact hmono
  have hlength_le : upper - lower ≤ p :=
    le_trans (Nat.sub_le upper lower) hupper_le
  rw [binFourier, primeDigitWord_binSet_eq_boundary_image hb hp d]
  change setFourier
      ((Finset.Ico lower upper).image (fun x : ℕ => (x : ZMod p))) k = _
  rw [boundary_image_eq_translate hlower_le, setFourier_translate,
    setFourier_initialInterval p (upper - lower) hlength_le]
  rfl

/-- Every cross-spectrum entry has the manuscript's ordered-bin interval
formula, including the cumulative starting phase of each bin. -/
theorem prime_crossSpectrum_eq_ordered_intervals {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p]
    (k k' : ZMod p) :
    crossSpectrum (primeDigitWord b p hb hp) k k' =
      ∑ d : Fin b,
        stdAddChar (-((orderedBinStart b p d.val : ZMod p) * (k + k'))) *
          intervalFourier p (orderedBinLength b p d.val) k *
          intervalFourier p (orderedBinLength b p d.val) k' := by
  classical
  unfold crossSpectrum
  apply Finset.sum_congr rfl
  intro d _
  rw [prime_binFourier_eq_ordered_interval hb hp,
    prime_binFourier_eq_ordered_interval hb hp]
  have hphase :
      stdAddChar (-((orderedBinStart b p d.val : ZMod p) * k)) *
          stdAddChar (-((orderedBinStart b p d.val : ZMod p) * k')) =
        stdAddChar
          (-((orderedBinStart b p d.val : ZMod p) * (k + k'))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    stdAddChar (-((orderedBinStart b p d.val : ZMod p) * k)) *
          intervalFourier p (orderedBinLength b p d.val) k *
          (stdAddChar (-((orderedBinStart b p d.val : ZMod p) * k')) *
            intervalFourier p (orderedBinLength b p d.val) k') =
        (stdAddChar (-((orderedBinStart b p d.val : ZMod p) * k)) *
          stdAddChar (-((orderedBinStart b p d.val : ZMod p) * k'))) *
          intervalFourier p (orderedBinLength b p d.val) k *
          intervalFourier p (orderedBinLength b p d.val) k' := by ring
    _ = _ := by rw [hphase]

/-! ## Identity and inverse multiplier checks -/

/-- The intrinsic prime digit kernel has one diagonal match at every nonzero
residue and none at zero. -/
theorem prime_multiplicativeCollision_one {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p] :
    multiplicativeCollision (primeDigitWord b p hb hp.pos) 1 = (p - 1 : ℕ) := by
  unfold multiplicativeCollision
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun r : ZMod p => sameBinKernel (primeDigitWord b p hb hp.pos) r (1 * r)) 0]
  simp only [one_mul]
  have hzero : primeDigitWord b p hb hp.pos 0 = none :=
    primeDigitWord_zero b p hb hp.pos
  rw [sameBinKernel_eq_indicator]
  simp only [hzero, ne_eq, not_true_eq_false, and_false, if_false, zero_add]
  calc
    ∑ r : {x : ZMod p // x ≠ 0},
        sameBinKernel (primeDigitWord b p hb hp.pos) r.val r.val =
        ∑ _r : {x : ZMod p // x ≠ 0}, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [sameBinKernel_eq_indicator]
          simp [primeDigitWord, r.property]
    _ = (p - 1 : ℕ) := by
      simp [Fintype.card_subtype_compl]

/-- Multiplicative collision is invariant under replacing a unit multiplier
by its explicit inverse. -/
theorem multiplicativeCollision_inverse [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) :
    multiplicativeCollision word aInv = multiplicativeCollision word a := by
  let e : ZMod N ≃ ZMod N :=
    { toFun := fun r => aInv * r
      invFun := fun r => a * r
      left_inv := by
        intro r
        simp only
        calc
          a * (aInv * r) = (a * aInv) * r := by ring
          _ = r := by rw [hinv, one_mul]
      right_inv := by
        intro r
        simp only
        calc
          aInv * (a * r) = (a * aInv) * r := by ring
          _ = r := by rw [hinv, one_mul] }
  unfold multiplicativeCollision
  apply Fintype.sum_equiv e
  intro r
  dsimp [e]
  have hcancel : a * (aInv * r) = r := by
    calc
      a * (aInv * r) = (a * aInv) * r := by ring
      _ = r := by rw [hinv, one_mul]
  rw [hcancel, sameBinKernel_symmetric]

/-! ## Canonical power orbit and actual generated cosets -/

/-- The canonical finite power map of the base into the prime unit group. -/
noncomputable def canonicalPrimePowerMap {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    Fin (primeBasePeriod b p hp hpb) → (ZMod p)ˣ :=
  fun i => (primeBaseUnit b p hp hpb) ^ i.val

/-- Full multiplicative order makes the canonical power map bijective. -/
theorem canonicalPrimePowerMap_bijective_of_full_order {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1) :
    Function.Bijective (canonicalPrimePowerMap hp hpb) := by
  let hu : Nat.Coprime p 1 := by simp
  have hfun : canonicalPrimePowerMap hp hpb =
      primePowerOrbitUnit hp hpb hu := by
    funext i
    apply Units.ext
    simp [canonicalPrimePowerMap, primePowerOrbitUnit, primeBaseUnit]
  rw [hfun]
  exact primePowerOrbitUnit_bijective_of_full_order hp hpb hu hfull

/-- The canonical full-order power enumeration as an equivalence. -/
noncomputable def canonicalPrimePowerEquiv {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1) :
    Fin (primeBasePeriod b p hp hpb) ≃ (ZMod p)ˣ :=
  Equiv.ofBijective (canonicalPrimePowerMap hp hpb)
    (canonicalPrimePowerMap_bijective_of_full_order hp hpb hfull)

/-- A primitive-root certificate supplies the exact full-order hypothesis
used by the canonical power equivalence. -/
theorem primeBasePeriod_eq_full_of_isPrimitiveRoot {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hprimitive : IsPrimitiveRoot (primeBaseUnit b p hp hpb) (p - 1)) :
    primeBasePeriod b p hp hpb = p - 1 := by
  simpa [primeBasePeriod, primeBaseUnit] using hprimitive.eq_orderOf.symm

/-- A primitive-root certificate therefore constructs the canonical finite
power-map equivalence onto every unit modulo the prime. -/
noncomputable def canonicalPrimePowerEquivOfPrimitiveRoot {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hprimitive : IsPrimitiveRoot (primeBaseUnit b p hp hpb) (p - 1)) :
    Fin (primeBasePeriod b p hp hpb) ≃ (ZMod p)ˣ :=
  canonicalPrimePowerEquiv hp hpb
    (primeBasePeriod_eq_full_of_isPrimitiveRoot hp hpb hprimitive)

/-- Units modulo a prime are canonically the nonzero residues. -/
noncomputable def primeUnitNonzeroEquiv (p : ℕ) (hp : Nat.Prime p) :
    (ZMod p)ˣ ≃ NonzeroResidue p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact
    { toFun := fun u => ⟨(u : ZMod p), Units.ne_zero u⟩
      invFun := fun r => Units.mk0 r.val r.property
      left_inv := by
        intro u
        apply Units.ext
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        rfl }

local instance primeBasePeriodNeZero {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    NeZero (primeBasePeriod b p hp hpb) :=
  ⟨(primeBasePeriod_pos hp hpb).ne'⟩

private theorem zmod_finEquiv_apply_val_local (n : ℕ) [NeZero n]
    (x : Fin n) : (ZMod.finEquiv n x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ _ => rfl

/-- The primitive power orbit in its natural cyclic clock coordinate. -/
noncomputable def canonicalPrimeOrbitEquiv {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1) :
    ZMod (primeBasePeriod b p hp hpb) ≃ NonzeroResidue p := by
  let L := primeBasePeriod b p hp hpb
  letI : NeZero L := ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  exact ((ZMod.finEquiv L).symm.toEquiv).trans
    ((canonicalPrimePowerEquiv hp hpb hfull).trans
      (primeUnitNonzeroEquiv p hp))

@[simp] theorem canonicalPrimeOrbitEquiv_apply {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1)
    (t : ZMod (primeBasePeriod b p hp hpb)) :
    (canonicalPrimeOrbitEquiv hp hpb hfull t).val =
      (((primeBaseUnit b p hp hpb) ^ t.val : (ZMod p)ˣ) : ZMod p) := by
  let L := primeBasePeriod b p hp hpb
  letI : NeZero L := ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  have hfin : ((ZMod.finEquiv L).symm t).val = t.val := by
    have h := (ZMod.finEquiv L).apply_symm_apply t
    calc
      ((ZMod.finEquiv L).symm t).val =
          (ZMod.finEquiv L ((ZMod.finEquiv L).symm t)).val :=
        (zmod_finEquiv_apply_val_local L _).symm
      _ = t.val := congrArg ZMod.val h
  change (((primeBaseUnit b p hp hpb) ^
      ((ZMod.finEquiv L).symm t).val : (ZMod p)ˣ) : ZMod p) = _
  rw [hfin]

/-- Addition on the cyclic exponent clock is multiplication by the matching
power of the base on the canonical nonzero-residue orbit. -/
theorem canonicalPrimeOrbitEquiv_motion {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1)
    (t lag : ZMod (primeBasePeriod b p hp hpb)) :
    (canonicalPrimeOrbitEquiv hp hpb hfull (t + lag)).val =
      (((primeBaseUnit b p hp hpb) ^ lag.val : (ZMod p)ˣ) : ZMod p) *
        (canonicalPrimeOrbitEquiv hp hpb hfull t).val := by
  let u := primeBaseUnit b p hp hpb
  let L := primeBasePeriod b p hp hpb
  letI : NeZero L := ⟨(primeBasePeriod_pos hp hpb).ne'⟩
  rw [canonicalPrimeOrbitEquiv_apply, canonicalPrimeOrbitEquiv_apply]
  have horder : orderOf u = L := by
    simp [u, L, primeBaseUnit, primeBasePeriod]
  have hunit : u ^ (t + lag).val = u ^ lag.val * u ^ t.val := by
    rw [ZMod.val_add]
    calc
      u ^ ((t.val + lag.val) % L) = u ^ (t.val + lag.val) := by
        rw [← horder]
        exact pow_mod_orderOf u (t.val + lag.val)
      _ = u ^ lag.val * u ^ t.val := by
        rw [pow_add]
        exact mul_comm _ _
  simpa [u] using congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hunit

/-- The manuscript's primitive-root autocorrelation slice with the cyclic
power orbit, its motion law, and the inverse multiplier all constructed
canonically. -/
theorem canonical_primitiveRoot_autocorrelation_slice {b p κ : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p]
    (hprimitive : IsPrimitiveRoot (primeBaseUnit b p hp hpb) (p - 1))
    (word : ZMod p → Option (Fin κ)) (hzero : word 0 = none)
    (lag : ZMod (primeBasePeriod b p hp hpb)) :
    let hfull := primeBasePeriod_eq_full_of_isPrimitiveRoot hp hpb hprimitive
    let a : (ZMod p)ˣ := (primeBaseUnit b p hp hpb) ^ lag.val
    fullOrbitAutocorrelation word (canonicalPrimeOrbitEquiv hp hpb hfull) lag =
      (p : ℂ)⁻¹ * ∑ k : ZMod p,
        crossSpectrum word k (-((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k) := by
  dsimp only
  let hfull := primeBasePeriod_eq_full_of_isPrimitiveRoot hp hpb hprimitive
  let a : (ZMod p)ˣ := (primeBaseUnit b p hp hpb) ^ lag.val
  apply fullOrbit_autocorrelation_slice word
    (canonicalPrimeOrbitEquiv hp hpb hfull) lag
    ((a : (ZMod p)ˣ) : ZMod p) ((a⁻¹ : (ZMod p)ˣ) : ZMod p) hzero
  · intro t
    exact canonicalPrimeOrbitEquiv_motion hp hpb hfull t lag
  · exact congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) (mul_inv_cancel a)

/-- Full order identifies the subgroup generated by the base with the entire
prime unit group. -/
theorem primeBaseOrbitSubgroup_eq_top_of_full_order {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hfull : primeBasePeriod b p hp hpb = p - 1) :
    primeBaseOrbitSubgroup b p hp hpb = ⊤ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  apply Subgroup.eq_top_of_card_eq
  rw [primeBaseOrbitSubgroup_card, hfull, Nat.card_eq_fintype_card,
    ZMod.card_units]

/-- The coset `c <b>` as the actual image of the subgroup generated by the
base, coerced into the prime residue field. -/
noncomputable local instance generatedOrbitSubgroupFintype {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) :
    Fintype (primeBaseOrbitSubgroup b p hp hpb) :=
  Fintype.ofFinite _

noncomputable def generatedOrbitCosetSet {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (c : (ZMod p)ˣ) :
    Finset (ZMod p) :=
  (Finset.univ : Finset (primeBaseOrbitSubgroup b p hp hpb)).image
    fun u => (((c * u.val : (ZMod p)ˣ) : ZMod p))

/-- At full order every generated coset is exactly the complete nonzero
residue set. -/
theorem generatedOrbitCosetSet_eq_fullNonzero_of_full_order {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p]
    (c : (ZMod p)ˣ) (hfull : primeBasePeriod b p hp hpb = p - 1) :
    generatedOrbitCosetSet hp hpb c = Finset.univ.erase 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have htop := primeBaseOrbitSubgroup_eq_top_of_full_order hp hpb hfull
  ext r
  rw [generatedOrbitCosetSet]
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨u, _, hu⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rw [← hu]
    exact Units.ne_zero (c * u.val)
  · intro hmem
    have hr : r ≠ 0 := (Finset.mem_erase.mp hmem).1
    let x : (ZMod p)ˣ := Units.mk0 r hr
    let u0 : (ZMod p)ˣ := c⁻¹ * x
    have hu0 : u0 ∈ primeBaseOrbitSubgroup b p hp hpb := by
      rw [htop]
      trivial
    apply Finset.mem_image.mpr
    refine ⟨⟨u0, hu0⟩, Finset.mem_univ _, ?_⟩
    change (((c * u0 : (ZMod p)ˣ) : ZMod p)) = r
    simp [u0, x]

/-- The exponential sum of an actual generated coset is exactly the subgroup
exponential sum indexed by `<b>`. -/
theorem generatedOrbitCoset_exponential {b p : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p]
    (c : (ZMod p)ˣ) (m : ZMod p) :
    subsetExponential (generatedOrbitCosetSet hp hpb c) m =
      ∑ u : primeBaseOrbitSubgroup b p hp hpb,
        stdAddChar (m * (((c * u.val : (ZMod p)ˣ) : ZMod p))) := by
  classical
  unfold subsetExponential generatedOrbitCosetSet
  rw [Finset.sum_image]
  intro u _ v _ huv
  apply Subtype.ext
  apply mul_left_cancel (a := c)
  exact Units.ext huv

/-- The individual-orbit formula specialized to an actual multiplicative
coset of the subgroup generated by the base. -/
theorem generatedOrbitCoset_collision_formula {b p κ : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p]
    (word : ZMod p → Option (Fin κ)) (c : (ZMod p)ˣ) (a : ZMod p) :
    subsetCollision word (generatedOrbitCosetSet hp hpb c) a =
      ((p : ℂ)⁻¹) ^ 2 * ∑ k : ZMod p, ∑ k' : ZMod p,
        crossSpectrum word k k' *
          subsetExponential (generatedOrbitCosetSet hp hpb c) (k + a * k') :=
  subsetCollision_formula word (generatedOrbitCosetSet hp hpb c) a

/-! ## The full nonzero-field exponential sum -/

/-- The complete nonzero residue set. -/
def fullNonzeroResidueSet (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  Finset.univ.erase 0

/-- The additive exponential sum over every nonzero residue has exactly the
two values used in the primitive-root collapse. -/
theorem fullNonzeroResidue_exponential [NeZero N] (m : ZMod N) :
    subsetExponential (fullNonzeroResidueSet N) m =
      if m = 0 then ((N - 1 : ℕ) : ℂ) else (-1 : ℂ) := by
  classical
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun x : ZMod N => stdAddChar (m * x)) (Finset.mem_univ 0)
  have hfull := sum_stdAddChar_mul (N := N) m
  unfold subsetExponential fullNonzeroResidueSet
  by_cases hm : m = 0
  · subst m
    simp [ZMod.card]
  · rw [if_neg hm]
    rw [if_neg hm] at hfull
    have hzeroTerm : stdAddChar (m * (0 : ZMod N)) = 1 := by simp
    rw [hfull, hzeroTerm] at hsplit
    linear_combination hsplit

/-- Omitting zero makes the aggregate collision equal its complete-nonzero
subset restriction. -/
theorem multiplicativeCollision_eq_fullNonzeroResidueSet [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N)
    (hzero : word 0 = none) :
    multiplicativeCollision word a =
      subsetCollision word (fullNonzeroResidueSet N) a := by
  classical
  unfold multiplicativeCollision subsetCollision fullNonzeroResidueSet
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun r : ZMod N => sameBinKernel word r (a * r))
    (Finset.mem_univ 0)
  have hkernel : sameBinKernel word 0 (a * 0) = 0 := by
    simp [sameBinKernel_eq_indicator, hzero]
  rw [hkernel, add_zero] at hsplit
  exact hsplit.symm

/-- For the complete nonzero field, the two-dimensional individual-orbit
readout collapses exactly to the one-line multiplicative slice. -/
theorem fullNonzero_orbit_formula_collapses_to_slice [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hzero : word 0 = none) (hinv : a * aInv = 1) :
    ((N : ℂ)⁻¹) ^ 2 * ∑ k : ZMod N, ∑ k' : ZMod N,
        crossSpectrum word k k' *
          subsetExponential (fullNonzeroResidueSet N) (k + a * k') =
      (N : ℂ)⁻¹ * ∑ k : ZMod N,
        crossSpectrum word k (-aInv * k) := by
  calc
    ((N : ℂ)⁻¹) ^ 2 * ∑ k : ZMod N, ∑ k' : ZMod N,
          crossSpectrum word k k' *
            subsetExponential (fullNonzeroResidueSet N) (k + a * k') =
        subsetCollision word (fullNonzeroResidueSet N) a :=
      (subsetCollision_formula word (fullNonzeroResidueSet N) a).symm
    _ = multiplicativeCollision word a :=
      (multiplicativeCollision_eq_fullNonzeroResidueSet word a hzero).symm
    _ = (N : ℂ)⁻¹ * ∑ k : ZMod N,
        crossSpectrum word k (-aInv * k) :=
      multiplicative_slice word a aInv hinv

/-! ## Singleton partitions and the decimal-seven field spectrum -/

/-- If precisely zero is omitted and active labels are injective, the
cross-spectrum is the additive exponential sum over all nonzero residues. -/
theorem crossSpectrum_eq_fullNonzero_exponential_of_injective [NeZero N]
    (word : ZMod N → Option (Fin κ))
    (hassigned : ∀ r, word r ≠ none ↔ r ≠ 0)
    (hinjective : ∀ {r s}, word r = word s → word r ≠ none → r = s)
    (k k' : ZMod N) :
    crossSpectrum word k k' =
      subsetExponential (fullNonzeroResidueSet N) (-(k + k')) := by
  classical
  have hkernel (r s : ZMod N) :
      sameBinKernel word r s = if r = s ∧ r ≠ 0 then 1 else 0 := by
    rw [sameBinKernel_eq_indicator]
    by_cases hmatch : word r = word s ∧ word r ≠ none
    · have hrs := hinjective hmatch.1 hmatch.2
      rw [if_pos hmatch, if_pos ⟨hrs, (hassigned r).mp hmatch.2⟩]
    · by_cases hrs : r = s ∧ r ≠ 0
      · have hactive : word r ≠ none := (hassigned r).mpr hrs.2
        exact False.elim (hmatch ⟨by rw [hrs.1], hactive⟩)
      · simp [hmatch, hrs]
  rw [crossSpectrum_eq_kernel_transform]
  simp_rw [hkernel]
  unfold subsetExponential fullNonzeroResidueSet
  calc
    (∑ r : ZMod N, ∑ s : ZMod N,
        (if r = s ∧ r ≠ 0 then 1 else 0) *
          stdAddChar (-(r * k) - s * k')) =
      ∑ r : ZMod N,
        if r ≠ 0 then stdAddChar (-(r * k) - r * k') else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          by_cases hr : r ≠ 0
          · simp [hr]
          · simp [hr]
    _ = ∑ r ∈ Finset.univ.erase 0,
        stdAddChar (-(k + k') * r) := by
          have herase : (Finset.univ.erase 0 : Finset (ZMod N)) =
              Finset.univ.filter fun r => r ≠ 0 := by
            ext r
            simp
          rw [herase, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro r _
          by_cases hr : r = 0
          · subst r
            simp
          · simp [hr]
            congr 1
            ring

/-- The exact decimal prime-seven cross-spectrum has value six on the
antidiagonal and minus one everywhere else. -/
theorem decimalSevenCrossSpectrum_certificate (k k' : ZMod 7) :
    crossSpectrum
        (primeDigitWord 10 7 (by norm_num) (by norm_num)) k k' =
      if k + k' = 0 then (6 : ℂ) else (-1 : ℂ) := by
  have hdp : DigitPartitioning 10 7 :=
    (digitPartitioning_iff (b := 10) (p := 7)
      (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [crossSpectrum_eq_fullNonzero_exponential_of_injective]
  · rw [fullNonzeroResidue_exponential]
    by_cases hsum : k + k' = 0
    · simp [hsum]
    · have hneg : -(k + k') ≠ 0 := neg_ne_zero.mpr hsum
      rw [if_neg hneg, if_neg hsum]
  · intro r
    by_cases hr : r = 0
    · subst r
      simp [primeDigitWord_zero]
    · simp [primeDigitWord, hr]
  · intro r s heq hrAssigned
    obtain ⟨d, hrd⟩ : ∃ d,
        primeDigitWord 10 7 (by norm_num) (by norm_num) r = some d := by
      cases hr : primeDigitWord 10 7 (by norm_num) (by norm_num) r with
      | none => exact False.elim (hrAssigned hr)
      | some d => exact ⟨d, rfl⟩
    have hsd : primeDigitWord 10 7 (by norm_num) (by norm_num) s = some d := by
      rw [← heq]
      exact hrd
    have hrData := (primeDigitWord_some_iff (by norm_num) (by norm_num)).mp hrd
    have hsData := (primeDigitWord_some_iff (by norm_num) (by norm_num)).mp hsd
    apply ZMod.val_injective
    exact hdp (ZMod.val_pos.mpr hrData.1) r.val_lt
      (ZMod.val_pos.mpr hsData.1) s.val_lt
      (hrData.2.trans hsData.2.symm)


end NField.Alignment.AutocorrelationFormula
