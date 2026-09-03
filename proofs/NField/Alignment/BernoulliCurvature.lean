/-
Author: Alexander S. Petty
-/

import NField.Alignment.PrimitiveAdditiveConvolution
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Bernoulli curvature on reduced residue classes

The exact finite evaluation of the second Bernoulli polynomial over a
reduced residue system.  The proof partitions every rational grid point by
its reduced denominator, evaluates the complete Bernoulli grid, and applies
finite Möbius inversion.
-/

namespace NField.Alignment.BernoulliCurvature

open scoped BigOperators ArithmeticFunction.Moebius
open NField.Alignment.PrimitiveAdditiveConvolution

/-- The second Bernoulli polynomial evaluated at the rational grid point
`a / k`. -/
def rationalBernoulliTwo (a k : ℕ) : ℚ :=
  (a : ℚ) ^ 2 / (k : ℚ) ^ 2 - (a : ℚ) / (k : ℚ) + 1 / 6

/-- The complete `k`-grid sum of the second Bernoulli polynomial. -/
def completeBernoulliTwoSum (k : ℕ) : ℚ :=
  ∑ a ∈ Finset.range k, rationalBernoulliTwo a k

/-- The same sum restricted to the reduced residue system modulo `k`.
For `k = 1` this includes the unique residue zero. -/
def reducedBernoulliTwoSum (k : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range k).filter fun a ↦ a.Coprime k,
    rationalBernoulliTwo a k

/-- The reduced-residue sum after multiplication by a natural coefficient. -/
def multipliedReducedBernoulliTwoSum (c k : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range k).filter fun a ↦ a.Coprime k,
    rationalBernoulliTwo ((c * a) % k) k

/-- Intrinsic unit-group presentation of the reduced Bernoulli sum. -/
noncomputable def unitBernoulliTwoSum (k : ℕ) [NeZero k] : ℚ :=
  ∑ u : (ZMod k)ˣ, rationalBernoulliTwo u.val.val k

theorem reducedResidues_eq_Ico {k : ℕ} (hk : 2 ≤ k) :
    (Finset.range k).filter (fun a ↦ a.Coprime k) =
      (Finset.Ico 1 k).filter (fun a ↦ a.Coprime k) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · intro ha
    refine ⟨⟨?_, ha.1⟩, ha.2⟩
    by_contra hnot
    have ha0 : a = 0 := by omega
    subst a
    simp at ha
    omega
  · intro ha
    exact ⟨ha.1.2, ha.2⟩

theorem reducedBernoulliTwoSum_eq_units
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) :
    reducedBernoulliTwoSum k = unitBernoulliTwoSum k := by
  letI : Fact (1 < k) := ⟨by omega⟩
  have hreindex := (primitiveNatEquiv k hk).sum_comp
    (fun u : (ZMod k)ˣ ↦ rationalBernoulliTwo u.val.val k)
  unfold unitBernoulliTwoSum
  rw [← hreindex]
  unfold reducedBernoulliTwoSum
  rw [reducedResidues_eq_Ico hk]
  rw [Finset.sum_subtype
    ((Finset.Ico 1 k).filter fun a ↦ a.Coprime k) (by intro; rfl)]
  apply Finset.sum_congr rfl
  intro a _ha
  simp [primitiveNatEquiv, ZMod.coe_unitOfCoprime,
    ZMod.val_natCast, Nat.mod_eq_of_lt
      (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]

/-- A unit multiplier merely permutes the reduced residues. -/
theorem multipliedReducedBernoulliTwoSum_eq
    {c k : ℕ} [NeZero k] (hk : 2 ≤ k) (hc : c.Coprime k) :
    multipliedReducedBernoulliTwoSum c k = reducedBernoulliTwoSum k := by
  letI : Fact (1 < k) := ⟨by omega⟩
  let cu : (ZMod k)ˣ := ZMod.unitOfCoprime c hc
  let e := primitiveNatEquiv k hk
  have hsubtype :
    multipliedReducedBernoulliTwoSum c k =
        ∑ a : ↑((Finset.Ico 1 k).filter fun a ↦ a.Coprime k),
          rationalBernoulliTwo ((c * a.val) % k) k := by
    unfold multipliedReducedBernoulliTwoSum
    rw [reducedResidues_eq_Ico hk]
    rw [Finset.sum_subtype
      ((Finset.Ico 1 k).filter fun a ↦ a.Coprime k) (by intro; rfl)]
  have hpoint : ∀ a : ↑((Finset.Ico 1 k).filter fun a ↦ a.Coprime k),
      rationalBernoulliTwo ((c * a.val) % k) k =
        rationalBernoulliTwo (cu * e a).val.val k := by
    intro a
    congr 1
    simp [cu, e, primitiveNatEquiv, ZMod.coe_unitOfCoprime,
      ZMod.val_mul, ZMod.val_natCast,
      Nat.mod_eq_of_lt
        (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]
  calc
    multipliedReducedBernoulliTwoSum c k =
        ∑ a : ↑((Finset.Ico 1 k).filter fun a ↦ a.Coprime k),
          rationalBernoulliTwo (cu * e a).val.val k := by
            rw [hsubtype]
            apply Finset.sum_congr rfl
            intro a _ha
            exact hpoint a
    _ = ∑ u : (ZMod k)ˣ, rationalBernoulliTwo (cu * u).val.val k := by
          exact (e.sum_comp
            (fun u : (ZMod k)ˣ ↦ rationalBernoulliTwo (cu * u).val.val k))
    _ = ∑ u : (ZMod k)ˣ, rationalBernoulliTwo u.val.val k := by
      let ecu : (ZMod k)ˣ ≃ (ZMod k)ˣ := Equiv.mulLeft cu
      exact ecu.sum_comp
        (fun u : (ZMod k)ˣ ↦ rationalBernoulliTwo u.val.val k)
    _ = reducedBernoulliTwoSum k :=
      (reducedBernoulliTwoSum_eq_units hk).symm

theorem sum_range_cast (n : ℕ) :
    (∑ a ∈ Finset.range n, (a : ℚ)) =
      (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sum_range_cast_sq (n : ℕ) :
    (∑ a ∈ Finset.range n, (a : ℚ) ^ 2) =
      (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The complete multiplication formula for `B₂` on a rational grid. -/
theorem completeBernoulliTwoSum_closed {k : ℕ} (hk : 0 < k) :
    completeBernoulliTwoSum k = 1 / (6 * (k : ℚ)) := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold completeBernoulliTwoSum rationalBernoulliTwo
  calc
    (∑ a ∈ Finset.range k,
        ((a : ℚ) ^ 2 / (k : ℚ) ^ 2 - (a : ℚ) / (k : ℚ) + 1 / 6)) =
        (∑ a ∈ Finset.range k, (a : ℚ) ^ 2) / (k : ℚ) ^ 2 -
          (∑ a ∈ Finset.range k, (a : ℚ)) / (k : ℚ) +
          (k : ℚ) / 6 := by
            simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_div]
            simp
            ring
    _ = _ := by
      rw [sum_range_cast_sq, sum_range_cast]
      field_simp [hkQ]
      ring

/-- Pairs consisting of a divisor `d | k` and a reduced numerator below
`d`. -/
def reducedFractionPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (k.divisors.product (Finset.range k)).filter fun da ↦
    da.2 < da.1 ∧ da.2.Coprime da.1

/-- Reduce `a / k` by its gcd. -/
def reduceGridPoint (k a : ℕ) : ℕ × ℕ :=
  let g := a.gcd k
  (k / g, a / g)

theorem reduceGridPoint_mem {k a : ℕ} (hk : 0 < k)
    (ha : a ∈ Finset.range k) :
    reduceGridPoint k a ∈ reducedFractionPairs k := by
  have hak : a < k := Finset.mem_range.mp ha
  let g := a.gcd k
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right a hk
  have hga : g ∣ a := Nat.gcd_dvd_left a k
  have hgk : g ∣ k := Nat.gcd_dvd_right a k
  have hgk_le : g ≤ k := Nat.gcd_le_right a hk
  have hdpos : 0 < k / g := Nat.div_pos hgk_le hgpos
  have hbd : a / g < k / g :=
    (Nat.div_lt_div_right hgpos.ne' hga hgk).2 hak
  have hcop : (a / g).Coprime (k / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hdk : k / g ∣ k :=
    ⟨g, (Nat.div_mul_cancel hgk).symm⟩
  unfold reduceGridPoint reducedFractionPairs
  dsimp [g]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hdk, hk.ne'⟩,
    Finset.mem_range.mpr (hbd.trans_le (Nat.div_le_self k g))⟩, hbd, hcop⟩

theorem reduceGridPoint_injective {k : ℕ} (hk : 0 < k) :
    Set.InjOn (reduceGridPoint k) (↑(Finset.range k) : Set ℕ) := by
  intro a _ha b _hb hab
  let ga := a.gcd k
  let gb := b.gcd k
  have hgak : ga ∣ k := Nat.gcd_dvd_right a k
  have hgbk : gb ∣ k := Nat.gcd_dvd_right b k
  have hgaa : ga ∣ a := Nat.gcd_dvd_left a k
  have hgbb : gb ∣ b := Nat.gcd_dvd_left b k
  have hga : 0 < ga := Nat.gcd_pos_of_pos_right a hk
  have hgb : 0 < gb := Nat.gcd_pos_of_pos_right b hk
  have hd : k / ga = k / gb := congrArg Prod.fst hab
  have hg : ga = gb := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < k / ga from
      Nat.div_pos (Nat.gcd_le_right a hk) hga)
    calc
      k / ga * ga = k := Nat.div_mul_cancel hgak
      _ = k / gb * gb := (Nat.div_mul_cancel hgbk).symm
      _ = k / ga * gb := by rw [hd]
  have hnum : a / ga = b / gb := congrArg Prod.snd hab
  have hnum' : a / gb = b / gb := by simpa [hg] using hnum
  calc
    a = ga * (a / ga) := (Nat.mul_div_cancel' hgaa).symm
    _ = gb * (b / gb) := by rw [hg, hnum']
    _ = b := Nat.mul_div_cancel' hgbb

theorem reduceGridPoint_surjective {k : ℕ} (hk : 0 < k) :
    ∀ da ∈ reducedFractionPairs k, ∃ a, ∃ _ : a ∈ Finset.range k,
      reduceGridPoint k a = da := by
  intro da hda
  rcases da with ⟨d,b⟩
  unfold reducedFractionPairs at hda
  have hbase := (Finset.mem_filter.mp hda).1
  have hpred := (Finset.mem_filter.mp hda).2
  have hdk : d ∣ k := (Nat.mem_divisors.mp (Finset.mem_product.mp hbase).1).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdk hk
  rcases hpred with ⟨hbd,hcop⟩
  let g := k / d
  let a := g * b
  have hgpos : 0 < g := Nat.div_pos (Nat.le_of_dvd hk hdk) hdpos
  have hgd : g * d = k := by
    dsimp [g]
    exact Nat.div_mul_cancel hdk
  have hak : a < k := by
    dsimp [a]
    rw [← hgd]
    exact (Nat.mul_lt_mul_left hgpos).2 hbd
  have hgcd : a.gcd k = g := by
    dsimp [a]
    rw [← hgd, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  refine ⟨a, Finset.mem_range.mpr hak, ?_⟩
  have hkdiv : k / g = d := by rw [← hgd, Nat.mul_div_cancel_left d hgpos]
  have hadiv : a / g = b := by
    dsimp [a]
    rw [Nat.mul_div_cancel_left b hgpos]
  simp [reduceGridPoint, hgcd, hkdiv, hadiv]

theorem rationalBernoulliTwo_reduce {k a : ℕ} (hk : 0 < k)
    (_ha : a ∈ Finset.range k) :
    rationalBernoulliTwo a k =
      rationalBernoulliTwo (reduceGridPoint k a).2
        (reduceGridPoint k a).1 := by
  let g := a.gcd k
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right a hk
  have hga : g ∣ a := Nat.gcd_dvd_left a k
  have hgk : g ∣ k := Nat.gcd_dvd_right a k
  have hka : g * (a / g) = a := Nat.mul_div_cancel' hga
  have hkk : g * (k / g) = k := Nat.mul_div_cancel' hgk
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hkaQ : (a : ℚ) = (g : ℚ) * ((a / g : ℕ) : ℚ) := by
    exact_mod_cast hka.symm
  have hkkQ : (k : ℚ) = (g : ℚ) * ((k / g : ℕ) : ℚ) := by
    exact_mod_cast hkk.symm
  change rationalBernoulliTwo a k = rationalBernoulliTwo (a / g) (k / g)
  unfold rationalBernoulliTwo
  rw [hkaQ, hkkQ]
  field_simp [hgQ]

theorem complete_eq_reduced_divisor_sum {k : ℕ} (hk : 0 < k) :
    completeBernoulliTwoSum k =
      ∑ d ∈ k.divisors, reducedBernoulliTwoSum d := by
  unfold completeBernoulliTwoSum
  calc
    (∑ a ∈ Finset.range k, rationalBernoulliTwo a k) =
        ∑ da ∈ reducedFractionPairs k,
          rationalBernoulliTwo da.2 da.1 := by
            apply Finset.sum_bij (fun a _ ↦ reduceGridPoint k a)
            · exact fun a ha ↦ reduceGridPoint_mem hk ha
            · intro a ha b hb
              exact reduceGridPoint_injective hk ha hb
            · exact reduceGridPoint_surjective hk
            · intro a ha
              exact rationalBernoulliTwo_reduce hk ha
    _ = _ := by
      unfold reducedFractionPairs reducedBernoulliTwoSum
      rw [Finset.sum_filter]
      rw [show
        (∑ da ∈ k.divisors.product (Finset.range k),
          if da.2 < da.1 ∧ da.2.Coprime da.1 then
            rationalBernoulliTwo da.2 da.1 else 0) =
          ∑ d ∈ k.divisors, ∑ a ∈ Finset.range k,
            if a < d ∧ a.Coprime d then rationalBernoulliTwo a d else 0 by
              exact Finset.sum_product _ _ _]
      apply Finset.sum_congr rfl
      intro d hd
      have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
      have hdle : d ≤ k := Nat.le_of_dvd hk hdk
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext a
        simp
        omega
      · intro a _ha
        rfl

/-- Exact Möbius evaluation of the reduced Bernoulli sum. -/
theorem reducedBernoulliTwoSum_eq_moebius {k : ℕ} (hk : 0 < k) :
    reducedBernoulliTwoSum k =
      ∑ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℚ) *
          (1 / (6 * ((k / d : ℕ) : ℚ))) := by
  have hinversion :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (R := ℚ)
      (f := reducedBernoulliTwoSum)
      (g := completeBernoulliTwoSum)).mp (by
        intro n hn
        exact (complete_eq_reduced_divisor_sum hn).symm) k hk
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun d q ↦ (ArithmeticFunction.moebius d : ℚ) *
      completeBernoulliTwoSum q)] at hinversion
  rw [← hinversion]
  apply Finset.sum_congr rfl
  intro d hd
  have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
  have hq : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk hdk)
    (Nat.pos_of_dvd_of_pos hdk hk)
  rw [completeBernoulliTwoSum_closed hq]

/-- The divisor form used in the manuscript's curvature term. -/
theorem reducedBernoulliTwoSum_eq_weighted_moebius {k : ℕ} (hk : 0 < k) :
    reducedBernoulliTwoSum k =
      (1 / (6 * (k : ℚ))) *
        ∑ d ∈ k.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (d : ℚ) := by
  rw [reducedBernoulliTwoSum_eq_moebius hk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdk hk
  have hqpos : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk hdk) hdpos
  have hprod : (k / d) * d = k := Nat.div_mul_cancel hdk
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hqQ : ((k / d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hprodQ : ((k / d : ℕ) : ℚ) * (d : ℚ) = (k : ℚ) := by
    exact_mod_cast hprod
  rw [← hprodQ]
  field_simp [hdQ, hqQ]

/-- The arithmetic function whose value is the weighted Möbius divisor
sum. -/
noncomputable def weightedMoebiusArithmetic : ArithmeticFunction ℚ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℚ).pmul
    (ArithmeticFunction.id : ArithmeticFunction ℚ)) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℚ)

theorem weightedMoebiusArithmetic_apply (k : ℕ) :
    weightedMoebiusArithmetic k =
      ∑ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℚ) * (d : ℚ) := by
  unfold weightedMoebiusArithmetic
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rfl

theorem weightedMoebiusArithmetic_multiplicative :
    weightedMoebiusArithmetic.IsMultiplicative := by
  unfold weightedMoebiusArithmetic
  exact
    (ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
      ArithmeticFunction.isMultiplicative_id.natCast).mul
        ArithmeticFunction.isMultiplicative_zeta.natCast

theorem weightedMoebiusArithmetic_prime_pow
    {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    weightedMoebiusArithmetic (p ^ e) = 1 - (p : ℚ) := by
  have hsum : ∀ n : ℕ, 0 < n →
      (∑ i ∈ Finset.range (n + 1),
        (ArithmeticFunction.moebius (p ^ i) : ℚ) * ((p ^ i : ℕ) : ℚ)) =
          1 - (p : ℚ) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hnzero : n = 0
        · subst n
          norm_num [Finset.sum_range_succ,
            ArithmeticFunction.moebius_apply_one,
            ArithmeticFunction.moebius_apply_prime hp]
          ring
        · rw [Finset.sum_range_succ, ih (Nat.pos_of_ne_zero hnzero)]
          have hpow : ArithmeticFunction.moebius (p ^ (n + 1)) = 0 := by
            rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
            simp [hnzero]
          rw [hpow]
          simp
  rw [weightedMoebiusArithmetic_apply,
    Nat.sum_divisors_prime_pow hp]
  exact hsum e he

/-- The product over the distinct prime divisors appearing in the paper. -/
noncomputable def bernoulliPrimeFactorProduct (k : ℕ) : ℚ :=
  ∏ p ∈ k.primeFactors, (1 - (p : ℚ))

theorem abs_bernoulliPrimeFactorProduct_le {k : ℕ} (hk : 0 < k) :
    |bernoulliPrimeFactorProduct k| ≤ (k : ℚ) := by
  have hprodNat : ∏ p ∈ k.primeFactors, p ≤ k :=
    Nat.le_of_dvd hk (Nat.prod_primeFactors_dvd k)
  unfold bernoulliPrimeFactorProduct
  rw [Finset.abs_prod]
  calc
    (∏ p ∈ k.primeFactors, |1 - (p : ℚ)|) =
        ∏ p ∈ k.primeFactors, ((p : ℚ) - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
          rw [abs_of_nonpos]
          · ring
          · exact sub_nonpos.mpr (by exact_mod_cast hpprime.one_le)
    _ ≤ ∏ p ∈ k.primeFactors, (p : ℚ) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
            exact sub_nonneg.mpr (by exact_mod_cast hpprime.one_le)
          · intro p hp
            norm_num
    _ = ((∏ p ∈ k.primeFactors, p : ℕ) : ℚ) := by push_cast; rfl
    _ ≤ (k : ℚ) := by exact_mod_cast hprodNat

/-- The weighted Möbius divisor sum is exactly the prime-factor product. -/
theorem weightedMoebiusSum_eq_primeFactorProduct {k : ℕ} (hk : 0 < k) :
    (∑ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℚ) * (d : ℚ)) =
      bernoulliPrimeFactorProduct k := by
  rw [← weightedMoebiusArithmetic_apply]
  induction k using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [weightedMoebiusArithmetic, bernoulliPrimeFactorProduct]
  | prime_pow p e hp he =>
      rw [weightedMoebiusArithmetic_prime_pow hp he]
      simp [bernoulliPrimeFactorProduct,
        Nat.primeFactors_prime_pow he.ne' hp]
  | coprime a b ha hb hab hia hib =>
      rw [weightedMoebiusArithmetic_multiplicative.map_mul_of_coprime hab,
        bernoulliPrimeFactorProduct, hab.primeFactors_mul,
        Finset.prod_union hab.disjoint_primeFactors,
        ← bernoulliPrimeFactorProduct, ← bernoulliPrimeFactorProduct,
        hia (by omega), hib (by omega)]

/-- Exact reduced-residue Bernoulli evaluation in the manuscript's displayed
prime-factor form. -/
theorem reducedBernoulliTwoSum_closed {k : ℕ} (hk : 0 < k) :
    reducedBernoulliTwoSum k =
      bernoulliPrimeFactorProduct k / (6 * (k : ℚ)) := by
  rw [reducedBernoulliTwoSum_eq_weighted_moebius hk,
    weightedMoebiusSum_eq_primeFactorProduct hk]
  ring

theorem floorQuotientSum_le_harmonic (N : ℕ) :
    (∑ k ∈ Finset.Icc 2 N, ((N / k : ℕ) : ℚ)) ≤
      (N : ℚ) * harmonic N := by
  calc
    (∑ k ∈ Finset.Icc 2 N, ((N / k : ℕ) : ℚ)) ≤
        ∑ k ∈ Finset.Icc 2 N, (N : ℚ) * (k : ℚ)⁻¹ := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := by
            have := (Finset.mem_Icc.mp hk).1
            omega
          have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
          apply (le_mul_inv_iff₀ hkQ).2
          have hmul := Nat.div_mul_le_self N k
          exact_mod_cast hmul
    _ = (N : ℚ) * ∑ k ∈ Finset.Icc 2 N, (k : ℚ)⁻¹ := by
          rw [Finset.mul_sum]
    _ ≤ (N : ℚ) * ∑ k ∈ Finset.Icc 1 N, (k : ℚ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            simp only [Finset.mem_Icc] at hk ⊢
            omega
          · intro k _hk _hnot
            positivity
    _ = (N : ℚ) * harmonic N := by rw [harmonic_eq_sum_Icc]

/-- The manuscript's curvature reservoir before evaluating each reduced
Bernoulli sum. -/
def carrierBernoulliCurvature (p : ℕ) : ℚ :=
  let N := p - 1
  (N : ℚ) / 6 +
    ∑ k ∈ Finset.Icc 2 N,
      ((N / k : ℕ) : ℚ) *
        multipliedReducedBernoulliTwoSum (p ^ 2) k

/-- Closed prime-factor form of the same curvature reservoir. -/
noncomputable def closedCarrierBernoulliCurvature (p : ℕ) : ℚ :=
  let N := p - 1
  (N : ℚ) / 6 +
    ∑ k ∈ Finset.Icc 2 N,
      ((N / k : ℕ) : ℚ) /
        (6 * (k : ℚ)) * bernoulliPrimeFactorProduct k

/-- Manuscript Proposition `Bernoulli-curvature evaluation`, with the actual
carrier multiplier and every reduced-residue sum exposed. -/
theorem bernoulli_curvature_evaluation
    {p : ℕ} (hp : p.Prime) :
    carrierBernoulliCurvature p = closedCarrierBernoulliCurvature p := by
  unfold carrierBernoulliCurvature closedCarrierBernoulliCurvature
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkN : k ≤ p - 1 := (Finset.mem_Icc.mp hk).2
  have hkpos : 0 < k := by omega
  have hkp : k < p := by omega
  letI : NeZero k := ⟨hkpos.ne'⟩
  have hcop : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp hkpos hkp).symm
  rw [multipliedReducedBernoulliTwoSum_eq hk2 hcop,
    reducedBernoulliTwoSum_closed hkpos]
  ring

/-- Explicit harmonic envelope for the curvature reservoir.  This is the
finite inequality behind the manuscript's `N log(2N)` estimate. -/
theorem abs_carrierBernoulliCurvature_le
    {p : ℕ} (hp : p.Prime) :
    |carrierBernoulliCurvature p| ≤
      ((p - 1 : ℕ) : ℚ) / 6 +
        ((p - 1 : ℕ) : ℚ) * harmonic (p - 1) / 6 := by
  rw [bernoulli_curvature_evaluation hp]
  unfold closedCarrierBernoulliCurvature
  dsimp only
  calc
    |((p - 1 : ℕ) : ℚ) / 6 +
        ∑ k ∈ Finset.Icc 2 (p - 1),
          (((p - 1) / k : ℕ) : ℚ) / (6 * (k : ℚ)) *
            bernoulliPrimeFactorProduct k| ≤
        ((p - 1 : ℕ) : ℚ) / 6 +
          ∑ k ∈ Finset.Icc 2 (p - 1),
            |(((p - 1) / k : ℕ) : ℚ) / (6 * (k : ℚ)) *
              bernoulliPrimeFactorProduct k| := by
          calc
            _ ≤ |((p - 1 : ℕ) : ℚ) / 6| +
                |∑ k ∈ Finset.Icc 2 (p - 1),
                  (((p - 1) / k : ℕ) : ℚ) / (6 * (k : ℚ)) *
                    bernoulliPrimeFactorProduct k| := abs_add_le _ _
            _ ≤ _ := by
              rw [abs_of_nonneg (by positivity)]
              gcongr
              exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((p - 1 : ℕ) : ℚ) / 6 +
          (1 / 6 : ℚ) *
            ∑ k ∈ Finset.Icc 2 (p - 1),
              (((p - 1) / k : ℕ) : ℚ) := by
          have hsum :
              (∑ k ∈ Finset.Icc 2 (p - 1),
                |(((p - 1) / k : ℕ) : ℚ) / (6 * (k : ℚ)) *
                  bernoulliPrimeFactorProduct k|) ≤
                (1 / 6 : ℚ) *
                  ∑ k ∈ Finset.Icc 2 (p - 1),
                    (((p - 1) / k : ℕ) : ℚ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro k hk
            have hkpos : 0 < k := by
              have := (Finset.mem_Icc.mp hk).1
              omega
            have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
            rw [abs_mul, abs_of_nonneg (by positivity :
              (0 : ℚ) ≤ (((p - 1) / k : ℕ) : ℚ) / (6 * (k : ℚ)))]
            calc
              (((p - 1) / k : ℕ) : ℚ) / (6 * (k : ℚ)) *
                  |bernoulliPrimeFactorProduct k| ≤
                (((p - 1) / k : ℕ) : ℚ) / (6 * (k : ℚ)) *
                  (k : ℚ) := by
                    gcongr
                    exact abs_bernoulliPrimeFactorProduct_le hkpos
              _ = (1 / 6 : ℚ) * (((p - 1) / k : ℕ) : ℚ) := by
                    field_simp [ne_of_gt hkQ]
          linarith
    _ ≤ ((p - 1 : ℕ) : ℚ) / 6 +
          (1 / 6 : ℚ) *
            (((p - 1 : ℕ) : ℚ) * harmonic (p - 1)) := by
          gcongr
          exact floorQuotientSum_le_harmonic (p - 1)
    _ = _ := by ring

end NField.Alignment.BernoulliCurvature
