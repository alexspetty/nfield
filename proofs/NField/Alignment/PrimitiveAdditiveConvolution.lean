/-
Author: Alexander S. Petty
-/

import NField.Alignment.ComplementaryPartition

/-!
# Primitive additive convolution

The common-scale decomposition of an additive Dedekind anti-diagonal.  Every
partition `X = k + (X-k)` is divided by `gcd(k,X)`, the common coefficient
scale is cancelled on the prime-square carrier, and finite Möbius inversion
recovers the primitive packet.
-/

namespace NField.Alignment.PrimitiveAdditiveConvolution

open scoped BigOperators
open NField.Alignment.ComplementaryPartition
open NField.Alignment.RademacherThreeTerm
open NField.Alignment.PrimeSquareReducedRatio
def additiveIndices (X : ℕ) : Finset ℕ := Finset.Ico 1 X

def scaledPrimitivePartitions (X : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  ((Finset.range (X+1)).product
    ((Finset.range (X+1)).product (Finset.range (X+1)))).filter fun r =>
      0 < r.1 ∧ 0 < r.2.1 ∧ r.2.1 < r.1 ∧
        r.2.1.Coprime r.1 ∧ 0 < r.2.2 ∧ r.2.2 * r.1 = X

def reducedPartition (X k : ℕ) : ℕ × (ℕ × ℕ) :=
  let g := k.gcd X
  (X/g, (k/g, g))

theorem reducedPartition_mem {X k : ℕ} (hk : k ∈ additiveIndices X) :
    reducedPartition X k ∈ scaledPrimitivePartitions X := by
  have hkI := Finset.mem_Ico.mp hk
  have hkpos : 0 < k := hkI.1
  have hkX : k < X := hkI.2
  let g := k.gcd X
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left X hkpos
  have hgk : g ∣ k := Nat.gcd_dvd_left k X
  have hgX : g ∣ X := Nat.gcd_dvd_right k X
  have hgk_le : g ≤ k := Nat.gcd_le_left X hkpos
  have hgX_le : g ≤ X := Nat.gcd_le_right k (by omega : 0 < X)
  have hapos : 0 < k/g := Nat.div_pos hgk_le hgpos
  have hdpos : 0 < X/g := Nat.div_pos hgX_le hgpos
  have had : k/g < X/g :=
    (Nat.div_lt_div_right hgpos.ne' hgk hgX).2 hkX
  have hcop : (k/g).Coprime (X/g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hscale : g * (X/g) = X := Nat.mul_div_cancel' hgX
  have hdle : X/g < X+1 := Nat.lt_succ_of_le (Nat.div_le_self X g)
  have hale : k/g < X+1 := had.trans hdle
  have hgle : g < X+1 := Nat.lt_succ_of_le hgX_le
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr hdle,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hale,
        Finset.mem_range.mpr hgle⟩⟩
  · change 0 < X/g ∧ 0 < k/g ∧ k/g < X/g ∧
      (k/g).Coprime (X/g) ∧ 0 < g ∧ g*(X/g)=X
    exact ⟨hdpos,hapos,had,hcop,hgpos,hscale⟩

theorem reducedPartition_injective {X : ℕ} :
    Set.InjOn (reducedPartition X) (↑(additiveIndices X) : Set ℕ) := by
  intro k _ l _ heq
  let gk := k.gcd X
  let gl := l.gcd X
  have hgk : gk ∣ k := Nat.gcd_dvd_left k X
  have hgl : gl ∣ l := Nat.gcd_dvd_left l X
  have haeq : k/gk = l/gl := congrArg (fun r => r.2.1) heq
  have hgeq : gk = gl := congrArg (fun r => r.2.2) heq
  have haeq' : k/gl = l/gl := by simpa [hgeq] using haeq
  calc
    k = gk * (k/gk) := (Nat.mul_div_cancel' hgk).symm
    _ = gl * (k/gl) := by rw [hgeq]
    _ = gl * (l/gl) := by rw [haeq']
    _ = l := Nat.mul_div_cancel' hgl

theorem reducedPartition_surjective {X : ℕ} :
    ∀ r ∈ scaledPrimitivePartitions X, ∃ k, ∃ _ : k ∈ additiveIndices X,
      reducedPartition X k = r := by
  intro r hr
  rcases r with ⟨d,a,g⟩
  have hpred := (Finset.mem_filter.mp hr).2
  change 0 < d ∧ 0 < a ∧ a < d ∧ a.Coprime d ∧
    0 < g ∧ g*d=X at hpred
  rcases hpred with ⟨hdpos,hapos,had,hcop,hgpos,hgd⟩
  let k := g*a
  have hkpos : 0 < k := Nat.mul_pos hgpos hapos
  have hkX : k < X := by
    rw [← hgd]
    exact (Nat.mul_lt_mul_left hgpos).2 had
  have hkmem : k ∈ additiveIndices X := Finset.mem_Ico.mpr ⟨hkpos,hkX⟩
  refine ⟨k,hkmem,?_⟩
  have hgcd : k.gcd X = g := by
    dsimp [k]
    rw [← hgd, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  have hXdiv : X/g=d := by rw [← hgd, Nat.mul_div_cancel_left d hgpos]
  have hkdiv : k/g=a := by dsimp [k]; rw [Nat.mul_div_cancel_left a hgpos]
  simp [reducedPartition, hgcd, hXdiv, hkdiv]

noncomputable def fullAdditiveConvolution (p X : ℕ) : ℚ :=
  ∑ k ∈ additiveIndices X,
    arithmeticCoefficientDedekindTerm k (X-k) (p^2)

noncomputable def scaledAdditiveConvolution (p X : ℕ) : ℚ :=
  ∑ r ∈ scaledPrimitivePartitions X,
    arithmeticCoefficientDedekindTerm r.2.1 (r.1-r.2.1) (p^2)

theorem full_eq_scaled {p X : ℕ} (hp : p.Prime) (hXp : X < p) :
    fullAdditiveConvolution p X = scaledAdditiveConvolution p X := by
  classical
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold fullAdditiveConvolution scaledAdditiveConvolution
  apply Finset.sum_bij (fun k _ => reducedPartition X k)
  · exact fun k hk => reducedPartition_mem hk
  · intro k hk l hl
    exact reducedPartition_injective hk hl
  · exact reducedPartition_surjective
  · intro k hk
    have hkI := Finset.mem_Ico.mp hk
    have hkpos : 0 < k := hkI.1
    have hkX : k < X := hkI.2
    let g := k.gcd X
    let d := X/g
    let a := k/g
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left X hkpos
    have hgk : g ∣ k := Nat.gcd_dvd_left k X
    have hgX : g ∣ X := Nat.gcd_dvd_right k X
    have hgk_le : g ≤ k := Nat.gcd_le_left X hkpos
    have hgX_le : g ≤ X := Nat.gcd_le_right k (by omega : 0 < X)
    have hapos : 0 < a := Nat.div_pos hgk_le hgpos
    have hdpos : 0 < d := Nat.div_pos hgX_le hgpos
    have had : a < d :=
      (Nat.div_lt_div_right hgpos.ne' hgk hgX).2 hkX
    have hbpos : 0 < d-a := Nat.sub_pos_of_lt had
    have hka : g*a=k := Nat.mul_div_cancel' hgk
    have hXd : g*d=X := Nat.mul_div_cancel' hgX
    have hsub : X-k = g*(d-a) := by
      rw [← hXd, ← hka, Nat.mul_sub_left_distrib]
    have hglt : g < p := (hgk_le.trans_lt hkX).trans hXp
    have halt : a < p := had.trans ((Nat.div_le_self X g).trans_lt hXp)
    have hdlt : d < p := (Nat.div_le_self X g).trans_lt hXp
    have hblt : d-a < p := (Nat.sub_lt hdpos hapos).trans hdlt
    have hgP : g.Coprime (p^2) := smallNatUnit_coprime hp hgpos hglt
    have haP : a.Coprime (p^2) := smallNatUnit_coprime hp hapos halt
    have hbP : (d-a).Coprime (p^2) := smallNatUnit_coprime hp hbpos hblt
    change arithmeticCoefficientDedekindTerm k (X-k) (p^2) =
      arithmeticCoefficientDedekindTerm
        (reducedPartition X k).2.1
        ((reducedPartition X k).1-(reducedPartition X k).2.1) (p^2)
    change arithmeticCoefficientDedekindTerm k (X-k) (p^2) =
      arithmeticCoefficientDedekindTerm a (d-a) (p^2)
    have hsub' : X - g*a = g*(d-a) := by rw [hka]; exact hsub
    rw [← hka, hsub']
    exact coefficient_common_scale hgP haP hbP

def primitivePartitionPairs (X : ℕ) : Finset (ℕ×ℕ) :=
  (X.divisors.product (Finset.range (X+1))).filter fun da =>
    0 < da.2 ∧ da.2 < da.1 ∧ da.2.Coprime da.1

noncomputable def primitiveAdditiveConvolution (p d : ℕ) : ℚ :=
  ∑ a ∈ (Finset.Ico 1 d).filter fun a => a.Coprime d,
    arithmeticCoefficientDedekindTerm a (d-a) (p^2)

theorem scaled_eq_pairs {p X : ℕ} (hX : 0 < X) :
    scaledAdditiveConvolution p X =
      ∑ da ∈ primitivePartitionPairs X,
        arithmeticCoefficientDedekindTerm da.2 (da.1-da.2) (p^2) := by
  unfold scaledAdditiveConvolution
  apply Finset.sum_bij (fun r _ => (r.1,r.2.1))
  · intro r hr
    have hp := (Finset.mem_filter.mp hr).2
    rcases r with ⟨d,a,g⟩
    change 0 < d ∧ 0 < a ∧ a < d ∧ a.Coprime d ∧
      0 < g ∧ g*d=X at hp
    rcases hp with ⟨hd,ha,had,hcop,hg,hgd⟩
    have hdvd : d ∣ X := ⟨g, hgd.symm.trans (Nat.mul_comm g d)⟩
    have hdX : d ≤ X := Nat.le_of_dvd hX hdvd
    change (d,a) ∈ primitivePartitionPairs X
    unfold primitivePartitionPairs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,
      Finset.mem_range.mpr (by omega)⟩,
      ha,had,hcop⟩
    exact Nat.mem_divisors.mpr ⟨hdvd,hX.ne'⟩
  · intro r hr s hs heq
    rcases r with ⟨d,a,g⟩
    rcases s with ⟨e,b,h⟩
    have hrp := (Finset.mem_filter.mp hr).2
    have hsp := (Finset.mem_filter.mp hs).2
    change 0 < d ∧ 0 < a ∧ a < d ∧ a.Coprime d ∧
      0 < g ∧ g*d=X at hrp
    change 0 < e ∧ 0 < b ∧ b < e ∧ b.Coprime e ∧
      0 < h ∧ h*e=X at hsp
    have hde : d=e := congrArg Prod.fst heq
    have hab : a=b := congrArg Prod.snd heq
    have hgh : g=h := Nat.eq_of_mul_eq_mul_right hrp.1 (by
      calc
        g*d = X := hrp.2.2.2.2.2
        _ = h*e := hsp.2.2.2.2.2.symm
        _ = h*d := by rw [hde])
    simp [hde,hab,hgh]
  · intro da hda
    rcases da with ⟨d,a⟩
    have hbase := (Finset.mem_filter.mp hda).1
    have hpred := (Finset.mem_filter.mp hda).2
    rcases hpred with ⟨ha,had,hcop⟩
    have hdvd := (Nat.mem_divisors.mp (Finset.mem_product.mp hbase).1).1
    let g := X/d
    have hd : 0 < d := by omega
    have hg : 0 < g := Nat.div_pos (Nat.le_of_dvd hX hdvd) hd
    have hgd : g*d=X := by
      dsimp [g]
      exact Nat.div_mul_cancel hdvd
    have hdX : d ≤ X := Nat.le_of_dvd hX hdvd
    have hgX : g ≤ X := Nat.le_of_dvd hX ⟨d,hgd.symm⟩
    let r : ℕ×(ℕ×ℕ) := (d,(a,g))
    have hr : r ∈ scaledPrimitivePartitions X := by
      change (d,(a,g)) ∈ scaledPrimitivePartitions X
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hdX),
          Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr
                (Nat.lt_succ_of_le ((Nat.le_of_lt had).trans hdX)),
              Finset.mem_range.mpr (Nat.lt_succ_of_le hgX)⟩⟩, ?_⟩
      exact ⟨hd,ha,had,hcop,hg,hgd⟩
    exact ⟨r,hr,rfl⟩
  · intro r hr
    rfl

theorem pairs_eq_divisor_sum {p X : ℕ} (hX : 0 < X) :
    (∑ da ∈ primitivePartitionPairs X,
        arithmeticCoefficientDedekindTerm da.2 (da.1-da.2) (p^2)) =
      ∑ d ∈ X.divisors, primitiveAdditiveConvolution p d := by
  unfold primitivePartitionPairs primitiveAdditiveConvolution
  rw [Finset.sum_filter]
  rw [show
    (∑ da ∈ X.divisors.product (Finset.range (X+1)),
      if 0 < da.2 ∧ da.2 < da.1 ∧ da.2.Coprime da.1 then
        arithmeticCoefficientDedekindTerm da.2 (da.1-da.2) (p^2) else 0) =
      ∑ d ∈ X.divisors, ∑ a ∈ Finset.range (X+1),
        if 0 < a ∧ a < d ∧ a.Coprime d then
          arithmeticCoefficientDedekindTerm a (d-a) (p^2) else 0 by
            exact Finset.sum_product _ _ _]
  apply Finset.sum_congr rfl
  intro d hd
  have hdX := Nat.le_of_dvd hX (Nat.mem_divisors.mp hd).1
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext a
    simp
    omega
  · intro a _ha
    rfl

theorem full_additive_convolution_divisor_sum
    {p X : ℕ} (hp : p.Prime) (hX : 0 < X) (hXp : X < p) :
    fullAdditiveConvolution p X =
      ∑ d ∈ X.divisors, primitiveAdditiveConvolution p d := by
  rw [full_eq_scaled hp hXp, scaled_eq_pairs hX, pairs_eq_divisor_sum hX]

/-- On the manuscript's range `0 < X < p`, the full additive convolution is
the divisor sum of its primitive pieces, and finite Möbius inversion recovers
each primitive piece.  Both formulas are derived from the actual Dedekind
anti-diagonal rather than accepted as hypotheses. -/
theorem primitive_additive_convolution
    {p : ℕ} (hp : p.Prime) :
    (∀ X, 0 < X → X < p →
      fullAdditiveConvolution p X =
        ∑ d ∈ X.divisors, primitiveAdditiveConvolution p d) ∧
    (∀ X, 0 < X → X < p →
      primitiveAdditiveConvolution p X =
        ∑ d ∈ X.divisors,
          (ArithmeticFunction.moebius d : ℚ) *
            fullAdditiveConvolution p (X / d)) := by
  refine ⟨fun X hX hXp ↦
    full_additive_convolution_divisor_sum hp hX hXp, ?_⟩
  have hinversion :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
      (R := ℚ)
      (f := primitiveAdditiveConvolution p)
      (g := fullAdditiveConvolution p)
      (Set.Ioo 0 p)
      (by
        intro m n hmn hn
        have hnpos : 0 < n := hn.1
        have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmn hnpos
        exact ⟨hmpos, (Nat.le_of_dvd hnpos hmn).trans_lt hn.2⟩)).mp (by
          intro n hnpos hnrange
          exact (full_additive_convolution_divisor_sum
            hp hnpos hnrange.2).symm)
  intro X hX hXp
  have hXinv := hinversion X hX ⟨hX, hXp⟩
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun d q ↦
      (ArithmeticFunction.moebius d : ℚ) *
        fullAdditiveConvolution p q)] at hXinv
  exact hXinv.symm

noncomputable def primitiveNatEquiv (X : ℕ) [NeZero X] (hX : 2 ≤ X) :
    ↑((Finset.Ico 1 X).filter fun a => a.Coprime X) ≃ (ZMod X)ˣ where
  toFun a := ZMod.unitOfCoprime a.val (by simpa using (Finset.mem_filter.mp a.property).2)
  invFun u := ⟨u.val.val, by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨?_, u.val.val_lt⟩,
      ZMod.val_coe_unit_coprime u⟩
    letI : Fact (1 < X) := ⟨by omega⟩
    exact ZMod.val_pos.mpr u.ne_zero⟩
  left_inv a := by
    apply Subtype.ext
    simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]
  right_inv u := by
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime]

theorem primitive_convolution_eq_packet
    {p X : ℕ} [NeZero X] (hX : 2 ≤ X) :
    primitiveAdditiveConvolution p X = 2 * partitionPacket (p^2) X := by
  letI : Fact (1 < X) := ⟨by omega⟩
  unfold primitiveAdditiveConvolution partitionPacket
  have hreindex := (primitiveNatEquiv X hX).sum_comp
    (fun u : (ZMod X)ˣ =>
      arithmeticCoefficientDedekindTerm u.val.val (-u).val.val (p^2))
  rw [← hreindex]
  rw [show 2 * (1 / 2 *
      (∑ i : ↑((Finset.Ico 1 X).filter fun a => a.Coprime X),
        arithmeticCoefficientDedekindTerm
          ((primitiveNatEquiv X hX i).val.val)
          ((-(primitiveNatEquiv X hX i)).val.val) (p^2))) =
      (∑ i : ↑((Finset.Ico 1 X).filter fun a => a.Coprime X),
        arithmeticCoefficientDedekindTerm
          ((primitiveNatEquiv X hX i).val.val)
          ((-(primitiveNatEquiv X hX i)).val.val) (p^2)) by ring]
  rw [Finset.sum_subtype
    ((Finset.Ico 1 X).filter fun a => a.Coprime X) (by intro; rfl)]
  apply Finset.sum_congr rfl
  intro a ha
  change arithmeticCoefficientDedekindTerm a.val (X-a.val) (p^2) =
    arithmeticCoefficientDedekindTerm
      (ZMod.unitOfCoprime a.val (by simpa using (Finset.mem_filter.mp a.property).2)).val.val
      (-ZMod.unitOfCoprime a.val
        (by simpa using (Finset.mem_filter.mp a.property).2)).val.val (p^2)
  rw [negUnit_val hX]
  simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp a.property).1).2]

end NField.Alignment.PrimitiveAdditiveConvolution
