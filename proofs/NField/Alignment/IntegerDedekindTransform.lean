/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.IntegerInverseResidue

/-! # Additive Dedekind transforms for all integer frequencies -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.IntegerDedekindTransform
open scoped BigOperators Topology Classical
open CarryBoundarySpectra DedekindInverseResidueTransform IntegerInverseResidue

def integerFullTransform (q : ℕ) (t : ℤ) : ℂ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ h : ZMod q, extendedDedekindValue q h * ZMod.stdAddChar (-((t:ZMod q)*h))

def integerUnitTransform (q : ℕ) (t : ℤ) : ℂ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ h : (ZMod q)ˣ, extendedDedekindValue q h.val * ZMod.stdAddChar (-((t:ZMod q)*h.val))

theorem integer_full_nat (q t : ℕ) : integerFullTransform q (t:ℤ)=fullDedekindTransform q t := by
  simp only [integerFullTransform,fullDedekindTransform,Int.cast_natCast]

theorem integer_unit_nat (q t : ℕ) : integerUnitTransform q (t:ℤ)=unitDedekindTransform q t := by
  simp only [integerUnitTransform,unitDedekindTransform,Int.cast_natCast,extendedDedekindValue]

theorem extended_dedekind_neg {q : ℕ} [NeZero q] (h : ZMod q) :
    extendedDedekindValue q (-h)= -extendedDedekindValue q h := by
  simp only [extendedDedekindValue_eq_sum,neg_mul,centered_sawtooth_neg_all,mul_neg,Finset.sum_neg_distrib]

theorem integer_full_neg {q : ℕ} (hq : 0<q) (t : ℤ) :
    integerFullTransform q (-t)= -integerFullTransform q t := by
  letI : NeZero q := ⟨hq.ne'⟩
  simp only [integerFullTransform,dif_neg hq.ne',Int.cast_neg]
  calc
    _ = ∑ h : ZMod q, extendedDedekindValue q (-h) *
        ZMod.stdAddChar (-(((-t):ZMod q)*(-h))) :=
      (Equiv.sum_comp (Equiv.neg (ZMod q)) (fun h : ZMod q =>
        extendedDedekindValue q h*ZMod.stdAddChar (-(((-t):ZMod q)*h)))).symm
    _ = _ := by
      simp only [extended_dedekind_neg,neg_mul,mul_neg,neg_neg,Finset.sum_neg_distrib]

theorem integer_unit_neg {q : ℕ} (hq : 0<q) (t : ℤ) :
    integerUnitTransform q (-t)= -integerUnitTransform q t := by
  letI : NeZero q := ⟨hq.ne'⟩
  simp only [integerUnitTransform,dif_neg hq.ne',Int.cast_neg]
  calc
    _ = ∑ h : (ZMod q)ˣ, extendedDedekindValue q (-h).val *
        ZMod.stdAddChar (-(((-t):ZMod q)*(-h).val)) :=
      (Equiv.sum_comp (Equiv.neg ((ZMod q)ˣ)) (fun h : (ZMod q)ˣ =>
        extendedDedekindValue q h.val*ZMod.stdAddChar (-(((-t):ZMod q)*h.val)))).symm
    _ = _ := by
      simp only [Units.val_neg,extended_dedekind_neg,neg_mul,mul_neg,neg_neg,Finset.sum_neg_distrib]

def integerFullSeriesSide (K : ℕ) (t : ℤ) : ℂ :=
  -(1/(Real.pi*Complex.I))*
    ∑ g ∈ (Int.gcd (K:ℤ) t).divisors.filter (fun g => 2≤K/g),
      (1/(g:ℂ))*integerInverseSeries (K/g) (t/(g:ℤ))

theorem integer_full_side_nat (K t : ℕ) :
    integerFullSeriesSide K (t:ℤ)=fullTransformSeriesSide K t := by
  simp only [integerFullSeriesSide,fullTransformSeriesSide,Int.gcd_eq_natAbs_gcd_natAbs,
    Int.natAbs_natCast,← Int.natCast_ediv,integer_series_nat]

theorem integer_full_side_neg_nat (K t : ℕ) :
    integerFullSeriesSide K (-(t:ℤ))= -fullTransformSeriesSide K t := by
  unfold integerFullSeriesSide
  simp only [Int.gcd_eq_natAbs_gcd_natAbs,Int.natAbs_neg,Int.natAbs_natCast]
  have hterm (g : ℕ) (hg : g∈(K.gcd t).divisors.filter (fun g => 2≤K/g)) :
      (1/(g:ℂ))*integerInverseSeries (K/g) ((-(t:ℤ))/(g:ℤ))=
        -((1/(g:ℂ))*inverseSawSeries (K/g) (t/g)) := by
    have hgt : g∣t := (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hg).1).trans (Nat.gcd_dvd_right K t)
    have hgtI : (g:ℤ)∣(t:ℤ) := by exact_mod_cast hgt
    rw [Int.neg_ediv_of_dvd hgtI,← Int.natCast_ediv,integer_series_neg_nat,mul_neg]
  rw [Finset.sum_congr rfl hterm,Finset.sum_neg_distrib]
  unfold fullTransformSeriesSide
  ring

/-- Title: `Exact additive transform for integer frequencies`. -/
theorem integer_additive_transform {K : ℕ} (hK : 2≤K) (t : ℤ) :
    integerFullTransform K t/(K:ℂ)=integerFullSeriesSide K t := by
  cases t with
  | ofNat t =>
      change integerFullTransform K (t:ℤ)/(K:ℂ)=integerFullSeriesSide K (t:ℤ)
      rw [integer_full_nat,integer_full_side_nat]
      exact fullTransformSeries_identity hK t
  | negSucc t =>
      change integerFullTransform K (-((t+1:ℕ):ℤ))/(K:ℂ)=integerFullSeriesSide K (-((t+1:ℕ):ℤ))
      rw [integer_full_neg (by omega),integer_full_nat,integer_full_side_neg_nat,neg_div]
      rw [fullTransformSeries_identity hK]

/-- Title: `Unit restriction by Möbius inversion for integer frequencies`. -/
theorem integer_unit_mobius {K : ℕ} (hK : 0<K) (t : ℤ) :
    integerUnitTransform K t=∑ d ∈ K.divisors, (ArithmeticFunction.moebius d:ℂ)*integerFullTransform (K/d) t := by
  have hpos (d : ℕ) (hd : d∈K.divisors) : 0<K/d :=
    Nat.div_pos (Nat.le_of_dvd hK (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)
  cases t with
  | ofNat t =>
      change integerUnitTransform K (t:ℤ)=∑ d ∈ K.divisors,
        (ArithmeticFunction.moebius d:ℂ)*integerFullTransform (K/d) (t:ℤ)
      simp only [integer_unit_nat,integer_full_nat]
      exact unitDedekindTransform_eq_mobius hK
  | negSucc t =>
      change integerUnitTransform K (-((t+1:ℕ):ℤ))=
        ∑ d ∈ K.divisors, (ArithmeticFunction.moebius d:ℂ)*integerFullTransform (K/d) (-((t+1:ℕ):ℤ))
      rw [integer_unit_neg hK,integer_unit_nat,unitDedekindTransform_eq_mobius hK]
      unfold unitTransformMobiusSide
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [integer_full_neg (hpos d hd),integer_full_nat,mul_neg]

end NField.Alignment.IntegerDedekindTransform
