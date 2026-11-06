/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CommonResetLift

/-! # Literal signed integer numerator indices in the exact-order kernel -/

noncomputable section

namespace NField.Alignment.CommonResetIntegerKernel

open scoped BigOperators
open CommonResetFourier CommonResetConductor CommonResetKernel CommonResetLift DedekindReciprocity

def integerDedekind (t : ℕ) (h : ℤ) : ℚ := arithmeticDedekindSum (h : ZMod t).val t

def integerKernel (t : ℕ) (h : ℤ) : ℝ := conductorKernel t (h : ZMod t).val

theorem integer_lift_to_divisor {d t : ℕ} [NeZero t] (hdt : d ∣ t) (h : ℤ) :
    ((h : ZMod t).val : ZMod d) = (h : ZMod d) := by
  have hc := congrArg (ZMod.castHom hdt (ZMod d)) (ZMod.natCast_zmod_val (h : ZMod t))
  simpa only [map_natCast, map_intCast] using hc

theorem dedekind_integer_lift {d t : ℕ} [NeZero t] (hd : 0 < d) (hdt : d ∣ t) (h : ℤ) :
    arithmeticDedekindSum (h : ZMod t).val d = integerDedekind d h := by
  letI : NeZero d := ⟨hd.ne'⟩
  have he : (arithmeticDedekindSum (h : ZMod t).val d : ℂ) =
      (integerDedekind d h : ℂ) := by
    rw [integerDedekind, ← residueDedekind_eq_rational, ← residueDedekind_eq_rational,
      integer_lift_to_divisor hdt, ZMod.natCast_zmod_val]
  exact_mod_cast he

theorem kernel_integer_lift {d t : ℕ} [NeZero t] (hd : 0 < d) (hdt : d ∣ t) (h : ℤ) :
    conductorKernel d (h : ZMod t).val = integerKernel d h := by
  letI : NeZero d := ⟨hd.ne'⟩
  apply conductorKernel_congr hd
  have he := congrArg ZMod.val (integer_lift_to_divisor hdt h)
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt (h : ZMod d))] using he

/-- Title: `Exact-order cotangent kernels include every signed integer numerator`. -/
theorem integer_kernel_cotangent {t : ℕ} [NeZero t] (ht : 2 ≤ t) (h : ℤ) :
    integerKernel t h = unitKernel (h : ZMod t) := by
  rw [integerKernel, conductorKernel_eq_units ht, ZMod.natCast_zmod_val]

/-- Title: `Divisor inversion holds for every signed integer numerator`. -/
theorem integer_conductor_inversion {t : ℕ} (ht : 0 < t) (h : ℤ) :
    (t : ℝ)*(integerDedekind t h : ℝ) = ∑ d ∈ t.divisors, integerKernel d h := by
  letI : NeZero t := ⟨ht.ne'⟩
  rw [integerDedekind, conductor_inversion ht]
  apply Finset.sum_congr rfl
  intro d hd
  exact kernel_integer_lift (Nat.pos_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd) h

/-- Title: `The printed Möbius kernel formula retains negative and nonunit numerators`. -/
theorem integer_conductor_moebius {t : ℕ} (ht : 0 < t) (h : ℤ) :
    integerKernel t h = ∑ d ∈ t.divisors,
      (ArithmeticFunction.moebius (t/d) : ℝ)*(d : ℝ)*(integerDedekind d h : ℝ) := by
  letI : NeZero t := ⟨ht.ne'⟩
  rw [integerKernel, conductor_moebius ht]
  apply Finset.sum_congr rfl
  intro d hd
  rw [dedekind_integer_lift (Nat.pos_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd)]

/-- Title: `The signed integer conductor kernel is odd`. -/
theorem integer_kernel_odd {t : ℕ} [NeZero t] (ht : 2 ≤ t) (h : ℤ) :
    integerKernel t (-h) = -integerKernel t h := by
  rw [integer_kernel_cotangent ht, integer_kernel_cotangent ht, Int.cast_neg, unitKernel_odd ht]

theorem integer_kernel_one (h : ℤ) : integerKernel 1 h = 0 := conductorKernel_one _

end NField.Alignment.CommonResetIntegerKernel
