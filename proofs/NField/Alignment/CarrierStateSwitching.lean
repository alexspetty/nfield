/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.ComplementaryPartition
import NField.Alignment.FloorStateSwitchingLedger
import NField.Alignment.PrimeSquareCubicEnergy

/-!
# Carrier-state switching

The manuscript's state burden is instantiated here on the actual
prime-square Dedekind prefixes.  The fresh increment formula is proved from
one-step prefix growth and exact cancellation of a complete reduced residue
block.  The abstract summation-by-parts ledger is then applied to these
concrete states.
-/

namespace NField.Alignment.CarrierStateSwitching

open scoped BigOperators
open NField.Alignment.ComplementaryPartition
open NField.Alignment.FloorStateSwitchingLedger
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.RademacherThreeTerm

/-- The collar prefix `Delta_{k,p}(X)` in exact rational arithmetic. -/
noncomputable def carrierPrefix (p k X : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc 1 X,
    if a.Coprime k then
      arithmeticCoefficientDedekindTerm (p ^ 2) a k
    else 0

/-- The stored burden for a finite selected family of carrier moduli. -/
noncomputable def carrierStateBurden
    (p : ℕ) (carriers : Finset ℕ) (X : ℕ) : ℚ :=
  ∑ k ∈ carriers,
    if 2 ≤ k ∧ k < X then carrierPrefix p k X else 0

/-- The fresh state increment. -/
noncomputable def freshCarrierIncrement
    (p : ℕ) (carriers : Finset ℕ) (X : ℕ) : ℚ :=
  carrierStateBurden p carriers X -
    carrierStateBurden p carriers (X - 1)

/-- Advancing a prefix by one appends precisely the new reduced-residue
term, or zero when the new numerator is not a unit. -/
theorem carrierPrefix_succ (p k X : ℕ) :
    carrierPrefix p k (X + 1) = carrierPrefix p k X +
      (if (X + 1).Coprime k then
        arithmeticCoefficientDedekindTerm (p ^ 2) (X + 1) k
      else 0) := by
  unfold carrierPrefix
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1)]

/-- One complete reduced-residue prefix cancels exactly. -/
theorem carrierPrefix_self_eq_zero
    {p k : ℕ} (hk : 2 ≤ k) (hpk : (p ^ 2).Coprime k) :
    carrierPrefix p k k = 0 := by
  letI : NeZero k := ⟨by omega⟩
  have hcomplex := sum_coefficientDedekindTerm_units_zero hk hpk
  have hrational :
      (∑ a ∈ Finset.range k,
        if a.Coprime k then
          arithmeticCoefficientDedekindTerm (p ^ 2) a k
        else 0) = 0 := by
    apply (Rat.cast_injective (α := ℂ))
    push_cast
    calc
      (∑ i ∈ Finset.range k,
          ↑(if i.Coprime k then
            arithmeticCoefficientDedekindTerm (p ^ 2) i k else 0)) =
          ∑ i ∈ Finset.range k,
            if i.Coprime k then
              ((arithmeticCoefficientDedekindTerm (p ^ 2) i k : ℚ) : ℂ)
            else 0 := by
              apply Finset.sum_congr rfl
              intro i _hi
              split
              · rfl
              · norm_num
      _ = 0 := hcomplex
  unfold carrierPrefix
  rw [show
      (∑ a ∈ Finset.Icc 1 k,
        if a.Coprime k then
          arithmeticCoefficientDedekindTerm (p ^ 2) a k
        else 0) =
      ∑ a ∈ Finset.range k,
        if a.Coprime k then
          arithmeticCoefficientDedekindTerm (p ^ 2) a k
        else 0 by
    rw [show Finset.Icc 1 k = insert k (Finset.Ico 1 k) by
      ext a
      simp
      omega]
    rw [Finset.sum_insert (by simp)]
    simp [Nat.coprime_self, show k ≠ 1 by omega]
    rw [show Finset.Ico 1 k = (Finset.range k).erase 0 by
      ext a
      simp
      omega]
    have herase := Finset.sum_erase_add
      (s := Finset.range k) (f := fun a =>
        if a.Coprime k then
          arithmeticCoefficientDedekindTerm (p ^ 2) a k
        else 0) (by simp [show 0 < k by omega] : 0 ∈ Finset.range k)
    simpa [show ¬Nat.Coprime 0 k by simp [show k ≠ 1 by omega]] using herase]
  exact hrational

/-- The actual fresh increment is the sum of the new Dedekind collision over
the selected lower carriers. -/
theorem freshCarrierIncrement_eq
    {p X : ℕ} (hp : p.Prime) (hX : 3 ≤ X)
    (carriers : Finset ℕ)
    (hcarriers : ∀ k ∈ carriers, 2 ≤ k ∧ k < p) :
    freshCarrierIncrement p carriers X =
      ∑ k ∈ carriers.filter fun k => 2 ≤ k ∧ k < X ∧ k.Coprime X,
        arithmeticCoefficientDedekindTerm (p ^ 2) X k := by
  classical
  have hpred : X = (X - 1) + 1 := by omega
  have hpred' : X - 1 + 1 = X := by omega
  unfold freshCarrierIncrement carrierStateBurden
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  have hkdata := hcarriers k hk
  have hpk : (p ^ 2).Coprime k :=
    (NField.Alignment.PrimeSquareReducedRatio.smallNatUnit_coprime
      hp (by omega : 0 < k) hkdata.2).symm
  by_cases hkX : k < X
  · by_cases hkold : k < X - 1
    · have hnew : X.Coprime k ↔ k.Coprime X := by
        rw [Nat.coprime_comm]
      rw [show carrierPrefix p k X = carrierPrefix p k (X - 1) +
          (if X.Coprime k then
            arithmeticCoefficientDedekindTerm (p ^ 2) X k else 0) by
        simpa [hpred'] using carrierPrefix_succ p k (X - 1)]
      simp [hkdata.1, hkX, hkold, hnew]
    · have hkeq : k = X - 1 := by omega
      subst k
      have hself := carrierPrefix_self_eq_zero
        (p := p) (k := X - 1) (by omega) hpk
      rw [show carrierPrefix p (X - 1) X =
          carrierPrefix p (X - 1) (X - 1) +
            (if X.Coprime (X - 1) then
              arithmeticCoefficientDedekindTerm (p ^ 2) X (X - 1)
            else 0) by
        simpa [hpred'] using carrierPrefix_succ p (X - 1) (X - 1)]
      rw [hself]
      simp [hkdata.1, hkX, Nat.coprime_comm]
  · have hknotold : ¬k < X - 1 := by omega
    simp [hkdata.1, hkX, hknotold]

/-- The dwell count `H_X = floor(N/X)`. -/
noncomputable def carrierDwell (N X : ℕ) : ℝ := ((N / X : ℕ) : ℝ)

/-- The rational state burden viewed in the real ledger. -/
noncomputable def carrierStateBurdenReal
    (p : ℕ) (carriers : Finset ℕ) (X : ℕ) : ℝ :=
  (carrierStateBurden p carriers X : ℝ)

/-- The actual fresh collision sum in the selected carrier family. -/
noncomputable def selectedCarrierFresh
    (p : ℕ) (carriers : Finset ℕ) (X : ℕ) : ℚ :=
  ∑ k ∈ carriers.filter fun k => 2 ≤ k ∧ k < X ∧ k.Coprime X,
    arithmeticCoefficientDedekindTerm (p ^ 2) X k

theorem carrierStateBurdenReal_two_eq_zero
    {p : ℕ} {carriers : Finset ℕ}
    (hcarriers : ∀ k ∈ carriers, 2 ≤ k) :
    carrierStateBurdenReal p carriers 2 = 0 := by
  have hsum : carrierStateBurden p carriers 2 = 0 := by
    unfold carrierStateBurden
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg]
    exact fun h => (not_lt_of_ge (hcarriers k hk)) h.2
  unfold carrierStateBurdenReal
  rw [hsum]
  norm_num

theorem carrierDwell_succ_boundary_eq_zero (N : ℕ) :
    carrierDwell N (N + 1) = 0 := by
  simp [carrierDwell]

theorem carrierDwell_three_ne_zero
    {N : ℕ} (hN : 3 ≤ N) :
    carrierDwell N 3 ≠ 0 := by
  have hpos : 0 < N / 3 := Nat.div_pos hN (by omega)
  unfold carrierDwell
  exact_mod_cast (ne_of_gt hpos)

theorem carrierStateBurdenReal_fresh
    {p X : ℕ} (hp : p.Prime) (hX : 3 ≤ X)
    (carriers : Finset ℕ)
    (hcarriers : ∀ k ∈ carriers, 2 ≤ k ∧ k < p) :
    carrierStateBurdenReal p carriers X -
        carrierStateBurdenReal p carriers (X - 1) =
      (selectedCarrierFresh p carriers X : ℝ) := by
  have hfresh := freshCarrierIncrement_eq hp hX carriers hcarriers
  unfold carrierStateBurdenReal selectedCarrierFresh
  unfold freshCarrierIncrement at hfresh
  rw [← hfresh]
  push_cast
  rfl

/-- The complete linear, quadratic, and charge/release switching ledger on
the manuscript's actual selected carrier states. -/
theorem exact_carrier_switching_ledger
    {p N : ℕ} (hp : p.Prime) (hN : 3 ≤ N)
    (carriers : Finset ℕ)
    (hcarriers : ∀ k ∈ carriers, 2 ≤ k ∧ k < p) :
    dwellBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) =
      ∑ X ∈ Finset.Icc 3 N,
        carrierDwell N X *
          (selectedCarrierFresh p carriers X : ℝ) ∧
    quadraticBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) =
      ∑ X ∈ Finset.Icc 3 N,
        carrierDwell N X *
          ((carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2 +
            2 * carrierStateBurdenReal p carriers (X - 1) *
              (carrierStateBurdenReal p carriers X -
                carrierStateBurdenReal p carriers (X - 1))) ∧
    (let J := fun X =>
        carrierStateBurdenReal p carriers (X - 1) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) +
          (1 / 2 : ℝ) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2;
      (∑ X ∈ Finset.Icc 3 N,
          carrierDwell N X * positivePart (J X)) =
        (∑ X ∈ Finset.Icc 3 N,
          carrierDwell N X * negativePart (J X)) +
        quadraticBurden N (carrierDwell N)
          (carrierStateBurdenReal p carriers) / 2) := by
  have hB : carrierStateBurdenReal p carriers 2 = 0 :=
    carrierStateBurdenReal_two_eq_zero (fun k hk => (hcarriers k hk).1)
  have hH : carrierDwell N (N + 1) = 0 :=
    carrierDwell_succ_boundary_eq_zero N
  have hlinear := NField.Alignment.FloorStateSwitchingLedger.exact_switching_ledger
    N hN (carrierDwell N) (carrierStateBurdenReal p carriers) hB hH
  have hquadratic := quadratic_switching_ledger
    N hN (carrierDwell N) (carrierStateBurdenReal p carriers) hB hH
  refine ⟨?_, hquadratic, ?_⟩
  · rw [hlinear]
    unfold lifetimeFresh
    apply Finset.sum_congr rfl
    intro X hX
    have hXrange := Finset.mem_Icc.mp hX
    rw [carrierStateBurdenReal_fresh hp hXrange.1 carriers hcarriers]
  · let J := fun X =>
      carrierStateBurdenReal p carriers (X - 1) *
          (carrierStateBurdenReal p carriers X -
            carrierStateBurdenReal p carriers (X - 1)) +
        (1 / 2 : ℝ) *
          (carrierStateBurdenReal p carriers X -
            carrierStateBurdenReal p carriers (X - 1)) ^ 2
    apply charge_release_balance N (carrierDwell N) J
      (quadraticBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers))
    rw [hquadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _hX
    dsimp [J]
    ring

/-- Exact coherent-area plus fluctuation decomposition for the manuscript's
actual carrier-state burden. -/
theorem carrier_burden_variance_identity
    {p N : ℕ} (hN : 3 ≤ N) (carriers : Finset ℕ) :
    let total := ∑ X ∈ Finset.Icc 3 N,
      (carrierDwell N X - carrierDwell N (X + 1)) *
        carrierStateBurdenReal p carriers X
    let mean := total / carrierDwell N 3
    total ^ 2 / carrierDwell N 3 +
        ∑ X ∈ Finset.Icc 3 N,
          (carrierDwell N X - carrierDwell N (X + 1)) *
            (carrierStateBurdenReal p carriers X - mean) ^ 2 =
      quadraticBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) := by
  exact burden_variance_identity N hN (carrierDwell N)
    (carrierStateBurdenReal p carriers)
    (carrierDwell_succ_boundary_eq_zero N)
    (carrierDwell_three_ne_zero hN)

/-- Exact sign criterion for one current in the manuscript's concrete
carrier-state switching process. -/
theorem carrier_switching_current_neg_iff
    (p : ℕ) (carriers : Finset ℕ) (X : ℕ) :
    let stored := carrierStateBurdenReal p carriers (X - 1)
    let fresh := carrierStateBurdenReal p carriers X - stored
    stored * fresh + (1 / 2 : ℝ) * fresh ^ 2 < 0 ↔
      stored * fresh < 0 ∧ |fresh| < 2 * |stored| := by
  exact switchingCurrent_neg_iff _ _

end NField.Alignment.CarrierStateSwitching
