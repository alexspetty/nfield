/-
Author: Alexander S. Petty
-/

import NField.Alignment.PrimeCarryFiberCentering

/-!
# Prime carry spectral bridge

The lag-one diagonal is encoded as an intrinsic cell weight.  Its carry
observable is the concrete class-centered table, while its signed boundary is
the prime-square endpoint family.  These identities permit finite Parseval to
compare the carry energy with the short-window sawtooth convolution.
-/

namespace NField.Alignment.PrimeCarrySpectralBridge

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionTransform
open NField.Alignment.CollisionTransformStrip
open NField.Alignment.NeutralityTheorem
open NField.Alignment.PairedBoundary
open NField.Alignment.PairedBoundaryFlux
open NField.Alignment.PrimeCarryEnergyBridge
open NField.Alignment.PrimeCarryFiberCentering
open NField.Alignment.PrimeSquareBoundaryFlux
open NField.Alignment.PrimeSquareCollisionWindow
open NField.Alignment.TheCollisionSpectrum

/-- Indicator weight of the complete lag-one diagonal modulo `p^2`. -/
noncomputable def primeDiagonalWeight
    {p : ℕ} (_hp : p.Prime) : ZMod (p ^ 2) → ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 _hp.ne_zero⟩
  exact imageIndicator
    (fun d : Fin p => (((p + 1) * d.val : ℕ) : ZMod (p ^ 2)))

/-- The carry observable of the diagonal indicator is exactly the diagonal
sawtooth signal. -/
theorem unitCarrySignal_primeDiagonalWeight
    {p : ℕ} [NeZero (p ^ 2)]
    (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    unitCarrySignal (primeDiagonalWeight hp) a =
      primeDiagonalSawtoothSignal hp a := by
  classical
  unfold unitCarrySignal carryObservable primeDiagonalWeight
  rw [imageIndicator_pairing]
  unfold primeDiagonalSawtoothSignal
  rw [Fin.sum_univ_eq_sum_range (fun d : ℕ =>
    centeredSawtooth (((((p + 1) * d : ℕ) : ZMod (p ^ 2)) + 1) * a.val) -
      centeredSawtooth ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) * a.val)) p]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro d _
  congr 3
  push_cast
  ring

/-- Consequently the diagonal carry observable is the actual class-centered
prime carry table. -/
theorem unitCarrySignal_primeDiagonalWeight_eq_centered
    {p : ℕ} [NeZero (p ^ 2)]
    (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    unitCarrySignal (primeDiagonalWeight hp) a = primeCarryCentered hp a := by
  rw [unitCarrySignal_primeDiagonalWeight hp,
    ← primeCarryCentered_eq_diagonalSawtooth hp]

/-- The cell flux of the diagonal indicator is the direct diagonal endpoint
sum. -/
theorem cellBoundaryFlux_primeDiagonalWeight
    {p : ℕ} [NeZero (p ^ 2)]
    (hp : p.Prime) (χ : Character (p ^ 2)) :
    cellBoundaryFlux (primeDiagonalWeight hp) χ =
      ∑ d ∈ Finset.range p,
        (χ ((((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2))) -
          χ ((((p + 1) * d : ℕ) : ZMod (p ^ 2)))) := by
  classical
  unfold cellBoundaryFlux primeDiagonalWeight
  rw [imageIndicator_pairing]
  rw [Fin.sum_univ_eq_sum_range (fun d : ℕ =>
    χ ((((p + 1) * d : ℕ) : ZMod (p ^ 2)) + 1) -
      χ ((((p + 1) * d : ℕ) : ZMod (p ^ 2)))) p]
  apply Finset.sum_congr rfl
  intro d _
  congr 2
  push_cast
  ring

theorem lagOneBoundaryLeft_eq_diagonalPoint
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (i : FirstWindowIndex p) :
    (lagOneBoundaryLeft hp i).val =
      ((((p + 1) * (i.val + 1) : ℕ) : ZMod (p ^ 2))) := by
  unfold lagOneBoundaryLeft lagOneStepUnit firstWindowUnit firstWindowNat
  rw [Units.val_mul, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime]
  push_cast
  ring

theorem lagOneBoundaryRight_eq_diagonalSuccessor
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (i : FirstWindowIndex p) :
    (lagOneBoundaryRight hp i).val =
      ((((p + 1) * i.val + 1 : ℕ) : ZMod (p ^ 2))) := by
  have hp2 := hp.two_le
  unfold lagOneBoundaryRight
  rw [Units.val_neg, lagOneBoundaryLeft_eq_diagonalPoint hp]
  apply ZMod.val_injective
  rw [ZMod.neg_val]
  have hnonzero :
      ((((p + 1) * ((Fin.rev i).val + 1) : ℕ) : ZMod (p ^ 2))) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hi : (Fin.rev i).val + 1 < p := by
      have := (Fin.rev i).isLt
      omega
    have hpos : 0 < (p + 1) * ((Fin.rev i).val + 1) := by positivity
    have hlt : (p + 1) * ((Fin.rev i).val + 1) < p ^ 2 := by
      nlinarith
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  rw [if_neg hnonzero, ZMod.val_natCast]
  have hleftlt : (p + 1) * ((Fin.rev i).val + 1) < p ^ 2 := by
    have hi : (Fin.rev i).val + 1 < p := by
      have := (Fin.rev i).isLt
      omega
    nlinarith
  rw [Nat.mod_eq_of_lt hleftlt, ZMod.val_natCast]
  have hrightlt : (p + 1) * i.val + 1 < p ^ 2 := by
    have hi := i.isLt
    have hiplus : i.val + 1 < p := by omega
    have hmul := (Nat.mul_lt_mul_left (Nat.succ_pos p)).2 hiplus
    have hprod : (p + 1) * p = p ^ 2 + p := by ring
    nlinarith
  rw [Nat.mod_eq_of_lt hrightlt, Fin.val_rev]
  have hj : p - 1 - (i.val + 1) + 1 = p - 1 - i.val := by omega
  rw [hj]
  have hindex : (p - 1 - i.val) + i.val = p - 1 := by omega
  have hlast : (p + 1) * (p - 1) + 1 = p ^ 2 := by
    rw [Nat.mul_sub_left_distrib]
    simp only [mul_one]
    have hmul : (p + 1) * p = p ^ 2 + p := by ring
    rw [hmul]
    omega
  have hsum :
      (p + 1) * (p - 1 - i.val) + ((p + 1) * i.val + 1) = p ^ 2 := by
    calc
      (p + 1) * (p - 1 - i.val) + ((p + 1) * i.val + 1) =
          (p + 1) * ((p - 1 - i.val) + i.val) + 1 := by ring
      _ = (p + 1) * (p - 1) + 1 := by rw [hindex]
      _ = p ^ 2 := hlast
  have hle : (p + 1) * (p - 1 - i.val) ≤ p ^ 2 := by omega
  rw [Nat.sub_eq_iff_eq_add hle]
  omega

theorem directDiagonal_upper_endpoint_sum
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (χ : Character (p ^ 2)) :
    (∑ d ∈ Finset.range p,
      χ (((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2))) =
      ∑ i : FirstWindowIndex p, χ (lagOneBoundaryRight hp i).val := by
  have hp2 := hp.two_le
  have hsplit := Finset.sum_range_succ
    (fun d : ℕ => χ (((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2))) (p - 1)
  have hsplit' :
      (∑ d ∈ Finset.range p,
        χ (((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2))) =
      (∑ d ∈ Finset.range (p - 1),
        χ (((p + 1) * d + 1 : ℕ) : ZMod (p ^ 2))) +
        χ (((p + 1) * (p - 1) + 1 : ℕ) : ZMod (p ^ 2)) := by
    simpa only [Nat.sub_add_cancel hp.one_le] using hsplit
  rw [hsplit']
  have hlast : (p + 1) * (p - 1) + 1 = p ^ 2 := by
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub hp.one_le]
    ring
  rw [hlast]
  have hmodne : p ^ 2 ≠ 1 := by nlinarith
  rw [ZMod.natCast_self, χ.map_zero' hmodne, add_zero]
  simp_rw [lagOneBoundaryRight_eq_diagonalSuccessor hp]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => χ (((p + 1) * i + 1 : ℕ) : ZMod (p ^ 2)))
      (p - 1)).symm

theorem directDiagonal_lower_endpoint_sum
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (χ : Character (p ^ 2)) :
    (∑ d ∈ Finset.range p,
      χ (((p + 1) * d : ℕ) : ZMod (p ^ 2))) =
      ∑ i : FirstWindowIndex p, χ (lagOneBoundaryLeft hp i).val := by
  have hp2 := hp.two_le
  have hsplit := Finset.sum_range_succ'
    (fun d : ℕ => χ (((p + 1) * d : ℕ) : ZMod (p ^ 2))) (p - 1)
  have hsplit' :
      (∑ d ∈ Finset.range p,
        χ (((p + 1) * d : ℕ) : ZMod (p ^ 2))) =
      (∑ d ∈ Finset.range (p - 1),
        χ (((p + 1) * (d + 1) : ℕ) : ZMod (p ^ 2))) +
        χ (((p + 1) * 0 : ℕ) : ZMod (p ^ 2)) := by
    simpa only [Nat.sub_add_cancel hp.one_le] using hsplit
  rw [hsplit']
  have hmodne : p ^ 2 ≠ 1 := by nlinarith
  rw [mul_zero, Nat.cast_zero, χ.map_zero' hmodne, add_zero]
  simp_rw [lagOneBoundaryLeft_eq_diagonalPoint hp]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => χ (((p + 1) * (i + 1) : ℕ) : ZMod (p ^ 2)))
      (p - 1)).symm

/-- The direct diagonal cell flux and the paired endpoint flux are the same
finite boundary. -/
theorem cellBoundaryFlux_primeDiagonalWeight_eq_lagOne
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (χ : Character (p ^ 2)) :
    cellBoundaryFlux (primeDiagonalWeight hp) χ =
      lagOneBoundaryFlux hp χ := by
  rw [cellBoundaryFlux_primeDiagonalWeight hp]
  rw [Finset.sum_sub_distrib,
    directDiagonal_upper_endpoint_sum hp,
    directDiagonal_lower_endpoint_sum hp]
  unfold lagOneBoundaryFlux lagOneUnitBoundary
  rw [pairedBoundary_pairing]
  rw [Finset.sum_sub_distrib]

/-- First-window sawtooth convolution on the prime-square unit group. -/
noncomputable def shortWindowSawtoothSignal
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) : ℂ := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  exact ∑ i : FirstWindowIndex p,
    centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val)

/-- The centered sawtooth takes real values. -/
theorem star_centeredSawtooth
    {m : ℕ} [NeZero m] (x : ZMod m) :
    star (centeredSawtooth x) = centeredSawtooth x := by
  unfold centeredSawtooth
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    have hstarCast : star (x.cast : ℂ) = x.cast := by
      rw [ZMod.cast_eq_val]
      exact map_natCast (starRingEnd ℂ) x.val
    simp [hstarCast]

/-- The short-window sawtooth convolution is real-valued. -/
theorem star_shortWindowSawtoothSignal
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    star (shortWindowSawtoothSignal hp a) =
      shortWindowSawtoothSignal hp a := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold shortWindowSawtoothSignal
  change (starRingEnd ℂ) (∑ i : FirstWindowIndex p,
    centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact star_centeredSawtooth _

/-- Oddness of the sawtooth makes the whole convolution odd. -/
theorem shortWindowSawtoothSignal_neg
    {p : ℕ} (hp : p.Prime) (a : UnitClass (p ^ 2)) :
    shortWindowSawtoothSignal hp (-a) =
      -shortWindowSawtoothSignal hp a := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold shortWindowSawtoothSignal
  simp_rw [Units.val_neg, mul_neg, centeredSawtooth_neg
    (by nlinarith [hp.two_le] : 2 ≤ p ^ 2)]
  rw [Finset.sum_neg_distrib]

/-- The unnormalized character transform of the convolution separates into
the generalized Bernoulli factor and the first-window character sum. -/
theorem characterTransform_shortWindowSawtoothSignal
    {p : ℕ} [NeZero (p ^ 2)]
    (hp : p.Prime) {χ : Character (p ^ 2)} (hχ : χ ≠ 1) :
    characterTransform (shortWindowSawtoothSignal hp) χ =
      bernoulliOne χ * shortWindowSum hp χ := by
  classical
  have hbase :
      (∑ x : UnitClass (p ^ 2),
        χ x.val * centeredSawtooth x.val) = bernoulliOne χ := by
    have hall := centeredSawtooth_transform_eq_bernoulliOne
      (m := p ^ 2) (by nlinarith [hp.two_le]) hχ
    unfold twistedTransform at hall
    simp only [one_mul] at hall
    rw [sum_character_pairing_eq_units] at hall
    calc
      (∑ x : UnitClass (p ^ 2),
          χ x.val * centeredSawtooth x.val) =
          ∑ x : UnitClass (p ^ 2),
            centeredSawtooth x.val * χ x.val := by
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = bernoulliOne χ := hall
  have hfixed (i : FirstWindowIndex p) :
      (∑ a : UnitClass (p ^ 2),
        χ a.val *
          centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val)) =
        χ (firstWindowUnit hp i).val * bernoulliOne χ := by
    let e : UnitClass (p ^ 2) ≃ UnitClass (p ^ 2) :=
      Equiv.mulLeft (firstWindowUnit hp i)
    calc
      (∑ a : UnitClass (p ^ 2),
          χ a.val *
            centeredSawtooth ((firstWindowUnit hp i)⁻¹.val * a.val)) =
        ∑ x : UnitClass (p ^ 2),
          χ ((firstWindowUnit hp i * x).val) *
            centeredSawtooth
              ((firstWindowUnit hp i)⁻¹.val *
                (firstWindowUnit hp i * x).val) := by
          exact (e.sum_comp (fun a : UnitClass (p ^ 2) =>
            χ a.val * centeredSawtooth
              ((firstWindowUnit hp i)⁻¹.val * a.val))).symm
      _ = ∑ x : UnitClass (p ^ 2),
          χ (firstWindowUnit hp i).val *
            (χ x.val * centeredSawtooth x.val) := by
          apply Finset.sum_congr rfl
          intro x _
          change χ ((firstWindowUnit hp i * x).val) *
              centeredSawtooth
                (((firstWindowUnit hp i)⁻¹ *
                  (firstWindowUnit hp i * x)).val) = _
          rw [Units.val_mul]
          rw [map_mul]
          simp
          ring
      _ = χ (firstWindowUnit hp i).val *
          (∑ x : UnitClass (p ^ 2),
            χ x.val * centeredSawtooth x.val) := by
          rw [Finset.mul_sum]
      _ = χ (firstWindowUnit hp i).val * bernoulliOne χ := by rw [hbase]
  unfold characterTransform shortWindowSawtoothSignal shortWindowSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hfixed]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every imprimitive odd prime-square character has zero first-window sum. -/
theorem shortWindowSum_eq_zero_of_imprimitive_odd
    {p : ℕ} [NeZero p] [NeZero (p ^ 2)]
    (hp : p.Prime) (χ : Character (p ^ 2))
    (himp : ¬χ.IsPrimitive) (hodd : χ.Odd) :
    shortWindowSum hp χ = 0 := by
  have hcond : χ.conductor ∣ p ^ 2 := χ.conductor_dvd_level
  obtain ⟨k, hk, hkcond⟩ := (Nat.dvd_prime_pow hp).mp hcond
  have hkne : k ≠ 2 := by
    intro hkeq
    subst k
    exact himp hkcond
  have hklt : k < 2 := by omega
  have hcondp : χ.conductor ∣ p := by
    rw [hkcond]
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp
  let hdiv : p ∣ p ^ 2 := dvd_pow_self p (by omega)
  let hthrough : χ.FactorsThrough p :=
    DirichletCharacter.FactorsThrough.mono (χ := χ)
      χ.factorsThrough_conductor hcondp hdiv
  let ψ : Character p := hthrough.χ₀
  have heq : χ = DirichletCharacter.changeLevel hthrough.dvd ψ := by
    exact hthrough.eq_changeLevel
  have hψne : ψ ≠ 1 := by
    intro hψone
    have hχone : χ = 1 := by
      rw [heq, hψone]
      simp
    subst χ
    have heven : (1 : Character (p ^ 2)).Even := by
      unfold DirichletCharacter.Even
      exact MulChar.one_apply isUnit_neg_one
    exact (1 : Character (p ^ 2)).not_even_and_odd ⟨heven, hodd⟩
  rw [heq]
  exact shortWindowSum_changeLevel_zero hp ψ hψne

/-- Inverting a character conjugates its first-window sum. -/
theorem shortWindowSum_inv
    {p : ℕ} (hp : p.Prime) (χ : Character (p ^ 2)) :
    shortWindowSum hp χ⁻¹ = star (shortWindowSum hp χ) := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  unfold shortWindowSum
  change (∑ i : FirstWindowIndex p,
    (χ : MulChar (ZMod (p ^ 2)) ℂ)⁻¹ (firstWindowUnit hp i).val) = _
  change _ = (starRingEnd ℂ) (∑ i : FirstWindowIndex p,
    χ (firstWindowUnit hp i).val)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (MulChar.star_apply' (χ : MulChar (ZMod (p ^ 2)) ℂ)
    (firstWindowUnit hp i).val).symm

/-- Normalized collision coefficients and unnormalized character transforms
are the same coordinates with inverse character labels. -/
theorem collisionCoefficient_inv_eq_characterTransform
    {m : ℕ} [NeZero m] (F : UnitClass m → ℂ) (χ : Character m) :
    collisionCoefficient F χ⁻¹ =
      (m.totient : ℂ)⁻¹ * characterTransform F χ := by
  unfold collisionCoefficient finiteCoefficient characterTransform
  rw [ZMod.card_units_eq_totient]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  have hstar := MulChar.star_apply'
    ((χ : MulChar (ZMod m) ℂ)⁻¹) u.val
  have hstar' : star ((χ : MulChar (ZMod m) ℂ)⁻¹ u.val) = χ u.val := by
    simpa using hstar
  rw [hstar']
  ring

/-- An odd signal has zero transform in every even character channel. -/
theorem characterTransform_odd_even_zero
    {m : ℕ} [NeZero m] (F : UnitClass m → ℂ)
    (hF : ∀ u, F (-u) = -F u)
    (χ : Character m) (heven : χ.Even) :
    characterTransform F χ = 0 := by
  classical
  unfold characterTransform
  have hreindex :
      (∑ u : UnitClass m, χ u.val * F u) =
        ∑ u : UnitClass m, χ (-u).val * F (-u) := by
    simpa using (Equiv.sum_comp (Equiv.neg (UnitClass m))
      (fun u : UnitClass m => χ u.val * F u)).symm
  have hneg :
      (∑ u : UnitClass m, χ (-u).val * F (-u)) =
        -∑ u : UnitClass m, χ u.val * F u := by
    calc
      (∑ u : UnitClass m, χ (-u).val * F (-u)) =
          ∑ u : UnitClass m, χ u.val * (-F u) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Units.val_neg, heven.eval_neg, hF]
      _ = -∑ u : UnitClass m, χ u.val * F u := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro u _
            ring
  have hself :
      (∑ u : UnitClass m, χ u.val * F u) =
        -∑ u : UnitClass m, χ u.val * F u := hreindex.trans hneg
  linear_combination (1 / 2 : ℂ) * hself

/-- The concrete prime carry transform vanishes on every imprimitive
character channel. -/
theorem characterTransform_primeCarryCentered_imprimitive_zero
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (hpodd : p ≠ 2) (χ : Character (p ^ 2))
    (himp : ¬χ.IsPrimitive) :
    characterTransform (primeCarryCentered hp) χ = 0 := by
  have himpInv : ¬(χ⁻¹).IsPrimitive := by
    intro hinv
    apply himp
    have := inverse_isPrimitive hinv
    simpa using this
  have hfactor := baseFactored_of_prime_lag_one_imprimitive hp himpInv
  have hzero := centeredCollisionTransform_baseFactored_zero (χ⁻¹) hfactor
  rw [collisionCoefficient_inv_eq_characterTransform] at hzero
  have htot : ((p ^ 2).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos hp.pos 2)).ne'
  have htransform :
      characterTransform (centeredLagOneSpectrum p) χ = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero htot)
  rw [show centeredLagOneSpectrum p = primeCarryCentered hp by
    funext a
    exact centeredLagOneSpectrum_eq_primeCarryCentered hp hpodd a] at htransform
  exact htransform

theorem odd_character_ne_one
    {m : ℕ} [NeZero m] (χ : Character m) (hodd : χ.Odd) : χ ≠ 1 := by
  intro hχ
  subst χ
  have heven : (1 : Character m).Even := by
    unfold DirichletCharacter.Even
    exact MulChar.one_apply isUnit_neg_one
  exact (1 : Character m).not_even_and_odd ⟨heven, hodd⟩

/-- Exact primitive-channel factorization of the concrete centered carry
transform through the generalized Bernoulli coefficient and the lag-one
boundary flux. -/
theorem primitive_characterTransform_factorization
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (χ : Character (p ^ 2)) (hprim : χ.IsPrimitive) :
    characterTransform (primeCarryCentered hp) χ =
      -(bernoulliOne χ * lagOneBoundaryFlux hp χ⁻¹) := by
  have hm : 2 ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hfac := carryBoundary_factorization hm
    (primeDiagonalWeight hp)
    (inverse_isPrimitive hprim : (χ⁻¹).IsPrimitive)
  rw [carryTransform_eq_characterTransform] at hfac
  simp only [inv_inv] at hfac
  have hsignal : unitCarrySignal (primeDiagonalWeight hp) =
      primeCarryCentered hp := by
    funext a
    exact unitCarrySignal_primeDiagonalWeight_eq_centered hp a
  rw [hsignal, cellBoundaryFlux_primeDiagonalWeight_eq_lagOne hp] at hfac
  exact hfac

/-- On every primitive odd channel the concrete carry transform has exactly
four times the squared mass of the short-window sawtooth convolution. -/
theorem primitiveOdd_characterTransform_normSq
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime)
    (χ : Character (p ^ 2)) (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    Complex.normSq (characterTransform (primeCarryCentered hp) χ) =
      4 * Complex.normSq
        (characterTransform (shortWindowSawtoothSignal hp) χ) := by
  have hfac := primitive_characterTransform_factorization hp χ hprim
  have hconv := characterTransform_shortWindowSawtoothSignal hp
    (odd_character_ne_one χ hodd)
  have hinvOdd : (χ⁻¹).Odd := by
    unfold DirichletCharacter.Odd at hodd ⊢
    rw [MulChar.inv_apply_eq_inv', hodd]
    simp
  have hflux := lagOneBoundaryFlux_normSq hp χ⁻¹
    hinvOdd
  have hshort := shortWindowSum_inv hp χ
  have hshortNorm :
      Complex.normSq (shortWindowSum hp χ⁻¹) =
        Complex.normSq (shortWindowSum hp χ) := by
    rw [hshort]
    change Complex.normSq ((starRingEnd ℂ) (shortWindowSum hp χ)) = _
    exact Complex.normSq_conj _
  rw [hfac, Complex.normSq_neg, Complex.normSq_mul, hflux,
    hconv, Complex.normSq_mul, hshortNorm]
  ring

/-- The four-to-one spectral mass identity holds on every character channel,
including the even and imprimitive zero sectors. -/
theorem characterTransform_normSq_bridge
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (hpodd : p ≠ 2) (χ : Character (p ^ 2)) :
    Complex.normSq (characterTransform (primeCarryCentered hp) χ) =
      4 * Complex.normSq
        (characterTransform (shortWindowSawtoothSignal hp) χ) := by
  rcases χ.even_or_odd with heven | hodd
  · have hcarry :
        characterTransform (primeCarryCentered hp) χ = 0 := by
      rw [← show unitCarrySignal (primeDiagonalWeight hp) =
          primeCarryCentered hp by
        funext a
        exact unitCarrySignal_primeDiagonalWeight_eq_centered hp a]
      have hz := carryTransform_even_zero
        (by nlinarith [hp.two_le] : 2 ≤ p ^ 2)
        (primeDiagonalWeight hp) χ⁻¹ (inverse_even heven)
      rw [carryTransform_eq_characterTransform] at hz
      simpa using hz
    have hwindow := characterTransform_odd_even_zero
      (shortWindowSawtoothSignal hp)
      (shortWindowSawtoothSignal_neg hp) χ heven
    rw [hcarry, hwindow]
    norm_num [Complex.normSq_apply]
  · by_cases hprim : χ.IsPrimitive
    · exact primitiveOdd_characterTransform_normSq hp χ hprim hodd
    · have hcarry :=
        characterTransform_primeCarryCentered_imprimitive_zero
          hp hpodd χ hprim
      have hwindowFormula := characterTransform_shortWindowSawtoothSignal hp
        (odd_character_ne_one χ hodd)
      have hshort := shortWindowSum_eq_zero_of_imprimitive_odd
        hp χ hprim hodd
      rw [hcarry, hwindowFormula, hshort]
      norm_num [Complex.normSq_apply]

/-- Finite Parseval transports the channelwise identity back to the concrete
unit-group square masses. -/
theorem primeCarry_squareMass_eq_shortWindow
    {p : ℕ} [NeZero p] [NeZero (allLagModulus p 1)]
    (hp : p.Prime) (hpodd : p ≠ 2) :
    (∑ a : UnitClass (p ^ 2), ‖primeCarryCentered hp a‖ ^ 2) =
      4 * ∑ a : UnitClass (p ^ 2),
        ‖shortWindowSawtoothSignal hp a‖ ^ 2 := by
  have hspectrum :
      (∑ χ : Character (p ^ 2),
        ‖characterTransform (primeCarryCentered hp) χ‖ ^ 2) =
      4 * ∑ χ : Character (p ^ 2),
        ‖characterTransform (shortWindowSawtoothSignal hp) χ‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [Complex.sq_norm, Complex.sq_norm,
      characterTransform_normSq_bridge hp hpodd χ]
  rw [character_parseval, character_parseval] at hspectrum
  have htot : 0 < (p ^ 2).totient := Nat.totient_pos.mpr (pow_pos hp.pos 2)
  have htotR : (0 : ℝ) < ((p ^ 2).totient : ℝ) := by exact_mod_cast htot
  apply (mul_left_cancel₀ (ne_of_gt htotR))
  calc
    ((p ^ 2).totient : ℝ) *
        (∑ a : UnitClass (p ^ 2), ‖primeCarryCentered hp a‖ ^ 2) =
      4 * (((p ^ 2).totient : ℝ) *
        ∑ a : UnitClass (p ^ 2), ‖shortWindowSawtoothSignal hp a‖ ^ 2) :=
          hspectrum
    _ = ((p ^ 2).totient : ℝ) *
        (4 * ∑ a : UnitClass (p ^ 2),
          ‖shortWindowSawtoothSignal hp a‖ ^ 2) := by ring

/-- The concrete energy is four times the short-window sawtooth square mass. -/
theorem primeCarryEnergy_eq_shortWindow
    {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) (hpodd : p ≠ 2) :
    primeCarryEnergy hp =
      4 * ∑ a : UnitClass (p ^ 2),
        ‖shortWindowSawtoothSignal hp a‖ ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (allLagModulus p 1) := by
    simpa [allLagModulus] using (inferInstance : NeZero (p ^ 2))
  unfold primeCarryEnergy
  exact primeCarry_squareMass_eq_shortWindow hp hpodd

end NField.Alignment.PrimeCarrySpectralBridge
