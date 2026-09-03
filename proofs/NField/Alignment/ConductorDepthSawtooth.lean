/-
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra

/-!
# Conductor-depth response of the centered sawtooth

This file proves the exact fiber distribution that underlies conductor-depth
stratification.  Its declarations are named for the mathematical objects they
formalize, independently of any manuscript ordering.
-/

namespace NField.Alignment.ConductorDepthSawtooth

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra

/-- The standard equivalence from `Fin n` to `ZMod n` is the natural-number
representative map. -/
theorem finEquiv_eq_natCast {n : ℕ} [NeZero n] (a : Fin n) :
    ZMod.finEquiv n a = (a.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [← ZMod.natCast_zmod_val (ZMod.finEquiv (n + 1) a)]
      rfl

/-- On a nonzero residue class modulo `q`, the centered sawtooth at modulus
`q * L` sums over the entire reduction fiber to the centered sawtooth modulo
`q`. -/
theorem sawtooth_fiber_distribution
    {q L : ℕ} [NeZero q] [NeZero (q * L)]
    (hq : 2 ≤ q) (hL : 0 < L) (A : Fin q) (hA : A.val ≠ 0) :
    (∑ j : Fin L,
      centeredSawtooth ((A.val + q * j.val : ℕ) : ZMod (q * L))) =
      centeredSawtooth (A.val : ZMod q) := by
  classical
  have hq0 : 0 < q := by omega
  have htop0 : (q * L : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero hq0.ne' hL.ne')
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpoint (j : Fin L) :
      (A.val + q * j.val : ℕ) < q * L := by
    have hAq := A.isLt
    have hj := j.isLt
    nlinarith
  have hnonzero (j : Fin L) :
      ((A.val + q * j.val : ℕ) : ZMod (q * L)) ≠ 0 := by
    intro hz
    have hdvd : q * L ∣ A.val + q * j.val :=
      (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hv' : (A.val + q * j.val) % (q * L) = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd
    rw [Nat.mod_eq_of_lt (hpoint j)] at hv'
    omega
  have hAcast : (A.val : ZMod q) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt A.isLt, hA] at hv
  have hsumj :
      (∑ j : Fin L, (j.val : ℂ)) = (L : ℂ) * (L - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range]
    field_simp
    have hsub : (L : ℂ) - 1 = ((L - 1 : ℕ) : ℂ) := by
      symm
      simpa using (Nat.cast_sub hL :
        ((L - 1 : ℕ) : ℂ) = (L : ℂ) - (1 : ℕ))
    rw [← Nat.cast_sum, hsub]
    norm_cast
    exact_mod_cast Finset.sum_range_id_mul_two L
  unfold centeredSawtooth
  simp only [hnonzero, hAcast, if_false]
  simp_rw [ZMod.val_natCast]
  simp_rw [Nat.mod_eq_of_lt (hpoint _)]
  rw [Nat.mod_eq_of_lt A.isLt]
  rw [Finset.sum_sub_distrib]
  simp_rw [Nat.cast_add, Nat.cast_mul]
  simp_rw [add_div]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hfactor (j : Fin L) :
      (q : ℂ) * (j.val : ℂ) / ((q : ℂ) * (L : ℂ)) =
        ((q : ℂ) / ((q : ℂ) * (L : ℂ))) * (j.val : ℂ) := by ring
  simp_rw [hfactor, ← Finset.mul_sum, hsumj]
  field_simp [htop0, hqC, hLC]
  ring

/-- Evaluation of a character raised from `p^t` to `p^N` on a natural
representative.  The statement includes nonunits, where both sides vanish. -/
theorem changeLevel_primePower_apply_nat
    {p t N a : ℕ} (hp : p.Prime) (ht : 1 ≤ t) (htN : t ≤ N)
    (ψ : Character (p ^ t)) :
    DirichletCharacter.changeLevel (pow_dvd_pow p htN) ψ
        (a : ZMod (p ^ N)) =
      ψ (a : ZMod (p ^ t)) := by
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_cases hpa : p ∣ a
  · have hnotTop : ¬IsUnit (a : ZMod (p ^ N)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact not_not_intro hpa
    have hnotLower : ¬IsUnit (a : ZMod (p ^ t)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact not_not_intro hpa
    rw [MulChar.map_nonunit _ hnotTop, MulChar.map_nonunit _ hnotLower]
  · have hcop : a.Coprime (p ^ N) := by
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hpa
    simpa using
      (DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ
        (pow_dvd_pow p htN) (Nat.isCoprime_iff_coprime.mpr hcop))

/-- Product-form specialization of `changeLevel_primePower_apply_nat`. -/
theorem changeLevel_primePower_product_apply_nat
    {p t s a : ℕ} (hp : p.Prime) (ht : 1 ≤ t)
    (ψ : Character (p ^ t)) :
    DirichletCharacter.changeLevel (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ
        (a : ZMod (p ^ t * p ^ s)) =
      ψ (a : ZMod (p ^ t)) := by
  letI : NeZero (p ^ t * p ^ s) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero)⟩
  by_cases hpa : p ∣ a
  · have hnotTop : ¬IsUnit (a : ZMod (p ^ t * p ^ s)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [← pow_add]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact not_not_intro hpa
    have hnotLower : ¬IsUnit (a : ZMod (p ^ t)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact not_not_intro hpa
    rw [MulChar.map_nonunit _ hnotTop, MulChar.map_nonunit _ hnotLower]
  · have hcop : a.Coprime (p ^ t * p ^ s) := by
      rw [← pow_add]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hpa
    simpa using
      (DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ
        (Nat.dvd_mul_right (p ^ t) (p ^ s))
        (Nat.isCoprime_iff_coprime.mpr hcop))

/-- The centered-sawtooth transform of a character induced from `p^t` is
unchanged when the ambient modulus is enlarged by a factor `p^s`. -/
theorem inducedSawtooth_distribution
    {p t s : ℕ} [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t)
    (ψ : Character (p ^ t)) :
    twistedTransform (m := p ^ t * p ^ s) centeredSawtooth
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ) 1 =
      twistedTransform (m := p ^ t) centeredSawtooth ψ 1 := by
  classical
  let q := p ^ t
  let L := p ^ s
  have hq : 2 ≤ q := by
    have hp2 := hp.two_le
    have hpow : p ≤ p ^ t := by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ t := Nat.pow_le_pow_right hp.pos ht
    omega
  have hL : 0 < L := pow_pos hp.pos _
  letI : Fact (1 < p ^ t) := ⟨by simpa [q] using (show 1 < q by omega)⟩
  letI : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero L := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (q * L) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne L)⟩
  let e : Fin L × Fin q ≃ Fin (q * L) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm L q))
  unfold twistedTransform
  simp only [one_mul]
  calc
    (∑ a : ZMod (q * L), centeredSawtooth a *
        DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ a) =
      ∑ z : Fin (q * L), centeredSawtooth (ZMod.finEquiv (q * L) z) *
        DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ
          (ZMod.finEquiv (q * L) z) := by
            symm
            apply Fintype.sum_equiv (ZMod.finEquiv (q * L)).toEquiv
            intro z
            rfl
    _ = ∑ ij : Fin L × Fin q,
        centeredSawtooth ((ij.2.val + q * ij.1.val : ℕ) : ZMod (q * L)) *
          ψ (ij.2.val : ZMod q) := by
            symm
            apply Fintype.sum_equiv e
            intro ij
            have hz :
                ZMod.finEquiv (q * L) (e ij) =
                  ((ij.2.val + q * ij.1.val : ℕ) : ZMod (q * L)) := by
              rw [finEquiv_eq_natCast]
              congr 1
            rw [hz]
            rw [changeLevel_primePower_product_apply_nat hp ht ψ]
            rw [show
              ((ij.2.val + q * ij.1.val : ℕ) : ZMod q) =
                (ij.2.val : ZMod q) by simp]
    _ = ∑ A : Fin q,
        (∑ j : Fin L,
          centeredSawtooth ((A.val + q * j.val : ℕ) : ZMod (q * L))) *
            ψ (A.val : ZMod q) := by
              rw [Fintype.sum_prod_type]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro A _
              rw [Finset.sum_mul]
    _ = ∑ A : Fin q,
        centeredSawtooth (A.val : ZMod q) * ψ (A.val : ZMod q) := by
          apply Finset.sum_congr rfl
          intro A _
          by_cases hA : A.val = 0
          · have hAz : A = 0 := Fin.ext hA
            subst A
            have hψ0 : ψ ((0 : Fin q).val : ZMod q) = 0 := by
              simpa using ψ.map_zero
            rw [hψ0]
            simp
          · rw [sawtooth_fiber_distribution hq hL A hA]
    _ = ∑ a : ZMod q, centeredSawtooth a * ψ a := by
      apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
      intro A
      change centeredSawtooth (A.val : ZMod q) * ψ (A.val : ZMod q) =
        centeredSawtooth (ZMod.finEquiv q A) * ψ (ZMod.finEquiv q A)
      rw [finEquiv_eq_natCast]

end NField.Alignment.ConductorDepthSawtooth
