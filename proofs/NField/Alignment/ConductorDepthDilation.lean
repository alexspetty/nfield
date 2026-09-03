/-
Author: Alexander S. Petty
-/

import NField.Alignment.ConductorDepthSawtooth

/-!
# Conductor-depth dilation

Exact prime-power dilation and unit-separation lemmas for induced Dirichlet
characters.  The two terminal theorems cover both sides of the conductor-depth
cutoff without finite certificates.
-/

namespace NField.Alignment.ConductorDepthDilation

open scoped BigOperators ComplexConjugate ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.ConductorDepthSawtooth

theorem centeredSawtooth_dilate_fiber
    {m D : ℕ} [NeZero m] [NeZero (m * D)]
    (hm : 2 ≤ m) (hD : 0 < D) (A : Fin m) (j : ℕ) :
    centeredSawtooth
        ((D * (A.val + m * j) : ℕ) : ZMod (m * D)) =
      centeredSawtooth (A.val : ZMod m) := by
  have hpoint : D * A.val < m * D := by
    nlinarith [A.isLt]
  have hcast :
      ((D * (A.val + m * j) : ℕ) : ZMod (m * D)) =
        ((D * A.val : ℕ) : ZMod (m * D)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    simp only [Nat.ModEq, mul_add]
    rw [show D * (m * j) = (m * D) * j by ac_rfl]
    simp
  rw [hcast]
  unfold centeredSawtooth
  by_cases hA : A.val = 0
  · simp [hA]
  · have hDA :
        ((D * A.val : ℕ) : ZMod (m * D)) ≠ 0 := by
      intro hz
      have hdvd := (ZMod.natCast_eq_zero_iff (D * A.val) (m * D)).mp hz
      have hle := Nat.le_of_dvd (Nat.mul_pos hD (Nat.pos_of_ne_zero hA)) hdvd
      omega
    have hAlow : (A.val : ZMod m) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt A.isLt, hA] at hv
    simp only [hDA, hAlow, if_false]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hpoint]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt A.isLt]
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hDC : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    field_simp [hmC, hDC]

theorem centeredSawtooth_dilate_nat
    {m D : ℕ} [NeZero m] [NeZero (m * D)]
    (hm : 2 ≤ m) (hD : 0 < D) (x : ℕ) :
    centeredSawtooth ((D * x : ℕ) : ZMod (m * D)) =
      centeredSawtooth (x : ZMod m) := by
  let A : Fin m := ⟨x % m, Nat.mod_lt _ (by omega)⟩
  have htop :
      ((D * x : ℕ) : ZMod (m * D)) =
        ((D * (A.val + m * (x / m)) : ℕ) : ZMod (m * D)) := by
    congr 1
    dsimp [A]
    rw [Nat.mod_add_div]
  have hlow : (x : ZMod m) = (A.val : ZMod m) := by
    rw [ZMod.natCast_eq_natCast_iff]
    simp [A, Nat.ModEq]
  rw [htop, hlow]
  exact centeredSawtooth_dilate_fiber hm hD A (x / m)

theorem changeLevel_primePower_triple_apply_nat
    {p t r v a : ℕ} (hp : p.Prime) (ht : 1 ≤ t)
    (ψ : Character (p ^ t)) :
    DirichletCharacter.changeLevel
        (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v)) ψ
        (a : ZMod ((p ^ t * p ^ r) * p ^ v)) =
      ψ (a : ZMod (p ^ t)) := by
  letI : NeZero ((p ^ t * p ^ r) * p ^ v) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero))
      (pow_ne_zero _ hp.ne_zero)⟩
  have hmod : (p ^ t * p ^ r) * p ^ v = p ^ (t + r + v) := by
    simp [pow_add, mul_assoc]
  by_cases hpa : p ∣ a
  · have hnotTop : ¬IsUnit (a : ZMod ((p ^ t * p ^ r) * p ^ v)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [hmod]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact not_not_intro hpa
    have hnotLower : ¬IsUnit (a : ZMod (p ^ t)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact not_not_intro hpa
    rw [MulChar.map_nonunit _ hnotTop, MulChar.map_nonunit _ hnotLower]
  · have hcop : a.Coprime ((p ^ t * p ^ r) * p ^ v) := by
      rw [hmod]
      rw [Nat.coprime_pow_right_iff (by omega)]
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hpa
    simpa using
      (DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ
        (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v))
        (Nat.isCoprime_iff_coprime.mpr hcop))

theorem inducedSawtooth_dilation_at
    {p t r v : ℕ}
    [NeZero ((p ^ t * p ^ r) * p ^ v)] [NeZero (p ^ t * p ^ r)]
    (hp : p.Prime) (ht : 1 ≤ t) (ψ : Character (p ^ t)) (k : ℕ) :
    twistedTransform (m := (p ^ t * p ^ r) * p ^ v) centeredSawtooth
        (DirichletCharacter.changeLevel
          (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v)) ψ)
        ((p ^ v * k : ℕ) : ZMod ((p ^ t * p ^ r) * p ^ v)) =
      (p ^ v : ℂ) *
        twistedTransform (m := p ^ t * p ^ r) centeredSawtooth
          (DirichletCharacter.changeLevel
            (Nat.dvd_mul_right (p ^ t) (p ^ r)) ψ)
          (k : ZMod (p ^ t * p ^ r)) := by
  classical
  let m := p ^ t * p ^ r
  let D := p ^ v
  have hm : 2 ≤ m := by
    have hpt : 2 ≤ p ^ t := by
      have hpow : p ≤ p ^ t := Nat.le_pow ht
      exact hp.two_le.trans hpow
    have hpr : 0 < p ^ r := pow_pos hp.pos _
    dsimp [m]
    nlinarith
  have hD : 0 < D := pow_pos hp.pos _
  letI : NeZero m := ⟨by simp [m, hp.ne_zero]⟩
  letI : NeZero D := ⟨hD.ne'⟩
  haveI : NeZero (m * D) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne D)⟩
  let e : Fin D × Fin m ≃ Fin (m * D) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm D m))
  unfold twistedTransform
  calc
    (∑ a : ZMod (m * D),
        centeredSawtooth (((p ^ v * k : ℕ) : ZMod (m * D)) * a) *
        DirichletCharacter.changeLevel
          (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v)) ψ a) =
      ∑ z : Fin (m * D),
        centeredSawtooth (((p ^ v * k : ℕ) : ZMod (m * D)) *
          ZMod.finEquiv (m * D) z) *
          DirichletCharacter.changeLevel
            (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v)) ψ
            (ZMod.finEquiv (m * D) z) := by
              symm
              apply Fintype.sum_equiv (ZMod.finEquiv (m * D)).toEquiv
              intro z
              rfl
    _ = ∑ ij : Fin D × Fin m,
        centeredSawtooth ((k * ij.2.val : ℕ) : ZMod m) *
          ψ (ij.2.val : ZMod (p ^ t)) := by
            symm
            apply Fintype.sum_equiv e
            intro ij
            have hz : ZMod.finEquiv (m * D) (e ij) =
                ((ij.2.val + m * ij.1.val : ℕ) : ZMod (m * D)) := by
              rw [finEquiv_eq_natCast]
              congr 1
            rw [hz]
            rw [show ((p ^ v * k : ℕ) : ZMod (m * D)) *
                ((ij.2.val + m * ij.1.val : ℕ) : ZMod (m * D)) =
              ((p ^ v * (k * (ij.2.val + m * ij.1.val)) : ℕ) :
                ZMod (m * D)) by
                push_cast
                ring]
            rw [centeredSawtooth_dilate_nat hm hD]
            rw [show
              ((k * (ij.2.val + m * ij.1.val) : ℕ) : ZMod m) =
                ((k * ij.2.val : ℕ) : ZMod m) by
                  push_cast
                  simp]
            rw [changeLevel_primePower_triple_apply_nat hp ht ψ]
            rw [show
              ((ij.2.val + m * ij.1.val : ℕ) : ZMod (p ^ t)) =
                (ij.2.val : ZMod (p ^ t)) by simp [m]]
    _ = (p ^ v : ℂ) * ∑ A : Fin m,
        centeredSawtooth ((k * A.val : ℕ) : ZMod m) *
          ψ (A.val : ZMod (p ^ t)) := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          dsimp [D]
          push_cast
          rfl
    _ = (p ^ v : ℂ) * ∑ a : ZMod m,
        centeredSawtooth ((k : ZMod m) * a) *
        DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ r)) ψ a := by
            congr 1
            apply Fintype.sum_equiv (ZMod.finEquiv m).toEquiv
            intro A
            change centeredSawtooth ((k * A.val : ℕ) : ZMod m) *
                ψ (A.val : ZMod (p ^ t)) =
              centeredSawtooth ((k : ZMod m) * ZMod.finEquiv m A) *
                DirichletCharacter.changeLevel
                  (Nat.dvd_mul_right (p ^ t) (p ^ r)) ψ (ZMod.finEquiv m A)
            rw [finEquiv_eq_natCast]
            rw [changeLevel_primePower_product_apply_nat hp ht ψ]
            congr 2
            push_cast
            rfl

theorem inducedSawtooth_dilation
    {p t r v : ℕ}
    [NeZero ((p ^ t * p ^ r) * p ^ v)] [NeZero (p ^ t * p ^ r)]
    (hp : p.Prime) (ht : 1 ≤ t) (ψ : Character (p ^ t)) :
    twistedTransform (m := (p ^ t * p ^ r) * p ^ v) centeredSawtooth
        (DirichletCharacter.changeLevel
          (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v)) ψ)
        (p ^ v : ZMod ((p ^ t * p ^ r) * p ^ v)) =
      (p ^ v : ℂ) *
        twistedTransform (m := p ^ t * p ^ r) centeredSawtooth
          (DirichletCharacter.changeLevel
            (Nat.dvd_mul_right (p ^ t) (p ^ r)) ψ) 1 := by
  simpa using inducedSawtooth_dilation_at hp ht ψ 1

theorem twistedTransform_unit_multiplier
    {m : ℕ} [NeZero m] (f : ZMod m → ℂ) (ψ : Character m)
    (u : (ZMod m)ˣ) (k : ZMod m) :
    twistedTransform f ψ ((u : ZMod m) * k) =
      ψ⁻¹ (u : ZMod m) * twistedTransform f ψ k := by
  classical
  unfold twistedTransform
  calc
    (∑ a : ZMod m, f (((u : ZMod m) * k) * a) * ψ a) =
      ∑ b : ZMod m,
        ψ⁻¹ (u : ZMod m) * (f (k * b) * ψ b) := by
          apply Fintype.sum_equiv u.mulLeft
          intro a
          simp only [Units.mulLeft_apply, map_mul]
          have hu : ψ (u : ZMod m) ≠ 0 := by
            exact (u.isUnit.map ψ).ne_zero
          rw [MulChar.inv_apply_eq_inv']
          change f ((u : ZMod m) * k * a) * ψ a =
            (ψ (u : ZMod m))⁻¹ *
              (f (k * ((u : ZMod m) * a)) *
                (ψ (u : ZMod m) * ψ a))
          rw [show k * ((u : ZMod m) * a) = (u : ZMod m) * k * a by ring]
          rw [show (ψ (u : ZMod m))⁻¹ *
                (f ((u : ZMod m) * k * a) * (ψ (u : ZMod m) * ψ a)) =
              (ψ (u : ZMod m))⁻¹ * ψ (u : ZMod m) *
                (f ((u : ZMod m) * k * a) * ψ a) by ring]
          rw [inv_mul_cancel₀ hu, one_mul]
    _ = ψ⁻¹ (u : ZMod m) * ∑ b : ZMod m, f (k * b) * ψ b := by
      rw [Finset.mul_sum]

theorem conductorDepth_twist_of_decomposition
    {p t r v u : ℕ}
    [NeZero ((p ^ t * p ^ r) * p ^ v)] [NeZero (p ^ t * p ^ r)]
    [NeZero (p ^ t)] (hp : p.Prime) (ht : 1 ≤ t)
    (hu : ¬p ∣ u) (ψ : Character (p ^ t)) :
    twistedTransform (m := (p ^ t * p ^ r) * p ^ v) centeredSawtooth
        (DirichletCharacter.changeLevel
          (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v)) ψ)
        ((p ^ v * u : ℕ) : ZMod ((p ^ t * p ^ r) * p ^ v)) =
      (p ^ v : ℂ) * ψ⁻¹ (u : ZMod (p ^ t)) *
        twistedTransform (m := p ^ t) centeredSawtooth ψ 1 := by
  let top := (p ^ t * p ^ r) * p ^ v
  have htop : top = p ^ (t + r + v) := by simp [top, pow_add, mul_assoc]
  have hcop : u.Coprime top := by
    rw [htop]
    rw [Nat.coprime_pow_right_iff (by omega)]
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact hu
  let U : (ZMod top)ˣ := ZMod.unitOfCoprime u hcop
  have hU : (U : ZMod top) = (u : ZMod top) := ZMod.coe_unitOfCoprime u hcop
  have hmult :
      ((p ^ v * u : ℕ) : ZMod top) =
        (U : ZMod top) * (p ^ v : ZMod top) := by
    rw [hU]
    push_cast
    ring
  rw [hmult]
  rw [twistedTransform_unit_multiplier]
  rw [inducedSawtooth_dilation hp ht ψ]
  rw [inducedSawtooth_distribution hp ht ψ]
  rw [MulChar.inv_apply_eq_inv']
  rw [show
    (DirichletCharacter.changeLevel
      (dvd_mul_of_dvd_left (Nat.dvd_mul_right (p ^ t) (p ^ r)) (p ^ v)) ψ)
        (U : ZMod top) = ψ (u : ZMod (p ^ t)) by
          rw [hU]
          exact changeLevel_primePower_triple_apply_nat hp ht ψ]
  rw [← MulChar.inv_apply_eq_inv']
  ring

/--
Transport the within-budget response from a factored prime-power modulus to an
arbitrary definitionally equal ambient modulus. Keeping this transport
separate prevents proof terms for divisibility and NeZero from leaking into
the mathematical statement.
-/
theorem conductorDepth_twist_of_factored_modulus
    {top p t r v u : ℕ}
    [NeZero top] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t)
    (hu : ¬p ∣ u) (ψ : Character (p ^ t))
    (htop : top = (p ^ t * p ^ r) * p ^ v)
    (hdvd : p ^ t ∣ top) :
    twistedTransform (m := top) centeredSawtooth
        (DirichletCharacter.changeLevel hdvd ψ)
        ((p ^ v * u : ℕ) : ZMod top) =
      (p ^ v : ℂ) * ψ⁻¹ (u : ZMod (p ^ t)) *
        twistedTransform (m := p ^ t) centeredSawtooth ψ 1 := by
  subst top
  letI : NeZero (p ^ t * p ^ r) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero)⟩
  simpa using
    (conductorDepth_twist_of_decomposition (p := p) (t := t)
      (r := r) (v := v) (u := u) hp ht hu ψ)

/--
Exact conductor-depth response at a fixed ambient level. A lag p^v u
inside the available depth budget contributes its multiplicity p^v and the
primitive unit twist.
-/
theorem conductorDepth_twist_within_budget
    {p t s v u : ℕ}
    [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t) (hv : v ≤ s)
    (hu : ¬p ∣ u) (ψ : Character (p ^ t)) :
    twistedTransform (m := p ^ t * p ^ s) centeredSawtooth
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ)
        ((p ^ v * u : ℕ) : ZMod (p ^ t * p ^ s)) =
      (p ^ v : ℂ) * ψ⁻¹ (u : ZMod (p ^ t)) *
        twistedTransform (m := p ^ t) centeredSawtooth ψ 1 := by
  apply conductorDepth_twist_of_factored_modulus
    (p := p) (t := t) (r := s - v) (v := v) (u := u) hp ht hu ψ
  · calc
      p ^ t * p ^ s = p ^ (t + s) := by rw [pow_add]
      _ = p ^ ((t + (s - v)) + v) := by
        congr 1
        omega
      _ = (p ^ t * p ^ (s - v)) * p ^ v := by
        rw [pow_add, pow_add]

theorem inducedSawtooth_base_dilation_at
    {p t v : ℕ} [NeZero (p ^ t * p ^ v)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t) (ψ : Character (p ^ t)) (k : ℕ) :
    twistedTransform (m := p ^ t * p ^ v) centeredSawtooth
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ v)) ψ)
        ((p ^ v * k : ℕ) : ZMod (p ^ t * p ^ v)) =
      (p ^ v : ℂ) *
        twistedTransform (m := p ^ t) centeredSawtooth ψ
          (k : ZMod (p ^ t)) := by
  classical
  let q := p ^ t
  let D := p ^ v
  have hq : 2 ≤ q := hp.two_le.trans (Nat.le_pow ht)
  have hD : 0 < D := pow_pos hp.pos _
  letI : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero D := ⟨hD.ne'⟩
  haveI : NeZero (q * D) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne D)⟩
  let e : Fin D × Fin q ≃ Fin (q * D) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm D q))
  unfold twistedTransform
  calc
    (∑ a : ZMod (q * D),
        centeredSawtooth (((p ^ v * k : ℕ) : ZMod (q * D)) * a) *
          DirichletCharacter.changeLevel
            (Nat.dvd_mul_right (p ^ t) (p ^ v)) ψ a) =
      ∑ z : Fin (q * D),
        centeredSawtooth (((p ^ v * k : ℕ) : ZMod (q * D)) *
          ZMod.finEquiv (q * D) z) *
          DirichletCharacter.changeLevel
            (Nat.dvd_mul_right (p ^ t) (p ^ v)) ψ
            (ZMod.finEquiv (q * D) z) := by
              symm
              apply Fintype.sum_equiv (ZMod.finEquiv (q * D)).toEquiv
              intro z
              rfl
    _ = ∑ ij : Fin D × Fin q,
        centeredSawtooth ((k * ij.2.val : ℕ) : ZMod q) *
          ψ (ij.2.val : ZMod q) := by
            symm
            apply Fintype.sum_equiv e
            intro ij
            have hz : ZMod.finEquiv (q * D) (e ij) =
                ((ij.2.val + q * ij.1.val : ℕ) : ZMod (q * D)) := by
              rw [finEquiv_eq_natCast]
              congr 1
            rw [hz]
            rw [show ((p ^ v * k : ℕ) : ZMod (q * D)) *
                ((ij.2.val + q * ij.1.val : ℕ) : ZMod (q * D)) =
              ((p ^ v * (k * (ij.2.val + q * ij.1.val)) : ℕ) :
                ZMod (q * D)) by
                  push_cast
                  ring]
            rw [centeredSawtooth_dilate_nat hq hD]
            rw [show
              ((k * (ij.2.val + q * ij.1.val) : ℕ) : ZMod q) =
                ((k * ij.2.val : ℕ) : ZMod q) by
                  push_cast
                  simp]
            rw [changeLevel_primePower_product_apply_nat hp ht ψ]
            rw [show
              ((ij.2.val + q * ij.1.val : ℕ) : ZMod q) =
                (ij.2.val : ZMod q) by simp]
    _ = (p ^ v : ℂ) * ∑ A : Fin q,
        centeredSawtooth ((k * A.val : ℕ) : ZMod q) *
          ψ (A.val : ZMod q) := by
            rw [Fintype.sum_prod_type]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            dsimp [D]
            push_cast
            rfl
    _ = (p ^ v : ℂ) * ∑ a : ZMod q,
        centeredSawtooth ((k : ZMod q) * a) * ψ a := by
          congr 1
          apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
          intro A
          change centeredSawtooth ((k * A.val : ℕ) : ZMod q) *
              ψ (A.val : ZMod q) =
            centeredSawtooth ((k : ZMod q) * ZMod.finEquiv q A) *
              ψ (ZMod.finEquiv q A)
          rw [finEquiv_eq_natCast]
          congr 2
          push_cast
          rfl

theorem conductorDepth_twist_vanishes_beyond_conductor
    {p t s r : ℕ}
    [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    twistedTransform (m := p ^ t * p ^ s) centeredSawtooth
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ)
        ((p ^ s * p ^ (r + 1) : ℕ) : ZMod (p ^ t * p ^ s)) = 0 := by
  rw [inducedSawtooth_base_dilation_at hp ht ψ (p ^ (r + 1))]
  have hnonunit : ¬IsUnit ((p ^ (r + 1) : ℕ) : ZMod (p ^ t)) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_pow_right_iff (by omega)]
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    simp
  have hlower :
      twistedTransform (m := p ^ t) centeredSawtooth ψ
        ((p ^ (r + 1) : ℕ) : ZMod (p ^ t)) = 0 := by
    rw [twistedTransform_eq_inv_mul centeredSawtooth hψ]
    rw [MulChar.map_nonunit _ hnonunit, zero_mul]
  rw [hlower, mul_zero]

theorem conductorDepth_twist_vanishes_of_overdepth_decomposition
    {p t s r u : ℕ} [NeZero (p ^ t * p ^ s)] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t) (hu : ¬p ∣ u)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive) :
    twistedTransform (m := p ^ t * p ^ s) centeredSawtooth
        (DirichletCharacter.changeLevel
          (Nat.dvd_mul_right (p ^ t) (p ^ s)) ψ)
        ((p ^ s * p ^ (r + 1) * u : ℕ) : ZMod (p ^ t * p ^ s)) = 0 := by
  let top := p ^ t * p ^ s
  have htop : top = p ^ (t + s) := by simp [top, pow_add]
  have hcop : u.Coprime top := by
    rw [htop]
    rw [Nat.coprime_pow_right_iff (by omega)]
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact hu
  let U : (ZMod top)ˣ := ZMod.unitOfCoprime u hcop
  have hU : (U : ZMod top) = (u : ZMod top) := ZMod.coe_unitOfCoprime u hcop
  have hmult :
      ((p ^ s * p ^ (r + 1) * u : ℕ) : ZMod top) =
        (U : ZMod top) *
          ((p ^ s * p ^ (r + 1) : ℕ) : ZMod top) := by
    rw [hU]
    push_cast
    ring
  rw [hmult]
  rw [twistedTransform_unit_multiplier]
  rw [conductorDepth_twist_vanishes_beyond_conductor hp ht hψ]
  rw [mul_zero]

/--
Transport higher-depth invisibility to an arbitrary ambient modulus equal to
the corresponding conductor times its depth budget.
-/
theorem conductorDepth_twist_vanishes_of_factored_modulus
    {top p t s r u : ℕ} [NeZero top] [NeZero (p ^ t)]
    (hp : p.Prime) (ht : 1 ≤ t) (hu : ¬p ∣ u)
    {ψ : Character (p ^ t)} (hψ : ψ.IsPrimitive)
    (htop : top = p ^ t * p ^ s) (hdvd : p ^ t ∣ top) :
    twistedTransform (m := top) centeredSawtooth
        (DirichletCharacter.changeLevel hdvd ψ)
        ((p ^ s * p ^ (r + 1) * u : ℕ) : ZMod top) = 0 := by
  subst top
  simpa using
    (conductorDepth_twist_vanishes_of_overdepth_decomposition
      (p := p) (t := t) (s := s) (r := r) (u := u)
      hp ht hu hψ)

end NField.Alignment.ConductorDepthDilation
