/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPeriodicTable
import NField.Alignment.CenteredCollisionSum
import NField.Alignment.CollisionCharacterStructure

/-!
# The collision transform and the critical strip

Finite all-lag reflection, exact fiber, centered-symmetry, character-gate,
Fourier-inversion, finite-prime-packet, and zero-ledger algebra for the Lean
companion to "The Collision Transform and the Critical Strip".
-/

namespace NField.Alignment.CollisionTransformStrip

open scoped BigOperators ComplexConjugate
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionPeriodicTable
open NField.Alignment.CenteredCollisionSum
open NField.Alignment.CollisionCharacterStructure

theorem allLagDiagonal_index_lt {b ell n : ℕ} (hb2 : 2 ≤ b)
    (hell : 1 ≤ ell) (hn : n ∈ allLagDiagonal b ell) :
    n < allLagModulus b ell := by
  unfold allLagDiagonal at hn
  rcases Finset.mem_image.mp hn with ⟨⟨d, k⟩, hdk, hnEq⟩
  subst n
  change (b ^ ell + 1) * d + b * k < allLagModulus b ell
  have hd : d < b := Finset.mem_range.mp (Finset.mem_product.mp hdk).1
  have hk : k < b ^ (ell - 1) :=
    Finset.mem_range.mp (Finset.mem_product.mp hdk).2
  have hKpos : 0 < b ^ (ell - 1) := pow_pos (by omega) _
  have hle :
      (b ^ ell + 1) * d + b * k ≤
        (b ^ ell + 1) * (b - 1) + b * (b ^ (ell - 1) - 1) := by
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left _ (by omega)
    · exact Nat.mul_le_mul_left _ (by omega)
  have hmax :
      (b ^ ell + 1) * (b - 1) + b * (b ^ (ell - 1) - 1) =
        allLagModulus b ell - 1 := by
    cases ell with
    | zero => omega
    | succ j =>
      unfold allLagModulus
      simp only [Nat.succ_sub_one]
      let B := b - 1
      let P := b ^ j
      let R := P - 1
      have hbEq : b = B + 1 := by
        dsimp [B]
        omega
      have hPEq : P = R + 1 := by
        dsimp [P, R]
        have hPpos : 0 < b ^ j := pow_pos (by omega) j
        exact (Nat.sub_add_cancel (by omega)).symm
      rw [pow_succ, show j + 1 + 1 = (j + 1) + 1 by omega, pow_succ]
      change ((P * b) + 1) * B + b * R = (P * b * b) - 1
      rw [hbEq, hPEq]
      ring_nf
      omega
  rw [hmax] at hle
  have hqpos : 0 < allLagModulus b ell :=
    pow_pos (by omega) (ell + 1)
  omega

theorem allLagDiagonal_zero_mem {b ell : ℕ} (hb2 : 2 ≤ b) :
    0 ∈ allLagDiagonal b ell := by
  unfold allLagDiagonal
  apply Finset.mem_image.mpr
  refine ⟨(0, 0), Finset.mem_product.mpr ⟨?_, ?_⟩, by simp⟩
  · exact Finset.mem_range.mpr (by omega)
  · exact Finset.mem_range.mpr (pow_pos (by omega) _)

theorem allLag_last_index_eq {b ell : ℕ} (hb2 : 2 ≤ b)
    (hell : 1 ≤ ell) :
    (b ^ ell + 1) * (b - 1) + b * (b ^ (ell - 1) - 1) =
      allLagModulus b ell - 1 := by
  cases ell with
  | zero => omega
  | succ j =>
    unfold allLagModulus
    simp only [Nat.succ_sub_one]
    let B := b - 1
    let P := b ^ j
    let R := P - 1
    have hbEq : b = B + 1 := by
      dsimp [B]
      omega
    have hPEq : P = R + 1 := by
      dsimp [P, R]
      have hPpos : 0 < b ^ j := pow_pos (by omega) j
      exact (Nat.sub_add_cancel (by omega)).symm
    rw [pow_succ, show j + 1 + 1 = (j + 1) + 1 by omega, pow_succ]
    change ((P * b) + 1) * B + b * R = (P * b * b) - 1
    rw [hbEq, hPEq]
    ring_nf
    omega

theorem allLagDiagonal_last_mem {b ell : ℕ} (hb2 : 2 ≤ b)
    (hell : 1 ≤ ell) :
    allLagModulus b ell - 1 ∈ allLagDiagonal b ell := by
  have hKpos : 0 < b ^ (ell - 1) := pow_pos (by omega) _
  unfold allLagDiagonal
  apply Finset.mem_image.mpr
  refine ⟨(b - 1, b ^ (ell - 1) - 1),
    Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_range.mpr (Nat.sub_lt (by omega) (by omega))
  · exact Finset.mem_range.mpr (Nat.sub_lt hKpos (by omega))
  · simpa using allLag_last_index_eq hb2 hell

theorem allLag_jump_pair_value {b ell a n : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell))
    (hn : n ∈ allLagDiagonal b ell) :
    floorJump (allLagModulus b ell) a n +
        floorJump (allLagModulus b ell)
          (allLagModulus b ell - a) n =
      1 + (if n = allLagModulus b ell - 1 then 1 else 0) -
        (if n = 0 then 1 else 0) := by
  have hq : 0 < allLagModulus b ell := pow_pos (by omega) _
  by_cases hn0 : n = 0
  · subst n
    rw [floorJump_complement_zero hq ha halt]
    simp
    omega
  by_cases hnlast : n = allLagModulus b ell - 1
  · subst n
    rw [floorJump_complement_last hq ha halt]
    simp
    omega
  · have hnlt := allLagDiagonal_index_lt hb2 hell hn
    have hnpos : 0 < n := by omega
    have hnnext : n + 1 < allLagModulus b ell := by omega
    rw [floorJump_complement_interior hq halt hnpos hnnext hcop]
    simp [hn0, hnlast]

theorem allLag_jump_pair_sum {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    ∑ n ∈ allLagDiagonal b ell,
      (floorJump (allLagModulus b ell) a n +
        floorJump (allLagModulus b ell)
          (allLagModulus b ell - a) n) = b ^ ell := by
  rw [Finset.sum_congr rfl
    (fun n hn => allLag_jump_pair_value hb2 hell ha halt hcop hn)]
  have hzero := allLagDiagonal_zero_mem (b := b) (ell := ell) hb2
  have hlast := allLagDiagonal_last_mem hb2 hell
  have hcard := allLagDiagonal_card hb2 hell
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [hzero, hlast, hcard]

theorem allLag_quotient_complement {b ell a : ℕ}
    (hb2 : 2 ≤ b) (_ha : 0 < a)
    (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    a / b + (allLagModulus b ell - a) / b = b ^ ell - 1 := by
  have hb : 0 < b := by omega
  have hmod : a % b ≠ 0 :=
    mod_base_ne_zero_of_coprime_power hb2 hcop
  have hmodulus : allLagModulus b ell = b ^ ell * b := by
    unfold allLagModulus
    rw [pow_succ]
  have hdiv : (b ^ ell * b - a) / b = b ^ ell - a / b - 1 :=
    complement_div hb (by simpa [hmodulus] using halt) hmod
  rw [hmodulus, hdiv]
  have hq : a / b < b ^ ell := by
    apply (Nat.div_lt_iff_lt_mul hb).2
    simpa [hmodulus] using halt
  let x := a / b
  change x + (b ^ ell - x - 1) = b ^ ell - 1
  change x < b ^ ell at hq
  have hx1 : x + 1 ≤ b ^ ell := by omega
  have hcancel := Nat.sub_add_cancel hx1
  have hsub : b ^ ell - x - 1 = b ^ ell - (x + 1) := by omega
  rw [hsub]
  have hsum : x + (b ^ ell - (x + 1)) + 1 = b ^ ell := by omega
  exact Nat.eq_sub_of_add_eq hsum

theorem allLagTable_reflection {b ell a : ℕ}
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ha : 0 < a) (halt : a < allLagModulus b ell)
    (hcop : Nat.Coprime a (allLagModulus b ell)) :
    allLagTable b ell a +
      allLagTable b ell (allLagModulus b ell - a) = -1 := by
  have hsum := allLag_jump_pair_sum hb2 hell ha halt hcop
  have hquot := allLag_quotient_complement hb2 ha halt hcop
  rw [Finset.sum_add_distrib] at hsum
  have hquotZ :
      ((a / b : ℕ) : ℤ) +
        (((allLagModulus b ell - a) / b : ℕ) : ℤ) =
          (b ^ ell : ℤ) - 1 := by
    have hcast : ((b ^ ell - 1 : ℕ) : ℤ) = (b ^ ell : ℤ) - 1 := by
      have hpow : 0 < b ^ ell := pow_pos (by omega) ell
      rw [Nat.cast_sub (by omega : 1 ≤ b ^ ell)]
      norm_num
    exact (Int.ofNat_inj.mpr hquot).trans hcast
  unfold allLagTable
  linear_combination hsum - hquotZ

def fiberCoordinates (b ell u : ℕ) : Finset ℕ :=
  (Finset.range (b ^ ell)).image fun k => u + b * k

theorem tableFiber_eq_coordinates {b ell u : ℕ} (hb2 : 2 ≤ b)
    (hu : u ∈ reducedResidues b) :
    tableFiber b ell u = fiberCoordinates b ell u := by
  have hb : 0 < b := by omega
  rcases Finset.mem_filter.mp hu with ⟨huRange, huCop⟩
  have huIco := Finset.mem_Ico.mp huRange
  have hmodulus : allLagModulus b ell = b ^ ell * b := by
    unfold allLagModulus
    rw [pow_succ]
  ext a
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨haReduced, haMod⟩
    rcases Finset.mem_filter.mp haReduced with ⟨haRange, haCop⟩
    have haIco := Finset.mem_Ico.mp haRange
    apply Finset.mem_image.mpr
    refine ⟨a / b, Finset.mem_range.mpr ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hb).2
      simpa [hmodulus] using haIco.2
    · have hdivision := Nat.mod_add_div a b
      rw [haMod] at hdivision
      omega
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    have hklt := Finset.mem_range.mp hk
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Ico.mpr
        constructor
        · omega
        · rw [hmodulus]
          calc
            u + b * k < b + b * k := Nat.add_lt_add_right huIco.2 _
            _ = b * (k + 1) := by ring
            _ ≤ b * b ^ ell := Nat.mul_le_mul_left b (by omega)
            _ = b ^ ell * b := Nat.mul_comm _ _
      · have hcopBase : Nat.Coprime (u + b * k) b :=
          (Nat.coprime_add_mul_left_left u b k).2 huCop
        exact hcopBase.pow_right (ell + 1)
    · simp [Nat.add_mod, Nat.mod_eq_of_lt huIco.2]

theorem tableFiber_card {b ell u : ℕ} (hb2 : 2 ≤ b)
    (hu : u ∈ reducedResidues b) :
    (tableFiber b ell u).card = b ^ ell := by
  rw [tableFiber_eq_coordinates hb2 hu]
  unfold fiberCoordinates
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro k hk j hj hkj
    have hmul : b * k = b * j := Nat.add_left_cancel hkj
    exact Nat.mul_left_cancel (by omega : 0 < b) hmul

def allLagUnitTable (b ell : ℕ) [NeZero (allLagModulus b ell)]
    (r : UnitClass (allLagModulus b ell)) : ℂ :=
  allLagTable b ell r.val.val

theorem allLagUnitTable_reflection {b ell : ℕ}
    [NeZero (allLagModulus b ell)] (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (r : UnitClass (allLagModulus b ell)) :
    allLagUnitTable b ell r + allLagUnitTable b ell (-r) = -1 := by
  let q := allLagModulus b ell
  have hqpos : 0 < q := pow_pos (by omega) _
  have hq2 : 2 ≤ q := by
    have hpow : 1 ≤ b ^ ell := by
      have := pow_pos (by omega : 0 < b) ell
      omega
    have hbq : b ≤ b ^ ell * b := by
      simpa using Nat.mul_le_mul_right b hpow
    change 2 ≤ allLagModulus b ell
    rw [show allLagModulus b ell = b ^ ell * b by
      unfold allLagModulus
      rw [pow_succ]]
    omega
  have halt : r.val.val < q := r.val.val_lt
  have hcop : Nat.Coprime r.val.val q := by
    apply (ZMod.isUnit_iff_coprime r.val.val q).mp
    rw [ZMod.natCast_zmod_val]
    exact r.isUnit
  have ha : 0 < r.val.val := by
    by_contra hnot
    have hzero : r.val.val = 0 := by omega
    rw [hzero] at hcop
    simp at hcop
    omega
  have hrzero : r.val ≠ 0 := by
    intro hzero
    have hzval := congrArg ZMod.val hzero
    have : r.val.val = 0 := by simpa using hzval
    exact (Nat.ne_of_gt ha) this
  have hnegval : (-r : UnitClass q).val.val = q - r.val.val := by
    change (-r.val).val = q - r.val.val
    rw [ZMod.neg_val, if_neg hrzero]
  unfold allLagUnitTable
  change (allLagTable b ell r.val.val : ℂ) +
    (allLagTable b ell (-r : UnitClass q).val.val : ℂ) = -1
  rw [hnegval]
  exact_mod_cast allLagTable_reflection hb2 hell ha halt hcop

theorem centered_allLagUnitTable_odd
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    {β : Type*} [Fintype β] [DecidableEq β]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ρ : UnitClass (allLagModulus b ell) → β)
    (rβ : β → β) (hβ : Function.Involutive rβ)
    (hcompat : ∀ a, ρ (-a) = rβ (ρ a))
    (hsurj : Function.Surjective ρ)
    (a : UnitClass (allLagModulus b ell)) :
    centeredSignal ρ (allLagUnitTable b ell) (-a) =
      -centeredSignal ρ (allLagUnitTable b ell) a := by
  apply centeredSignal_reflection_odd ρ (allLagUnitTable b ell)
    (fun r => -r) rβ
  · intro r
    simp
  · exact hβ
  · exact hcompat
  · exact allLagUnitTable_reflection hb2 hell
  · exact hsurj

noncomputable def collisionCoefficient {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (χ : Character q) : ℂ :=
  finiteCoefficient F fun r => χ r.val

theorem collisionCoefficient_inversion {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (r : UnitClass q) :
    ∑ χ : Character q, collisionCoefficient F χ * χ r.val = F r := by
  classical
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hcard : Fintype.card (UnitClass q) = q.totient :=
    ZMod.card_units_eq_totient q
  unfold collisionCoefficient finiteCoefficient
  rw [hcard]
  calc
    (∑ χ : Character q,
        ((q.totient : ℂ)⁻¹ *
          ∑ t : UnitClass q, F t * star (χ t.val)) * χ r.val) =
      (q.totient : ℂ)⁻¹ *
        ∑ t : UnitClass q,
          (∑ χ : Character q, star (χ t.val) * χ r.val) * F t := by
            calc
              (∑ χ : Character q,
                  ((q.totient : ℂ)⁻¹ *
                    ∑ t : UnitClass q, F t * star (χ t.val)) * χ r.val) =
                (q.totient : ℂ)⁻¹ *
                  ∑ χ : Character q,
                    (∑ t : UnitClass q, F t * star (χ t.val)) * χ r.val := by
                      conv_rhs => rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro χ _
                      ring
              _ = (q.totient : ℂ)⁻¹ *
                  ∑ χ : Character q,
                    ∑ t : UnitClass q,
                      (F t * star (χ t.val)) * χ r.val := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro χ _
                        rw [Finset.sum_mul]
              _ = (q.totient : ℂ)⁻¹ *
                  ∑ t : UnitClass q,
                    ∑ χ : Character q,
                      (F t * star (χ t.val)) * χ r.val := by
                        rw [Finset.sum_comm]
              _ = (q.totient : ℂ)⁻¹ *
                  ∑ t : UnitClass q,
                    (∑ χ : Character q, star (χ t.val) * χ r.val) * F t := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro t _
                        rw [Finset.sum_mul]
                        apply Finset.sum_congr rfl
                        intro χ _
                        ring
    _ = (q.totient : ℂ)⁻¹ *
        ∑ t : UnitClass q,
          (if t = r then (q.totient : ℂ) else 0) * F t := by
            simp_rw [unit_character_orthogonality]
    _ = (q.totient : ℂ)⁻¹ * ((q.totient : ℂ) * F r) := by simp
    _ = F r := by field_simp

theorem collisionCoefficient_even_zero {q : ℕ} [NeZero q]
    (f : UnitClass q → ℂ) (χ : Character q)
    (hf : ∀ r, f (-r) = -f r)
    (hχ : ∀ r : UnitClass q, χ (-r).val = χ r.val) :
    collisionCoefficient f χ = 0 := by
  apply finiteCoefficient_eq_zero_of_odd_even (fun r : UnitClass q => -r)
  · intro r
    simp
  · exact hf
  · exact hχ

theorem even_character_invariant_under_negation
    {q : ℕ} [NeZero q] (χ : Character q)
    (heven : χ (-1 : ZMod q) = 1) (r : UnitClass q) :
    χ (-r).val = χ r.val := by
  have hneg : (-r : UnitClass q).val = (-1 : ZMod q) * r.val := by
    simp
  rw [hneg, map_mul, heven, one_mul]

theorem collisionCoefficient_factored_zero
    {q : ℕ} [NeZero q] {β : Type*} [Fintype β]
    [DecidableEq β] (ρ : UnitClass q → β) (f : UnitClass q → ℂ)
    (hfiber : ∀ u, ∑ a : Fiber ρ u, f a = 0)
    (ψ : β → ℂ) (χ : Character q)
    (hfactor : ∀ a, χ a.val = ψ (ρ a)) :
    collisionCoefficient f χ = 0 := by
  exact finiteCoefficient_eq_zero_of_fiber_zero ρ f hfiber ψ
    (fun a => χ a.val) hfactor

theorem centered_allLag_even_character_zero
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    {β : Type*} [Fintype β] [DecidableEq β]
    (hb2 : 2 ≤ b) (hell : 1 ≤ ell)
    (ρ : UnitClass (allLagModulus b ell) → β)
    (rβ : β → β) (hβ : Function.Involutive rβ)
    (hcompat : ∀ a, ρ (-a) = rβ (ρ a))
    (hsurj : Function.Surjective ρ)
    (χ : Character (allLagModulus b ell))
    (heven : χ (-1 : ZMod (allLagModulus b ell)) = 1) :
    collisionCoefficient
      (centeredSignal ρ (allLagUnitTable b ell)) χ = 0 := by
  apply collisionCoefficient_even_zero
  · exact centered_allLagUnitTable_odd hb2 hell ρ rβ hβ
      hcompat hsurj
  · exact even_character_invariant_under_negation χ heven

theorem centered_allLag_factored_character_zero
    {b ell : ℕ} [NeZero (allLagModulus b ell)]
    {β : Type*} [Fintype β] [DecidableEq β]
    (ρ : UnitClass (allLagModulus b ell) → β)
    (hsurj : Function.Surjective ρ)
    (ψ : β → ℂ) (χ : Character (allLagModulus b ell))
    (hfactor : ∀ a, χ a.val = ψ (ρ a)) :
    collisionCoefficient
      (centeredSignal ρ (allLagUnitTable b ell)) χ = 0 := by
  have hfiber : ∀ u, ∑ a : Fiber ρ u,
      centeredSignal ρ (allLagUnitTable b ell) a = 0 := by
    intro u
    apply centeredSignal_fiber_sum_zero
    obtain ⟨a, ha⟩ := hsurj u
    exact ⟨⟨a, ha⟩⟩
  exact collisionCoefficient_factored_zero ρ
    (centeredSignal ρ (allLagUnitTable b ell)) hfiber ψ χ hfactor

theorem finite_prime_packet_decomposition
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (F : UnitClass q → ℂ) (residue : ι → UnitClass q)
    (weight : ι → ℂ) :
    ∑ i, F (residue i) * weight i =
      ∑ χ : Character q, collisionCoefficient F χ *
        ∑ i, χ (residue i).val * weight i := by
  classical
  calc
    (∑ i, F (residue i) * weight i) =
      ∑ i, (∑ χ : Character q,
        collisionCoefficient F χ * χ (residue i).val) * weight i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [collisionCoefficient_inversion]
    _ = ∑ i, ∑ χ : Character q,
        collisionCoefficient F χ *
          (χ (residue i).val * weight i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro χ _
            ring
    _ = ∑ χ : Character q, ∑ i,
        collisionCoefficient F χ *
          (χ (residue i).val * weight i) := by
            rw [Finset.sum_comm]
    _ = ∑ χ : Character q, collisionCoefficient F χ *
        ∑ i, χ (residue i).val * weight i := by
          apply Finset.sum_congr rfl
          intro χ _
          rw [Finset.mul_sum]

noncomputable def activeCharacters {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) : Finset (Character q) :=
  Finset.univ.filter fun χ => collisionCoefficient F χ ≠ 0

noncomputable def collisionZeroLedger {q : ℕ} [NeZero q]
    (F : UnitClass q → ℂ) (multiplicity : Character q → ℕ) : ℂ :=
  ∑ χ ∈ activeCharacters F,
    collisionCoefficient F χ * (multiplicity χ : ℂ)

theorem isolated_active_channel_has_nonzero_ledger
    {q : ℕ} [NeZero q] (F : UnitClass q → ℂ)
    (multiplicity : Character q → ℕ) (χ₀ : Character q)
    (hactive : collisionCoefficient F χ₀ ≠ 0)
    (hmult : 0 < multiplicity χ₀)
    (hisolated : ∀ χ ∈ activeCharacters F, χ ≠ χ₀ → multiplicity χ = 0) :
    collisionZeroLedger F multiplicity ≠ 0 := by
  classical
  have hmem : χ₀ ∈ activeCharacters F := by
    simp [activeCharacters, hactive]
  have hcast : (multiplicity χ₀ : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hmult)
  unfold collisionZeroLedger
  rw [Finset.sum_eq_single χ₀]
  · exact mul_ne_zero hactive hcast
  · intro χ hχ hne
    rw [hisolated χ hχ hne, Nat.cast_zero, mul_zero]
  · intro hnot
    exact (hnot hmem).elim

def transformVerificationBases : Finset ℕ := {3, 5, 7, 10, 12}

def transformVerificationRepresentatives : Finset ℕ := Finset.Icc 1 3

theorem transform_direct_check_case_count :
    ∑ b ∈ transformVerificationBases,
      (reducedResidues (allLagModulus b 1)).card *
        transformVerificationRepresentatives.card = 468 := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem selected_base_direct_collision_regression :
    ∀ b ∈ transformVerificationBases,
      ∀ a ∈ reducedResidues (allLagModulus b 1),
        ∀ t ∈ transformVerificationRepresentatives,
          directAllLagDeviation b 1 (allLagModulus b 1 * t + a) =
            allLagTable b 1 a := by
  decide

end NField.Alignment.CollisionTransformStrip
