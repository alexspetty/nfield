/-
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionTransformStrip
import NField.Alignment.ConductorDepthSawtooth

/-!
# Prime carry-table column law

This module proves the exact column sums of the lag-one prime carry table.  The
proof uses affine permutation of residues modulo the prime and keeps the floor
arithmetic finite.
-/

namespace NField.Alignment.PrimeCarryTableColumnLaw

open scoped BigOperators ZMod
open NField.Alignment.CollisionCharacterStructure
open NField.Alignment.CollisionFluctuationSum
open NField.Alignment.CollisionPeriodicTable
open NField.Alignment.ConductorDepthSawtooth

/-- An affine map with unit slope permutes all residues, so the sum of its
least representatives is unchanged. -/
theorem sum_affine_mod
    {b m K : ℕ} (hb : 0 < b) (hcop : m.Coprime b) :
    ∑ q ∈ Finset.range b, (m * q + K) % b = b * (b - 1) / 2 := by
  classical
  letI : NeZero b := ⟨hb.ne'⟩
  let u : UnitClass b := ZMod.unitOfCoprime m hcop
  let affine : ZMod b ≃ ZMod b :=
    u.mulLeft.trans (Equiv.addRight (K : ZMod b))
  let e : Fin b ≃ Fin b :=
    (ZMod.finEquiv b).toEquiv.trans
      (affine.trans (ZMod.finEquiv b).toEquiv.symm)
  have heval (q : Fin b) :
      (e q).val = (m * q.val + K) % b := by
    calc
      (e q).val = ((ZMod.finEquiv b) (e q)).val := by
        rw [finEquiv_eq_natCast, ZMod.val_natCast,
          Nat.mod_eq_of_lt (e q).isLt]
      _ = (affine ((ZMod.finEquiv b) q)).val := by
        simp [e]
      _ = (m * q.val + K) % b := by
        unfold affine u
        rw [finEquiv_eq_natCast]
        simp only [Equiv.trans_apply, Units.mulLeft_apply,
          ZMod.coe_unitOfCoprime]
        change ((m : ZMod b) * (q.val : ZMod b) + (K : ZMod b)).val =
          (m * q.val + K) % b
        rw [ZMod.val_add, ZMod.val_mul, ZMod.val_natCast,
          ZMod.val_natCast]
        simp [Nat.add_mod, Nat.mul_mod]
  calc
    (∑ q ∈ Finset.range b, (m * q + K) % b) =
        ∑ q : Fin b, (m * q.val + K) % b := by
      rw [Fin.sum_univ_eq_sum_range
        (fun q : ℕ => (m * q + K) % b) b]
    _ = ∑ q : Fin b, (e q).val := by
      apply Finset.sum_congr rfl
      intro q _
      rw [heval]
    _ = ∑ q : Fin b, q.val := e.sum_comp (fun q : Fin b => q.val)
    _ = ∑ q ∈ Finset.range b, q := by
      rw [Fin.sum_univ_eq_sum_range (fun q : ℕ => q) b]
    _ = b * (b - 1) / 2 := Finset.sum_range_id b

/-- The floor sum attached to an affine permutation of residues.  The oddness
of the modulus makes the half-integral expression an ordinary natural
number. -/
theorem sum_affine_div
    {b m K : ℕ} (hb : 0 < b) (hbodd : Odd b) (hcop : m.Coprime b) :
    ∑ q ∈ Finset.range b, (m * q + K) / b =
      (m - 1) * ((b - 1) / 2) + K := by
  rcases hbodd with ⟨t, ht⟩
  have hbform : b = 2 * t + 1 := by omega
  have hhalf : (b - 1) / 2 = t := by omega
  have hpred : b - 1 = 2 * t := by omega
  have htri : b * (b - 1) / 2 = b * t := by
    rw [hpred, show b * (2 * t) = 2 * (b * t) by ring,
      Nat.mul_div_right (b * t) (by decide : 0 < 2)]
  have hpoint (q : ℕ) :
      b * ((m * q + K) / b) + (m * q + K) % b = m * q + K := by
    simpa [Nat.mul_comm] using Nat.div_add_mod (m * q + K) b
  have hsum :
      b * (∑ q ∈ Finset.range b, (m * q + K) / b) +
          ∑ q ∈ Finset.range b, (m * q + K) % b =
        m * (∑ q ∈ Finset.range b, q) + b * K := by
    calc
      b * (∑ q ∈ Finset.range b, (m * q + K) / b) +
          ∑ q ∈ Finset.range b, (m * q + K) % b =
        ∑ q ∈ Finset.range b,
          (b * ((m * q + K) / b) + (m * q + K) % b) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ q ∈ Finset.range b, (m * q + K) := by
            apply Finset.sum_congr rfl
            intro q _
            exact hpoint q
      _ = m * (∑ q ∈ Finset.range b, q) + b * K := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp
  rw [sum_affine_mod hb hcop, Finset.sum_range_id] at hsum
  rw [htri] at hsum
  have hcancel :
      (∑ q ∈ Finset.range b, (m * q + K) / b) + t = m * t + K := by
    apply Nat.eq_of_mul_eq_mul_left hb
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hsum
  rw [hhalf]
  by_cases htzero : t = 0
  · simp [htzero] at hcancel ⊢
    exact hcancel
  · have hm : 0 < m := by
      by_contra hm0
      have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst m
      simp at hcop
      omega
    have hmform : m = (m - 1) + 1 := by omega
    have hmult : m * t = (m - 1) * t + t := by
      conv_lhs => rw [hmform]
      ring
    rw [hmult] at hcancel
    omega

/-- Clearing one base digit before dividing by the square modulus is exact. -/
theorem square_floor_depth_reduction
    {b m q s : ℕ} (hb : 0 < b) :
    m * (b * q + s) / b ^ 2 = (m * q + m * s / b) / b := by
  rw [pow_two, ← Nat.div_div_eq_div_mul]
  rw [show m * (b * q + s) = b * (m * q) + m * s by ring]
  rw [Nat.mul_add_div hb]

/-- Summing one square-depth floor down a complete base column. -/
theorem sum_square_floor_column
    {b m s : ℕ} (hb : 0 < b) (hbodd : Odd b) (hcop : m.Coprime b) :
    ∑ q ∈ Finset.range b, m * (b * q + s) / b ^ 2 =
      (m - 1) * ((b - 1) / 2) + m * s / b := by
  calc
    (∑ q ∈ Finset.range b, m * (b * q + s) / b ^ 2) =
        ∑ q ∈ Finset.range b, (m * q + m * s / b) / b := by
          apply Finset.sum_congr rfl
          intro q _
          exact square_floor_depth_reduction hb
    _ = (m - 1) * ((b - 1) / 2) + m * s / b :=
      sum_affine_div hb hbodd hcop

theorem coprime_of_prime_mod
    {p m r : ℕ} (hp : p.Prime) (hrpos : 0 < r)
    (hmod : m % p = r) : m.Coprime p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdiv
  have hz := Nat.dvd_iff_mod_eq_zero.mp hdiv
  rw [hmod] at hz
  omega

/-- Every lower interior carry multiplier is a unit modulo the prime base. -/
theorem lower_multiplier_coprime
    {p d : ℕ} (hp : p.Prime) (hdpos : 0 < d) (hdlt : d < p) :
    ((p + 1) * d).Coprime p := by
  apply coprime_of_prime_mod (r := d) hp hdpos
  rw [show (p + 1) * d = p * d + d by ring]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hdlt]

/-- Every upper interior carry multiplier is a unit modulo the prime base. -/
theorem upper_multiplier_coprime
    {p d : ℕ} (hp : p.Prime) (hdlt : d + 1 < p) :
    ((p + 1) * d + 1).Coprime p := by
  apply coprime_of_prime_mod (r := d + 1) hp (by omega)
  rw [show (p + 1) * d + 1 = p * d + (d + 1) by ring]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hdlt]

/-- Exact contribution of one interior diagonal point to a complete residue
column of the prime carry table. -/
theorem interior_floorJump_column
    {p d s : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hdpos : 0 < d) (hdlt : d < p - 1) :
    ∑ q ∈ Finset.range p,
        floorJump (p ^ 2) (p * q + s) ((p + 1) * d) =
      (((p - 1) / 2 : ℕ) : ℤ) +
        (((d + 1) * s / p : ℕ) : ℤ) - ((d * s / p : ℕ) : ℤ) := by
  have hp0 : 0 < p := hp.pos
  have hpOdd : Odd p := hp.odd_of_ne_two hpodd
  have hdltp : d < p := by omega
  have hdupper : d + 1 < p := by omega
  have hminus := sum_square_floor_column hp0 hpOdd
    (lower_multiplier_coprime hp hdpos hdltp) (s := s)
  have hplus := sum_square_floor_column hp0 hpOdd
    (upper_multiplier_coprime hp hdupper) (s := s)
  have hKminus : ((p + 1) * d) * s / p =
      d * s + d * s / p := by
    rw [show ((p + 1) * d) * s = p * (d * s) + d * s by ring,
      Nat.mul_add_div hp0]
  have hKplus : (((p + 1) * d + 1) * s) / p =
      d * s + (d + 1) * s / p := by
    rw [show ((p + 1) * d + 1) * s =
        p * (d * s) + (d + 1) * s by ring,
      Nat.mul_add_div hp0]
  unfold floorJump
  rw [Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  rw [hplus, hminus, hKplus, hKminus]
  have hpluspred : (p + 1) * d + 1 - 1 = (p + 1) * d := by omega
  have hminuspred : (p + 1) * d - 1 + 1 = (p + 1) * d := by
    have : 0 < (p + 1) * d := by positivity
    omega
  rw [hpluspred]
  have hmulPred :
      ((p + 1) * d - 1) * ((p - 1) / 2) + ((p - 1) / 2) =
        (p + 1) * d * ((p - 1) / 2) := by
    calc
      ((p + 1) * d - 1) * ((p - 1) / 2) + ((p - 1) / 2) =
          (((p + 1) * d - 1) + 1) * ((p - 1) / 2) := by
            symm
            simpa using Nat.add_mul ((p + 1) * d - 1) 1 ((p - 1) / 2)
      _ = (p + 1) * d * ((p - 1) / 2) := by rw [hminuspred]
  omega

/-- The zero diagonal point contributes no threshold crossing. -/
theorem zero_floorJump_column
    {p s : ℕ} (_hp0 : 0 < p) (hslt : s < p) :
    ∑ q ∈ Finset.range p,
        floorJump (p ^ 2) (p * q + s) 0 = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hqlt : q < p := Finset.mem_range.mp hq
  have halt : p * q + s < p ^ 2 := by
    nlinarith
  unfold floorJump
  simp [Nat.div_eq_of_lt halt]

/-- At the final diagonal point every nonzero proper row crosses exactly once. -/
theorem floorJump_last_eq_one
    {M a : ℕ} (hM : 0 < M) (ha : 0 < a) (halt : a < M) :
    floorJump M a (M - 1) = 1 := by
  have hsucc : M - 1 + 1 = M := by omega
  have htop : M * a / M = a := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left a hM
  unfold floorJump
  rw [hsucc, htop, pred_mul_div_self hM ha halt]
  omega

/-- The exceptional final diagonal point contributes one in each of the
`p` rows of a nonzero residue column. -/
theorem endpoint_floorJump_column
    {p s : ℕ} (hp0 : 0 < p) (hspos : 0 < s) (hslt : s < p) :
    ∑ q ∈ Finset.range p,
        floorJump (p ^ 2) (p * q + s) ((p + 1) * (p - 1)) = p := by
  have hindex : (p + 1) * (p - 1) = p ^ 2 - 1 := by
    let k := p - 1
    have hpform : p = k + 1 := by
      dsimp [k]
      omega
    have hadd : (p + 1) * (p - 1) + 1 = p ^ 2 := by
      rw [hpform]
      simp
      ring
    omega
  rw [hindex]
  have hpoint (q : ℕ) (hq : q ∈ Finset.range p) :
      floorJump (p ^ 2) (p * q + s) (p ^ 2 - 1) = 1 := by
    have hqlt : q < p := Finset.mem_range.mp hq
    have ha : 0 < p * q + s := by omega
    have halt : p * q + s < p ^ 2 := by nlinarith
    exact floorJump_last_eq_one (pow_pos hp0 2) ha halt
  rw [Finset.sum_congr rfl hpoint]
  simp

/-- The finite carry increments telescope across all interior diagonal
points. -/
theorem interior_increment_telescope
    {p s : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hspos : 0 < s) (hslt : s < p) :
    ∑ d ∈ Finset.Ico 1 (p - 1),
        ((((d + 1) * s / p : ℕ) : ℤ) - ((d * s / p : ℕ) : ℤ)) =
      (s - 1 : ℕ) := by
  let F : ℕ → ℤ := fun d => (((d * s / p : ℕ) : ℤ))
  have hp3 : 3 ≤ p := by omega
  have hall := Finset.sum_range_sub F (p - 1)
  have hsplit := Finset.sum_range_eq_add_Ico
    (fun d => F (d + 1) - F d) (by omega : 0 < p - 1)
  rw [hsplit] at hall
  have hzero : F 0 = 0 := by simp [F]
  have hone : F 1 = 0 := by
    unfold F
    rw [one_mul, Nat.div_eq_of_lt hslt]
    simp
  have htop : F (p - 1) = (s - 1 : ℕ) := by
    unfold F
    rw [pred_mul_div_self hp.pos hspos hslt]
  rw [hzero, hone, htop] at hall
  simpa [F] using hall

/-- The manuscript's raw threshold-crossing count, written directly as its
finite floor-jump table. -/
def carryThresholdCount (p a : ℕ) : ℤ :=
  ∑ d ∈ Finset.range p,
    floorJump (p ^ 2) a ((p + 1) * d)

/-- The threshold count is exactly the diagonal-slice sum already used by
the collision table. -/
theorem carryThresholdCount_eq_diagonalSum (p a : ℕ) :
    carryThresholdCount p a =
      ∑ n ∈ diagonalSlices p, floorJump (p ^ 2) a n := by
  unfold carryThresholdCount diagonalSlices
  rw [Finset.sum_image]
  intro d _ e _ hde
  exact Nat.mul_left_cancel (by omega : 0 < p + 1) hde

/-- Exact complete-column sum of the raw prime carry table. -/
theorem carryThresholdCount_column_law
    {p s : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hspos : 0 < s) (hslt : s < p) :
    ∑ q ∈ Finset.range p, carryThresholdCount p (p * q + s) =
      (((p * (p - 1) / 2 + s : ℕ) : ℤ)) := by
  classical
  have hp3 : 3 ≤ p := by omega
  have hp0 : 0 < p := hp.pos
  have hzero :
      ∑ q ∈ Finset.range p,
        floorJump (p ^ 2) (p * q + s) ((p + 1) * 0) = 0 := by
    simpa using zero_floorJump_column hp0 hslt
  have hlast :
      ∑ q ∈ Finset.range p,
        floorJump (p ^ 2) (p * q + s) ((p + 1) * (p - 1)) = p :=
    endpoint_floorJump_column hp0 hspos hslt
  have hinterior :
      ∑ d ∈ Finset.Ico 1 (p - 1),
          ∑ q ∈ Finset.range p,
            floorJump (p ^ 2) (p * q + s) ((p + 1) * d) =
        ((p - 2 : ℕ) : ℤ) * (((p - 1) / 2 : ℕ) : ℤ) +
          ((s - 1 : ℕ) : ℤ) := by
    calc
      (∑ d ∈ Finset.Ico 1 (p - 1),
          ∑ q ∈ Finset.range p,
            floorJump (p ^ 2) (p * q + s) ((p + 1) * d)) =
        ∑ d ∈ Finset.Ico 1 (p - 1),
          ((((p - 1) / 2 : ℕ) : ℤ) +
            (((d + 1) * s / p : ℕ) : ℤ) -
              ((d * s / p : ℕ) : ℤ)) := by
                apply Finset.sum_congr rfl
                intro d hd
                exact interior_floorJump_column hp hpodd
                  (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd).2
      _ = ((p - 2 : ℕ) : ℤ) * (((p - 1) / 2 : ℕ) : ℤ) +
          ((s - 1 : ℕ) : ℤ) := by
            rw [show (∑ d ∈ Finset.Ico 1 (p - 1),
                ((((p - 1) / 2 : ℕ) : ℤ) +
                  (((d + 1) * s / p : ℕ) : ℤ) -
                    ((d * s / p : ℕ) : ℤ))) =
              (∑ d ∈ Finset.Ico 1 (p - 1),
                (((p - 1) / 2 : ℕ) : ℤ)) +
              ∑ d ∈ Finset.Ico 1 (p - 1),
                ((((d + 1) * s / p : ℕ) : ℤ) -
                  ((d * s / p : ℕ) : ℤ)) by
                    simp_rw [add_sub_assoc]
                    rw [Finset.sum_add_distrib]]
            rw [interior_increment_telescope hp hpodd hspos hslt]
            have hcard : (Finset.Ico 1 (p - 1)).card = p - 2 := by
              simp
              omega
            simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  unfold carryThresholdCount
  rw [Finset.sum_comm]
  let columnFlux : ℕ → ℤ := fun d =>
    ∑ q ∈ Finset.range p,
      floorJump (p ^ 2) (p * q + s) ((p + 1) * d)
  change (∑ d ∈ Finset.range p, columnFlux d) = _
  have hzero' : columnFlux 0 = 0 := by
    simpa [columnFlux] using hzero
  have hlast' : columnFlux (p - 1) = p := by
    simpa [columnFlux] using hlast
  have hinterior' :
      ∑ d ∈ Finset.Ico 1 (p - 1), columnFlux d =
        ((p - 2 : ℕ) : ℤ) * (((p - 1) / 2 : ℕ) : ℤ) +
          ((s - 1 : ℕ) : ℤ) := by
    simpa [columnFlux] using hinterior
  have hrange : Finset.range p =
      insert 0 (Finset.Ico 1 (p - 1) ∪ {p - 1}) := by
    ext d
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hrange]
  have hzero_not_mem : 0 ∉ Finset.Ico 1 (p - 1) ∪ {p - 1} := by
    simp
    omega
  rw [Finset.sum_insert hzero_not_mem, hzero', zero_add]
  have hlast_not_mem : p - 1 ∉ Finset.Ico 1 (p - 1) := by simp
  rw [Finset.sum_union (by simp), Finset.sum_singleton,
    hinterior', hlast']
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by
    rcases hp.odd_of_ne_two hpodd with ⟨t, ht⟩
    have hpred : p - 1 = 2 * t := by omega
    rw [hpred]
    simp
  have htri : p * (p - 1) / 2 = p * ((p - 1) / 2) := by
    rw [show p * (p - 1) = 2 * (p * ((p - 1) / 2)) by
      nlinarith]
    exact Nat.mul_div_right _ (by decide : 0 < 2)
  rw [htri]
  rw [Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (by omega : 2 ≤ p),
    Nat.cast_sub hspos]
  have hhalfZ :
      2 * ((((p - 1) / 2 : ℕ) : ℤ)) = (p : ℤ) - 1 := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hhalf
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub hp.one_le] using hcast
  linear_combination -hhalfZ

/-- The raw threshold count is the uncentered term in the existing collision
table. -/
theorem fluctuationTable_eq_thresholdCount
    {p q s : ℕ} (hp0 : 0 < p) (hslt : s < p) :
    fluctuationTable p (p * q + s) =
      -1 - (q : ℤ) + carryThresholdCount p (p * q + s) := by
  have hquot : (p * q + s) / p = q := by
    rw [Nat.mul_add_div hp0, Nat.div_eq_of_lt hslt, Nat.add_zero]
  unfold fluctuationTable
  rw [hquot, carryThresholdCount_eq_diagonalSum]

/-- Exact column sum of the centered integer carry statistic. -/
theorem fluctuationTable_column_sum
    {p s : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hspos : 0 < s) (hslt : s < p) :
    ∑ q ∈ Finset.range p, fluctuationTable p (p * q + s) =
      (s : ℤ) - p := by
  have hpoint (q : ℕ) (hq : q ∈ Finset.range p) :
      fluctuationTable p (p * q + s) =
        -1 - (q : ℤ) + carryThresholdCount p (p * q + s) :=
    fluctuationTable_eq_thresholdCount hp.pos hslt
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib,
    carryThresholdCount_column_law hp hpodd hspos hslt]
  have hqsumNat : ∑ q ∈ Finset.range p, q = p * (p - 1) / 2 :=
    Finset.sum_range_id p
  have hqsumInt : ∑ q ∈ Finset.range p, (q : ℤ) =
      ((p * (p - 1) / 2 : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, hqsumNat]
  rw [show (∑ q ∈ Finset.range p, (-1 - (q : ℤ))) =
      -(p : ℤ) - ((p * (p - 1) / 2 : ℕ) : ℤ) by
        rw [Finset.sum_sub_distrib, hqsumInt]
        simp]
  push_cast
  ring

/-- The exact rational class mean used to center the collision energy. -/
theorem fluctuationTable_column_mean
    {p s : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hspos : 0 < s) (hslt : s < p) :
    (p : ℚ)⁻¹ *
        ∑ q ∈ Finset.range p, (fluctuationTable p (p * q + s) : ℚ) =
      -((p - s : ℕ) : ℚ) / (p : ℚ) := by
  have hsum := fluctuationTable_column_sum hp hpodd hspos hslt
  rw [← Int.cast_sum, hsum]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Nat.cast_sub (Nat.le_of_lt hslt)]
  push_cast
  field_simp [hpq]
  ring

end NField.Alignment.PrimeCarryTableColumnLaw
