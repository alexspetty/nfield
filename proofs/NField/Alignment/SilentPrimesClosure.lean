/-
Author: Alexander S. Petty
-/

import NField.Alignment.SilentPrimes

open scoped BigOperators

namespace NField.Alignment.SilentPrimesClosure

open ZMod
open NField.CollisionDefinition
open NField.Alignment.SilentPrimes
open NField.Alignment.BinDerangements
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.SpectralPower

theorem silentInteger_first_term (b ell : ℕ) :
    silentInteger b ell 1 = b ^ ell * (b - 1) + 1 := by
  rfl

theorem silentInteger_step {b ell u : ℕ} (hb : 1 ≤ b)
    (hu : u + 1 ≤ b) :
    silentInteger b ell u =
      silentInteger b ell (u + 1) + (b ^ ell - 1) := by
  have hpow : 1 ≤ b ^ ell := one_le_pow₀ hb
  have hsplit : b - u = (b - (u + 1)) + 1 := by omega
  unfold silentInteger
  rw [hsplit, Nat.mul_add]
  omega

theorem silentInteger_le_next_power {b ell u : ℕ}
    (hb : 1 ≤ b) (hub : u ≤ b) :
    silentInteger b ell u ≤ b ^ (ell + 1) := by
  rw [silentInteger_eq_displayed hb hub]
  exact Nat.sub_le _ _

/-- Global silence also has an explicit uniform bound, so the fixed-base,
fixed-lag set of global silent primes is finite. -/
theorem globallySilentAt_bound {b p ell : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    (hsilent : GloballySilentAt b p ell (by omega) hp) :
    p ≤ b ^ (ell + 1) := by
  obtain ⟨u, hu, hdvd⟩ :=
    (globallySilentAt_iff_exists_dvd_silentInteger hb2 hp hbp).mp hsilent
  have hurange := Finset.mem_Ico.mp hu
  have hpos : 0 < silentInteger b ell u :=
    silentInteger_pos (by omega)
  exact (Nat.le_of_dvd hpos hdvd).trans
    (silentInteger_le_next_power (by omega) (by omega))

/-- The inverse coordinate written in the manuscript. -/
def coordinateMultiplier (b p c : ℕ) [NeZero p] : ZMod p :=
  1 - (b : ZMod p) * (c : ZMod p)⁻¹

theorem coordinateMultiplier_parameter {b p c : ℕ}
    (hp : Nat.Prime p) [NeZero p] (hc0 : 0 < c) (hcp : c < p) :
    (c : ZMod p) * (1 - coordinateMultiplier b p c) = (b : ZMod p) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcne : (c : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcp]
    exact hc0.ne'
  unfold coordinateMultiplier
  field_simp
  ring

theorem coordinateMultiplier_ne_one {b p c : ℕ}
    (hp : Nat.Prime p) [NeZero p] (hb0 : 0 < b) (hbp : b < p)
    (hc0 : 0 < c) (hcp : c < p) :
    coordinateMultiplier b p c ≠ 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hbne : (b : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hbp]
    exact hb0.ne'
  have hcne : (c : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcp]
    exact hc0.ne'
  intro hone
  unfold coordinateMultiplier at hone
  have hzero : (b : ZMod p) * (c : ZMod p)⁻¹ = 0 := by
    exact sub_eq_self.mp hone
  exact mul_ne_zero hbne (inv_ne_zero hcne) hzero

theorem coordinateMultiplier_ne_zero {b p c : ℕ}
    (hp : Nat.Prime p) [NeZero p] (hbp : b < p)
    (hc0 : 0 < c) (hcp : c < p) (hcb : c ≠ b) :
    coordinateMultiplier b p c ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcne : (c : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcp]
    exact hc0.ne'
  intro hzero
  have hparam := coordinateMultiplier_parameter (b := b) hp hc0 hcp
  rw [hzero, sub_zero, mul_one] at hparam
  have hval := congrArg ZMod.val hparam
  simp only [ZMod.val_natCast_of_lt hcp,
    ZMod.val_natCast_of_lt hbp] at hval
  exact hcb hval

theorem gateParameter_coordinateMultiplier {b p c : ℕ}
    (hp : Nat.Prime p) [NeZero p] (hb0 : 0 < b) (hbp : b < p)
    (hc0 : 0 < c) (hcp : c < p) :
    gateParameter b p (coordinateMultiplier b p c) = c := by
  apply gateParameter_eq_of_identity hp hcp
    (coordinateMultiplier_ne_one hp hb0 hbp hc0 hcp)
  exact coordinateMultiplier_parameter hp hc0 hcp

theorem coordinateMultiplier_gateParameter {b p : ℕ}
    (hp : Nat.Prime p) [NeZero p] (hb0 : 0 < b) (hbp : b < p)
    {g : ZMod p} (hg1 : g ≠ 1) :
    coordinateMultiplier b p (gateParameter b p g) = g := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcpos : 0 < gateParameter b p g :=
    gateParameter_pos hb0 hp hbp hg1
  have hcne : ((gateParameter b p g : ℕ) : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero,
      ZMod.val_natCast_of_lt (gateParameter_lt g)]
    exact hcpos.ne'
  have hparam := gateParameter_mul_one_sub (b := b) hp hg1
  have hquot : (b : ZMod p) *
      ((gateParameter b p g : ℕ) : ZMod p)⁻¹ = 1 - g := by
    rw [← hparam]
    field_simp
  unfold coordinateMultiplier
  rw [hquot]
  ring

def positiveComparisonSet (b p Q c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter fun m => m * b < (m * c) % p

theorem positive_point_collision {b p Q c m : ℕ} [NeZero p]
    (_hb : 0 < b) (hcp : c < p) (hQp : Q < p)
    {g : ZMod p}
    (hparam : (c : ZMod p) * (1 - g) = (b : ZMod p))
    (hm : m ∈ positiveComparisonSet b p Q c) :
    let z : ZMod p := (m : ZMod p) * (c : ZMod p)
    z ≠ 0 ∧ z.val % b = (g * z).val % b := by
  have hm' := Finset.mem_filter.mp hm
  have hmrange := Finset.mem_Icc.mp hm'.1
  have hmlt : m < p := lt_of_le_of_lt hmrange.2 hQp
  let z : ZMod p := (m : ZMod p) * (c : ZMod p)
  have hzval : z.val = (m * c) % p := by
    dsimp [z]
    rw [ZMod.val_mul, ZMod.val_natCast_of_lt hmlt,
      ZMod.val_natCast_of_lt hcp]
  have hsuccess : m * b < z.val := by simpa [hzval] using hm'.2
  have hz0 : z ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    omega
  have hrelation : g * z = z - (m * b : ℕ) := by
    dsimp [z]
    push_cast
    linear_combination -((m : ZMod p) * hparam)
  have hmb : m * b ≤ z.val := Nat.le_of_lt hsuccess
  have hsub_lt : z.val - m * b < p :=
    lt_of_le_of_lt (Nat.sub_le _ _) z.val_lt
  have hgzval : (g * z).val = z.val - m * b := by
    have hcast : ((z.val - m * b : ℕ) : ZMod p) = z - (m * b : ℕ) := by
      rw [Nat.cast_sub hmb, ZMod.natCast_zmod_val]
    rw [hrelation, ← hcast, ZMod.val_natCast_of_lt hsub_lt]
  refine ⟨hz0, ?_⟩
  rw [hgzval]
  have hsplit : z.val = (z.val - m * b) + m * b :=
    (Nat.sub_add_cancel hmb).symm
  conv_lhs => rw [hsplit]
  simp [Nat.add_mod]

theorem negative_point_collision {b p Q c m : ℕ} [NeZero p]
    (hcp : c < p) (hQp : Q < p)
    {g : ZMod p}
    (hparam : (c : ZMod p) * (1 - g) = (b : ZMod p))
    (hm : m ∈ positiveComparisonSet b p Q c) :
    let z : ZMod p := -((m : ZMod p) * (c : ZMod p))
    z ≠ 0 ∧ z.val % b = (g * z).val % b := by
  have hm' := Finset.mem_filter.mp hm
  have hmrange := Finset.mem_Icc.mp hm'.1
  have hmlt : m < p := lt_of_le_of_lt hmrange.2 hQp
  let a : ZMod p := (m : ZMod p) * (c : ZMod p)
  have haval : a.val = (m * c) % p := by
    dsimp [a]
    rw [ZMod.val_mul, ZMod.val_natCast_of_lt hmlt,
      ZMod.val_natCast_of_lt hcp]
  have hsuccess : m * b < a.val := by simpa [haval] using hm'.2
  have ha0 : a ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    omega
  letI : NeZero a := ⟨ha0⟩
  let z : ZMod p := -a
  have hz0 : z ≠ 0 := neg_ne_zero.mpr ha0
  have hzval : z.val = p - a.val := by
    dsimp [z]
    exact ZMod.val_neg_of_ne_zero a
  have hrelation : g * z = z + (m * b : ℕ) := by
    dsimp [z, a]
    push_cast
    linear_combination ((m : ZMod p) * hparam)
  have hsum_lt : z.val + m * b < p := by
    rw [hzval]
    have havalle : a.val ≤ p := Nat.le_of_lt a.val_lt
    omega
  have hgzval : (g * z).val = z.val + m * b := by
    have hcast : ((z.val + m * b : ℕ) : ZMod p) = z + (m * b : ℕ) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]
    rw [hrelation, ← hcast, ZMod.val_natCast_of_lt hsum_lt]
  refine ⟨hz0, ?_⟩
  change z.val % b = (g * z).val % b
  rw [hgzval]
  simp [Nat.add_mod]

theorem collision_has_positive_coordinate {b p c : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hbp : b < p) [NeZero p]
    {g x : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1)
    (hcpos : 0 < c) (hcltp : c < p)
    (hparam : (c : ZMod p) * (1 - g) = (b : ZMod p))
    (hcollision : x ≠ 0 ∧ x.val % b = (g * x).val % b) :
    ∃ m ∈ positiveComparisonSet b p ((p - 1) / b) c,
      x = (m : ZMod p) * (c : ZMod p) ∨
        x = -((m : ZMod p) * (c : ZMod p)) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hx0 := hcollision.1
  have hy0 : g * x ≠ 0 := mul_ne_zero hg0 hx0
  have hxpos : 0 < x.val := ZMod.val_pos.mpr hx0
  have hypos : 0 < (g * x).val := ZMod.val_pos.mpr hy0
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    simp [ZMod.val_natCast_of_lt hbp, hb.ne']
  let qx := x.val / b
  let qy := (g * x).val / b
  have hqne : qx ≠ qy := by
    intro hqeq
    have hxdiv : x.val % b + b * qx = x.val := by
      simpa [qx] using Nat.mod_add_div x.val b
    have hydiv : (g * x).val % b + b * qy = (g * x).val := by
      simpa [qy] using Nat.mod_add_div (g * x).val b
    have hval : x.val = (g * x).val := by
      calc
        x.val = x.val % b + b * qx := hxdiv.symm
        _ = (g * x).val % b + b * qy := by rw [hcollision.2, hqeq]
        _ = (g * x).val := hydiv
    have heq : x = g * x := ZMod.val_injective (n := p) hval
    have hgx : g * x = 1 * x := by simpa using heq.symm
    exact hg1 (mul_right_cancel₀ hx0 hgx)
  rcases lt_or_gt_of_ne hqne with hq_lt | hq_gt
  · let m := qy - qx
    have hmpos : 0 < m := by dsimp [m]; omega
    have hshiftNat : (g * x).val = x.val + m * b := by
      have hxdiv : x.val % b + b * qx = x.val := by
        simpa [qx] using Nat.mod_add_div x.val b
      have hydiv : (g * x).val % b + b * qy = (g * x).val := by
        simpa [qy] using Nat.mod_add_div (g * x).val b
      have hqm : qx + m = qy := by dsimp [m]; omega
      calc
        (g * x).val = (g * x).val % b + b * qy := hydiv.symm
        _ = x.val % b + b * (qx + m) := by
          rw [← hcollision.2, hqm]
        _ = (x.val % b + b * qx) + m * b := by ring
        _ = x.val + m * b := by rw [hxdiv]
    have hshiftZ : g * x = x + ((m * b : ℕ) : ZMod p) := by
      calc
        g * x = ((g * x).val : ZMod p) :=
          (ZMod.natCast_zmod_val (g * x)).symm
        _ = ((x.val + m * b : ℕ) : ZMod p) := by rw [hshiftNat]
        _ = x + ((m * b : ℕ) : ZMod p) := by
          rw [Nat.cast_add, ZMod.natCast_zmod_val]
    have hobs := increasing_quotient_obstruction
      (p := p) (b := (b : ZMod p)) (c := (c : ZMod p))
      (g := g) (x := x) (y := g * x) (m := m)
      hparam rfl (by simpa [ZMod.val_natCast_of_lt hbp] using hshiftZ)
    have hzero : x + (m : ZMod p) * (c : ZMod p) = 0 :=
      mul_left_cancel₀ hb0 (by simpa using hobs)
    have hxneg : x = -((m : ZMod p) * (c : ZMod p)) := by
      linear_combination hzero
    let a : ZMod p := (m : ZMod p) * (c : ZMod p)
    have ha0 : a ≠ 0 := by
      intro ha
      have : x = 0 := by simpa [a, ha] using hxneg
      exact hx0 this
    letI : NeZero a := ⟨ha0⟩
    have havel : a.val = (m * c) % p := by
      rw [ZMod.val_mul]
      have hmltp : m < p := by
        have hylt := (g * x).val_lt
        rw [hshiftNat] at hylt
        have hmb_lt : m * b < p := by omega
        have hmlemb : m ≤ m * b := Nat.le_mul_of_pos_right m hb
        omega
      rw [ZMod.val_natCast_of_lt hmltp, ZMod.val_natCast_of_lt hcltp]
    have hxval : x.val = p - a.val := by
      rw [hxneg]
      exact ZMod.val_neg_of_ne_zero a
    have hsuccess : m * b < (m * c) % p := by
      rw [← havel]
      have hylt := (g * x).val_lt
      rw [hshiftNat, hxval] at hylt
      omega
    have hmQ : m ≤ (p - 1) / b := by
      apply (Nat.le_div_iff_mul_le hb).2
      omega
    refine ⟨m, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hmpos, hmQ⟩, hsuccess⟩, ?_⟩
    exact Or.inr hxneg
  · let n := qx - qy
    have hnpos : 0 < n := by dsimp [n]; omega
    have hshiftNat : x.val = (g * x).val + n * b := by
      have hxdiv : x.val % b + b * qx = x.val := by
        simpa [qx] using Nat.mod_add_div x.val b
      have hydiv : (g * x).val % b + b * qy = (g * x).val := by
        simpa [qy] using Nat.mod_add_div (g * x).val b
      have hqn : qy + n = qx := by dsimp [n]; omega
      calc
        x.val = x.val % b + b * qx := hxdiv.symm
        _ = (g * x).val % b + b * (qy + n) := by
          rw [hcollision.2, hqn]
        _ = ((g * x).val % b + b * qy) + n * b := by ring
        _ = (g * x).val + n * b := by rw [hydiv]
    have hshiftZ : x = g * x + ((n * b : ℕ) : ZMod p) := by
      calc
        x = (x.val : ZMod p) := (ZMod.natCast_zmod_val x).symm
        _ = (((g * x).val + n * b : ℕ) : ZMod p) := by rw [hshiftNat]
        _ = g * x + ((n * b : ℕ) : ZMod p) := by
          rw [Nat.cast_add, ZMod.natCast_zmod_val]
    have hobs := decreasing_quotient_obstruction
      (p := p) (b := (b : ZMod p)) (c := (c : ZMod p))
      (g := g) (x := x) (y := g * x) (n := n)
      hparam rfl (by simpa [ZMod.val_natCast_of_lt hbp] using hshiftZ)
    have hzero : x - (n : ZMod p) * (c : ZMod p) = 0 :=
      mul_left_cancel₀ hb0 (by simpa using hobs)
    have hxposcoord : x = (n : ZMod p) * (c : ZMod p) := by
      linear_combination hzero
    have hnltp : n < p := by
      have hxlt := x.val_lt
      rw [hshiftNat] at hxlt
      have hnb_lt : n * b < p := by omega
      have hnlenb : n ≤ n * b := Nat.le_mul_of_pos_right n hb
      omega
    have hxval : x.val = (n * c) % p := by
      rw [hxposcoord, ZMod.val_mul, ZMod.val_natCast_of_lt hnltp,
        ZMod.val_natCast_of_lt hcltp]
    have hsuccess : n * b < (n * c) % p := by
      rw [← hxval]
      rw [hshiftNat]
      omega
    have hnQ : n ≤ (p - 1) / b := by
      apply (Nat.le_div_iff_mul_le hb).2
      have hmodlt : (n * c) % p < p := Nat.mod_lt _ hp.pos
      omega
    refine ⟨n, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hnpos, hnQ⟩, hsuccess⟩, ?_⟩
    exact Or.inl hxposcoord

def transformedCollisionSet (b p : ℕ) [NeZero p]
    (g : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun x => x ≠ 0 ∧ x.val % b = (g * x).val % b

theorem transformedCollisionCount_eq_card (b p : ℕ) [NeZero p]
    (g : ZMod p) :
    transformedCollisionCount b p g = (transformedCollisionSet b p g).card := by
  unfold transformedCollisionCount transformedCollisionSet
  simp only [Finset.sum_boole]
  exact congrArg Finset.card (by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and])

def positiveCoordinatePoints (b p Q c : ℕ) : Finset (ZMod p) :=
  (positiveComparisonSet b p Q c).image fun m : ℕ =>
    (m : ZMod p) * (c : ZMod p)

def negativeCoordinatePoints (b p Q c : ℕ) : Finset (ZMod p) :=
  (positiveComparisonSet b p Q c).image fun m : ℕ =>
    -((m : ZMod p) * (c : ZMod p))

theorem transformedCollisionSet_eq_coordinate_points
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    let c := gateParameter b p g
    transformedCollisionSet b p g =
      positiveCoordinatePoints b p ((p - 1) / b) c ∪
        negativeCoordinatePoints b p ((p - 1) / b) c := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let c := gateParameter b p g
  have hb : 0 < b := by omega
  have hcpos : 0 < c := gateParameter_pos hb hp hbp hg1
  have hcltp : c < p := gateParameter_lt g
  have hparam : (c : ZMod p) * (1 - g) = (b : ZMod p) :=
    gateParameter_mul_one_sub hp hg1
  have hQp : (p - 1) / b < p := by
    have hle : (p - 1) / b ≤ p - 1 := Nat.div_le_self _ _
    omega
  change transformedCollisionSet b p g =
    positiveCoordinatePoints b p ((p - 1) / b) c ∪
      negativeCoordinatePoints b p ((p - 1) / b) c
  ext x
  simp only [transformedCollisionSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union, positiveCoordinatePoints,
    negativeCoordinatePoints, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨m, hm, hpoint⟩ := collision_has_positive_coordinate
      hb hp hbp hg0 hg1 hcpos hcltp hparam hx
    rcases hpoint with hpos | hneg
    · exact Or.inl ⟨m, hm, hpos.symm⟩
    · exact Or.inr ⟨m, hm, hneg.symm⟩
  · rintro (⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact positive_point_collision hb hcltp hQp hparam hm
    · exact negative_point_collision hcltp hQp hparam hm

theorem coordinate_points_card
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (_hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    let c := gateParameter b p g
    (positiveCoordinatePoints b p ((p - 1) / b) c ∪
      negativeCoordinatePoints b p ((p - 1) / b) c).card =
        2 * (positiveComparisonSet b p ((p - 1) / b) c).card := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let c := gateParameter b p g
  let successes := positiveComparisonSet b p ((p - 1) / b) c
  have hb : 0 < b := by omega
  have hcpos : 0 < c := gateParameter_pos hb hp hbp hg1
  have hcltp : c < p := gateParameter_lt g
  have hc0 : (c : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcltp]
    exact hcpos.ne'
  have hQp : (p - 1) / b < p := by
    have hle : (p - 1) / b ≤ p - 1 := Nat.div_le_self _ _
    omega
  have hinj : Set.InjOn
      (fun m : ℕ => (m : ZMod p) * (c : ZMod p)) successes := by
    intro m hm n hn heq
    have hmrange := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    have hnrange := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hcast : (m : ZMod p) = (n : ZMod p) :=
      mul_right_cancel₀ hc0 heq
    have hmlt : m < p := lt_of_le_of_lt hmrange.2 hQp
    have hnlt : n < p := lt_of_le_of_lt hnrange.2 hQp
    have hval := congrArg ZMod.val hcast
    simpa [ZMod.val_natCast_of_lt hmlt, ZMod.val_natCast_of_lt hnlt] using hval
  have hposcard : (positiveCoordinatePoints b p ((p - 1) / b) c).card =
      successes.card := by
    unfold positiveCoordinatePoints
    change (Finset.image (fun m : ℕ => (m : ZMod p) * (c : ZMod p))
      successes).card = successes.card
    exact Finset.card_image_iff.mpr hinj
  have hnegcard : (negativeCoordinatePoints b p ((p - 1) / b) c).card =
      successes.card := by
    unfold negativeCoordinatePoints
    change (Finset.image (fun m : ℕ => -((m : ZMod p) * (c : ZMod p)))
      successes).card = successes.card
    apply Finset.card_image_iff.mpr
    intro m hm n hn heq
    apply hinj hm hn
    exact neg_injective heq
  have hdisjoint : Disjoint
      (positiveCoordinatePoints b p ((p - 1) / b) c)
      (negativeCoordinatePoints b p ((p - 1) / b) c) := by
    apply Finset.disjoint_left.mpr
    intro x hxpos hxneg
    obtain ⟨m, hm, hxm⟩ := Finset.mem_image.mp hxpos
    obtain ⟨n, hn, hxn⟩ := Finset.mem_image.mp hxneg
    have hmrange := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    have hnrange := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have heq : (m : ZMod p) * (c : ZMod p) =
        -((n : ZMod p) * (c : ZMod p)) := hxm.trans hxn.symm
    have hsumzero : ((m + n : ℕ) : ZMod p) * (c : ZMod p) = 0 := by
      push_cast
      linear_combination heq
    have hcastzero : ((m + n : ℕ) : ZMod p) = 0 := by
      apply mul_right_cancel₀ hc0
      simpa using hsumzero
    have hQbound : 2 * ((p - 1) / b) ≤ p - 1 := by
      have hdiv := (Nat.le_div_iff_mul_le hb).1
        (show (p - 1) / b ≤ (p - 1) / b from le_rfl)
      have h2b : 2 * ((p - 1) / b) ≤ b * ((p - 1) / b) := by
        exact Nat.mul_le_mul_right ((p - 1) / b) hb2
      exact h2b.trans (by simpa [Nat.mul_comm] using hdiv)
    have hmnslt : m + n < p := by omega
    have hmnspos : 0 < m + n := by omega
    have hcastne : ((m + n : ℕ) : ZMod p) ≠ 0 := by
      rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hmnslt]
      exact hmnspos.ne'
    exact hcastne hcastzero
  change (positiveCoordinatePoints b p ((p - 1) / b) c ∪
      negativeCoordinatePoints b p ((p - 1) / b) c).card =
    2 * successes.card
  rw [Finset.card_union_of_disjoint hdisjoint, hposcard, hnegcard]
  omega

theorem collision_coordinate_positive_comparisons
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    collisionCount (primeDigitWord b p (by omega) hp.pos) g =
      2 * (positiveComparisonSet b p ((p - 1) / b)
        (gateParameter b p g)).card := by
  rw [collisionCount_eq_transformedCollisionCount (by omega) hp hbp g hg0,
    transformedCollisionCount_eq_card,
    transformedCollisionSet_eq_coordinate_points hb2 hp hbp hg0 hg1,
    coordinate_points_card hb2 hp hbp hg0 hg1]

/-- The centered fractional part of a positive rational numerator over `p`,
written directly with its canonical remainder. -/
def rationalSawtooth (p n : ℕ) : ℚ :=
  ((n % p : ℕ) : ℚ) / (p : ℚ) - 1 / 2

theorem rationalSawtooth_sub_pos_iff {p a d : ℕ} (hp : 0 < p) :
    0 < rationalSawtooth p a - rationalSawtooth p d ↔
      d % p < a % p := by
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  unfold rationalSawtooth
  constructor
  · intro h
    have hdiv : ((d % p : ℕ) : ℚ) / (p : ℚ) <
        ((a % p : ℕ) : ℚ) / (p : ℚ) := by linarith
    have hcast : ((d % p : ℕ) : ℚ) < ((a % p : ℕ) : ℚ) :=
      (div_lt_div_iff_of_pos_right hpq).1 hdiv
    exact_mod_cast hcast
  · intro h
    have hcast : ((d % p : ℕ) : ℚ) < ((a % p : ℕ) : ℚ) := by
      exact_mod_cast h
    have hdiv : ((d % p : ℕ) : ℚ) / (p : ℚ) <
        ((a % p : ℕ) : ℚ) / (p : ℚ) :=
      (div_lt_div_iff_of_pos_right hpq).2 hcast
    linarith

theorem rationalSawtooth_sub_neg_iff {p a d : ℕ} (hp : 0 < p) :
    rationalSawtooth p a - rationalSawtooth p d < 0 ↔
      a % p < d % p := by
  have h := rationalSawtooth_sub_pos_iff (p := p) (a := d) (d := a) hp
  constructor
  · intro hneg
    apply h.mp
    linarith
  · intro hres
    have hpos := h.mpr hres
    linarith

/-- The comparison in the constructive coordinate formula never lands on
the threshold. -/
theorem residue_threshold_ne {p b c m : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hm0 : 0 < m) (hmp : m < p)
    (hbp : b < p) (hcp : c < p)
    (hmb : m * b < p) (hcb : c ≠ b) :
    (m * c) % p ≠ m * b := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro heq
  have hcast : ((m * c : ℕ) : ZMod p) = ((m * b : ℕ) : ZMod p) := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast, ZMod.val_natCast, heq,
      Nat.mod_eq_of_lt hmb]
  push_cast at hcast
  have hmne : (m : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hmp]
    exact hm0.ne'
  have hcbcast : (c : ZMod p) = (b : ZMod p) :=
    mul_left_cancel₀ hmne hcast
  have hval := congrArg ZMod.val hcbcast
  simp only [ZMod.val_natCast_of_lt hcp,
    ZMod.val_natCast_of_lt hbp] at hval
  exact hcb hval

/-- The manuscript's sign term, written over exact rationals.  A separate
theorem below proves that its argument is nonzero in the constructive range. -/
def sawtoothSign (p a d : ℕ) : ℤ :=
  if 0 < rationalSawtooth p a - rationalSawtooth p d then 1 else -1

/-- The signed comparison sum is exactly the positive-comparison count
rewritten with `+1` and `-1` entries. -/
def signedComparison (b p Q c m : ℕ) : ℤ :=
  if m ∈ positiveComparisonSet b p Q c then 1 else -1

theorem signedComparison_eq_sawtoothSign
    {b p Q c m : ℕ} (hp : 0 < p) (hmb : m * b < p)
    (hm : m ∈ Finset.Icc 1 Q) :
    signedComparison b p Q c m = sawtoothSign p (m * c) (m * b) := by
  simp only [signedComparison, positiveComparisonSet, sawtoothSign,
    Finset.mem_filter, hm, true_and]
  have hiff := rationalSawtooth_sub_pos_iff (p := p)
    (a := m * c) (d := m * b) hp
  have hmbmod : (m * b) % p = m * b := Nat.mod_eq_of_lt hmb
  by_cases hcomparison : m * b < (m * c) % p
  · have hsaw : 0 < rationalSawtooth p (m * c) -
        rationalSawtooth p (m * b) := hiff.mpr (by
      simpa [hmbmod] using hcomparison)
    simp [hcomparison, hsaw]
  · have hsaw : ¬0 < rationalSawtooth p (m * c) -
        rationalSawtooth p (m * b) := by
      intro hsaw
      have hres := hiff.mp hsaw
      apply hcomparison
      simpa [hmbmod] using hres
    simp [hcomparison, hsaw]

theorem constructive_sawtooth_difference_ne_zero
    {p b c m : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hm0 : 0 < m) (hmp : m < p)
    (hbp : b < p) (hcp : c < p) (hmb : m * b < p) (hcb : c ≠ b) :
    rationalSawtooth p (m * c) - rationalSawtooth p (m * b) ≠ 0 := by
  have hthreshold := residue_threshold_ne hp hm0 hmp hbp hcp hmb hcb
  have hmbmod : (m * b) % p = m * b := Nat.mod_eq_of_lt hmb
  intro hzero
  rcases lt_trichotomy ((m * c) % p) ((m * b) % p) with hlt | heq | hgt
  · have hneg := (rationalSawtooth_sub_neg_iff (p := p)
      (a := m * c) (d := m * b) hp.pos).2 hlt
    linarith
  · apply hthreshold
    simpa [hmbmod] using heq
  · have hpos := (rationalSawtooth_sub_pos_iff (p := p)
      (a := m * c) (d := m * b) hp.pos).2 hgt
    linarith

theorem signedComparison_sum_identity {b p Q c : ℕ} :
    ((2 * (positiveComparisonSet b p Q c).card : ℕ) : ℤ) =
      (Q : ℤ) + ∑ m ∈ Finset.Icc 1 Q, signedComparison b p Q c m := by
  classical
  let domain := Finset.Icc 1 Q
  let successes := positiveComparisonSet b p Q c
  have hsubset : successes ⊆ domain := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hcard : domain.card = Q := by
    by_cases hQ : Q = 0
    · simp [domain, hQ]
    · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ
      dsimp [domain]
      rw [Nat.card_Icc]
      omega
  have hfilter : domain.filter (fun m => m ∈ successes) = successes := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hsubset h, h⟩
  have hindicator :
      (∑ m ∈ domain, if m ∈ successes then (1 : ℤ) else 0) =
        successes.card := by
    calc
      (∑ m ∈ domain, if m ∈ successes then (1 : ℤ) else 0) =
          ∑ m ∈ domain.filter (fun m => m ∈ successes), (1 : ℤ) := by
            symm
            rw [Finset.sum_filter]
      _ = successes.card := by rw [hfilter]; simp
  have hsum : (∑ m ∈ domain, signedComparison b p Q c m) =
      (2 * successes.card : ℤ) - Q := by
    rw [show (∑ m ∈ domain, signedComparison b p Q c m) =
        ∑ m ∈ domain, (2 * (if m ∈ successes then (1 : ℤ) else 0) - 1) by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hs : m ∈ successes <;>
        simp [signedComparison, successes, hs]]
    calc
      (∑ m ∈ domain, (2 * (if m ∈ successes then (1 : ℤ) else 0) - 1)) =
          2 * (∑ m ∈ domain, if m ∈ successes then (1 : ℤ) else 0) -
            domain.card := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              simp
      _ = (2 * successes.card : ℤ) - Q := by
            rw [hindicator, hcard]
  rw [show positiveComparisonSet b p Q c = successes by rfl]
  change ((2 * successes.card : ℕ) : ℤ) = (Q : ℤ) +
    ∑ m ∈ domain, signedComparison b p Q c m
  rw [hsum]
  push_cast
  ring

theorem collision_coordinate_signed_sawtooth
    {b p : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] {g : ZMod p} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    let Q := (p - 1) / b
    let c := gateParameter b p g
    ((collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℤ) =
      (Q : ℤ) + ∑ m ∈ Finset.Icc 1 Q,
        sawtoothSign p (m * c) (m * b) := by
  let Q := (p - 1) / b
  let c := gateParameter b p g
  have hcount := collision_coordinate_positive_comparisons hb2 hp hbp hg0 hg1
  change ((collisionCount (primeDigitWord b p (by omega) hp.pos) g : ℕ) : ℤ) =
    (Q : ℤ) + ∑ m ∈ Finset.Icc 1 Q,
      sawtoothSign p (m * c) (m * b)
  rw [hcount]
  calc
    ((2 * (positiveComparisonSet b p Q c).card : ℕ) : ℤ) =
        (Q : ℤ) + ∑ m ∈ Finset.Icc 1 Q,
          signedComparison b p Q c m := signedComparison_sum_identity
    _ = (Q : ℤ) + ∑ m ∈ Finset.Icc 1 Q,
          sawtoothSign p (m * c) (m * b) := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      have hmrange := Finset.mem_Icc.mp hm
      have hQmul : Q * b ≤ p - 1 := Nat.div_mul_le_self (p - 1) b
      have hmb : m * b < p := by
        have hmle : m * b ≤ Q * b := Nat.mul_le_mul_right b hmrange.2
        omega
      exact signedComparison_eq_sawtoothSign hp.pos hmb hm

def failureComparisonSet (b p Q c : ℕ) : Finset ℕ :=
  Finset.Icc 1 Q \ positiveComparisonSet b p Q c

theorem comparison_domain_card (Q : ℕ) :
    (Finset.Icc 1 Q).card = Q := by
  rw [Nat.card_Icc]
  omega

theorem positive_failure_card_identity (b p Q c : ℕ) :
    (positiveComparisonSet b p Q c).card +
      (failureComparisonSet b p Q c).card = Q := by
  have hsubset : positiveComparisonSet b p Q c ⊆ Finset.Icc 1 Q := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hcardle : (positiveComparisonSet b p Q c).card ≤ Q := by
    have := Finset.card_le_card hsubset
    simpa [comparison_domain_card] using this
  unfold failureComparisonSet
  rw [Finset.card_sdiff_of_subset hsubset, comparison_domain_card]
  omega

theorem coordinateMultiplier_collision_count
    {b p c : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] (hbc : b < c) (hcp : c < p) :
    collisionCount (primeDigitWord b p (by omega) hp.pos)
        (coordinateMultiplier b p c) =
      2 * (positiveComparisonSet b p ((p - 1) / b) c).card := by
  have hg0 := coordinateMultiplier_ne_zero hp hbp (by omega) hcp (by omega)
  have hg1 := coordinateMultiplier_ne_one hp (by omega) hbp (by omega) hcp
  rw [collision_coordinate_positive_comparisons hb2 hp hbp hg0 hg1]
  rw [gateParameter_coordinateMultiplier hp (by omega) hbp (by omega) hcp]

/-- Pointwise bridge from the intrinsic collision count to the manuscript's
`2Q - 2 sum Y_m` profile. -/
theorem coordinateMultiplier_collision_failure_profile
    {b p c : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] (hbc : b < c) (hcp : c < p) :
    collisionCount (primeDigitWord b p (by omega) hp.pos)
        (coordinateMultiplier b p c) =
      2 * ((p - 1) / b) -
        2 * (failureComparisonSet b p ((p - 1) / b) c).card := by
  rw [coordinateMultiplier_collision_count hb2 hp hbp hbc hcp]
  have hcard := positive_failure_card_identity b p ((p - 1) / b) c
  omega

theorem equalInterval_inter_card (a d b : ℕ) (hb : 0 < b) :
    ((Finset.Icc a (a + b - 1)) ∩
      (Finset.Icc d (d + b - 1))).card = b - Nat.dist a d := by
  have hinter :
      (Finset.Icc a (a + b - 1)) ∩
          (Finset.Icc d (d + b - 1)) =
        Finset.Icc (max a d) (min (a + b - 1) (d + b - 1)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_Icc]
    omega
  rw [hinter, Nat.card_Icc]
  by_cases h : a ≤ d
  · rw [Nat.dist_eq_sub_of_le h]
    have hab : a + b - 1 ≤ d + b - 1 := by omega
    rw [max_eq_right h, min_eq_left hab]
    omega
  · have h' : d ≤ a := by omega
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h']
    have hdb : d + b - 1 ≤ a + b - 1 := by omega
    rw [max_eq_left h', min_eq_right hdb]
    omega

theorem card_biUnion_inter_biUnion
    {ι κ α : Type*} [DecidableEq α]
    (s : Finset ι) (t : Finset κ)
    (left : ι → Finset α) (right : κ → Finset α)
    (hleft : (↑s : Set ι).PairwiseDisjoint left)
    (hright : (↑t : Set κ).PairwiseDisjoint right) :
    ((s.biUnion left) ∩ (t.biUnion right)).card =
      ∑ i ∈ s, ∑ j ∈ t, ((left i) ∩ (right j)).card := by
  classical
  let pieces : ι → Finset α := fun i =>
    t.biUnion fun j => left i ∩ right j
  have hpieces_subset (i : ι) : pieces i ⊆ left i := by
    intro x hx
    simp only [pieces, Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hx⟩ := hx
    exact (Finset.mem_inter.mp hx).1
  have hinner (i : ι) :
      (↑t : Set κ).PairwiseDisjoint (fun j => left i ∩ right j) := by
    intro j hj k hk hjk
    apply Finset.disjoint_left.mpr
    intro x hxj hxk
    have hxjr := (Finset.mem_inter.mp hxj).2
    have hxkr := (Finset.mem_inter.mp hxk).2
    exact (Finset.disjoint_left.mp (hright hj hk hjk)) hxjr hxkr
  have houter : (↑s : Set ι).PairwiseDisjoint pieces := by
    intro i hi j hj hij
    exact (hleft hi hj hij).mono (hpieces_subset i) (hpieces_subset j)
  have hunion :
      (s.biUnion left) ∩ (t.biUnion right) = s.biUnion pieces := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_biUnion, pieces]
    constructor
    · rintro ⟨⟨i, hi, hxi⟩, ⟨j, hj, hxj⟩⟩
      exact ⟨i, hi, j, hj, hxi, hxj⟩
    · rintro ⟨i, hi, j, hj, hx⟩
      exact ⟨⟨i, hi, hx.1⟩, ⟨j, hj, hx.2⟩⟩
  rw [hunion, Finset.card_biUnion houter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.card_biUnion (hinner i)]

def ceilingStart (p m k : ℕ) : ℕ := k * p ⌈/⌉ m

theorem ceilingStart_gap {p b m k l : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hkl : k < l) (hbm : b * m < p) :
    ceilingStart p m k + b ≤ ceilingStart p m l := by
  let a := ceilingStart p m k
  have ha_pos : 0 < a := by
    dsimp [a, ceilingStart]
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    have hkp : k * p = 0 := by
      have hle : k * p ≤ m * 0 :=
        (ceilDiv_le_iff_le_mul hm).1 (by simp [hzero])
      omega
    rcases Nat.mul_eq_zero.mp hkp with hk0 | hp0
    · omega
    · omega
  have hminimal : m * (a - 1) < k * p := by
    by_contra hnot
    have hle : k * p ≤ m * (a - 1) := by omega
    have hceil : ceilingStart p m k ≤ a - 1 := by
      exact (ceilDiv_le_iff_le_mul hm).2 hle
    dsimp [a] at hceil
    omega
  by_contra hnot
  have hceil_le : ceilingStart p m l ≤ a + b - 1 := by omega
  have hlp : l * p ≤ m * (a + b - 1) :=
    (ceilDiv_le_iff_le_mul hm).1 hceil_le
  have hsplit : a + b - 1 = (a - 1) + b := by omega
  rw [hsplit, Nat.mul_add] at hlp
  have hmb : m * b < p := by
    rw [Nat.mul_comm]
    exact hbm
  have hstep : (k + 1) * p ≤ l * p :=
    Nat.mul_le_mul_right p (by omega)
  have hsum : m * (a - 1) + m * b < (k + 1) * p := by
    rw [Nat.add_mul]
    omega
  omega

def ceilingInterval (p b m k : ℕ) : Finset ℕ :=
  Finset.Icc (ceilingStart p m k) (ceilingStart p m k + b - 1)

theorem ceilingIntervals_pairwiseDisjoint {p b m : ℕ}
    (hb : 0 < b) (hm : 0 < m) (hbm : b * m < p) :
    (↑(Finset.Ico 1 m) : Set ℕ).PairwiseDisjoint
      (ceilingInterval p b m) := by
  intro k hk l hl hkl
  have hk' := Finset.mem_Ico.mp hk
  have hl' := Finset.mem_Ico.mp hl
  apply Finset.disjoint_left.mpr
  intro x hxk hxl
  have hxk' := Finset.mem_Icc.mp hxk
  have hxl' := Finset.mem_Icc.mp hxl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hgap := ceilingStart_gap hm hk'.1 hlt hbm
    omega
  · have hgap := ceilingStart_gap hm hl'.1 hgt hbm
    omega

def ceilingIntervalUnion (p b m : ℕ) : Finset ℕ :=
  (Finset.Ico 1 m).biUnion (ceilingInterval p b m)

theorem ceilingIntervalUnion_subset_constructiveCoordinates
    {p b m : ℕ} (hm : 0 < m) (hbm : b * m < p) :
    ceilingIntervalUnion p b m ⊆ Finset.Icc (b + 1) (p - 1) := by
  intro c hc
  obtain ⟨k, hk, hcinterval⟩ := Finset.mem_biUnion.mp hc
  have hkrange := Finset.mem_Ico.mp hk
  have hcbounds := Finset.mem_Icc.mp hcinterval
  have hstartgt : b < ceilingStart p m k := by
    by_contra hnot
    have hstartle : ceilingStart p m k ≤ b := by omega
    have hkp : k * p ≤ m * b :=
      (ceilDiv_le_iff_le_mul hm).1 hstartle
    have hple : p ≤ k * p := by
      have := Nat.mul_le_mul_right p hkrange.1
      simpa using this
    have hmb : m * b < p := by
      rw [Nat.mul_comm]
      exact hbm
    omega
  have hfinish : ceilingStart p m k + b ≤ p := by
    have hgap := ceilingStart_gap hm hkrange.1 hkrange.2 hbm
    have hmself : ceilingStart p m m = p := by
      unfold ceilingStart
      apply Nat.le_antisymm
      · exact (ceilDiv_le_iff_le_mul hm).2 le_rfl
      · by_contra hnot
        have hceil : (m * p) ⌈/⌉ m ≤ p - 1 := by omega
        have hmul : m * p ≤ m * (p - 1) :=
          (ceilDiv_le_iff_le_mul hm).1 hceil
        have hp : 0 < p := by omega
        have hpred : p - 1 < p := Nat.sub_lt hp (by omega)
        have hstrict : m * (p - 1) < m * p :=
          (Nat.mul_lt_mul_left hm).2 hpred
        exact (Nat.not_lt_of_ge hmul) hstrict
    rwa [hmself] at hgap
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem mem_ceilingInterval_iff {p b m k c : ℕ}
    (hb : 0 < b) (hbc : b ≤ c) (hm : 0 < m) :
    c ∈ ceilingInterval p b m k ↔
      k * p ≤ m * c ∧ m * (c - b) < k * p := by
  unfold ceilingInterval ceilingStart
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨hlower, hupper⟩
    have hkp : k * p ≤ m * c :=
      (ceilDiv_le_iff_le_mul hm).1 hlower
    have hcsub : c - b < k * p ⌈/⌉ m := by omega
    have hsub : m * (c - b) < k * p := by
      by_contra hnot
      have hle : k * p ≤ m * (c - b) := by omega
      have hceil : k * p ⌈/⌉ m ≤ c - b :=
        (ceilDiv_le_iff_le_mul hm).2 hle
      omega
    exact ⟨hkp, hsub⟩
  · rintro ⟨hkp, hsub⟩
    have hlower : k * p ⌈/⌉ m ≤ c :=
      (ceilDiv_le_iff_le_mul hm).2 hkp
    have hcsub : c - b < k * p ⌈/⌉ m := by
      by_contra hnot
      have hceil : k * p ⌈/⌉ m ≤ c - b := by omega
      have hle : k * p ≤ m * (c - b) :=
        (ceilDiv_le_iff_le_mul hm).1 hceil
      omega
    exact ⟨hlower, by omega⟩

theorem mod_lt_mul_iff_mem_ceilingIntervalUnion
    {p b m c : ℕ} (hp : 0 < p) (hb : 0 < b) (hm : 0 < m)
    (hbc : b < c) (hcp : c < p) (hmb : m * b < p) :
    (m * c) % p < m * b ↔ c ∈ ceilingIntervalUnion p b m := by
  constructor
  · intro hmod
    let k := m * c / p
    have hdiv := Nat.mod_add_div (m * c) p
    have hmcgt : m * b < m * c := (Nat.mul_lt_mul_left hm).2 hbc
    have hkpos : 0 < k := by
      by_contra hnot
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hnot
      have hkzero' : m * c / p = 0 := by simpa [k] using hkzero
      rw [hkzero'] at hdiv
      simp at hdiv
      omega
    have hmclt : m * c < m * p := (Nat.mul_lt_mul_left hm).2 hcp
    have hklt : k < m := by
      exact (Nat.div_lt_iff_lt_mul hp).2 (by
        simpa [k, Nat.mul_comm] using hmclt)
    have hkp : k * p ≤ m * c := by
      dsimp [k]
      exact (Nat.le_div_iff_mul_le hp).1 le_rfl
    have hsplit : m * c = m * (c - b) + m * b := by
      calc
        m * c = m * ((c - b) + b) := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hbc)]
        _ = m * (c - b) + m * b := by ring
    have hsub : m * (c - b) < k * p := by
      dsimp [k] at hdiv ⊢
      simp only [Nat.mul_comm p] at hdiv
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_Ico.mpr ⟨hkpos, hklt⟩, ?_⟩
    exact (mem_ceilingInterval_iff hb (Nat.le_of_lt hbc) hm).2
      ⟨hkp, hsub⟩
  · intro hmem
    obtain ⟨k, hk, hkinterval⟩ := Finset.mem_biUnion.mp hmem
    have hkrange := Finset.mem_Ico.mp hk
    have hkineq :=
      (mem_ceilingInterval_iff hb (Nat.le_of_lt hbc) hm).1 hkinterval
    have hsplit : m * c = m * (c - b) + m * b := by
      calc
        m * c = m * ((c - b) + b) := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hbc)]
        _ = m * (c - b) + m * b := by ring
    have hmclt : m * c < (k + 1) * p := by
      calc
        m * c = m * (c - b) + m * b := hsplit
        _ < k * p + p := by omega
        _ = (k + 1) * p := by ring
    have hkle : k ≤ m * c / p :=
      (Nat.le_div_iff_mul_le hp).2 hkineq.1
    have hdivlt : m * c / p < k + 1 :=
      (Nat.div_lt_iff_lt_mul hp).2 hmclt
    have hq : m * c / p = k := by omega
    have hdiv := Nat.mod_add_div (m * c) p
    rw [hq] at hdiv
    simp only [Nat.mul_comm p] at hdiv
    omega

/-- The manuscript's floor crossing.  It is one exactly on the wrapped side
of the residue comparison and zero otherwise. -/
def floorCrossing (p b m c : ℕ) : ℕ :=
  m * c / p - m * (c - b) / p

theorem floorCrossing_eq_indicator
    {p b m c : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hbc : b < c) (hmb : m * b < p) :
    floorCrossing p b m c =
      if (m * c) % p < m * b then 1 else 0 := by
  let q := m * c / p
  have hdivq : (m * c) % p + q * p = m * c := by
    simpa [q, Nat.mul_comm] using Nat.mod_add_div (m * c) p
  have hmcgt : m * b < m * c := (Nat.mul_lt_mul_left hm).2 hbc
  have hsplit : m * c = m * (c - b) + m * b := by
    calc
      m * c = m * ((c - b) + b) := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt hbc)]
      _ = m * (c - b) + m * b := by ring
  by_cases hmod : (m * c) % p < m * b
  · have hqpos : 0 < q := by
      by_contra hnot
      have hqzero : q = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hqzero] at hdivq
      simp at hdivq
      omega
    have hlower : (q - 1) * p ≤ m * (c - b) := by
      have hqsplit : q * p = (q - 1) * p + p := by
        calc
          q * p = ((q - 1) + 1) * p := by
            rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hqpos)]
          _ = (q - 1) * p + p := by ring
      omega
    have hupper : m * (c - b) < q * p := by omega
    have hlediv : q - 1 ≤ m * (c - b) / p :=
      (Nat.le_div_iff_mul_le hp).2 hlower
    have hdivlt : m * (c - b) / p < q :=
      (Nat.div_lt_iff_lt_mul hp).2 hupper
    have hfloor : m * (c - b) / p = q - 1 := by omega
    simp only [hmod, if_true, floorCrossing]
    change q - m * (c - b) / p = 1
    rw [hfloor]
    omega
  · have hmodge : m * b ≤ (m * c) % p := by omega
    have hlower : q * p ≤ m * (c - b) := by omega
    have hrem : (m * c) % p < p := Nat.mod_lt _ hp
    have hupper : m * (c - b) < (q + 1) * p := by
      calc
        m * (c - b) ≤ q * p + (m * c) % p := by omega
        _ < q * p + p := by omega
        _ = (q + 1) * p := by ring
    have hlediv : q ≤ m * (c - b) / p :=
      (Nat.le_div_iff_mul_le hp).2 hlower
    have hdivlt : m * (c - b) / p < q + 1 :=
      (Nat.div_lt_iff_lt_mul hp).2 hupper
    have hfloor : m * (c - b) / p = q := by omega
    simp only [hmod, if_false, floorCrossing]
    change q - m * (c - b) / p = 0
    rw [hfloor]
    simp

theorem floorCrossing_eq_one_iff_mem_ceilingIntervalUnion
    {p b m c : ℕ} (hp : 0 < p) (hb : 0 < b) (hm : 0 < m)
    (hbc : b < c) (hcp : c < p) (hmb : m * b < p) :
    floorCrossing p b m c = 1 ↔
      c ∈ ceilingIntervalUnion p b m := by
  rw [floorCrossing_eq_indicator hp hm hbc hmb]
  rw [← mod_lt_mul_iff_mem_ceilingIntervalUnion hp hb hm hbc hcp hmb]
  by_cases hcomparison : (m * c) % p < m * b <;> simp [hcomparison]

theorem failure_comparison_iff_ceiling_interval
    {b p c m : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    [NeZero p] (hbc : b < c) (hcp : c < p)
    (hm : m ∈ Finset.Icc 1 ((p - 1) / b)) :
    m ∈ failureComparisonSet b p ((p - 1) / b) c ↔
      c ∈ ceilingIntervalUnion p b m := by
  have hmrange := Finset.mem_Icc.mp hm
  have hQmul : ((p - 1) / b) * b ≤ p - 1 :=
    Nat.div_mul_le_self (p - 1) b
  have hmb : m * b < p := by
    have hmle : m * b ≤ ((p - 1) / b) * b :=
      Nat.mul_le_mul_right b hmrange.2
    omega
  have hQp : (p - 1) / b < p := by
    have hle : (p - 1) / b ≤ p - 1 := Nat.div_le_self _ _
    omega
  have hmp : m < p := lt_of_le_of_lt hmrange.2 hQp
  have hne := residue_threshold_ne hp hmrange.1 hmp hbp hcp hmb (by omega)
  constructor
  · intro hfailure
    have hnot : ¬m * b < (m * c) % p := by
      have hparts := Finset.mem_sdiff.mp hfailure
      intro hlt
      apply hparts.2
      exact Finset.mem_filter.mpr ⟨hm, hlt⟩
    have hlt : (m * c) % p < m * b := by omega
    exact (mod_lt_mul_iff_mem_ceilingIntervalUnion hp.pos (by omega)
      hmrange.1 hbc hcp hmb).mp hlt
  · intro hinterval
    have hlt : (m * c) % p < m * b :=
      (mod_lt_mul_iff_mem_ceilingIntervalUnion hp.pos (by omega)
        hmrange.1 hbc hcp hmb).mpr hinterval
    apply Finset.mem_sdiff.mpr
    refine ⟨hm, ?_⟩
    intro hpositive
    have hgt := (Finset.mem_filter.mp hpositive).2
    omega

theorem ceilingInterval_card {p b m k : ℕ} (hb : 0 < b) :
    (ceilingInterval p b m k).card = b := by
  unfold ceilingInterval
  rw [Nat.card_Icc]
  omega

theorem ceilingIntervalUnion_card {p b m : ℕ}
    (hb : 0 < b) (hm : 0 < m) (hbm : b * m < p) :
    (ceilingIntervalUnion p b m).card = b * (m - 1) := by
  unfold ceilingIntervalUnion
  rw [Finset.card_biUnion (ceilingIntervals_pairwiseDisjoint hb hm hbm)]
  simp [ceilingInterval_card hb, Nat.mul_comm]

theorem ceilingIntervalUnion_inter_card {p b m n : ℕ}
    (hb : 0 < b) (hm : 0 < m) (hn : 0 < n)
    (hbm : b * m < p) (hbn : b * n < p) :
    ((ceilingIntervalUnion p b m) ∩
      (ceilingIntervalUnion p b n)).card =
      ∑ k ∈ Finset.Ico 1 m, ∑ l ∈ Finset.Ico 1 n,
        (b - Nat.dist (ceilingStart p m k) (ceilingStart p n l)) := by
  unfold ceilingIntervalUnion
  rw [card_biUnion_inter_biUnion
    (Finset.Ico 1 m) (Finset.Ico 1 n)
    (ceilingInterval p b m) (ceilingInterval p b n)
    (ceilingIntervals_pairwiseDisjoint hb hm hbm)
    (ceilingIntervals_pairwiseDisjoint hb hn hbn)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  exact equalInterval_inter_card _ _ b hb

noncomputable def diagonalVariance (b Q R : ℕ) : ℚ :=
  let N := b * (Q - 1) + R
  4 * (((b * Q * (Q - 1) : ℕ) : ℚ) / (2 * N) -
    ((b ^ 2 * Q * (Q - 1) * (2 * Q - 1) : ℕ) : ℚ) /
      (6 * N ^ 2))

theorem diagonalVariance_remainder_identity {b Q R : ℕ}
    (hQ : 1 ≤ Q) (hN : 0 < b * (Q - 1) + R) :
    diagonalVariance b Q R - (2 * (Q : ℚ) / 3) =
      (2 * (Q : ℚ) *
        ((b : ℚ) * ((R : ℚ) - b) * ((Q : ℚ) - 3) -
          (b : ℚ) ^ 2 - ((R : ℚ) - b) ^ 2)) /
        (3 * (b * (Q - 1) + R : ℕ) ^ 2) := by
  have hNq : (((b * (Q - 1) + R : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast hN.ne'
  have h2Q : 1 ≤ 2 * Q := by omega
  unfold diagonalVariance
  dsimp
  field_simp [hNq]
  push_cast
  rw [Nat.cast_sub hQ, Nat.cast_sub h2Q]
  push_cast
  ring

theorem diagonalNumerator_bounds {B q r : ℚ}
    (hB : 0 < B) (hr0 : 0 ≤ r) (hrB : r < B) (hq2 : 2 ≤ q) :
    let A := B * (r - B) * (q - 3) - B ^ 2 - (r - B) ^ 2
    A ≤ 0 ∧ -A ≤ 3 * B ^ 2 * q := by
  let E : ℚ := B - r
  let A : ℚ := B * (r - B) * (q - 3) - B ^ 2 - (r - B) ^ 2
  have hE0 : 0 ≤ E := by dsimp [E]; linarith
  have hEB : E ≤ B := by dsimp [E]; linarith
  have hBE : B * E ≤ B ^ 2 := by nlinarith
  have hBr : B * r ≤ B ^ 2 := by nlinarith
  have hE2 : E ^ 2 ≤ B ^ 2 := by nlinarith
  have hArewrite :
      A = -(B * E * (q - 2)) - B * r - E ^ 2 := by
    dsimp [A, E]
    ring
  have htail : 0 ≤ q - 2 := by linarith
  have hBEtail : B * E * (q - 2) ≤ B ^ 2 * q := calc
    B * E * (q - 2) ≤ B ^ 2 * (q - 2) :=
      mul_le_mul_of_nonneg_right hBE htail
    _ ≤ B ^ 2 * q :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg B)
  change A ≤ 0 ∧ -A ≤ 3 * B ^ 2 * q
  constructor
  · rw [hArewrite]
    have hterm1 : 0 ≤ B * E * (q - 2) := by positivity
    have hterm2 : 0 ≤ B * r := by positivity
    nlinarith [sq_nonneg E]
  · rw [hArewrite]
    nlinarith

theorem diagonalDenominator_bound {B q N : ℚ}
    (hB : 0 < B) (hq2 : 2 ≤ q) (hN : B * (q - 1) ≤ N) :
    6 * B ^ 2 * q ^ 2 ≤ 24 * N ^ 2 := by
  have hhalf0 : 0 ≤ B * q / 2 := by positivity
  have hhalf : B * q / 2 ≤ B * (q - 1) := by
    have := mul_le_mul_of_nonneg_left (show q / 2 ≤ q - 1 by linarith) hB.le
    linarith
  have hNhalf : B * q / 2 ≤ N := hhalf.trans hN
  have hN0 : 0 ≤ N := hhalf0.trans hNhalf
  have hNsquare : (B * q / 2) ^ 2 ≤ N ^ 2 := by
    nlinarith
  nlinarith

theorem diagonalRemainderExpression_abs_le_ten
    {B q r N : ℚ} (hB : 0 < B) (hr0 : 0 ≤ r) (hrB : r < B)
    (hq2 : 2 ≤ q) (hNpos : 0 < N) (hNlower : B * (q - 1) ≤ N) :
    |2 * q *
        (B * (r - B) * (q - 3) - B ^ 2 - (r - B) ^ 2) /
      (3 * N ^ 2)| ≤ 10 := by
  let A : ℚ := B * (r - B) * (q - 3) - B ^ 2 - (r - B) ^ 2
  have hA : A ≤ 0 ∧ -A ≤ 3 * B ^ 2 * q := by
    simpa [A] using diagonalNumerator_bounds hB hr0 hrB hq2
  have hdenBound : 6 * B ^ 2 * q ^ 2 ≤ 24 * N ^ 2 :=
    diagonalDenominator_bound hB hq2 hNlower
  have hnum : 2 * q * (-A) ≤ 6 * B ^ 2 * q ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hA.2
      (show 0 ≤ 2 * q by positivity)
    nlinarith
  have hnumN : 2 * q * (-A) ≤ 24 * N ^ 2 := hnum.trans hdenBound
  have hden : 0 < 3 * N ^ 2 := by positivity
  change |2 * q * A / (3 * N ^ 2)| ≤ 10
  have hquot_nonpos : 2 * q * A / (3 * N ^ 2) ≤ 0 := by
    have hnum_nonpos : 2 * q * A ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hA.1
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden.le
  rw [abs_of_nonpos hquot_nonpos]
  rw [← neg_div]
  apply (div_le_iff₀ hden).2
  calc
    -(2 * q * A) = 2 * q * (-A) := by ring
    _ ≤ 24 * N ^ 2 := hnumN
    _ ≤ 10 * (3 * N ^ 2) := by nlinarith [sq_nonneg N]

theorem diagonalVariance_remainder_abs_le_ten {b Q R : ℕ}
    (hb : 0 < b) (hQ : 1 ≤ Q) (hR : R < b)
    (hN : 0 < b * (Q - 1) + R) :
    |diagonalVariance b Q R - (2 * (Q : ℚ) / 3)| ≤ 10 := by
  by_cases hQone : Q = 1
  · subst Q
    norm_num [diagonalVariance]
  rw [diagonalVariance_remainder_identity hQ hN]
  have hQtwo : 2 ≤ Q := by omega
  apply diagonalRemainderExpression_abs_le_ten
  · exact_mod_cast hb
  · positivity
  · exact_mod_cast hR
  · exact_mod_cast hQtwo
  · exact_mod_cast hN
  · have hnat : b * (Q - 1) ≤ b * (Q - 1) + R := Nat.le_add_right _ _
    exact_mod_cast hnat

end NField.Alignment.SilentPrimesClosure
