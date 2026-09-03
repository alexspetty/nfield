/-
Author: Alexander S. Petty
-/

import NField.Alignment.DedekindReciprocity

/-!
# The three-modulus floor partition

For pairwise coprime positive moduli, every point in the open integer box has
a unique largest normalized coordinate.  Counting the three possible largest
coordinates gives the floor-product identity underlying Rademacher's
three-term reciprocity law.
-/

namespace NField.Alignment.ThreeModulusFloorPartition

open scoped BigOperators

/-- Interior positive representatives for a modulus. -/
def positiveInterior (m : ℕ) : Finset ℕ := Finset.Ico 1 m

theorem mem_positiveInterior_iff {m x : ℕ} :
    x ∈ positiveInterior m ↔ 0 < x ∧ x < m := by
  simp [positiveInterior]
  omega

/-- Coprimality prevents two interior normalized coordinates from tying. -/
theorem cross_product_ne
    {a b x y : ℕ} (hab : a.Coprime b)
    (hx : x ∈ positiveInterior a) (_hy : y ∈ positiveInterior b) :
    a * y ≠ b * x := by
  intro heq
  have hadvd : a ∣ b * x := by
    use y
    simpa [Nat.mul_comm] using heq.symm
  have hax : a ∣ x := hab.dvd_of_dvd_mul_left hadvd
  have hx' := mem_positiveInterior_iff.mp hx
  exact (Nat.not_dvd_of_pos_of_lt hx'.1 hx'.2) hax

/-- A cross-product comparison is the strict comparison of the corresponding
rational coordinates; equality is absent by coprimality. -/
theorem cross_le_iff_ratio_lt
    {a b x y : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : x ∈ positiveInterior a) (hy : y ∈ positiveInterior b) :
    a * y ≤ b * x ↔
      (y : ℚ) / (b : ℚ) < (x : ℚ) / (a : ℚ) := by
  have hne := cross_product_ne hab hx hy
  rw [div_lt_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast ha)]
  constructor
  · intro hle
    have hlt : a * y < b * x := lt_of_le_of_ne hle hne
    exact_mod_cast (by simpa [Nat.mul_comm] using hlt)
  · intro hlt
    have hlt' : a * y < b * x := by
      have hnat : y * a < x * b := by exact_mod_cast hlt
      simpa [Nat.mul_comm] using hnat
    exact hlt'.le

/-- A quotient counts the positive interior integers below its rational
boundary. -/
theorem quotient_eq_indicator_sum
    {a b x : ℕ} (ha : 0 < a) (hx : x < a) :
    b * x / a =
      ∑ y ∈ positiveInterior b, if a * y ≤ b * x then 1 else 0 := by
  by_cases hb : b = 0
  · subst b
    simp [positiveInterior]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hquot : b * x / a ≤ b - 1 := by
      have hlt : b * x / a < b := by
        rw [Nat.div_lt_iff_lt_mul ha]
        exact Nat.mul_lt_mul_of_pos_left hx hbpos
      omega
    rw [ZMod.div_eq_filter_card ha hquot]
    have hsucc : (b - 1).succ = b := by omega
    rw [hsucc]
    simp only [positiveInterior]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _hy
    simp [Nat.mul_comm]

/-- One floor product counts the box points for which its displayed
coordinate is largest. -/
theorem floorProduct_eq_indicator_sum
    {a b c x : ℕ} (ha : 0 < a) (hx : x < a) :
    (b * x / a) * (c * x / a) =
      ∑ y ∈ positiveInterior b, ∑ z ∈ positiveInterior c,
        if a * y ≤ b * x ∧ a * z ≤ c * x then 1 else 0 := by
  rw [quotient_eq_indicator_sum ha hx, quotient_eq_indicator_sum ha hx]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases hy : a * y ≤ b * x <;>
    by_cases hz : a * z ≤ c * x <;> simp [hy, hz]

/-- At each interior box point exactly one normalized coordinate is largest. -/
theorem largestCoordinate_indicator_sum
    {a b c x y z : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c)
    (hx : x ∈ positiveInterior a)
    (hy : y ∈ positiveInterior b)
    (hz : z ∈ positiveInterior c) :
    (if a * y ≤ b * x ∧ a * z ≤ c * x then 1 else 0) +
        (if b * x ≤ a * y ∧ b * z ≤ c * y then 1 else 0) +
        (if c * x ≤ a * z ∧ c * y ≤ b * z then 1 else 0) = 1 := by
  have hxy := cross_le_iff_ratio_lt ha hb hab hx hy
  have hxz := cross_le_iff_ratio_lt ha hc hac hx hz
  have hyx := cross_le_iff_ratio_lt hb ha hab.symm hy hx
  have hyz := cross_le_iff_ratio_lt hb hc hbc hy hz
  have hzx := cross_le_iff_ratio_lt hc ha hac.symm hz hx
  have hzy := cross_le_iff_ratio_lt hc hb hbc.symm hz hy
  simp only [hxy, hxz, hyx, hyz, hzx, hzy]
  let X : ℚ := (x : ℚ) / (a : ℚ)
  let Y : ℚ := (y : ℚ) / (b : ℚ)
  let Z : ℚ := (z : ℚ) / (c : ℚ)
  change (if Y < X ∧ Z < X then 1 else 0) +
      (if X < Y ∧ Z < Y then 1 else 0) +
      (if X < Z ∧ Y < Z then 1 else 0) = 1
  have hXY : X ≠ Y := by
    intro heq
    have hcross : a * y = b * x := by
      have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      dsimp [X, Y] at heq
      field_simp [haQ, hbQ] at heq
      have hnat : a * y = x * b := by exact_mod_cast heq.symm
      simpa [Nat.mul_comm] using hnat
    exact cross_product_ne hab hx hy hcross
  have hXZ : X ≠ Z := by
    intro heq
    have hcross : a * z = c * x := by
      have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
      dsimp [X, Z] at heq
      field_simp [haQ, hcQ] at heq
      have hnat : a * z = x * c := by exact_mod_cast heq.symm
      simpa [Nat.mul_comm] using hnat
    exact cross_product_ne hac hx hz hcross
  have hYZ : Y ≠ Z := by
    intro heq
    have hcross : b * z = c * y := by
      have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
      dsimp [Y, Z] at heq
      field_simp [hbQ, hcQ] at heq
      have hnat : b * z = y * c := by exact_mod_cast heq.symm
      simpa [Nat.mul_comm] using hnat
    exact cross_product_ne hbc hy hz hcross
  rcases lt_or_gt_of_ne hXY with hXYlt | hYXlt
  · rcases lt_or_gt_of_ne hYZ with hYZlt | hZYlt
    · simp [hXYlt, hYZlt, hXYlt.trans hYZlt,
        not_lt_of_ge hXYlt.le, not_lt_of_ge hYZlt.le]
    · by_cases hZX : Z < X
      · simp [hXYlt, hZYlt, hZX, not_lt_of_ge hXYlt.le,
          not_lt_of_ge hZYlt.le, not_lt_of_ge hZX.le]
      · have hXZlt : X < Z := lt_of_le_of_ne (le_of_not_gt hZX) hXZ
        simp [hXYlt, hZYlt, hXZlt, not_lt_of_ge hXYlt.le,
          not_lt_of_ge hZYlt.le, not_lt_of_ge hXZlt.le]
  · rcases lt_or_gt_of_ne hXZ with hXZlt | hZXlt
    · simp [hYXlt, hXZlt, hYXlt.trans hXZlt,
        not_lt_of_ge hYXlt.le, not_lt_of_ge hXZlt.le]
    · by_cases hZY : Z < Y
      · simp [hYXlt, hZXlt, hZY, not_lt_of_ge hYXlt.le,
          not_lt_of_ge hZXlt.le, not_lt_of_ge hZY.le]
      · have hYZlt : Y < Z := lt_of_le_of_ne (le_of_not_gt hZY) hYZ
        simp [hYXlt, hZXlt, hYZlt, not_lt_of_ge hYXlt.le,
          not_lt_of_ge hZXlt.le, not_lt_of_ge hYZlt.le]

/-- The exact three-modulus floor-product partition. -/
theorem threeModulus_floorProduct_sum
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    (∑ x ∈ positiveInterior a, (b * x / a) * (c * x / a)) +
        (∑ y ∈ positiveInterior b, (a * y / b) * (c * y / b)) +
        (∑ z ∈ positiveInterior c, (a * z / c) * (b * z / c)) =
      (a - 1) * (b - 1) * (c - 1) := by
  let RX := fun x y z : ℕ =>
    if a * y ≤ b * x ∧ a * z ≤ c * x then 1 else 0
  let RY := fun x y z : ℕ =>
    if b * x ≤ a * y ∧ b * z ≤ c * y then 1 else 0
  let RZ := fun x y z : ℕ =>
    if c * x ≤ a * z ∧ c * y ≤ b * z then 1 else 0
  have hA :
      (∑ x ∈ positiveInterior a, (b * x / a) * (c * x / a)) =
        ∑ x ∈ positiveInterior a, ∑ y ∈ positiveInterior b,
          ∑ z ∈ positiveInterior c, RX x y z := by
    apply Finset.sum_congr rfl
    intro x hx
    simpa [RX] using floorProduct_eq_indicator_sum ha
      (mem_positiveInterior_iff.mp hx).2 (b := b) (c := c)
  have hB :
      (∑ y ∈ positiveInterior b, (a * y / b) * (c * y / b)) =
        ∑ y ∈ positiveInterior b, ∑ x ∈ positiveInterior a,
          ∑ z ∈ positiveInterior c, RY x y z := by
    apply Finset.sum_congr rfl
    intro y hy
    simpa [RY, and_comm] using floorProduct_eq_indicator_sum hb
      (mem_positiveInterior_iff.mp hy).2 (b := a) (c := c)
  have hC :
      (∑ z ∈ positiveInterior c, (a * z / c) * (b * z / c)) =
        ∑ z ∈ positiveInterior c, ∑ x ∈ positiveInterior a,
          ∑ y ∈ positiveInterior b, RZ x y z := by
    apply Finset.sum_congr rfl
    intro z hz
    simpa [RZ, and_comm] using floorProduct_eq_indicator_sum hc
      (mem_positiveInterior_iff.mp hz).2 (b := a) (c := b)
  have hBreorder :
      (∑ y ∈ positiveInterior b, ∑ x ∈ positiveInterior a,
          ∑ z ∈ positiveInterior c, RY x y z) =
        ∑ x ∈ positiveInterior a, ∑ y ∈ positiveInterior b,
          ∑ z ∈ positiveInterior c, RY x y z := by
    rw [Finset.sum_comm]
  have hCreorder :
      (∑ z ∈ positiveInterior c, ∑ x ∈ positiveInterior a,
          ∑ y ∈ positiveInterior b, RZ x y z) =
        ∑ x ∈ positiveInterior a, ∑ y ∈ positiveInterior b,
          ∑ z ∈ positiveInterior c, RZ x y z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.sum_comm]
  rw [hA, hB, hC, hBreorder, hCreorder]
  calc
    (∑ x ∈ positiveInterior a, ∑ y ∈ positiveInterior b,
          ∑ z ∈ positiveInterior c, RX x y z) +
        (∑ x ∈ positiveInterior a, ∑ y ∈ positiveInterior b,
          ∑ z ∈ positiveInterior c, RY x y z) +
        (∑ x ∈ positiveInterior a, ∑ y ∈ positiveInterior b,
          ∑ z ∈ positiveInterior c, RZ x y z) =
        ∑ x ∈ positiveInterior a, ∑ y ∈ positiveInterior b,
          ∑ z ∈ positiveInterior c,
            (RX x y z + RY x y z + RZ x y z) := by
              simp only [Finset.sum_add_distrib]
    _ = ∑ _x ∈ positiveInterior a, ∑ _y ∈ positiveInterior b,
          ∑ _z ∈ positiveInterior c, 1 := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro z hz
            exact largestCoordinate_indicator_sum ha hb hc hab hac hbc hx hy hz
    _ = (a - 1) * (b - 1) * (c - 1) := by
          simp [positiveInterior, Nat.mul_assoc]

end NField.Alignment.ThreeModulusFloorPartition
