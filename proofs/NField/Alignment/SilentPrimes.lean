/-
Author: Alexander S. Petty
-/

import NField.Alignment.BinDerangements

/-!
# Silent primes and finite collision variance

Reusable arithmetic and finite-probability proofs for the Lean companion to
"Silent Primes and the Variance of the Collision Count".
-/

namespace NField.Alignment.SilentPrimes

open scoped BigOperators
open ZMod
open NField.CollisionDefinition
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.Alignment.PhaseFilteredRamanujan
open NField.Alignment.BinDerangements

/-! ## The finite silent-prime recipe -/

/-- The positive normal form of the manuscript's silent integer
`b^(ell+1) - u * (b^ell - 1)`. -/
def silentInteger (b ell u : ℕ) : ℕ :=
  b ^ ell * (b - u) + u

/-- The positive normal form is exactly the displayed subtraction formula. -/
theorem silentInteger_eq_displayed {b ell u : ℕ}
    (hb : 1 ≤ b) (hu : u ≤ b) :
    silentInteger b ell u = b ^ (ell + 1) - u * (b ^ ell - 1) := by
  have hpow : 1 ≤ b ^ ell := one_le_pow₀ hb
  have hmul : u * (b ^ ell - 1) ≤ b ^ ell * b := by
    calc
      u * (b ^ ell - 1) ≤ b * (b ^ ell - 1) :=
        Nat.mul_le_mul hu (le_refl _)
      _ ≤ b * b ^ ell := Nat.mul_le_mul_left b (Nat.sub_le _ _)
      _ = b ^ ell * b := by ring
  unfold silentInteger
  rw [pow_succ]
  symm
  apply (Nat.sub_eq_iff_eq_add hmul).2
  calc
    b ^ ell * b = b ^ ell * ((b - u) + u) := by
      rw [Nat.sub_add_cancel hu]
    _ = b ^ ell * (b - u) + u * b ^ ell := by ring
    _ = b ^ ell * (b - u) + u * ((b ^ ell - 1) + 1) := by
      rw [Nat.sub_add_cancel hpow]
    _ = b ^ ell * (b - u) + u + u * (b ^ ell - 1) := by ring

/-- Every admissible silent integer is positive. -/
theorem silentInteger_pos {b ell u : ℕ} (hu : 0 < u) :
    0 < silentInteger b ell u := by
  unfold silentInteger
  omega

/-- The displayed divisor condition is exactly equality with the deranging
multiplier indexed by `u`. -/
theorem power_eq_derangingMultiplier_iff_dvd_silentInteger
    {b p ell u : ℕ} (hb : 0 < b) (hp : Nat.Prime p)
    (hbp : b < p) [NeZero p] (hu0 : 0 < u) (hub : u < b) :
    (b : ZMod p) ^ ell = derangingMultiplier b p u ↔
      p ∣ silentInteger b ell u := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcpos : 0 < b - u := Nat.sub_pos_of_lt hub
  have hcltp : b - u < p := lt_trans (Nat.sub_lt hb hu0) hbp
  have hc0 : ((b - u : ℕ) : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hcltp]
    exact hcpos.ne'
  have hcast : ((silentInteger b ell u : ℕ) : ZMod p) =
      (b : ZMod p) ^ ell * (b - u : ℕ) + u := by
    simp [silentInteger, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  constructor
  · intro hpower
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [hcast, hpower]
    unfold derangingMultiplier
    field_simp
    simp
  · intro hdvd
    have hzero : ((silentInteger b ell u : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [hcast] at hzero
    unfold derangingMultiplier
    apply (mul_right_cancel₀ hc0)
    field_simp at hzero ⊢
    linear_combination hzero

/-- Global silence for the intrinsic prime digit partition at a power lag. -/
def GloballySilentAt (b p ell : ℕ) [NeZero p]
    (hb : 0 < b) (hp : Nat.Prime p) : Prop :=
  collisionCount (primeDigitWord b p hb hp.pos) ((b : ZMod p) ^ ell) = 0

/-- Exact factor recipe for globally silent primes. -/
theorem globallySilentAt_iff_exists_dvd_silentInteger
    {b p ell : ℕ} (hb2 : 2 ≤ b) (hp : Nat.Prime p)
    (hbp : b < p) [NeZero p] :
    GloballySilentAt b p ell (by omega) hp ↔
      ∃ u ∈ Finset.Ico 1 b, p ∣ silentInteger b ell u := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast_of_lt hbp]
    omega
  have hpow0 : (b : ZMod p) ^ ell ≠ 0 := pow_ne_zero _ hb0
  unfold GloballySilentAt
  constructor
  · intro hzero
    have hmem : (b : ZMod p) ^ ell ∈ derangingFamily b p :=
      (mem_derangingFamily_iff hb2 hp hbp ((b : ZMod p) ^ ell)).mpr
        ⟨hpow0, hzero⟩
    have hmem' : (b : ZMod p) ^ ell ∈
        (Finset.Ico 1 b).image (derangingMultiplier b p) := by
      simpa only [derangingFamily] using hmem
    obtain ⟨u, hu, hpower⟩ := Finset.mem_image.mp hmem'
    have hu' := Finset.mem_Ico.mp hu
    exact ⟨u, hu,
      (power_eq_derangingMultiplier_iff_dvd_silentInteger
        (by omega) hp hbp (by omega) hu'.2).mp hpower.symm⟩
  · rintro ⟨u, hu, hdvd⟩
    have hu' := Finset.mem_Ico.mp hu
    have hpower : (b : ZMod p) ^ ell = derangingMultiplier b p u :=
      (power_eq_derangingMultiplier_iff_dvd_silentInteger
        (by omega) hp hbp (by omega) hu'.2).mpr hdvd
    have hmem' : (b : ZMod p) ^ ell ∈
        (Finset.Ico 1 b).image (derangingMultiplier b p) :=
      Finset.mem_image.mpr ⟨u, hu, hpower.symm⟩
    have hmem : (b : ZMod p) ^ ell ∈ derangingFamily b p := by
      simpa only [derangingFamily] using hmem'
    exact ((mem_derangingFamily_iff hb2 hp hbp
      ((b : ZMod p) ^ ell)).mp hmem).2

/-- The intrinsic digit read along the power orbit of the base. -/
def repetendDigit (b p j : ℕ) : ℕ :=
  digitBin b p ((b ^ j) % p)

/-- Repetend silence over the full Fermat window.  For a prime not dividing
the base, this window consists of complete repetitions of the exact
multiplicative orbit, so its zero predicate is unchanged. -/
def RepetendSilentAt (b p ell : ℕ) : Prop :=
  ∀ j : Fin (p - 1),
    repetendDigit b p j.val ≠ repetendDigit b p (j.val + ell)

instance decidableRepetendSilentAt (b p ell : ℕ) :
    Decidable (RepetendSilentAt b p ell) := by
  unfold RepetendSilentAt
  infer_instance

/-- A repetend-silent prime at lag `ell` cannot exceed `b^(ell+1)`. -/
theorem repetendSilentAt_bound {b p ell : ℕ}
    (hb2 : 2 ≤ b) (hp : Nat.Prime p) (hbp : b < p)
    (hsilent : RepetendSilentAt b p ell) :
    p ≤ b ^ (ell + 1) := by
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  by_contra hnot
  have hlarge : b ^ (ell + 1) < p := by omega
  have hpowlt : b ^ ell < p := by
    have hle : b ^ ell ≤ b ^ (ell + 1) := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  let j0 : Fin (p - 1) := ⟨0, Nat.sub_pos_of_lt hp.one_lt⟩
  have hneq := hsilent j0
  have hleft : repetendDigit b p 0 = 0 := by
    simp [repetendDigit, digitBin, Nat.mod_eq_of_lt hp.one_lt,
      Nat.div_eq_of_lt hbp]
  have hright : repetendDigit b p ell = 0 := by
    unfold repetendDigit digitBin
    rw [Nat.mod_eq_of_lt hpowlt]
    rw [Nat.div_eq_of_lt]
    simpa [pow_succ, Nat.mul_comm] using hlarge
  apply hneq
  have hzeroeq :
      repetendDigit b p 0 = repetendDigit b p ell :=
    hleft.trans hright.symm
  simpa [j0] using hzeroeq

/-- The exact nine lag-one silent integers in base ten. -/
theorem decimal_lag_one_silent_integers :
    (Finset.Ico 1 10).image (silentInteger 10 1) =
      ({19, 28, 37, 46, 55, 64, 73, 82, 91} : Finset ℕ) := by
  decide

/-- A directly executable scan of the complete range allowed by the
repetend bound. -/
def decimalLagOneRepetendSilentPrimes : Finset ℕ :=
  (Finset.Icc 11 100).filter fun p =>
    Nat.Prime p ∧ RepetendSilentAt 10 p 1

/-- Exact finite certificate for the base-ten lag-one repetend list. -/
theorem decimal_lag_one_repetend_silent_certificate :
    decimalLagOneRepetendSilentPrimes =
      ({11, 13, 19, 23, 37, 41, 73} : Finset ℕ) := by
  decide

/-- The seven base-ten lag-one primes are exactly the globally silent ones. -/
theorem decimal_lag_one_globally_silent_iff {p : ℕ}
    (hp : Nat.Prime p) (hbp : 10 < p) [NeZero p] :
    GloballySilentAt 10 p 1 (by omega) hp ↔
      p ∈ ({11, 13, 19, 23, 37, 41, 73} : Finset ℕ) := by
  rw [globallySilentAt_iff_exists_dvd_silentInteger (b := 10) (ell := 1)
    (by omega) hp hbp]
  constructor
  · rintro ⟨u, hu, hdvd⟩
    have hu' := Finset.mem_Ico.mp hu
    have hu0 : 1 ≤ u := hu'.1
    have hult : u < 10 := hu'.2
    have hpos : 0 < silentInteger 10 1 u := silentInteger_pos (by omega)
    have hple : p ≤ silentInteger 10 1 u := Nat.le_of_dvd hpos hdvd
    have hle : p ≤ 91 := by
      norm_num [silentInteger] at hple
      omega
    interval_cases p <;> interval_cases u
    all_goals try { norm_num at hp }
    all_goals try { norm_num [silentInteger] at hdvd }
    all_goals decide
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

/-- The same seven primes are exactly the repetend-silent primes at lag one. -/
theorem decimal_lag_one_repetend_silent_iff {p : ℕ}
    (hp : Nat.Prime p) (hbp : 10 < p) :
    RepetendSilentAt 10 p 1 ↔
      p ∈ ({11, 13, 19, 23, 37, 41, 73} : Finset ℕ) := by
  constructor
  · intro hsilent
    have hle : p ≤ 100 := by
      simpa using repetendSilentAt_bound (b := 10) (ell := 1)
        (by omega) hp hbp hsilent
    have hmem : p ∈ decimalLagOneRepetendSilentPrimes := by
      simp [decimalLagOneRepetendSilentPrimes, hp, hsilent]
      omega
    rw [decimal_lag_one_repetend_silent_certificate] at hmem
    exact hmem
  · intro hmem
    have hmem' : p ∈ decimalLagOneRepetendSilentPrimes := by
      rw [decimal_lag_one_repetend_silent_certificate]
      exact hmem
    exact (Finset.mem_filter.mp hmem').2.2

/-! ## The exact constructive mean -/

/-- The two displayed forms of the manuscript's exact mean agree. -/
theorem constructive_mean_second_form {b Q R : ℕ}
    (hN : 0 < b * (Q - 1) + R) :
    ((Q * (b * (Q - 1) + 2 * R) : ℕ) : ℚ) /
        (b * (Q - 1) + R : ℕ) =
      (Q : ℚ) + (Q * R : ℕ) / (b * (Q - 1) + R : ℕ) := by
  have hdenom : ((b * (Q - 1) + R : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hN.ne'
  field_simp
  push_cast
  ring

/-! ## A finite variance ledger -/

/-- Uniform population mean on a finite nonempty coordinate type. -/
noncomputable def populationMean {α : Type*} [Fintype α]
    (f : α → ℚ) : ℚ :=
  (Fintype.card α : ℚ)⁻¹ * ∑ x, f x

/-- Uniform population variance, written as second moment minus mean square. -/
noncomputable def populationVariance {α : Type*} [Fintype α]
    (f : α → ℚ) : ℚ :=
  populationMean (fun x => f x ^ 2) - populationMean f ^ 2

/-- Indicator of membership in one failure interval. -/
def eventIndicator {α μ : Type*} [DecidableEq α]
    (events : μ → Finset α) (m : μ) (x : α) : ℚ :=
  if x ∈ events m then 1 else 0

/-- Total number of failure intervals containing a coordinate. -/
noncomputable def failureTotal {α μ : Type*} [Fintype μ] [DecidableEq α]
    (events : μ → Finset α) (x : α) : ℚ :=
  ∑ m, eventIndicator events m x

/-- Summing one event indicator gives the event cardinality. -/
theorem sum_eventIndicator {α μ : Type*} [Fintype α] [DecidableEq α]
    (events : μ → Finset α) (m : μ) :
    ∑ x : α, eventIndicator events m x = (events m).card := by
  classical
  unfold eventIndicator
  rw [Finset.sum_boole]
  congr
  ext x
  simp

/-- The first moment of the failure total is the sum of event sizes. -/
theorem sum_failureTotal {α μ : Type*} [Fintype α] [Fintype μ]
    [DecidableEq α] (events : μ → Finset α) :
    ∑ x : α, failureTotal events x =
      ∑ m : μ, ((events m).card : ℚ) := by
  classical
  unfold failureTotal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact sum_eventIndicator events m

/-- The second moment is the complete pairwise-overlap ledger. -/
theorem sum_failureTotal_sq {α μ : Type*} [Fintype α] [Fintype μ]
    [DecidableEq α] (events : μ → Finset α) :
    ∑ x : α, failureTotal events x ^ 2 =
      ∑ m : μ, ∑ n : μ, ((events m ∩ events n).card : ℚ) := by
  classical
  unfold failureTotal
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  calc
    (∑ x : α, eventIndicator events m x * eventIndicator events n x) =
        ∑ x : α, if x ∈ events m ∩ events n then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hm : x ∈ events m <;>
            by_cases hn : x ∈ events n <;>
            simp [eventIndicator, hm, hn]
    _ = ((events m ∩ events n).card : ℚ) := by
          simpa [eventIndicator] using
            (sum_eventIndicator
              (fun _ : Unit => events m ∩ events n) ())

/-- Exact abstract interval-overlap variance.  Supplying the manuscript's
interval sets turns the right side into its `H_mn` ledger. -/
theorem failureTotal_variance_eq_overlap_ledger
    {α μ : Type*} [Fintype α] [Nonempty α] [Fintype μ]
    [DecidableEq α] (events : μ → Finset α) :
    populationVariance (failureTotal events) =
      (Fintype.card α : ℚ)⁻¹ *
          (∑ m : μ, ∑ n : μ, ((events m ∩ events n).card : ℚ)) -
        ((Fintype.card α : ℚ)⁻¹ *
          ∑ m : μ, ((events m).card : ℚ)) ^ 2 := by
  unfold populationVariance populationMean
  rw [sum_failureTotal_sq, sum_failureTotal]

/-- Population variance is unchanged by translation and scales quadratically. -/
theorem populationVariance_affine {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℚ) (a k : ℚ) :
    populationVariance (fun x => a + k * f x) =
      k ^ 2 * populationVariance f := by
  classical
  have hN : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hsum1 :
      (∑ x : α, (a + k * f x)) =
        (Fintype.card α : ℚ) * a + k * ∑ x : α, f x := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp
  have hsum2 :
      (∑ x : α, (a + k * f x) ^ 2) =
        (Fintype.card α : ℚ) * a ^ 2 +
          (2 * a * k) * ∑ x : α, f x +
          k ^ 2 * ∑ x : α, f x ^ 2 := by
    calc
      (∑ x : α, (a + k * f x) ^ 2) =
          ∑ x : α, (a ^ 2 + (2 * a * k) * f x + k ^ 2 * f x ^ 2) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = (Fintype.card α : ℚ) * a ^ 2 +
          (2 * a * k) * ∑ x : α, f x +
          k ^ 2 * ∑ x : α, f x ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.mul_sum, Finset.mul_sum]
            simp
  unfold populationVariance populationMean
  rw [hsum2, hsum1]
  field_simp [hN]
  ring

/-- The collision profile `2Q - 2 sum Y_m` has four times the failure-count
variance, exactly as in the manuscript. -/
theorem collisionProfile_variance_eq_four_mul
    {α μ : Type*} [Fintype α] [Nonempty α] [Fintype μ]
    [DecidableEq α] (events : μ → Finset α) (Q : ℕ) :
    populationVariance
        (fun x => (2 * Q : ℚ) - 2 * failureTotal events x) =
      4 * populationVariance (failureTotal events) := by
  have h := populationVariance_affine
    (failureTotal events) (2 * (Q : ℚ)) (-2)
  norm_num [pow_two] at h
  simpa [sub_eq_add_neg] using h

/-- Combined exact overlap formula for the collision profile. -/
theorem collisionProfile_variance_eq_overlap_ledger
    {α μ : Type*} [Fintype α] [Nonempty α] [Fintype μ]
    [DecidableEq α] (events : μ → Finset α) (Q : ℕ) :
    populationVariance
        (fun x => (2 * Q : ℚ) - 2 * failureTotal events x) =
      4 * ((Fintype.card α : ℚ)⁻¹ *
          (∑ m : μ, ∑ n : μ, ((events m ∩ events n).card : ℚ)) -
        ((Fintype.card α : ℚ)⁻¹ *
          ∑ m : μ, ((events m).card : ℚ)) ^ 2) := by
  rw [collisionProfile_variance_eq_four_mul,
    failureTotal_variance_eq_overlap_ledger]

end NField.Alignment.SilentPrimes
