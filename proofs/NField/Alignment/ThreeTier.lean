/-
Author: Alexander S. Petty
-/

import NField.Alignment.DigitPartitionedField
import NField.Alignment.SupportedRoughDecomposition
import NField.Golden.Threshold

/-!
# Complement pairing and the Three-Tier gap

This module formalizes the synchronized long-division proof used by
"The Three-Tier Theorem."

The definitions work with arbitrary positive rough parts, including composite
ones.  A common clearing depth contributes a multiplier `u` coprime to the
rough part.  Every nonzero residue occurs `m` times among the positive
numerators, while the zero residue contributes the `m - 1` terminating
fractions.  Complementary rough residues are paired before the alignment is
normalized.
-/

namespace NField.Alignment.ThreeTier

theorem digit_complement (b t q : ℕ) (hb : 0 < b) (ht : 0 < t)
    (_hq : 0 < q) (hqt : q < t) (hnd : ¬ t ∣ b * q) :
    (b * (t - q)) / t = b - 1 - (b * q) / t := by
  let d := (b * q) / t
  let r := (b * q) % t
  have hrlt : r < t := Nat.mod_lt _ ht
  have hrne : r ≠ 0 := by
    intro hr0
    exact hnd ((Nat.dvd_iff_mod_eq_zero).2 hr0)
  have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
  have hdecomp : r + t * d = b * q := by
    exact Nat.mod_add_div (b * q) t
  have hprodlt : b * q < b * t := Nat.mul_lt_mul_of_pos_left hqt hb
  have hdlt : d < b := (Nat.div_lt_iff_lt_mul ht).2 (by simpa [Nat.mul_comm] using hprodlt)
  have hbparts : b - 1 - d + d + 1 = b := by omega
  have htparts : t - q + q = t := by omega
  have hrle : r ≤ t := by omega
  have hrparts : t - r + r = t := by omega
  have hmain : b * (t - q) = (b - 1 - d) * t + (t - r) := by
    let c := b - 1 - d
    let s := t - q
    let w := t - r
    change b * s = c * t + w
    have hb' : c + d + 1 = b := by simpa [c] using hbparts
    have ht' : s + q = t := by simpa [s] using htparts
    have hr' : w + r = t := by simpa [w] using hrparts
    nlinarith [hdecomp]
  apply Nat.div_eq_of_lt_le
  · simpa [d] using (show (b - 1 - d) * t ≤ b * (t - q) by
      rw [hmain]
      omega)
  · simpa [d] using (show b * (t - q) < (b - 1 - d + 1) * t by
      rw [hmain]
      nlinarith)

theorem complement_mod (x t r : ℕ) (ht : 0 < t) (hr : 0 < r)
    (hrt : r < t) (hcop : Nat.Coprime t x) :
    (x * (t - r)) % t = t - (x * r) % t := by
  let q := (x * r) % t
  let q' := (x * (t - r)) % t
  have hq_lt : q < t := Nat.mod_lt _ ht
  have hq'_lt : q' < t := Nat.mod_lt _ ht
  have hq_ne : q ≠ 0 := by
    intro hq0
    have hdvd : t ∣ x * r := (Nat.dvd_iff_mod_eq_zero).2 (by simpa [q] using hq0)
    have : t ∣ r := hcop.dvd_of_dvd_mul_left hdvd
    exact (Nat.not_dvd_of_pos_of_lt hr hrt) this
  have hq_pos : 0 < q := Nat.pos_of_ne_zero hq_ne
  have hsum_mod : (q + q') % t = 0 := by
    dsimp [q, q']
    rw [← Nat.add_mod]
    rw [← Nat.mul_add]
    rw [Nat.add_sub_of_le hrt.le]
    simp
  have ht_le_sum : t ≤ q + q' := by
    by_contra hnot
    have hlt : q + q' < t := by omega
    rw [Nat.mod_eq_of_lt hlt] at hsum_mod
    omega
  have hsum_lt : q + q' < 2 * t := by omega
  have hdiv : (q + q') / t = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using ht_le_sum
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum_lt
  have hsum_eq : q + q' = t := by
    calc
      q + q' = (q + q') % t + t * ((q + q') / t) :=
        (Nat.mod_add_div (q + q') t).symm
      _ = t := by rw [hsum_mod, hdiv]; simp
  dsimp [q, q'] at hsum_eq ⊢
  omega

def positiveResidues (t : ℕ) : Finset ℕ := Finset.Icc 1 (t - 1)

theorem complement_mem_positiveResidues {t r : ℕ}
    (hr : r ∈ positiveResidues t) : t - r ∈ positiveResidues t := by
  simp only [positiveResidues, Finset.mem_Icc] at hr ⊢
  omega

theorem sum_complement (t : ℕ) (f : ℕ → ℕ) :
    (∑ r ∈ positiveResidues t, f (t - r)) =
      ∑ r ∈ positiveResidues t, f r := by
  classical
  refine Finset.sum_bij (fun r _ => t - r) ?_ ?_ ?_ ?_
  · exact fun r hr => complement_mem_positiveResidues hr
  · intro r₁ hr₁ r₂ hr₂ heq
    simp only [positiveResidues, Finset.mem_Icc] at hr₁ hr₂
    omega
  · intro s hs
    refine ⟨t - s, complement_mem_positiveResidues hs, ?_⟩
    simp only [positiveResidues, Finset.mem_Icc] at hs
    omega
  · intro r hr
    rfl

theorem card_positiveResidues (t : ℕ) :
    (positiveResidues t).card = t - 1 := by
  simp [positiveResidues]

theorem paired_sum_bound {t L : ℕ} (f : ℕ → ℕ)
    (hpair : ∀ r ∈ positiveResidues t, f r + f (t - r) ≤ L) :
    2 * (∑ r ∈ positiveResidues t, f r) ≤ (t - 1) * L := by
  let S := ∑ r ∈ positiveResidues t, f r
  calc
    2 * S = S + S := by omega
    _ = (∑ r ∈ positiveResidues t, f r) +
        ∑ r ∈ positiveResidues t, f (t - r) := by
          rw [sum_complement]
    _ = ∑ r ∈ positiveResidues t, (f r + f (t - r)) := by
          simp only [Finset.sum_add_distrib]
    _ ≤ ∑ _r ∈ positiveResidues t, L := Finset.sum_le_sum fun r hr => hpair r hr
    _ = (t - 1) * L := by simp [card_positiveResidues]

def periodicResidue (b t u r j : ℕ) : ℕ :=
  ((b ^ j * u) * r) % t

def periodicDigit (b t u r j : ℕ) : ℕ :=
  NField.CollisionDefinition.digitBin b t (periodicResidue b t u r j)

def periodicMatchAt (b t u r j : ℕ) : Prop :=
  periodicDigit b t u r j = periodicDigit b t u 1 j

/-- The literal denominator-`n` digit read after a common clearing depth. -/
def clearedDigit (b n k D j : ℕ) : ℕ :=
  NField.Alignment.digitAt b n k (D + j)

/-- If `n=t*m` and `m ∣ b^D`, the denominator-`n` digit reduces exactly to
the rough-residue digit with multiplier `b^D/m`. -/
theorem clearedDigit_eq_periodicDigit {b t m k D j : ℕ}
    (hm : 0 < m) (hD : m ∣ b ^ D) :
    clearedDigit b (t * m) k D j =
      periodicDigit b t (NField.Alignment.clearingCofactor b m D) (k % t) j := by
  let u := NField.Alignment.clearingCofactor b m D
  have hbD : b ^ D = m * u := by
    unfold u NField.Alignment.clearingCofactor
    exact (Nat.mul_div_cancel' hD).symm
  unfold clearedDigit NField.Alignment.digitAt periodicDigit periodicResidue
  rw [pow_add, hbD]
  have hnum : m * u * b ^ j * k = m * (b ^ j * u * k) := by ring
  rw [hnum, Nat.mul_comm t m, Nat.mul_mod_mul_left]
  unfold NField.CollisionDefinition.digitBin
  have hdigitnum : b * (m * ((b ^ j * u * k) % t)) =
      m * (b * ((b ^ j * u * k) % t)) := by ring
  rw [hdigitnum, Nat.mul_div_mul_left _ _ hm]
  simp [u, Nat.mul_mod]

/-- Equality with the reference digit on the original denominator clock. -/
def clearedMatchAt (b t m k D j : ℕ) : Prop :=
  clearedDigit b (t * m) k D j = clearedDigit b (t * m) 1 D j

theorem clearedMatchAt_iff_periodicMatchAt {b t m k D j : ℕ}
    (hm : 0 < m) (hD : m ∣ b ^ D) :
    clearedMatchAt b t m k D j ↔
      periodicMatchAt b t (NField.Alignment.clearingCofactor b m D) (k % t) j := by
  unfold clearedMatchAt periodicMatchAt
  rw [clearedDigit_eq_periodicDigit hm hD, clearedDigit_eq_periodicDigit hm hD]
  have href : periodicDigit b t (NField.Alignment.clearingCofactor b m D)
      (1 % t) j =
      periodicDigit b t (NField.Alignment.clearingCofactor b m D) 1 j := by
    unfold periodicDigit periodicResidue
    exact congrArg (NField.CollisionDefinition.digitBin b t)
      (NField.CollisionDefinition.transportedRemainder_mod_right t
        (b ^ j * NField.Alignment.clearingCofactor b m D) 1)
  rw [href]

noncomputable def periodicMatchPositions (b t u r L : ℕ) : Finset ℕ := by
  classical
  exact
  (Finset.range L).filter (periodicMatchAt b t u r)

noncomputable def periodicMatchCount (b t u r L : ℕ) : ℕ :=
  (periodicMatchPositions b t u r L).card

theorem periodicResidue_complement {b t u r j : ℕ} (ht : 0 < t)
    (hr : 0 < r) (hrt : r < t) (hbt : Nat.Coprime t b)
    (htu : Nat.Coprime t u) :
    periodicResidue b t u (t - r) j = t - periodicResidue b t u r j := by
  apply complement_mod _ t r ht hr hrt
  exact (hbt.pow_right j).mul_right htu

theorem periodicDigit_complement {b t u r j : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hr : 0 < r) (hrt : r < t) (hbt : Nat.Coprime t b)
    (htu : Nat.Coprime t u) :
    periodicDigit b t u (t - r) j = b - 1 - periodicDigit b t u r j := by
  let q := periodicResidue b t u r j
  have hq_lt : q < t := by
    exact Nat.mod_lt _ ht
  have hxu : Nat.Coprime t (b ^ j * u) := (hbt.pow_right j).mul_right htu
  have hq_ne : q ≠ 0 := by
    intro hq0
    have hdvd : t ∣ (b ^ j * u) * r :=
      (Nat.dvd_iff_mod_eq_zero).2 (by simpa [q, periodicResidue] using hq0)
    have : t ∣ r := hxu.dvd_of_dvd_mul_left hdvd
    exact (Nat.not_dvd_of_pos_of_lt hr hrt) this
  have hq_pos : 0 < q := Nat.pos_of_ne_zero hq_ne
  have hnd : ¬t ∣ b * q := by
    intro hdvd
    have : t ∣ q := hbt.dvd_of_dvd_mul_left hdvd
    exact (Nat.not_dvd_of_pos_of_lt hq_pos hq_lt) this
  unfold periodicDigit
  rw [periodicResidue_complement ht hr hrt hbt htu]
  exact digit_complement b t q hb ht hq_pos hq_lt hnd

theorem complementary_matches_exclusive {b t u r j : ℕ} (hb : 0 < b)
    (ht : 0 < t) (hr : 0 < r) (hrt : r < t)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) (hbeven : Even b) :
    ¬(periodicMatchAt b t u r j ∧ periodicMatchAt b t u (t - r) j) := by
  intro hboth
  have hcomp := periodicDigit_complement hb ht hr hrt hbt htu (j := j)
  rcases hbeven with ⟨c, hc⟩
  unfold periodicMatchAt at hboth
  omega

theorem periodicMatchPositions_disjoint {b t u r L : ℕ} (hb : 0 < b)
    (ht : 0 < t) (hr : 0 < r) (hrt : r < t)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) (hbeven : Even b) :
    Disjoint (periodicMatchPositions b t u r L)
      (periodicMatchPositions b t u (t - r) L) := by
  classical
  rw [Finset.disjoint_left]
  intro j hj hmate
  unfold periodicMatchPositions at hj hmate
  have hj' := (Finset.mem_filter.mp hj).2
  have hmate' := (Finset.mem_filter.mp hmate).2
  exact complementary_matches_exclusive hb ht hr hrt hbt htu hbeven ⟨hj', hmate'⟩

theorem periodicMatchCount_pair_le {b t u r L : ℕ} (hb : 0 < b)
    (ht : 0 < t) (hr : 0 < r) (hrt : r < t)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) (hbeven : Even b) :
    periodicMatchCount b t u r L + periodicMatchCount b t u (t - r) L ≤ L := by
  classical
  let A := periodicMatchPositions b t u r L
  let B := periodicMatchPositions b t u (t - r) L
  have hdis : Disjoint A B := periodicMatchPositions_disjoint hb ht hr hrt hbt htu hbeven
  have hsubset : A ∪ B ⊆ Finset.range L := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjA | hjB
    · unfold A periodicMatchPositions at hjA
      exact (Finset.mem_filter.mp hjA).1
    · unfold B periodicMatchPositions at hjB
      exact (Finset.mem_filter.mp hjB).1
  unfold periodicMatchCount
  change A.card + B.card ≤ L
  calc
    A.card + B.card = (A ∪ B).card := (Finset.card_union_of_disjoint hdis).symm
    _ ≤ (Finset.range L).card := Finset.card_le_card hsubset
    _ = L := Finset.card_range L

/-- Moving a finite sum forward by one index changes only its two endpoints. -/
theorem sum_shift_succ (f : ℕ → ℕ) (L : ℕ) :
    (∑ j ∈ Finset.range L, f (j + 1)) + f 0 =
      (∑ j ∈ Finset.range L, f j) + f L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

/-- Multiplying the common clearing multiplier by the base advances every
rough residue by one synchronized position. -/
theorem periodicResidue_mul_base (b t u r j : ℕ) :
    periodicResidue b t (b * u) r j = periodicResidue b t u r (j + 1) := by
  unfold periodicResidue
  congr 1
  rw [pow_succ]
  ring

theorem periodicMatchAt_mul_base (b t u r j : ℕ) :
    periodicMatchAt b t (b * u) r j ↔ periodicMatchAt b t u r (j + 1) := by
  simp only [periodicMatchAt, periodicDigit, periodicResidue_mul_base]

/-- A comparison window closes when its length is a multiplicative period. -/
theorem periodicResidue_wrap {b t u r L : ℕ}
    (hperiod : b ^ L % t = 1 % t) :
    periodicResidue b t u r L = periodicResidue b t u r 0 := by
  unfold periodicResidue
  simp only [pow_zero, one_mul]
  calc
    (b ^ L * u * r) % t = (b ^ L * (u * r)) % t := by simp [Nat.mul_assoc]
    _ = ((b ^ L % t) * ((u * r) % t)) % t := by simp [Nat.mul_mod]
    _ = ((1 % t) * ((u * r) % t)) % t := by rw [hperiod]
    _ = (u * r) % t := by rw [← Nat.mul_mod]; simp

theorem periodicMatchAt_wrap {b t u r L : ℕ}
    (hperiod : b ^ L % t = 1 % t) :
    periodicMatchAt b t u r L ↔ periodicMatchAt b t u r 0 := by
  unfold periodicMatchAt periodicDigit
  rw [periodicResidue_wrap hperiod, periodicResidue_wrap hperiod]

/-- Advancing the common clearing depth once rotates a full-period match
window and leaves its number of matches unchanged. -/
theorem periodicMatchCount_mul_base {b t u r L : ℕ}
    (hperiod : b ^ L % t = 1 % t) :
    periodicMatchCount b t (b * u) r L = periodicMatchCount b t u r L := by
  classical
  unfold periodicMatchCount periodicMatchPositions
  simp only [Finset.card_filter]
  simp_rw [periodicMatchAt_mul_base]
  let f : ℕ → ℕ := fun j => if periodicMatchAt b t u r j then 1 else 0
  change (∑ j ∈ Finset.range L, f (j + 1)) = ∑ j ∈ Finset.range L, f j
  have hshift := sum_shift_succ f L
  have hwrap : f L = f 0 := by
    unfold f
    rw [if_congr (periodicMatchAt_wrap hperiod) rfl rfl]
  omega

/-- The same invariance holds after any number of extra clearing digits. -/
theorem periodicMatchCount_mul_base_pow {b t u r L q : ℕ}
    (hperiod : b ^ L % t = 1 % t) :
    periodicMatchCount b t (b ^ q * u) r L = periodicMatchCount b t u r L := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hu : b ^ (q + 1) * u = b * (b ^ q * u) := by
        rw [pow_succ]
        ac_rfl
      calc
        periodicMatchCount b t (b ^ (q + 1) * u) r L =
            periodicMatchCount b t (b * (b ^ q * u)) r L := by rw [hu]
        _ = periodicMatchCount b t (b ^ q * u) r L :=
          periodicMatchCount_mul_base hperiod
        _ = periodicMatchCount b t u r L := ih

/-- The clearing cofactor at depth `D+q` is the old cofactor multiplied by
`b^q`. -/
theorem clearingCofactor_add {b m D q : ℕ} (hD : m ∣ b ^ D) :
    NField.Alignment.clearingCofactor b m (D + q) =
      b ^ q * NField.Alignment.clearingCofactor b m D := by
  unfold NField.Alignment.clearingCofactor
  rw [pow_add, Nat.mul_comm (b ^ D) (b ^ q), Nat.mul_div_assoc (b ^ q) hD]

/-- This is the manuscript's clearing-depth independence statement for one
rough residue on a full synchronized period. -/
theorem periodicMatchCount_independent_of_later_clearing_depth
    {b t m D q r L : ℕ} (hD : m ∣ b ^ D)
    (hperiod : b ^ L % t = 1 % t) :
    periodicMatchCount b t
        (NField.Alignment.clearingCofactor b m (D + q)) r L =
      periodicMatchCount b t
        (NField.Alignment.clearingCofactor b m D) r L := by
  rw [clearingCofactor_add hD]
  exact periodicMatchCount_mul_base_pow hperiod

noncomputable def periodicNonterminatingMatchTotal
    (b t u L : ℕ) : ℕ :=
  ∑ r ∈ positiveResidues t, periodicMatchCount b t u r L

noncomputable def periodicFieldMatchTotal
    (b t m u L : ℕ) : ℕ :=
  (m - 1) * L + m * periodicNonterminatingMatchTotal b t u L

noncomputable def synchronizedCompositeAlignmentReal
    (b t m u L : ℕ) : ℝ :=
  (periodicFieldMatchTotal b t m u L : ℝ) /
    (((t * m - 1) * L : ℕ) : ℝ)

noncomputable def finiteComplementBoundReal (t m : ℕ) : ℝ :=
  (((m : ℝ) * (t + 1)) / 2 - 1) / ((t : ℝ) * m - 1)

noncomputable def roughCeilingReal (t : ℕ) : ℝ :=
  ((t : ℝ) + 1) / (2 * t)

/-- Summing over all nonzero rough residues preserves the clearing-depth
rotation invariance. -/
theorem periodicNonterminatingMatchTotal_independent_of_later_clearing_depth
    {b t m D q L : ℕ} (hD : m ∣ b ^ D)
    (hperiod : b ^ L % t = 1 % t) :
    periodicNonterminatingMatchTotal b t
        (NField.Alignment.clearingCofactor b m (D + q)) L =
      periodicNonterminatingMatchTotal b t
        (NField.Alignment.clearingCofactor b m D) L := by
  unfold periodicNonterminatingMatchTotal
  apply Finset.sum_congr rfl
  intro r _hr
  exact periodicMatchCount_independent_of_later_clearing_depth hD hperiod

/-- Therefore the normalized composite-rough-part alignment is independent of
every later valid clearing depth when `L` closes the base orbit modulo `t`. -/
theorem synchronizedCompositeAlignmentReal_independent_of_later_clearing_depth
    {b t m D q L : ℕ} (hD : m ∣ b ^ D)
    (hperiod : b ^ L % t = 1 % t) :
    synchronizedCompositeAlignmentReal b t m
        (NField.Alignment.clearingCofactor b m (D + q)) L =
      synchronizedCompositeAlignmentReal b t m
        (NField.Alignment.clearingCofactor b m D) L := by
  unfold synchronizedCompositeAlignmentReal periodicFieldMatchTotal
  rw [periodicNonterminatingMatchTotal_independent_of_later_clearing_depth
    hD hperiod]

theorem periodicNonterminatingMatchTotal_bound {b t u L : ℕ}
    (hb : 0 < b) (ht : 0 < t) (hbt : Nat.Coprime t b)
    (htu : Nat.Coprime t u) (hbeven : Even b) :
    2 * periodicNonterminatingMatchTotal b t u L ≤ (t - 1) * L := by
  unfold periodicNonterminatingMatchTotal
  apply paired_sum_bound
  intro r hr
  have hrange : 1 ≤ r ∧ r ≤ t - 1 := by
    simpa [positiveResidues] using hr
  exact periodicMatchCount_pair_le hb ht (by omega) (by omega) hbt htu hbeven

theorem synchronizedCompositeAlignmentReal_le_finite_bound {b t m u L : ℕ}
    (hb : 0 < b) (ht : 1 < t) (hm : 1 ≤ m) (hL : 0 < L)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) (hbeven : Even b) :
    synchronizedCompositeAlignmentReal b t m u L ≤ finiteComplementBoundReal t m := by
  let S := periodicNonterminatingMatchTotal b t u L
  have hsum := periodicNonterminatingMatchTotal_bound hb (by omega) hbt htu hbeven (L := L)
  change 2 * S ≤ (t - 1) * L at hsum
  have hsumR0 : ((2 * S : ℕ) : ℝ) ≤ (((t - 1) * L : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hsumR : (2 : ℝ) * S ≤ ((t : ℝ) - 1) * L := by
    simpa [Nat.cast_sub (by omega : 1 ≤ t)] using hsumR0
  have htm : 1 < t * m := by nlinarith
  have htmR : (1 : ℝ) < (t : ℝ) * m := by exact_mod_cast htm
  have hden : 0 < (t : ℝ) * m - 1 := by linarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  unfold synchronizedCompositeAlignmentReal periodicFieldMatchTotal finiteComplementBoundReal
  change (((m - 1) * L + m * S : ℕ) : ℝ) /
      (((t * m - 1) * L : ℕ) : ℝ) ≤
    (((m : ℝ) * ((t : ℝ) + 1)) / 2 - 1) / ((t : ℝ) * m - 1)
  push_cast [Nat.cast_sub hm, Nat.cast_sub htm.le]
  have hnum : ((m : ℝ) - 1) * L + (m : ℝ) * S ≤
      (((m : ℝ) * ((t : ℝ) + 1)) / 2 - 1) * L := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ m by positivity)
      (sub_nonneg.mpr hsumR)]
  calc
    (((m : ℝ) - 1) * L + (m : ℝ) * S) / (((t : ℝ) * m - 1) * L) ≤
        ((((m : ℝ) * ((t : ℝ) + 1)) / 2 - 1) * L) /
          (((t : ℝ) * m - 1) * L) :=
      div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hden hLR))
    _ = (((m : ℝ) * ((t : ℝ) + 1)) / 2 - 1) / ((t : ℝ) * m - 1) := by
      field_simp

theorem finiteComplementBoundReal_lt_roughCeiling {t m : ℕ}
    (ht : 1 < t) (hm : 1 ≤ m) :
    finiteComplementBoundReal t m < roughCeilingReal t := by
  have htm : 1 < t * m := by nlinarith
  have htR : (0 : ℝ) < t := by positivity
  have htOne : (1 : ℝ) < t := by exact_mod_cast ht
  have htmR : (1 : ℝ) < (t : ℝ) * m := by exact_mod_cast htm
  have hden : 0 < (t : ℝ) * m - 1 := by linarith
  rw [finiteComplementBoundReal, roughCeilingReal]
  have hidentity :
      (((t : ℝ) + 1) / (2 * t)) -
        ((((m : ℝ) * ((t : ℝ) + 1)) / 2 - 1) / ((t : ℝ) * m - 1)) =
          ((t : ℝ) - 1) / (2 * t * ((t : ℝ) * m - 1)) := by
    field_simp
    ring
  have hgap : 0 < ((t : ℝ) - 1) / (2 * t * ((t : ℝ) * m - 1)) := by
    exact div_pos (sub_pos.mpr htOne) (mul_pos (mul_pos (by norm_num) htR) hden)
  linarith

theorem roughCeilingReal_le_three_fifths {t : ℕ} (ht : 5 ≤ t) :
    roughCeilingReal t ≤ (3 : ℝ) / 5 := by
  have htR : (0 : ℝ) < t := by positivity
  have htFive : (5 : ℝ) ≤ t := by exact_mod_cast ht
  rw [roughCeilingReal]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * t)]
  nlinarith

theorem periodicMatchAt_iff_of_digitPartitioning {b p u r j : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : NField.Alignment.DigitPartitioning b p)
    (htu : Nat.Coprime p u) (hr : 0 < r) (hrt : r < p) :
    periodicMatchAt b p u r j ↔ r = 1 := by
  have hsync := NField.Alignment.synchronizedAlignedAtPosition_iff
    hp hpb hdp htu (k := r) (j := j)
  have hrmod : r % p = r := Nat.mod_eq_of_lt hrt
  unfold NField.Alignment.synchronizedAlignedAtPosition
    NField.Alignment.synchronizedAligned at hsync
  unfold periodicMatchAt periodicDigit periodicResidue
  have hequiv :
      NField.CollisionDefinition.digitBin b p (((b ^ j * u) * r) % p) =
          NField.CollisionDefinition.digitBin b p (((b ^ j * u) * 1) % p) ↔
        NField.CollisionDefinition.digitBin b p ((r * (b ^ j * u)) % p) =
          NField.CollisionDefinition.digitBin b p ((b ^ j * u) % p) := by
    simp [Nat.mul_comm]
  rw [hequiv]
  constructor
  · intro hmatch
    have hz : r % p ≠ 0 := by simpa [hrmod] using hr.ne'
    have hc := hsync.mp (Or.inr hmatch)
    rcases hc with hzero | hone
    · exact (hz hzero).elim
    · simpa [hrmod] using hone
  · intro hr1
    subst r
    simp

theorem periodicMatchCount_of_digitPartitioning {b p u r L : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : NField.Alignment.DigitPartitioning b p)
    (htu : Nat.Coprime p u) (hr : 0 < r) (hrt : r < p) :
    periodicMatchCount b p u r L = if r = 1 then L else 0 := by
  classical
  unfold periodicMatchCount periodicMatchPositions
  by_cases hr1 : r = 1
  · subst r
    simp [periodicMatchAt]
  · have hnone : (Finset.range L).filter (periodicMatchAt b p u r) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj
      exact fun hmatch => hr1 ((periodicMatchAt_iff_of_digitPartitioning
        hp hpb hdp htu hr hrt (j := j)).mp hmatch)
    rw [hnone]
    simp [hr1]

theorem periodicNonterminatingMatchTotal_of_digitPartitioning {b p u L : ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hdp : NField.Alignment.DigitPartitioning b p)
    (htu : Nat.Coprime p u) :
    periodicNonterminatingMatchTotal b p u L = L := by
  classical
  unfold periodicNonterminatingMatchTotal
  rw [Finset.sum_eq_single 1]
  · have hp1 : 1 < p := hp.one_lt
    rw [periodicMatchCount_of_digitPartitioning hp hpb hdp htu (by omega) hp1]
    simp
  · intro r hrmem hrne
    have hrange : 1 ≤ r ∧ r ≤ p - 1 := by simpa [positiveResidues] using hrmem
    rw [periodicMatchCount_of_digitPartitioning hp hpb hdp htu (by omega) (by omega)]
    simp [hrne]
  · intro hone
    have hp1 : 1 < p := hp.one_lt
    exfalso
    apply hone
    simp only [positiveResidues, Finset.mem_Icc]
    omega

theorem synchronizedCompositeAlignmentReal_eq_digitPartitioningFormula
    {b p m u L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : NField.Alignment.DigitPartitioning b p) (htu : Nat.Coprime p u)
    (hm : 1 ≤ m) (hL : 0 < L) :
    synchronizedCompositeAlignmentReal b p m u L =
      NField.Golden.alignmentFormulaReal p m := by
  have hpm : 1 < p * m := by nlinarith [hp.two_le]
  have hdenR : (0 : ℝ) < (p : ℝ) * m - 1 := by
    have hpmR : (1 : ℝ) < (p : ℝ) * m := by exact_mod_cast hpm
    linarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [synchronizedCompositeAlignmentReal, periodicFieldMatchTotal,
    periodicNonterminatingMatchTotal_of_digitPartitioning hp hpb hdp htu,
    NField.Golden.alignmentFormulaReal]
  push_cast [Nat.cast_sub hm, Nat.cast_sub hpm.le]
  field_simp
  ring

noncomputable def numeratorPeriodicMatchCount (b t u L k : ℕ) : ℕ :=
  if k % t = 0 then L else periodicMatchCount b t u (k % t) L

noncomputable def numeratorFieldMatchTotal (b t m u L : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (t * m - 1), numeratorPeriodicMatchCount b t u L k

/-- The manuscript's numerator score on the original denominator clock.
Multiples of the rough part are the terminating rows and receive all `L`
matches by convention. -/
noncomputable def clearedNumeratorMatchCount
    (b t m k D L : ℕ) : ℕ := by
  classical
  exact if t ∣ k then L else
    ((Finset.range L).filter (clearedMatchAt b t m k D)).card

noncomputable def clearedFieldMatchTotal
    (b t m D L : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (t * m - 1), clearedNumeratorMatchCount b t m k D L

theorem clearedNumeratorMatchCount_eq_periodic {b t m k D L : ℕ}
    (hm : 0 < m) (hD : m ∣ b ^ D) :
    clearedNumeratorMatchCount b t m k D L =
      numeratorPeriodicMatchCount b t
        (NField.Alignment.clearingCofactor b m D) L k := by
  classical
  unfold clearedNumeratorMatchCount numeratorPeriodicMatchCount
  by_cases htk : t ∣ k
  · rw [if_pos htk, if_pos ((Nat.dvd_iff_mod_eq_zero).mp htk)]
  · rw [if_neg htk, if_neg (mt (Nat.dvd_iff_mod_eq_zero).mpr htk)]
    unfold periodicMatchCount periodicMatchPositions
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [clearedMatchAt_iff_periodicMatchAt hm hD]

theorem sum_mod_blocks (t m : ℕ) (f : ℕ → ℕ) :
    (∑ k ∈ Finset.range (t * m), f (k % t)) =
      m * ∑ r ∈ Finset.range t, f r := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have htail : (∑ x ∈ Finset.range t, f ((t * m + x) % t)) =
          ∑ r ∈ Finset.range t, f r := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxt : x < t := Finset.mem_range.mp hx
        simp [Nat.add_mod, Nat.mod_eq_of_lt hxt]
      rw [htail, Nat.succ_mul]

theorem range_eq_insert_positiveResidues {t : ℕ} (ht : 0 < t) :
    Finset.range t = insert 0 (positiveResidues t) := by
  ext r
  simp only [Finset.mem_range, Finset.mem_insert, positiveResidues, Finset.mem_Icc]
  omega

theorem range_product_eq_insert_positive {t m : ℕ} (ht : 0 < t) (hm : 1 ≤ m) :
    Finset.range (t * m) = insert 0 (Finset.Icc 1 (t * m - 1)) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  have htm : 0 < t * m := Nat.mul_pos ht (by omega)
  omega

theorem numeratorFieldMatchTotal_eq_periodicFieldMatchTotal
    {b t m u L : ℕ} (ht : 0 < t) (hm : 1 ≤ m) :
    numeratorFieldMatchTotal b t m u L = periodicFieldMatchTotal b t m u L := by
  classical
  let f : ℕ → ℕ := fun r => if r = 0 then L else periodicMatchCount b t u r L
  let S := periodicNonterminatingMatchTotal b t u L
  let N := numeratorFieldMatchTotal b t m u L
  have hblock := sum_mod_blocks t m f
  have hresidue : (∑ r ∈ Finset.range t, f r) = L + S := by
    rw [range_eq_insert_positiveResidues ht, Finset.sum_insert]
    · have hzero : f 0 = L := by simp [f]
      rw [hzero]
      unfold S periodicNonterminatingMatchTotal
      apply congrArg (fun x => L + x)
      apply Finset.sum_congr rfl
      intro r hr
      have hrange : 1 ≤ r ∧ r ≤ t - 1 := by simpa [positiveResidues] using hr
      simp [f, show r ≠ 0 by omega]
    · simp [positiveResidues]
  have hfull : (∑ k ∈ Finset.range (t * m), f (k % t)) = m * (L + S) := by
    simpa [hresidue] using hblock
  have hpositive : (∑ k ∈ Finset.Icc 1 (t * m - 1), f (k % t)) = N := by
    unfold N numeratorFieldMatchTotal
    apply Finset.sum_congr rfl
    intro k hk
    unfold numeratorPeriodicMatchCount
    simp only [f]
  have hsplit : L + N = m * (L + S) := by
    rw [← hfull, range_product_eq_insert_positive ht hm, Finset.sum_insert]
    · simp [f, hpositive]
    · simp
  have hmSplit : m * L = (m - 1) * L + L := by
    calc
      m * L = ((m - 1) + 1) * L := by rw [Nat.sub_add_cancel hm]
      _ = (m - 1) * L + L := by simp [Nat.add_mul]
  unfold periodicFieldMatchTotal
  change N = (m - 1) * L + m * S
  rw [Nat.mul_add] at hsplit
  omega

/-- The direct numerator-by-numerator sum equals the residue-grouped sum used
in the complement proof. -/
theorem clearedFieldMatchTotal_eq_periodicFieldMatchTotal
    {b t m D L : ℕ} (ht : 0 < t) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedFieldMatchTotal b t m D L =
      periodicFieldMatchTotal b t m
        (NField.Alignment.clearingCofactor b m D) L := by
  unfold clearedFieldMatchTotal
  rw [show (∑ k ∈ Finset.Icc 1 (t * m - 1),
      clearedNumeratorMatchCount b t m k D L) =
      numeratorFieldMatchTotal b t m
        (NField.Alignment.clearingCofactor b m D) L by
    unfold numeratorFieldMatchTotal
    apply Finset.sum_congr rfl
    intro k _hk
    exact clearedNumeratorMatchCount_eq_periodic (by omega) hD]
  exact numeratorFieldMatchTotal_eq_periodicFieldMatchTotal ht hm

theorem roughPart_odd_of_even_base {t b : ℕ} (hcop : Nat.Coprime t b)
    (hbeven : Even b) : Odd t := by
  apply Nat.coprime_two_right.mp
  exact hcop.of_dvd_right (even_iff_two_dvd.mp hbeven)

theorem roughPart_ge_five {t b : ℕ} (ht : 0 < t)
    (hcop : Nat.Coprime t b) (hbeven : Even b)
    (ht1 : t ≠ 1) (ht3 : t ≠ 3) : 5 ≤ t := by
  rcases roughPart_odd_of_even_base hcop hbeven with ⟨q, hq⟩
  omega

theorem three_not_dvd_supported {b m : ℕ} (h3b : ¬3 ∣ b)
    (hm : NField.Alignment.Supported b m) : ¬3 ∣ m := by
  intro h3m
  rcases hm with ⟨D, hD⟩
  have hpow : 3 ∣ b ^ D := dvd_trans h3m hD
  exact h3b (Nat.prime_three.dvd_of_dvd_pow hpow)

theorem threeCore_ge_seven_elevenths_iff {m : ℕ} (hm : 1 ≤ m) :
    (7 : ℝ) / 11 ≤ NField.Golden.alignmentFormulaReal 3 m ↔ 4 ≤ m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  unfold NField.Golden.alignmentFormulaReal
  change (7 : ℝ) / 11 ≤ ((2 : ℝ) * m - 1) / ((3 : ℝ) * m - 1) ↔ 4 ≤ m
  constructor
  · intro h
    rw [le_div_iff₀ hden] at h
    norm_num at h
    exact_mod_cast (show (4 : ℝ) ≤ m by nlinarith)
  · intro hm4
    have hm4R : (4 : ℝ) ≤ m := by exact_mod_cast hm4
    rw [le_div_iff₀ hden]
    norm_num
    nlinarith

theorem threeCore_lt_two_thirds {m : ℕ} (hm : 1 ≤ m) :
    NField.Golden.alignmentFormulaReal 3 m < (2 : ℝ) / 3 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  unfold NField.Golden.alignmentFormulaReal
  change ((2 : ℝ) * m - 1) / ((3 : ℝ) * m - 1) < (2 : ℝ) / 3
  rw [div_lt_iff₀ hden]
  norm_num
  nlinarith

theorem threeCore_eq_seven_elevenths_iff {m : ℕ} (hm : 1 ≤ m) :
    NField.Golden.alignmentFormulaReal 3 m = (7 : ℝ) / 11 ↔ m = 4 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  unfold NField.Golden.alignmentFormulaReal
  change ((2 : ℝ) * m - 1) / ((3 : ℝ) * m - 1) = (7 : ℝ) / 11 ↔ m = 4
  constructor
  · intro h
    rw [div_eq_iff hden.ne'] at h
    norm_num at h
    exact_mod_cast (show (m : ℝ) = 4 by nlinarith)
  · rintro rfl
    norm_num

theorem threeCore_eq_three_fifths_iff {m : ℕ} (hm : 1 ≤ m) :
    NField.Golden.alignmentFormulaReal 3 m = (3 : ℝ) / 5 ↔ m = 2 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (3 : ℝ) * m - 1 := by nlinarith
  unfold NField.Golden.alignmentFormulaReal
  change ((2 : ℝ) * m - 1) / ((3 : ℝ) * m - 1) = (3 : ℝ) / 5 ↔ m = 2
  constructor
  · intro h
    rw [div_eq_iff hden.ne'] at h
    norm_num at h
    exact_mod_cast (show (m : ℝ) = 2 by nlinarith)
  · rintro rfl
    norm_num

theorem threeCore_one :
    NField.Golden.alignmentFormulaReal 3 1 = (1 : ℝ) / 2 := by
  norm_num [NField.Golden.alignmentFormulaReal]

theorem threeCore_two :
    NField.Golden.alignmentFormulaReal 3 2 = (3 : ℝ) / 5 := by
  norm_num [NField.Golden.alignmentFormulaReal]

theorem three_fifths_lt_goldenReciprocal :
    (3 : ℝ) / 5 < NField.Golden.goldenReciprocal := by
  rw [NField.Golden.goldenReciprocal]
  nlinarith [NField.Golden.sqrt_five_sq, Real.sqrt_nonneg 5]

theorem goldenReciprocal_lt_seven_elevenths :
    NField.Golden.goldenReciprocal < (7 : ℝ) / 11 := by
  rw [NField.Golden.goldenReciprocal]
  nlinarith [NField.Golden.sqrt_five_sq, Real.sqrt_nonneg 5]

theorem threeCore_golden_threshold_supported {b m : ℕ} (hm : 1 ≤ m)
    (hsupported : NField.Alignment.Supported b m) (h3b : ¬3 ∣ b) :
    NField.Golden.goldenReciprocal ≤ NField.Golden.alignmentFormulaReal 3 m ↔
      4 ≤ m := by
  constructor
  · intro hgolden
    have hm3 := (NField.Golden.prime_three_golden_threshold hm).mp hgolden
    have hmne : m ≠ 3 := by
      intro hm3eq
      apply three_not_dvd_supported h3b hsupported
      simp [hm3eq]
    omega
  · intro hm4
    exact (NField.Golden.prime_three_golden_threshold hm).mpr (by omega)

noncomputable def canonicalRoughAlignmentReal (b t m u L : ℕ) : ℝ :=
  if t = 1 then 1 else synchronizedCompositeAlignmentReal b t m u L

/-- The literal synchronized alignment from the manuscript.  The rough-one
case is terminating and is assigned alignment one. -/
noncomputable def clearedAlignmentReal (b t m D L : ℕ) : ℝ :=
  if t = 1 then 1 else
    (clearedFieldMatchTotal b t m D L : ℝ) /
      (((t * m - 1) * L : ℕ) : ℝ)

theorem clearedAlignmentReal_eq_canonicalRoughAlignmentReal
    {b t m D L : ℕ} (ht : 0 < t) (hm : 1 ≤ m) (hD : m ∣ b ^ D) :
    clearedAlignmentReal b t m D L = canonicalRoughAlignmentReal b t m
      (NField.Alignment.clearingCofactor b m D) L := by
  unfold clearedAlignmentReal canonicalRoughAlignmentReal
  split
  · rfl
  · rw [synchronizedCompositeAlignmentReal,
      clearedFieldMatchTotal_eq_periodicFieldMatchTotal ht hm hD]

/-- The literal manuscript alignment is independent of every later clearing
depth when the comparison length is a full rough-part period. -/
theorem clearedAlignmentReal_independent_of_later_clearing_depth
    {b t m D q L : ℕ} (ht : 0 < t) (hm : 1 ≤ m)
    (hD : m ∣ b ^ D) (hperiod : b ^ L % t = 1 % t) :
    clearedAlignmentReal b t m (D + q) L =
      clearedAlignmentReal b t m D L := by
  have hDq : m ∣ b ^ (D + q) := by
    rcases hD with ⟨c, hc⟩
    refine ⟨c * b ^ q, ?_⟩
    rw [pow_add, hc]
    ring
  rw [clearedAlignmentReal_eq_canonicalRoughAlignmentReal ht hm hDq,
    clearedAlignmentReal_eq_canonicalRoughAlignmentReal ht hm hD]
  unfold canonicalRoughAlignmentReal
  by_cases ht1 : t = 1
  · simp [ht1]
  · rw [if_neg ht1, if_neg ht1]
    exact synchronizedCompositeAlignmentReal_independent_of_later_clearing_depth
      hD hperiod

theorem canonicalRoughAlignmentReal_eq_one_of_rough_one {b m u L : ℕ} :
    canonicalRoughAlignmentReal b 1 m u L = 1 := by
  simp [canonicalRoughAlignmentReal]

theorem canonicalRoughAlignmentReal_eq_threeCore {b m u L : ℕ}
    (hb : 2 ≤ b) (h3b : ¬3 ∣ b) (htu : Nat.Coprime 3 u)
    (hm : 1 ≤ m) (hL : 0 < L) :
    canonicalRoughAlignmentReal b 3 m u L =
      NField.Golden.alignmentFormulaReal 3 m := by
  rw [canonicalRoughAlignmentReal, if_neg (by norm_num)]
  exact synchronizedCompositeAlignmentReal_eq_digitPartitioningFormula
    Nat.prime_three h3b
      (NField.Alignment.digitPartitioning_of_le (by norm_num) h3b (by omega))
      htu hm hL

theorem canonicalRoughAlignmentReal_lt_three_fifths_of_other_rough
    {b t m u L : ℕ} (hb : 2 ≤ b) (hbeven : Even b) (ht : 0 < t)
    (ht1 : t ≠ 1) (ht3 : t ≠ 3) (hm : 1 ≤ m) (hL : 0 < L)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) :
    canonicalRoughAlignmentReal b t m u L < (3 : ℝ) / 5 := by
  rw [canonicalRoughAlignmentReal, if_neg ht1]
  have hbpos : 0 < b := by omega
  have hfinite := synchronizedCompositeAlignmentReal_le_finite_bound
    hbpos (by omega) hm hL hbt htu hbeven
  have hstrict := finiteComplementBoundReal_lt_roughCeiling
    (t := t) (m := m) (by omega) hm
  have hrough := roughCeilingReal_le_three_fifths
    (roughPart_ge_five ht hbt hbeven ht1 ht3)
  exact lt_of_le_of_lt hfinite (lt_of_lt_of_le hstrict hrough)

theorem canonicalRoughAlignmentReal_threeCore_range {b m u L : ℕ}
    (hb : 2 ≤ b) (h3b : ¬3 ∣ b) (htu : Nat.Coprime 3 u)
    (hm : 1 ≤ m) (hL : 0 < L) (hm4 : 4 ≤ m) :
    (7 : ℝ) / 11 ≤ canonicalRoughAlignmentReal b 3 m u L ∧
      canonicalRoughAlignmentReal b 3 m u L < (2 : ℝ) / 3 := by
  rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu hm hL]
  exact ⟨(threeCore_ge_seven_elevenths_iff hm).mpr hm4,
    threeCore_lt_two_thirds hm⟩

theorem canonicalRoughAlignmentReal_gap {b t m u L : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (ht : 0 < t) (hm : 1 ≤ m) (hL : 0 < L)
    (hsupported : NField.Alignment.Supported b m)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) :
    ¬((3 : ℝ) / 5 < canonicalRoughAlignmentReal b t m u L ∧
      canonicalRoughAlignmentReal b t m u L < (7 : ℝ) / 11) := by
  by_cases ht1 : t = 1
  · subst t
    rw [canonicalRoughAlignmentReal_eq_one_of_rough_one]
    norm_num
  by_cases ht3 : t = 3
  · subst t
    rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu hm hL]
    by_cases hm4 : 4 ≤ m
    · intro hgap
      have hlower := (threeCore_ge_seven_elevenths_iff hm).mpr hm4
      linarith
    · have hmne3 : m ≠ 3 := by
        intro hm3
        apply three_not_dvd_supported h3b hsupported
        simp [hm3]
      have hmCases : m = 1 ∨ m = 2 := by omega
      rcases hmCases with rfl | rfl
      · rw [threeCore_one]
        norm_num
      · rw [threeCore_two]
        norm_num
  · have hlow := canonicalRoughAlignmentReal_lt_three_fifths_of_other_rough
      hb hbeven ht ht1 ht3 hm hL hbt htu
    intro hgap
    linarith

theorem canonicalRoughAlignmentReal_golden_iff {b t m u L : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (ht : 0 < t) (hm : 1 ≤ m) (hL : 0 < L)
    (hsupported : NField.Alignment.Supported b m)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) :
    NField.Golden.goldenReciprocal ≤ canonicalRoughAlignmentReal b t m u L ↔
      t = 1 ∨ (t = 3 ∧ 4 ≤ m) := by
  constructor
  · intro hgolden
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    by_cases ht3 : t = 3
    · right
      refine ⟨ht3, ?_⟩
      subst t
      rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu hm hL] at hgolden
      exact (threeCore_golden_threshold_supported hm hsupported h3b).mp hgolden
    · have hbelow := canonicalRoughAlignmentReal_lt_three_fifths_of_other_rough
        hb hbeven ht ht1 ht3 hm hL hbt htu
      linarith [three_fifths_lt_goldenReciprocal]
  · rintro (ht1 | ⟨ht3, hm4⟩)
    · subst t
      rw [canonicalRoughAlignmentReal_eq_one_of_rough_one]
      linarith [goldenReciprocal_lt_seven_elevenths]
    · subst t
      rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu hm hL]
      exact (threeCore_golden_threshold_supported hm hsupported h3b).mpr hm4

theorem canonicalRoughAlignmentReal_eq_three_fifths_iff {b t m u L : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (ht : 0 < t) (hm : 1 ≤ m) (hL : 0 < L)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) :
    canonicalRoughAlignmentReal b t m u L = (3 : ℝ) / 5 ↔
      t = 3 ∧ m = 2 := by
  constructor
  · intro heq
    by_cases ht1 : t = 1
    · subst t
      rw [canonicalRoughAlignmentReal_eq_one_of_rough_one] at heq
      norm_num at heq
    by_cases ht3 : t = 3
    · refine ⟨ht3, ?_⟩
      subst t
      rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu hm hL] at heq
      exact (threeCore_eq_three_fifths_iff hm).mp heq
    · have hbelow := canonicalRoughAlignmentReal_lt_three_fifths_of_other_rough
        hb hbeven ht ht1 ht3 hm hL hbt htu
      linarith
  · rintro ⟨rfl, rfl⟩
    rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu (by norm_num) hL,
      threeCore_two]

theorem canonicalRoughAlignmentReal_eq_seven_elevenths_iff {b t m u L : ℕ}
    (hb : 2 ≤ b) (hbeven : Even b) (h3b : ¬3 ∣ b)
    (ht : 0 < t) (hm : 1 ≤ m) (hL : 0 < L)
    (hbt : Nat.Coprime t b) (htu : Nat.Coprime t u) :
    canonicalRoughAlignmentReal b t m u L = (7 : ℝ) / 11 ↔
      t = 3 ∧ m = 4 := by
  constructor
  · intro heq
    by_cases ht1 : t = 1
    · subst t
      rw [canonicalRoughAlignmentReal_eq_one_of_rough_one] at heq
      norm_num at heq
    by_cases ht3 : t = 3
    · refine ⟨ht3, ?_⟩
      subst t
      rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu hm hL] at heq
      exact (threeCore_eq_seven_elevenths_iff hm).mp heq
    · have hbelow := canonicalRoughAlignmentReal_lt_three_fifths_of_other_rough
        hb hbeven ht ht1 ht3 hm hL hbt htu
      linarith
  · rintro ⟨rfl, rfl⟩
    rw [canonicalRoughAlignmentReal_eq_threeCore hb h3b htu (by norm_num) hL]
    exact (threeCore_eq_seven_elevenths_iff (by norm_num)).mpr rfl

end NField.Alignment.ThreeTier
