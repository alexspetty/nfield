/-
Author: Alexander S. Petty
-/

import Mathlib
import NField.Alignment.DigitPartitioning
import NField.Golden.Threshold

/-!
# Coset alignment and its sharp uniform bound

Reusable finite and asymptotic algebra for "The Alignment Limit for All
Primes".  The digit histogram and orbit-bin sum are concrete.  The alignment
formula is then expressed through the two integers used by the manuscript:
the orbit length `L` and its bin sum `T`.
-/

namespace NField.Alignment

open scoped BigOperators
open NField.CollisionDefinition

/-- The canonical nonzero residue representatives below `p`. -/
def nonzeroResidues (p : ℕ) : Finset ℕ :=
  (Finset.range p).erase 0

/-- The number of nonzero residues in digit bin `d`. -/
def digitBinPopulation (b p d : ℕ) : ℕ :=
  ((nonzeroResidues p).filter fun r => digitBin b p r = d).card

/-- The sum of squared digit-bin populations. -/
def digitBinSquareSum (b p : ℕ) : ℕ :=
  ∑ d ∈ Finset.range b, (digitBinPopulation b p d) ^ 2

/-- Every nonzero residue is contained in the population of its own digit bin. -/
theorem one_le_digitBinPopulation_of_residue {b p r : ℕ}
    (hr0 : 0 < r) (hrp : r < p) :
    1 ≤ digitBinPopulation b p (digitBin b p r) := by
  apply Finset.card_pos.mpr
  exact ⟨r, by simp [nonzeroResidues, hr0.ne', hrp]⟩

/-- The digit-bin populations partition all `p-1` nonzero residues. -/
theorem digitBinPopulation_sum {b p : ℕ} (hb : 0 < b) (hp : 0 < p) :
    ∑ d ∈ Finset.range b, digitBinPopulation b p d = p - 1 := by
  have hmaps : ∀ r ∈ nonzeroResidues p, digitBin b p r ∈ Finset.range b := by
    intro r hr
    have hrp : r < p := by
      have := (Finset.mem_erase.mp hr).2
      simpa [nonzeroResidues] using this
    exact Finset.mem_range.mpr (digitBin_lt_base hb hp hrp)
  unfold digitBinPopulation
  rw [← Finset.card_eq_sum_card_fiberwise hmaps]
  have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr hp
  simp [nonzeroResidues, Finset.card_erase_of_mem hzero]

/-- Digit partitioning forces every bin population to be zero or one. -/
theorem digitBinPopulation_le_one_of_digitPartitioning {b p d : ℕ}
    (hdp : DigitPartitioning b p) : digitBinPopulation b p d ≤ 1 := by
  rw [digitBinPopulation, Finset.card_le_one_iff]
  intro r s hr hs
  have hr' := Finset.mem_filter.mp hr
  have hs' := Finset.mem_filter.mp hs
  have hrmem := Finset.mem_erase.mp hr'.1
  have hsmem := Finset.mem_erase.mp hs'.1
  exact hdp (Nat.pos_of_ne_zero hrmem.1) (Finset.mem_range.mp hrmem.2)
    (Nat.pos_of_ne_zero hsmem.1) (Finset.mem_range.mp hsmem.2)
    (hr'.2.trans hs'.2.symm)

/-- In the digit-partitioning case the global bin-square sum is exactly
`p-1`. -/
theorem digitBinSquareSum_eq_of_digitPartitioning {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) (hdp : DigitPartitioning b p) :
    digitBinSquareSum b p = p - 1 := by
  unfold digitBinSquareSum
  calc
    ∑ d ∈ Finset.range b, (digitBinPopulation b p d) ^ 2 =
        ∑ d ∈ Finset.range b, digitBinPopulation b p d := by
      apply Finset.sum_congr rfl
      intro d _
      have hle := digitBinPopulation_le_one_of_digitPartitioning
        (b := b) (p := p) (d := d) hdp
      nlinarith
    _ = p - 1 := digitBinPopulation_sum hb hp

/-- A length-`L` sequence of nonzero reference states. -/
structure ReferenceOrbit (p L : ℕ) where
  state : Fin L → ℕ
  state_pos : ∀ i, 0 < state i
  state_lt : ∀ i, state i < p

/-- The actual synchronized reference states `b^i u mod p`. -/
def powerReferenceOrbit {b p u L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hu : Nat.Coprime p u) : ReferenceOrbit p L where
  state i := (b ^ (i : ℕ) * u) % p
  state_pos i := by
    have hcop : Nat.Coprime p (b ^ (i : ℕ) * u) :=
      (prime_coprime_base_pow hp hpb).mul_right hu
    have hnotdvd : ¬p ∣ b ^ (i : ℕ) * u := hp.coprime_iff_not_dvd.mp hcop
    exact Nat.pos_of_ne_zero fun hz =>
      hnotdvd ((Nat.dvd_iff_mod_eq_zero).2 hz)
  state_lt i := Nat.mod_lt _ hp.pos

/-- The manuscript's orbit-bin sum `T(C)`. -/
def orbitBinSum (b p L : ℕ) (orbit : ReferenceOrbit p L) : ℕ :=
  ∑ i : Fin L, digitBinPopulation b p (digitBin b p (orbit.state i))

/-- The bin sum along the synchronized power orbit. -/
def powerOrbitBinSum {b p u L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hu : Nat.Coprime p u) : ℕ :=
  orbitBinSum b p L (powerReferenceOrbit hp hpb hu)

/-- A sum of natural numbers, each at least one, is the cardinality only when
every summand is one. -/
theorem sum_eq_card_iff_eq_one {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (hone : ∀ x ∈ s, 1 ≤ f x) :
    ∑ x ∈ s, f x = s.card ↔ ∀ x ∈ s, f x = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haone : 1 ≤ f a := hone a (by simp)
      have htail : ∀ x ∈ s, 1 ≤ f x := by
        intro x hx
        exact hone x (by simp [hx])
      have hsum : s.card ≤ ∑ x ∈ s, f x := by
        calc
          s.card = ∑ x ∈ s, 1 := by simp
          _ ≤ ∑ x ∈ s, f x := Finset.sum_le_sum fun x hx => htail x hx
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      constructor
      · intro h
        have hfa : f a = 1 := by omega
        have hs : ∑ x ∈ s, f x = s.card := by omega
        have hall := (ih htail).mp hs
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact hfa
        · exact hall x hxs
      · intro hall
        have hfa : f a = 1 := hall a (by simp)
        have htailall : ∀ x ∈ s, f x = 1 := by
          intro x hx
          exact hall x (by simp [hx])
        rw [hfa, (ih htail).mpr htailall]
        omega

/-- Every orbit position contributes at least its reference state. -/
theorem orbitBinSum_ge_length {b p L : ℕ} (orbit : ReferenceOrbit p L) :
    L ≤ orbitBinSum b p L orbit := by
  classical
  calc
    L = ∑ _i : Fin L, 1 := by simp
    _ ≤ ∑ i : Fin L,
        digitBinPopulation b p (digitBin b p (orbit.state i)) :=
      Finset.sum_le_sum fun i _ =>
        one_le_digitBinPopulation_of_residue (orbit.state_pos i) (orbit.state_lt i)

/-- The correction vanishes exactly when every visited state lies in a
singleton digit bin. -/
theorem orbitBinSum_eq_length_iff {b p L : ℕ} (orbit : ReferenceOrbit p L) :
    orbitBinSum b p L orbit = L ↔
      ∀ i : Fin L,
        digitBinPopulation b p (digitBin b p (orbit.state i)) = 1 := by
  classical
  unfold orbitBinSum
  simpa using sum_eq_card_iff_eq_one Finset.univ
    (fun i : Fin L => digitBinPopulation b p (digitBin b p (orbit.state i)))
    (by
      intro i _
      exact one_le_digitBinPopulation_of_residue
        (orbit.state_pos i) (orbit.state_lt i))

/-- A uniform bound on every visited population bounds the orbit-bin sum. -/
theorem orbitBinSum_le_of_population_bound {b p L c : ℕ}
    (orbit : ReferenceOrbit p L)
    (hbound : ∀ i : Fin L,
      digitBinPopulation b p (digitBin b p (orbit.state i)) ≤ c) :
    orbitBinSum b p L orbit ≤ L * c := by
  classical
  unfold orbitBinSum
  calc
    ∑ i : Fin L, digitBinPopulation b p (digitBin b p (orbit.state i)) ≤
        ∑ _i : Fin L, c := Finset.sum_le_sum fun i _ => hbound i
    _ = L * c := by simp

/-- Integer total match score from `m-1` terminating fractions and the orbit
bin sum repeated across `m` residue blocks. -/
def cosetTotalMatchCount (m L T : ℕ) : ℕ :=
  (m - 1) * L + m * T

/-- Exact rational alignment obtained by normalizing the integer score. -/
noncomputable def cosetAlignment (p m L T : ℕ) : ℚ :=
  (cosetTotalMatchCount m L T : ℚ) / ((p * m - 1) * L : ℕ)

/-- The manuscript's displayed exact formula. -/
theorem cosetAlignment_eq {p m L T : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hL : 0 < L) :
    cosetAlignment p m L T =
      (((m - 1 : ℕ) : ℚ) + (m : ℚ) * T / L) / (p * m - 1 : ℕ) := by
  have hpm : 1 ≤ p * m := by nlinarith
  unfold cosetAlignment cosetTotalMatchCount
  push_cast [Nat.cast_sub hm, Nat.cast_sub hpm]
  field_simp

/-- Subtracting the collision-free baseline isolates the exact correction. -/
theorem cosetAlignment_correction {p m L T : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hL : 0 < L) :
    cosetAlignment p m L T -
        (((2 * m - 1 : ℕ) : ℚ) / (p * m - 1 : ℕ)) =
      (m : ℚ) * ((T : ℚ) - L) /
        ((L : ℚ) * (p * m - 1 : ℕ)) := by
  rw [cosetAlignment_eq hp hm hL]
  have hpm : 1 ≤ p * m := by nlinarith
  have h2m : 1 ≤ 2 * m := by omega
  push_cast [Nat.cast_sub hm, Nat.cast_sub hpm, Nat.cast_sub h2m]
  field_simp
  ring

/-- The correction is nonnegative because every orbit state belongs to a
nonempty bin. -/
theorem cosetAlignment_correction_nonneg {p m L T : ℕ}
    (hp : 2 ≤ p) (hm : 1 ≤ m) (hL : 0 < L) (hTL : L ≤ T) :
    0 ≤ cosetAlignment p m L T -
      (((2 * m - 1 : ℕ) : ℚ) / (p * m - 1 : ℕ)) := by
  rw [cosetAlignment_correction hp hm hL]
  have hcast : (L : ℚ) ≤ T := by exact_mod_cast hTL
  have hdiff : (0 : ℚ) ≤ (T : ℚ) - L := by linarith
  have hpm2 : 2 ≤ p * m := Nat.mul_le_mul hp hm
  have hden : (0 : ℚ) < (p * m - 1 : ℕ) := by
    exact_mod_cast (show 0 < p * m - 1 by omega)
  positivity

/-- The exact correction is zero precisely at `T=L`. -/
theorem cosetAlignment_correction_eq_zero_iff {p m L T : ℕ}
    (hp : 2 ≤ p) (hm : 1 ≤ m) (hL : 0 < L) :
    cosetAlignment p m L T =
        (((2 * m - 1 : ℕ) : ℚ) / (p * m - 1 : ℕ)) ↔ T = L := by
  have hmQ : (m : ℚ) ≠ 0 := by positivity
  have hLQ : (L : ℚ) ≠ 0 := by positivity
  have hpm2 : 2 ≤ p * m := Nat.mul_le_mul hp hm
  have hden : ((p * m - 1 : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p * m - 1 := by omega
    positivity
  constructor
  · intro heq
    have hzero :
        cosetAlignment p m L T -
          (((2 * m - 1 : ℕ) : ℚ) / (p * m - 1 : ℕ)) = 0 :=
      sub_eq_zero.mpr heq
    rw [cosetAlignment_correction hp hm hL] at hzero
    field_simp [hLQ, hden] at hzero
    have hzero' : (m : ℚ) * ((T : ℚ) - L) = 0 := by simpa using hzero
    have hdiff : (T : ℚ) - L = 0 :=
      (mul_eq_zero.mp hzero').resolve_left hmQ
    exact_mod_cast (sub_eq_zero.mp hdiff)
  · intro hTL
    subst T
    exact (sub_eq_zero.mp (by
      rw [cosetAlignment_correction hp hm hL]
      simp))

/-- Real form used for limits and inequalities. -/
noncomputable def cosetAlignmentReal (p m L T : ℕ) : ℝ :=
  ((m : ℝ) - 1 + (m : ℝ) * T / L) / ((p : ℝ) * m - 1)

/-- Casting the exact rational alignment gives the real formula. -/
theorem cosetAlignment_cast_eq_real {p m L T : ℕ} (hp : 2 ≤ p)
    (hm : 1 ≤ m) (hL : 0 < L) :
    ((cosetAlignment p m L T : ℚ) : ℝ) = cosetAlignmentReal p m L T := by
  rw [cosetAlignment_eq hp hm hL]
  have hpm : 1 ≤ p * m := by nlinarith
  push_cast [Nat.cast_sub hm, Nat.cast_sub hpm]
  rfl

/-- Real form of the manuscript's exact collision correction. -/
theorem cosetAlignmentReal_correction {p m L T : ℕ}
    (hp : 2 ≤ p) (hm : 1 ≤ m) (hL : 0 < L) :
    cosetAlignmentReal p m L T -
        (((2 * m - 1 : ℕ) : ℝ) / (p * m - 1 : ℕ)) =
      (m : ℝ) * ((T : ℝ) - L) /
        ((L : ℝ) * (p * m - 1 : ℕ)) := by
  have hpm : 1 ≤ p * m := by nlinarith
  have h2m : 1 ≤ 2 * m := by omega
  unfold cosetAlignmentReal
  push_cast [Nat.cast_sub hm, Nat.cast_sub hpm, Nat.cast_sub h2m]
  field_simp
  ring

/-- The real correction is zero exactly when the orbit-bin sum is the orbit
length. -/
theorem cosetAlignmentReal_eq_baseline_iff {p m L T : ℕ}
    (hp : 2 ≤ p) (hm : 1 ≤ m) (hL : 0 < L) :
    cosetAlignmentReal p m L T =
        (((2 * m - 1 : ℕ) : ℝ) / (p * m - 1 : ℕ)) ↔ T = L := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hLR : (L : ℝ) ≠ 0 := by positivity
  have hpm2 : 2 ≤ p * m := Nat.mul_le_mul hp hm
  have hpm : 0 < p * m - 1 := by omega
  have hden : (((p * m - 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  constructor
  · intro heq
    have hzero :
        cosetAlignmentReal p m L T -
          (((2 * m - 1 : ℕ) : ℝ) / (p * m - 1 : ℕ)) = 0 :=
      sub_eq_zero.mpr heq
    rw [cosetAlignmentReal_correction hp hm hL] at hzero
    field_simp [hLR, hden] at hzero
    have hzero' : (m : ℝ) * ((T : ℝ) - L) = 0 := by simpa using hzero
    have hdiff : (T : ℝ) - L = 0 :=
      (mul_eq_zero.mp hzero').resolve_left hmR
    exact_mod_cast (sub_eq_zero.mp hdiff)
  · intro hTL
    subst T
    apply sub_eq_zero.mp
    rw [cosetAlignmentReal_correction hp hm hL]
    simp

/-- Along a fixed orbit-bin sum, the alignment has the paper's subsequential
limit `(L+T)/(pL)`. -/
theorem cosetAlignmentReal_tendsto {p L T : ℕ} (hp : 0 < p) (hL : 0 < L) :
    Filter.Tendsto (fun m => cosetAlignmentReal p m L T) Filter.atTop
      (nhds (((L + T : ℕ) : ℝ) / ((p * L : ℕ) : ℝ))) := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hLR : (L : ℝ) ≠ 0 := by positivity
  have hbase := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) (-1) (-1) (1 + (T : ℝ) / L) (d := (p : ℝ)) hpR
  convert hbase using 1
  · funext m
    simp only [cosetAlignmentReal, sub_eq_add_neg]
    ring
  · push_cast
    field_simp

/-- A fixed orbit-bin sum has the same limit along every multiplicity
subsequence tending to infinity. -/
theorem cosetAlignmentReal_tendsto_along
    {ι : Type*} {l : Filter ι} {p L T : ℕ} {m : ι → ℕ}
    (hp : 0 < p) (hL : 0 < L) (hm : Filter.Tendsto m l Filter.atTop) :
    Filter.Tendsto (fun i => cosetAlignmentReal p (m i) L T) l
      (nhds (((L + T : ℕ) : ℝ) / ((p * L : ℕ) : ℝ))) :=
  (cosetAlignmentReal_tendsto hp hL).comp hm

/-- An equidistributed orbit-bin sum yields the closed form involving the
global square sum `S`. -/
theorem equidistributed_coset_limit {p L T S : ℕ} (hp : 1 < p) (hL : 0 < L)
    (hequidist : (T : ℚ) / L = (S : ℚ) / (p - 1 : ℕ)) :
    (((L + T : ℕ) : ℚ) / (p * L : ℕ)) =
      (((p - 1 : ℕ) : ℚ) + S) / ((p : ℚ) * (p - 1 : ℕ)) := by
  have hpone : 1 ≤ p := by omega
  have hpminus : (0 : ℚ) < (p - 1 : ℕ) := by
    exact_mod_cast (Nat.sub_pos_iff_lt.mpr hp)
  have hLR : (L : ℚ) ≠ 0 := by positivity
  have hpR : (p : ℚ) ≠ 0 := by positivity
  have hpcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.cast_sub hpone]
    norm_num
  have hpminus' : (p : ℚ) - 1 ≠ 0 := by
    rw [← hpcast]
    exact ne_of_gt hpminus
  rw [hpcast] at hequidist
  push_cast [Nat.cast_sub hpone]
  calc
    ((L : ℚ) + T) / ((p : ℚ) * L) =
        (1 + (T : ℚ) / L) / p := by
      field_simp
    _ = (1 + (S : ℚ) / (p - 1)) / p := by rw [hequidist]
    _ = ((p : ℚ) - 1 + S) / ((p : ℚ) * (p - 1)) := by
      field_simp [hpR, hpminus']

/-- If every selected coset has the same normalized orbit-bin sum, the
alignment converges to one global limit even when the selected coset varies
with the supported factor. -/
theorem equidistributed_cosetAlignmentReal_tendsto {p L S : ℕ}
    (hp : 1 < p) (_hL : 0 < L) (T : ℕ → ℕ)
    (hequidist : ∀ m, (T m : ℝ) / L = (S : ℝ) / (p - 1 : ℕ)) :
    Filter.Tendsto (fun m => cosetAlignmentReal p m L (T m)) Filter.atTop
      (nhds ((((p - 1 : ℕ) : ℝ) + S) /
        ((p : ℝ) * (p - 1 : ℕ)))) := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hpmNat : 0 < p - 1 := Nat.sub_pos_iff_lt.mpr hp
  have hpmR : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpmNat)
  have hbase := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) (-1) (-1) (1 + (S : ℝ) / (p - 1 : ℕ))
      (d := (p : ℝ)) hpR
  convert hbase using 1
  · funext m
    simp only [cosetAlignmentReal, sub_eq_add_neg]
    calc
      ((m : ℝ) + -1 + (m : ℝ) * (T m : ℝ) / (L : ℝ)) /
          ((p : ℝ) * (m : ℝ) + -1) =
          ((m : ℝ) + -1 + (m : ℝ) * ((T m : ℝ) / (L : ℝ))) /
            ((p : ℝ) * (m : ℝ) + -1) := by ring
      _ = ((m : ℝ) + -1 + (m : ℝ) * ((S : ℝ) / (p - 1 : ℕ))) /
          ((p : ℝ) * (m : ℝ) + -1) := by
        rw [hequidist m]
      _ = (-1 + (1 + (S : ℝ) / (p - 1 : ℕ)) * (m : ℝ)) /
          (-1 + (p : ℝ) * (m : ℝ)) := by
        ring
  · congr 1
    field_simp [hpR, hpmR]

/-- Filter-level form of the equidistributed-coset theorem.  It follows the
manuscript's quantifier: any supported multiplicity sequence tending to
infinity has the same limit, even if its selected coset changes. -/
theorem equidistributed_cosetAlignmentReal_tendsto_along
    {ι : Type*} {l : Filter ι} {p L S : ℕ} {m T : ι → ℕ}
    (hp : 1 < p) (_hL : 0 < L) (hm : Filter.Tendsto m l Filter.atTop)
    (hequidist : ∀ i, (T i : ℝ) / L = (S : ℝ) / (p - 1 : ℕ)) :
    Filter.Tendsto (fun i => cosetAlignmentReal p (m i) L (T i)) l
      (nhds ((((p - 1 : ℕ) : ℝ) + S) /
        ((p : ℝ) * (p - 1 : ℕ)))) := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hpmNat : 0 < p - 1 := Nat.sub_pos_iff_lt.mpr hp
  have hpmR : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpmNat)
  have hbase := (tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) (-1) (-1) (1 + (S : ℝ) / (p - 1 : ℕ))
      (d := (p : ℝ)) hpR).comp hm
  convert hbase using 1
  · funext i
    simp only [Function.comp_apply, cosetAlignmentReal, sub_eq_add_neg]
    calc
      ((m i : ℝ) + -1 + (m i : ℝ) * (T i : ℝ) / (L : ℝ)) /
          ((p : ℝ) * (m i : ℝ) + -1) =
          ((m i : ℝ) + -1 + (m i : ℝ) * ((T i : ℝ) / (L : ℝ))) /
            ((p : ℝ) * (m i : ℝ) + -1) := by ring
      _ = ((m i : ℝ) + -1 + (m i : ℝ) * ((S : ℝ) / (p - 1 : ℕ))) /
          ((p : ℝ) * (m i : ℝ) + -1) := by rw [hequidist i]
      _ = (-1 + (1 + (S : ℝ) / (p - 1 : ℕ)) * (m i : ℝ)) /
          (-1 + (p : ℝ) * (m i : ℝ)) := by ring
  · congr 1
    field_simp [hpR, hpmR]

/-- A digit-partitioning orbit has `T=L` and recovers the earlier exact
formula. -/
theorem singleton_orbit_alignment {p m L : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hL : 0 < L) :
    cosetAlignment p m L L =
      (((2 * m - 1 : ℕ) : ℚ) / (p * m - 1 : ℕ)) := by
  exact (cosetAlignment_correction_eq_zero_iff hp hm hL).2 rfl

/-- Exact alignment attached directly to a concrete reference orbit. -/
noncomputable def referenceOrbitAlignment
    (p m L : ℕ) {b : ℕ} (orbit : ReferenceOrbit p L) : ℚ :=
  cosetAlignment p m L (orbitBinSum b p L orbit)

/-- The exact finite formula for a concrete reference orbit. -/
theorem referenceOrbitAlignment_eq {b p m L : ℕ}
    (orbit : ReferenceOrbit p L) (hp : 2 ≤ p) (hm : 1 ≤ m) (hL : 0 < L) :
    referenceOrbitAlignment (b := b) p m L orbit =
      (((m - 1 : ℕ) : ℚ) +
        (m : ℚ) * orbitBinSum b p L orbit / L) /
        (p * m - 1 : ℕ) := by
  exact cosetAlignment_eq hp hm hL

/-- The concrete orbit correction is nonnegative. -/
theorem referenceOrbitAlignment_correction_nonneg {b p m L : ℕ}
    (orbit : ReferenceOrbit p L) (hp : 2 ≤ p) (hm : 1 ≤ m) (hL : 0 < L) :
    0 ≤ referenceOrbitAlignment (b := b) p m L orbit -
      (((2 * m - 1 : ℕ) : ℚ) / (p * m - 1 : ℕ)) := by
  exact cosetAlignment_correction_nonneg hp hm hL (orbitBinSum_ge_length orbit)

/-- The concrete orbit correction vanishes exactly on singleton visited bins. -/
theorem referenceOrbitAlignment_eq_baseline_iff {b p m L : ℕ}
    (orbit : ReferenceOrbit p L) (hp : 2 ≤ p) (hm : 1 ≤ m) (hL : 0 < L) :
    referenceOrbitAlignment (b := b) p m L orbit =
        (((2 * m - 1 : ℕ) : ℚ) / (p * m - 1 : ℕ)) ↔
      ∀ i : Fin L,
        digitBinPopulation b p (digitBin b p (orbit.state i)) = 1 := by
  rw [referenceOrbitAlignment,
    cosetAlignment_correction_eq_zero_iff hp hm hL,
    orbitBinSum_eq_length_iff]

/-- The real exact formula is strictly below `3/5` whenever every visited bin
has size at most `c` and `2c ≤ p-1`. -/
theorem cosetAlignmentReal_lt_three_fifths {p m L T c : ℕ}
    (hp : 5 ≤ p) (hm : 1 ≤ m) (hL : 0 < L)
    (hT : T ≤ L * c) (hc : 2 * c ≤ p - 1) :
    cosetAlignmentReal p m L T < (3 : ℝ) / 5 := by
  have hden : 0 < (p : ℝ) * m - 1 := by
    have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hLR : (0 : ℝ) < L := by positivity
  have hTR : (T : ℝ) / L ≤ c := by
    apply (div_le_iff₀ hLR).2
    exact_mod_cast (show T ≤ c * L by simpa [Nat.mul_comm] using hT)
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hmul : (m : ℝ) * ((T : ℝ) / L) ≤ (m : ℝ) * c :=
    mul_le_mul_of_nonneg_left hTR hmR
  have hnum :
      (m : ℝ) - 1 + (m : ℝ) * T / L ≤
        (m : ℝ) - 1 + (m : ℝ) * c := by
    calc
      (m : ℝ) - 1 + (m : ℝ) * T / L =
          (m : ℝ) - 1 + (m : ℝ) * ((T : ℝ) / L) := by ring
      _ ≤ (m : ℝ) - 1 + (m : ℝ) * c := by
        convert add_le_add_left hmul ((m : ℝ) - 1) using 1 <;> ring
  have hcR : (2 : ℝ) * c ≤ (p : ℝ) - 1 := by
    have hcast : ((2 * c : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hc
    push_cast [Nat.cast_sub (show 1 ≤ p by omega)] at hcast
    simpa using hcast
  have hscaled : (2 : ℝ) * c * m ≤ ((p : ℝ) - 1) * m :=
    mul_le_mul_of_nonneg_right hcR hmR
  rw [cosetAlignmentReal, div_lt_iff₀ hden]
  calc
    (m : ℝ) - 1 + (m : ℝ) * T / L
        ≤ (m : ℝ) - 1 + (m : ℝ) * c := hnum
    _ < ((3 : ℝ) / 5) * ((p : ℝ) * m - 1) := by
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
      have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith

/-- The rational threshold lies strictly below the reciprocal golden ratio. -/
theorem three_fifths_lt_goldenReciprocal :
    (3 : ℝ) / 5 < NField.Golden.goldenReciprocal := by
  rw [NField.Golden.goldenReciprocal]
  nlinarith [NField.Golden.sqrt_five_sq, Real.sqrt_nonneg 5]

/-- Therefore the uniform `3/5` estimate implies the golden estimate. -/
theorem cosetAlignmentReal_lt_goldenReciprocal {p m L T c : ℕ}
    (hp : 5 ≤ p) (hm : 1 ≤ m) (hL : 0 < L)
    (hT : T ≤ L * c) (hc : 2 * c ≤ p - 1) :
    cosetAlignmentReal p m L T < NField.Golden.goldenReciprocal :=
  lt_trans (cosetAlignmentReal_lt_three_fifths hp hm hL hT hc)
    three_fifths_lt_goldenReciprocal

/-- The concrete reference-orbit form of the uniform `3/5` theorem. -/
theorem referenceOrbitAlignmentReal_lt_three_fifths {b p m L c : ℕ}
    (orbit : ReferenceOrbit p L) (hp : 5 ≤ p) (hm : 1 ≤ m) (hL : 0 < L)
    (hbound : ∀ i : Fin L,
      digitBinPopulation b p (digitBin b p (orbit.state i)) ≤ c)
    (hc : 2 * c ≤ p - 1) :
    cosetAlignmentReal p m L (orbitBinSum b p L orbit) < (3 : ℝ) / 5 := by
  exact cosetAlignmentReal_lt_three_fifths hp hm hL
    (orbitBinSum_le_of_population_bound orbit hbound) hc

/-- The base-two, prime-five family has the exact sharpness formula. -/
theorem sharpness_family_eq {m L : ℕ} (hL : 0 < L) :
    cosetAlignmentReal 5 m L (2 * L) =
      ((3 : ℝ) * m - 1) / ((5 : ℝ) * m - 1) := by
  unfold cosetAlignmentReal
  have hLR : (L : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The sharpness family tends to `3/5`. -/
theorem sharpness_family_tendsto {L : ℕ} (hL : 0 < L) :
    Filter.Tendsto (fun m => cosetAlignmentReal 5 m L (2 * L)) Filter.atTop
      (nhds ((3 : ℝ) / 5)) := by
  convert cosetAlignmentReal_tendsto (p := 5) (L := L) (T := 2 * L)
    (by norm_num) hL using 1
  push_cast
  field_simp
  norm_num

end NField.Alignment
