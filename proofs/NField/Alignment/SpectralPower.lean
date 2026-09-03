/-
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.ZMod
import NField.Alignment.SpectralStructure

/-!
# Additive spectral power of the digit function

Reusable formal core for the Lean companion to "The Spectral Power of the
Digit Function".  The definitions use the standard unnormalized Fourier
transform on `ZMod N`.  A value of `none` marks a residue omitted from the
digit partition.  For the manuscript's prime digit word, precisely residue
zero is omitted.
-/

namespace NField.Alignment.SpectralPower

open scoped BigOperators
open NField.Alignment
open NField.CollisionDefinition
open ZMod

variable {N κ : ℕ}

/-! ## Bin coordinates and their additive Fourier power -/

/-- The residues carrying one declared label. -/
def binSet [NeZero N] (word : ZMod N → Option (Fin κ)) (d : Fin κ) :
    Finset (ZMod N) :=
  Finset.univ.filter fun r => word r = some d

/-- The unnormalized additive Fourier coefficient of one bin indicator. -/
noncomputable def setFourier [NeZero N]
    (S : Finset (ZMod N)) (k : ZMod N) : ℂ :=
  ∑ r ∈ S, stdAddChar (-(r * k))

/-- The unnormalized additive Fourier coefficient of one bin indicator. -/
noncomputable def binFourier [NeZero N]
    (word : ZMod N → Option (Fin κ)) (d : Fin κ) (k : ZMod N) : ℂ :=
  setFourier (binSet word d) k

/-- Spectral power obtained by summing the squared magnitudes of all bin
coordinates.  It is kept in `ℂ` so it can be compared directly with the
finite Fourier transform; every summand is real and nonnegative. -/
noncomputable def spectralPower [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k : ZMod N) : ℂ :=
  ∑ d, starRingEnd ℂ (binFourier word d k) * binFourier word d k

/-- Relabel the coordinate attached to each active residue. -/
def relabelWord {digits : ℕ} (e : Fin κ ≃ Fin digits)
    (word : ZMod N → Option (Fin κ)) : ZMod N → Option (Fin digits) :=
  fun r => (word r).map e

theorem binSet_relabelWord {digits : ℕ} [NeZero N]
    (e : Fin κ ≃ Fin digits) (word : ZMod N → Option (Fin κ)) (d : Fin digits) :
    binSet (relabelWord e word) d = binSet word (e.symm d) := by
  classical
  ext r
  simp [binSet, relabelWord]
  constructor
  · rintro ⟨a, hword, hea⟩
    have ha : a = e.symm d := by
      apply e.injective
      simpa using hea
    simpa [ha] using hword
  · intro hword
    exact ⟨e.symm d, hword, e.apply_symm_apply d⟩

theorem binFourier_relabelWord {digits : ℕ} [NeZero N]
    (e : Fin κ ≃ Fin digits) (word : ZMod N → Option (Fin κ))
    (d : Fin digits) (k : ZMod N) :
    binFourier (relabelWord e word) d k = binFourier word (e.symm d) k := by
  rw [binFourier, binFourier, binSet_relabelWord]

/-- Spectral power is invariant under any bijective relabeling of the digit
coordinates. -/
theorem spectralPower_relabelWord {digits : ℕ} [NeZero N]
    (e : Fin κ ≃ Fin digits) (word : ZMod N → Option (Fin κ)) (k : ZMod N) :
    spectralPower (relabelWord e word) k = spectralPower word k := by
  classical
  unfold spectralPower
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro d _
  rw [binFourier_relabelWord]

/-- The total ordered same-bin mass. -/
def binSquareMass [NeZero N]
    (word : ZMod N → Option (Fin κ)) : ℕ :=
  ∑ d, (binSet word d).card ^ 2

theorem binFourier_zero [NeZero N]
    (word : ZMod N → Option (Fin κ)) (d : Fin κ) :
    binFourier word d 0 = (binSet word d).card := by
  simp [binFourier, setFourier]

/-- The zero frequency is exactly the ordered same-bin collision mass. -/
theorem spectralPower_zero [NeZero N]
    (word : ZMod N → Option (Fin κ)) :
    spectralPower word 0 = (binSquareMass word : ℂ) := by
  simp [spectralPower, binSquareMass, binFourier_zero, pow_two]

theorem setFourier_power_eq_card_of_card_le_one [NeZero N]
    (S : Finset (ZMod N)) (k : ZMod N) (hcard : S.card ≤ 1) :
    starRingEnd ℂ (setFourier S k) * setFourier S k = (S.card : ℂ) := by
  classical
  have hcases : S.card = 0 ∨ S.card = 1 := by omega
  rcases hcases with hzero | hone
  · rw [Finset.card_eq_zero.mp hzero]
    simp [setFourier]
  · obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp hone
    simp only [setFourier, Finset.sum_singleton, Finset.card_singleton,
      Nat.cast_one]
    rw [show starRingEnd ℂ (stdAddChar (-(r * k))) =
        stdAddChar (r * k) by
      simpa only [starRingEnd_apply, neg_neg] using
        (AddChar.map_neg_eq_conj (stdAddChar (N := N)) (-(r * k))).symm]
    rw [← AddChar.map_add_eq_mul]
    simp

/-- Cyclic translation of a residue set. -/
def translateSet [NeZero N] (a : ZMod N) (S : Finset (ZMod N)) :
    Finset (ZMod N) :=
  S.image fun r => a + r

/-- Translating a set changes its Fourier coefficient only by a unit phase. -/
theorem setFourier_translate [NeZero N]
    (S : Finset (ZMod N)) (a k : ZMod N) :
    setFourier (translateSet a S) k =
      stdAddChar (-(a * k)) * setFourier S k := by
  classical
  unfold setFourier translateSet
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [show -((a + r) * k) = -(a * k) + -(r * k) by ring,
      AddChar.map_add_eq_mul]
  · intro r _ s _ hrs
    exact add_left_cancel hrs

/-- Consequently, squared Fourier magnitude is translation-invariant. -/
theorem setFourier_power_translate [NeZero N]
    (S : Finset (ZMod N)) (a k : ZMod N) :
    starRingEnd ℂ (setFourier (translateSet a S) k) *
        setFourier (translateSet a S) k =
      starRingEnd ℂ (setFourier S k) * setFourier S k := by
  rw [setFourier_translate]
  have hphase : starRingEnd ℂ (stdAddChar (-(a * k))) =
      stdAddChar (a * k) := by
    simpa only [starRingEnd_apply, neg_neg] using
      (AddChar.map_neg_eq_conj (stdAddChar (N := N)) (-(a * k))).symm
  rw [map_mul, hphase]
  have hunit : stdAddChar (a * k) * stdAddChar (-(a * k)) = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  calc
    stdAddChar (a * k) * starRingEnd ℂ (setFourier S k) *
        (stdAddChar (-(a * k)) * setFourier S k) =
      (stdAddChar (a * k) * stdAddChar (-(a * k))) *
        (starRingEnd ℂ (setFourier S k) * setFourier S k) := by ring
    _ = starRingEnd ℂ (setFourier S k) * setFourier S k := by
      rw [hunit, one_mul]

/-! ## Exact interval kernel -/

/-- Fourier coefficient of the initial interval with `n` consecutive
positions.  Translating an interval only changes this coefficient by a unit
phase, so its squared magnitude is the kernel used below. -/
noncomputable def intervalFourier (N n : ℕ) [NeZero N]
    (k : ZMod N) : ℂ :=
  ∑ j ∈ Finset.range n,
    stdAddChar (-((j : ZMod N) * k))

noncomputable def intervalPower (N n : ℕ) [NeZero N]
    (k : ZMod N) : ℂ :=
  starRingEnd ℂ (intervalFourier N n k) * intervalFourier N n k

/-- The initial cyclic interval represented by `0, ..., n-1`. -/
def initialIntervalSet (N n : ℕ) [NeZero N] : Finset (ZMod N) :=
  (Finset.range n).image fun j : ℕ => (j : ZMod N)

theorem setFourier_initialInterval (N n : ℕ) [NeZero N]
    (hn : n ≤ N) (k : ZMod N) :
    setFourier (initialIntervalSet N n) k = intervalFourier N n k := by
  classical
  unfold setFourier initialIntervalSet intervalFourier
  rw [Finset.sum_image]
  intro i hi j hj hij
  have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) hn
  have hjN : j < N := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
  have hval := congrArg ZMod.val hij
  simpa [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using hval

/-- A cyclic interval is a translate of the initial interval. -/
def IsCyclicInterval [NeZero N] (S : Finset (ZMod N)) (n : ℕ) : Prop :=
  ∃ a : ZMod N, S = translateSet a (initialIntervalSet N n)

theorem setFourier_power_eq_intervalPower_of_isCyclicInterval [NeZero N]
    {S : Finset (ZMod N)} {n : ℕ} (hn : n ≤ N)
    (hinterval : IsCyclicInterval S n) (k : ZMod N) :
    starRingEnd ℂ (setFourier S k) * setFourier S k =
      intervalPower N n k := by
  rcases hinterval with ⟨a, rfl⟩
  rw [setFourier_power_translate, intervalPower,
    setFourier_initialInterval N n hn]

theorem intervalFourier_eq_geom (N n : ℕ) [NeZero N]
    (k : ZMod N) :
    intervalFourier N n k =
      ∑ j ∈ Finset.range n, (stdAddChar (-k)) ^ j := by
  apply Finset.sum_congr rfl
  intro j _
  rw [← AddChar.map_nsmul_eq_pow]
  congr 2
  simp [nsmul_eq_mul]

/-- Exact geometric-quotient form of the nonzero-frequency interval
transform.  This is algebraically equivalent to the sine quotient printed in
the manuscript. -/
theorem intervalFourier_eq_geom_quotient (N n : ℕ) [NeZero N]
    {k : ZMod N} (hk : k ≠ 0) :
    intervalFourier N n k =
      ((stdAddChar (-k)) ^ n - 1) / (stdAddChar (-k) - 1) := by
  rw [intervalFourier_eq_geom]
  apply geom_sum_eq
  intro hchar
  have hzero : -k = 0 := injective_stdAddChar (by simpa using hchar)
  exact hk (by simpa using hzero)

theorem intervalPower_zero (N n : ℕ) [NeZero N] :
    intervalPower N n 0 = (n ^ 2 : ℕ) := by
  simp [intervalPower, intervalFourier, pow_two]

/-- If `κ` populations have the two lengths `q` and `q+1`, and their total
is `κ*q+ρ`, then exactly `ρ` have the larger length. -/
theorem two_length_count_certificate
    (n : Fin κ → ℕ) {q ρ : ℕ}
    (hlength : ∀ d, n d = q ∨ n d = q + 1)
    (htotal : ∑ d, n d = κ * q + ρ) :
    (Finset.univ.filter fun d : Fin κ => n d = q).card = κ - ρ ∧
      (Finset.univ.filter fun d : Fin κ => n d = q + 1).card = ρ := by
  classical
  let large := Finset.univ.filter fun d : Fin κ => n d = q + 1
  have hpoint (d : Fin κ) :
      n d = q + if d ∈ large then 1 else 0 := by
    rcases hlength d with hsmall | hlarge
    · have hd : d ∉ large := by simp [large, hsmall]
      simp [hsmall, hd]
    · have hd : d ∈ large := by simp [large, hlarge]
      simp [hlarge, hd]
  have hsum : ∑ d, n d = κ * q + large.card := by
    calc
      ∑ d, n d = ∑ d, (q + if d ∈ large then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d _
        exact hpoint d
      _ = (∑ _d : Fin κ, q) +
          ∑ d : Fin κ, if d ∈ large then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = κ * q + large.card := by
        simp [large]
  have hlarge : large.card = ρ := by omega
  have hsmallSet :
      Finset.univ.filter (fun d : Fin κ => n d = q) =
        Finset.univ \ large := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, large]
    constructor
    · intro hq hq1
      omega
    · intro hnot
      exact (hlength d).resolve_right hnot
  constructor
  · rw [hsmallSet, Finset.card_sdiff]
    simp [hlarge]
  · simpa [large] using hlarge

/-- Exact hypotheses used when the bins are intervals of two possible
lengths.  Separating this finite model makes the logical dependency of the
two-kernel formula explicit. -/
structure TwoLengthIntervalModel [NeZero N]
    (word : ZMod N → Option (Fin κ)) (q ρ : ℕ) : Prop where
  length_cases : ∀ d, (binSet word d).card = q ∨
    (binSet word d).card = q + 1
  small_count :
    (Finset.univ.filter fun d : Fin κ => (binSet word d).card = q).card =
      κ - ρ
  large_count :
    (Finset.univ.filter fun d : Fin κ =>
      (binSet word d).card = q + 1).card = ρ
  interval_power : ∀ d k,
    starRingEnd ℂ (setFourier (binSet word d) k) *
      setFourier (binSet word d) k =
        intervalPower N (binSet word d).card k

/-- The exact two-length spectral formula, stated with the finite character
kernel.  The geometric-quotient theorem above converts each nonzero-frequency
kernel into a closed form. -/
theorem spectralPower_eq_two_interval_kernels [NeZero N]
    (word : ZMod N → Option (Fin κ)) {q ρ : ℕ}
    (model : TwoLengthIntervalModel word q ρ) (k : ZMod N) :
    spectralPower word k =
      (κ - ρ : ℕ) * intervalPower N q k +
        (ρ : ℕ) * intervalPower N (q + 1) k := by
  classical
  have hterm (d : Fin κ) :
      starRingEnd ℂ (setFourier (binSet word d) k) *
          setFourier (binSet word d) k =
        if (binSet word d).card = q then intervalPower N q k
        else intervalPower N (q + 1) k := by
    rw [model.interval_power]
    by_cases hq : (binSet word d).card = q
    · simp [hq]
    · have hlarge := (model.length_cases d).resolve_left hq
      simp [hlarge]
  have hcomplement :
      Finset.univ.filter (fun d : Fin κ => (binSet word d).card ≠ q) =
        Finset.univ.filter (fun d : Fin κ =>
          (binSet word d).card = q + 1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hq
      exact (model.length_cases d).resolve_left hq
    · intro hlarge hq
      omega
  unfold spectralPower binFourier
  simp_rw [hterm]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hcomplement, model.small_count, model.large_count]

/-- The two-kernel formula with the bin counts derived rather than assumed. -/
theorem spectralPower_eq_two_interval_kernels_of_lengths [NeZero N]
    (word : ZMod N → Option (Fin κ)) {q ρ : ℕ}
    (hlength : ∀ d, (binSet word d).card = q ∨
      (binSet word d).card = q + 1)
    (htotal : ∑ d, (binSet word d).card = κ * q + ρ)
    (hinterval : ∀ d k,
      starRingEnd ℂ (setFourier (binSet word d) k) *
        setFourier (binSet word d) k =
          intervalPower N (binSet word d).card k)
    (k : ZMod N) :
    spectralPower word k =
      (κ - ρ : ℕ) * intervalPower N q k +
        (ρ : ℕ) * intervalPower N (q + 1) k := by
  have hcounts := two_length_count_certificate
    (fun d => (binSet word d).card) hlength htotal
  exact spectralPower_eq_two_interval_kernels word
    { length_cases := hlength
      small_count := hcounts.1
      large_count := hcounts.2
      interval_power := hinterval } k

/-- Reader-facing form of the two-kernel theorem from actual cyclic interval
data, rather than an already-computed Fourier power hypothesis. -/
theorem spectralPower_eq_two_interval_kernels_of_cyclicIntervals [NeZero N]
    (word : ZMod N → Option (Fin κ)) {q ρ : ℕ}
    (hlength : ∀ d, (binSet word d).card = q ∨
      (binSet word d).card = q + 1)
    (htotal : ∑ d, (binSet word d).card = κ * q + ρ)
    (hshort : ∀ d, (binSet word d).card ≤ N)
    (hinterval : ∀ d,
      IsCyclicInterval (binSet word d) (binSet word d).card)
    (k : ZMod N) :
    spectralPower word k =
      (κ - ρ : ℕ) * intervalPower N q k +
        (ρ : ℕ) * intervalPower N (q + 1) k := by
  apply spectralPower_eq_two_interval_kernels_of_lengths word
    hlength htotal
  · intro d frequency
    exact setFourier_power_eq_intervalPower_of_isCyclicInterval
      (hshort d) (hinterval d) frequency

/-- Singleton or empty bins give constant power equal to the active support
size. -/
theorem spectralPower_eq_of_bin_card_le_one [NeZero N]
    (word : ZMod N → Option (Fin κ))
    (hbins : ∀ d, (binSet word d).card ≤ 1) (k : ZMod N) :
    spectralPower word k = (∑ d, (binSet word d).card : ℕ) := by
  unfold spectralPower binFourier
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  exact setFourier_power_eq_card_of_card_le_one
    (binSet word d) k (hbins d)

/-- Constancy is stated intrinsically, without choosing the constant. -/
def SpectralFlat [NeZero N]
    (word : ZMod N → Option (Fin κ)) : Prop :=
  ∀ k l, spectralPower word k = spectralPower word l

/-- For finite natural populations, equality of the square sum and the mass
sum is equivalent to every population being zero or one. -/
theorem sum_sq_eq_sum_iff_le_one {ι : Type*} [Fintype ι]
    (n : ι → ℕ) :
    (∑ i, n i ^ 2) = ∑ i, n i ↔ ∀ i, n i ≤ 1 := by
  classical
  constructor
  · intro heq i
    by_contra hi
    have hstrict : n i < n i ^ 2 := by
      have : 2 ≤ n i := by omega
      nlinarith
    have hle : ∀ j ∈ (Finset.univ : Finset ι), n j ≤ n j ^ 2 := by
      intro j _
      by_cases hz : n j = 0
      · simp [hz]
      · have : 1 ≤ n j := Nat.one_le_iff_ne_zero.mpr hz
        nlinarith
    have hlt := Finset.sum_lt_sum hle
      ⟨i, Finset.mem_univ i, hstrict⟩
    omega
  · intro hle
    apply Finset.sum_congr rfl
    intro i _
    have := hle i
    nlinarith

/-! ## Additive overlap and the correlation transform -/

/-- Cyclic overlap of a finite set with its translate by `h`. -/
def setOverlap [NeZero N] (S : Finset (ZMod N)) (h : ZMod N) : ℕ :=
  (S.filter fun r => r + h ∈ S).card

/-- Additive same-label collision count. -/
def additiveCollision [NeZero N]
    (word : ZMod N → Option (Fin κ)) (h : ZMod N) : ℕ :=
  ∑ d, setOverlap (binSet word d) h

/-- Multiplicative same-label collision count.  This is the comparison object
obtained by replacing additive translation with multiplication by `g`. -/
def multiplicativeCollisionCount [NeZero N]
    (word : ZMod N → Option (Fin κ)) (g : ZMod N) : ℕ :=
  ∑ d, ((binSet word d).filter fun r => g * r ∈ binSet word d).card

/-- Indicator-sum form of the multiplicative collision count. -/
theorem multiplicativeCollisionCount_eq_indicator_sum [NeZero N]
    (word : ZMod N → Option (Fin κ)) (g : ZMod N) :
    multiplicativeCollisionCount word g =
      ∑ d : Fin κ, ∑ r : ZMod N,
        if word r = some d ∧ word (g * r) = some d then 1 else 0 := by
  classical
  unfold multiplicativeCollisionCount
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.card_filter]
  simp only [binSet, Finset.sum_filter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : word r = some d <;> simp [hr]

/-- The overlap at zero is the number of active residues. -/
theorem setOverlap_zero [NeZero N] (S : Finset (ZMod N)) :
    setOverlap S 0 = S.card := by
  simp [setOverlap]

theorem additiveCollision_zero [NeZero N]
    (word : ZMod N → Option (Fin κ)) :
    additiveCollision word 0 = ∑ d, (binSet word d).card := by
  simp [additiveCollision, setOverlap_zero]

/-- Distance of a cyclic shift from zero using its canonical representative. -/
def circularDistance (N : ℕ) [NeZero N] (h : ZMod N) : ℕ :=
  min h.val (N - h.val)

/-- The additional short-interval hypothesis needed for the triangular
overlap profile. -/
structure ShortTwoLengthIntervalModel [NeZero N]
    (word : ZMod N → Option (Fin κ)) (q ρ : ℕ) : Prop
    extends TwoLengthIntervalModel word q ρ where
  overlap_profile : ∀ d h,
    setOverlap (binSet word d) h =
      (binSet word d).card - circularDistance N h

/-- Exact sum of the two triangular profiles determined by the two bin
lengths. -/
theorem additiveCollision_eq_two_triangles [NeZero N]
    (word : ZMod N → Option (Fin κ)) {q ρ : ℕ}
    (model : ShortTwoLengthIntervalModel word q ρ) (h : ZMod N) :
    additiveCollision word h =
      (κ - ρ) * (q - circularDistance N h) +
        ρ * (q + 1 - circularDistance N h) := by
  classical
  have hterm (d : Fin κ) :
      setOverlap (binSet word d) h =
        if (binSet word d).card = q then q - circularDistance N h
        else q + 1 - circularDistance N h := by
    rw [model.overlap_profile]
    by_cases hq : (binSet word d).card = q
    · simp [hq]
    · have hlarge := (model.length_cases d).resolve_left hq
      simp [hlarge]
  have hcomplement :
      Finset.univ.filter (fun d : Fin κ => (binSet word d).card ≠ q) =
        Finset.univ.filter (fun d : Fin κ =>
          (binSet word d).card = q + 1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hq
      exact (model.length_cases d).resolve_left hq
    · intro hlarge hq
      omega
  unfold additiveCollision
  simp_rw [hterm]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hcomplement, model.small_count, model.large_count]
  norm_num

/-- The finite Fourier transform of a cyclic set overlap is the squared
magnitude of the set's Fourier coefficient. -/
theorem dft_setOverlap [NeZero N]
    (S : Finset (ZMod N)) (k : ZMod N) :
    𝓕 (fun h => (setOverlap S h : ℂ)) k =
      starRingEnd ℂ (setFourier S k) * setFourier S k := by
  classical
  have hoverlap (h : ZMod N) :
      (setOverlap S h : ℂ) =
        ∑ r ∈ S, if r + h ∈ S then (1 : ℂ) else 0 := by
    simp [setOverlap]
  have hinner (r : ZMod N) :
      (∑ h : ZMod N,
          stdAddChar (-(h * k)) *
            (if r + h ∈ S then (1 : ℂ) else 0)) =
        stdAddChar (r * k) * setFourier S k := by
    calc
      (∑ h : ZMod N,
          stdAddChar (-(h * k)) *
            (if r + h ∈ S then (1 : ℂ) else 0)) =
          ∑ s : ZMod N,
            stdAddChar (-((s - r) * k)) *
              (if s ∈ S then (1 : ℂ) else 0) := by
        apply Fintype.sum_equiv (Equiv.addLeft r)
        intro h
        change stdAddChar (-(h * k)) *
            (if r + h ∈ S then (1 : ℂ) else 0) =
          stdAddChar (-(((r + h) - r) * k)) *
            (if r + h ∈ S then (1 : ℂ) else 0)
        rw [show r + h - r = h by abel]
      _ = ∑ s ∈ S, stdAddChar (-((s - r) * k)) := by
        simp
      _ = ∑ s ∈ S,
          stdAddChar (r * k) * stdAddChar (-(s * k)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [show -((s - r) * k) = r * k + -(s * k) by ring,
          AddChar.map_add_eq_mul]
      _ = stdAddChar (r * k) * setFourier S k := by
        simp [setFourier, Finset.mul_sum]
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, hoverlap, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  congr 1
  simp only [setFourier, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [starRingEnd_apply, neg_neg] using
    (AddChar.map_neg_eq_conj (stdAddChar (N := N)) (-(r * k)))

/-- The manuscript's additive collision transform identity. -/
theorem dft_additiveCollision [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k : ZMod N) :
    𝓕 (fun h => (additiveCollision word h : ℂ)) k =
      spectralPower word k := by
  classical
  have hfun : (fun h => (additiveCollision word h : ℂ)) =
      ∑ d : Fin κ, fun h => (setOverlap (binSet word d) h : ℂ) := by
    funext h
    simp [additiveCollision]
  rw [hfun, map_sum]
  simp [spectralPower, binFourier, dft_setOverlap]

/-- Exact inverse-transform recovery of the additive collision profile. -/
theorem inverseDFT_spectralPower [NeZero N]
    (word : ZMod N → Option (Fin κ)) :
    𝓕⁻ (spectralPower word) =
      fun h => (additiveCollision word h : ℂ) := by
  apply (ZMod.dft (N := N)).injective
  rw [LinearEquiv.apply_symm_apply]
  ext k
  exact (dft_additiveCollision word k).symm

/-- Parseval in the normalization used by the manuscript. -/
theorem total_spectralPower [NeZero N]
    (word : ZMod N → Option (Fin κ)) :
    ∑ k, spectralPower word k =
      (N : ℂ) * ∑ d, (binSet word d).card := by
  have hpower : spectralPower word =
      𝓕 (fun h => (additiveCollision word h : ℂ)) := by
    funext k
    exact (dft_additiveCollision word k).symm
  calc
    ∑ k, spectralPower word k = 𝓕 (spectralPower word) 0 := by
      rw [ZMod.dft_apply_zero]
    _ = 𝓕 (𝓕 (fun h => (additiveCollision word h : ℂ))) 0 := by
      rw [hpower]
    _ = (N : ℂ) * (additiveCollision word 0 : ℂ) := by
      rw [ZMod.dft_dft]
      simp
    _ = (N : ℂ) * ∑ d, (binSet word d).card := by
      rw [additiveCollision_zero]

/-- A constant spectrum must take the Parseval-forced support value. -/
theorem spectralFlat_value [NeZero N]
    (word : ZMod N → Option (Fin κ)) (hflat : SpectralFlat word)
    (k : ZMod N) :
    spectralPower word k = (∑ d, (binSet word d).card : ℕ) := by
  have hsum := total_spectralPower word
  have hconstant :
      ∑ l, spectralPower word l = (N : ℂ) * spectralPower word k := by
    calc
      ∑ l, spectralPower word l = ∑ _l : ZMod N, spectralPower word k := by
        apply Finset.sum_congr rfl
        intro l _
        exact hflat l k
      _ = (N : ℂ) * spectralPower word k := by
        simp [ZMod.card]
  rw [hconstant] at hsum
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  exact mul_left_cancel₀ hN hsum

/-! ## The intrinsic prime digit word -/

/-- The coordinate encoding of the long-division digit function.  Residue
zero is omitted and every nonzero residue is encoded by its intrinsic digit
coordinate. -/
def primeDigitWord (b p : ℕ) (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    ZMod p → Option (Fin b) :=
  fun r => if _hr : r = 0 then none else
    some ⟨digitBin b p r.val,
      digitBin_lt_base hb hp r.val_lt⟩

@[simp] theorem primeDigitWord_zero (b p : ℕ) (hb : 0 < b) (hp : 0 < p)
    [NeZero p] : primeDigitWord b p hb hp 0 = none := by
  simp [primeDigitWord]

theorem primeDigitWord_some_iff {b p : ℕ} (hb : 0 < b) (hp : 0 < p)
    [NeZero p] {r : ZMod p} {d : Fin b} :
    primeDigitWord b p hb hp r = some d ↔
      r ≠ 0 ∧ digitBin b p r.val = d.val := by
  simp only [primeDigitWord]
  by_cases hr : r = 0
  · simp [hr]
  · simp [hr, Fin.ext_iff]

/-- The intrinsic coordinate encoding contains exactly the `p - 1` nonzero
residues. -/
theorem primeDigitWord_total_bin_size {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    ∑ d, (binSet (primeDigitWord b p hb hp) d).card = p - 1 := by
  classical
  simp only [binSet, Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner (r : ZMod p) :
      (∑ d : Fin b,
          if primeDigitWord b p hb hp r = some d then 1 else 0) =
        if r = 0 then 0 else 1 := by
    by_cases hr : r = 0
    · simp [hr]
    · simp [primeDigitWord, hr]
  simp_rw [hinner]
  calc
    (∑ r : ZMod p, if r = 0 then 0 else 1) =
        ∑ r : ZMod p, if r ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : r = 0 <;> simp [hr]
    _ = (Finset.univ.filter fun r : ZMod p => r ≠ 0).card := by
      simpa using
        (Finset.sum_boole (R := ℕ) (fun r : ZMod p => r ≠ 0) Finset.univ)
    _ = (Finset.univ.erase (0 : ZMod p)).card := by
      congr 1
      ext r
      simp
    _ = p - 1 := by
      rw [Finset.card_erase_of_mem (by simp)]
      simp [ZMod.card]

/-- The `ZMod` coordinate bin has exactly the population used by the earlier
alignment companions. -/
theorem primeDigitWord_bin_card {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] (d : Fin b) :
    (binSet (primeDigitWord b p hb hp) d).card =
      digitBinPopulation b p d.val := by
  classical
  unfold binSet digitBinPopulation
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    rw [Finset.mem_filter] at hr ⊢
    have hword := (primeDigitWord_some_iff hb hp).mp hr.2
    exact ⟨by
      rw [nonzeroResidues]
      exact Finset.mem_erase.mpr
        ⟨(ZMod.val_ne_zero r).mpr hword.1,
          Finset.mem_range.mpr r.val_lt⟩,
      hword.2⟩
  · intro r _ s _ hrs
    exact ZMod.val_injective p hrs
  · intro x hx
    rw [Finset.mem_filter] at hx
    have hxmem := Finset.mem_erase.mp hx.1
    have hxlt := Finset.mem_range.mp hxmem.2
    let r : ZMod p := x
    have hrval : r.val = x := ZMod.val_natCast_of_lt hxlt
    have hrne : r ≠ 0 := by
      rw [← ZMod.val_ne_zero, hrval]
      exact hxmem.1
    refine ⟨r, ?_, hrval⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ r,
      (primeDigitWord_some_iff hb hp).mpr ⟨hrne, by simpa [hrval] using hx.2⟩⟩

/-- Empty-or-singleton coordinate bins are exactly injectivity of the
long-division digit map. -/
theorem digitPartitioning_iff_prime_bin_card_le_one {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    DigitPartitioning b p ↔
      ∀ d, (binSet (primeDigitWord b p hb hp) d).card ≤ 1 := by
  constructor
  · intro hdp d
    rw [primeDigitWord_bin_card hb hp d]
    exact digitBinPopulation_le_one_of_digitPartitioning hdp
  · intro hbins r s hr0 hrp hs0 hsp hdigit
    have hdlt := digitBin_lt_base hb hp hrp
    let d : Fin b := ⟨digitBin b p r, hdlt⟩
    have hcard : digitBinPopulation b p d.val ≤ 1 := by
      rw [← primeDigitWord_bin_card hb hp d]
      exact hbins d
    rw [digitBinPopulation, Finset.card_le_one_iff] at hcard
    apply hcard
    · simp [nonzeroResidues, hr0.ne', hrp, d]
    · simp [nonzeroResidues, hs0.ne', hsp, d, hdigit]

/-- Exact zero-mode identity in the manuscript's original bin-population
notation. -/
theorem prime_spectralPower_zero {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    spectralPower (primeDigitWord b p hb hp) 0 =
      (digitBinSquareSum b p : ℂ) := by
  rw [spectralPower_zero]
  congr 1
  unfold binSquareMass digitBinSquareSum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro d hd
  have hdb : d < b := Finset.mem_range.mp hd
  let df : Fin b := ⟨d, hdb⟩
  have hcard := primeDigitWord_bin_card hb hp df
  simpa [hdb, df] using hcard

/-- Total spectral power for the intrinsic prime digit word. -/
theorem prime_total_spectralPower {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    ∑ k, spectralPower (primeDigitWord b p hb hp) k =
      (p * (p - 1) : ℕ) := by
  rw [total_spectralPower, primeDigitWord_total_bin_size hb hp]
  norm_cast

/-- Exact flatness criterion before translating it into the elementary
prime/base inequality. -/
theorem prime_spectralFlat_iff_digitPartitioning {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    SpectralFlat (primeDigitWord b p hb hp) ↔ DigitPartitioning b p := by
  constructor
  · intro hflat
    have hvalue := spectralFlat_value
      (primeDigitWord b p hb hp) hflat (0 : ZMod p)
    rw [spectralPower_zero] at hvalue
    have hmass : binSquareMass (primeDigitWord b p hb hp) =
        ∑ d, (binSet (primeDigitWord b p hb hp) d).card := by
      exact_mod_cast hvalue
    have hbins : ∀ d,
        (binSet (primeDigitWord b p hb hp) d).card ≤ 1 := by
      apply (sum_sq_eq_sum_iff_le_one
        (fun d => (binSet (primeDigitWord b p hb hp) d).card)).mp
      exact hmass
    exact (digitPartitioning_iff_prime_bin_card_le_one hb hp).mpr hbins
  · intro hdp k l
    have hbins :=
      (digitPartitioning_iff_prime_bin_card_le_one hb hp).mp hdp
    rw [spectralPower_eq_of_bin_card_le_one _ hbins k,
      spectralPower_eq_of_bin_card_le_one _ hbins l]

/-- The manuscript's three-way flatness boundary. -/
theorem prime_spectralFlat_iff_le {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p] :
    SpectralFlat (primeDigitWord b p hb hp.pos) ↔ p ≤ b + 1 := by
  rw [prime_spectralFlat_iff_digitPartitioning hb hp.pos,
    digitPartitioning_iff hb hp hpb]

/-! ## Exact manuscript certificates -/

def decimalThirteenDigitWord : ZMod 13 → Option (Fin 10) :=
  primeDigitWord 10 13 (by norm_num) (by norm_num)

def decimalThirteenBinSizes : List ℕ :=
  List.ofFn fun d : Fin 10 => (binSet decimalThirteenDigitWord d).card

theorem decimalThirteenBinSizes_certificate :
    decimalThirteenBinSizes = [1, 1, 1, 2, 1, 1, 2, 1, 1, 1] := by
  decide

theorem decimalThirteenBinSquareMass_certificate :
    binSquareMass decimalThirteenDigitWord = 16 := by
  decide

theorem decimalThirteenSpectralPower_zero :
    spectralPower decimalThirteenDigitWord 0 = 16 := by
  rw [spectralPower_zero, decimalThirteenBinSquareMass_certificate]
  norm_num

def decimalThirteenCollisionProfile : List ℕ :=
  List.ofFn fun h : Fin 13 =>
    additiveCollision decimalThirteenDigitWord (h.val : ZMod 13)

theorem decimalThirteenCollisionProfile_certificate :
    decimalThirteenCollisionProfile =
      [12, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] := by
  decide

/-- The manuscript's final contrast: equal flat additive power does not fix
the multiplicative order. -/
theorem baseEightAndTen_modSeven_flat :
    SpectralFlat (primeDigitWord 8 7 (by norm_num) (by norm_num)) ∧
      SpectralFlat (primeDigitWord 10 7 (by norm_num) (by norm_num)) := by
  constructor
  · exact (prime_spectralFlat_iff_le (b := 8) (p := 7)
      (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  · exact (prime_spectralFlat_iff_le (b := 10) (p := 7)
      (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)

theorem baseEightAndTen_modSeven_orders :
    orderOf (8 : ZMod 7) = 1 ∧ orderOf (10 : ZMod 7) = 6 := by
  constructor
  · have h : (8 : ZMod 7) = 1 := by decide
    rw [h, orderOf_one]
  · rw [orderOf_eq_iff (by norm_num : 0 < 6)]
    constructor
    · decide
    · intro m hm hpos
      interval_cases m <;> decide

end NField.Alignment.SpectralPower
