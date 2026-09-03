/-
Author: Alexander S. Petty
-/

import NField.Alignment.AutocorrelationFormula
import Mathlib.Analysis.Real.Sqrt

/-!
# Phase-filtered Ramanujan sums and the spectral gate

Reusable formal core for the Lean companion to
"Phase-Filtered Ramanujan Sums and the Spectral Gate".
-/

namespace NField.Alignment.PhaseFilteredRamanujan

open scoped BigOperators
open ZMod
open NField.Alignment
open NField.Alignment.SpectralPower
open NField.Alignment.AutocorrelationFormula

variable {N κ : ℕ}

/-! ## The prime Ramanujan selector -/

/-- All nonzero residues as a finite set. -/
def nonzeroSet (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  Finset.univ.erase 0

/-- The Ramanujan sum over nonzero residues of a cyclic modulus.  The name
`primeRamanujan` reflects the manuscript's use at a prime modulus. -/
noncomputable def primeRamanujan (N : ℕ) [NeZero N] (m : ZMod N) : ℂ :=
  subsetExponential (nonzeroSet N) m

/-- The two values of the nonzero-residue additive character sum. -/
theorem primeRamanujan_eq [NeZero N] (m : ZMod N) :
    primeRamanujan N m =
      if m = 0 then ((N - 1 : ℕ) : ℂ) else (-1 : ℂ) := by
  classical
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun x : ZMod N => stdAddChar (m * x)) (Finset.mem_univ 0)
  have hfull := sum_stdAddChar_mul (N := N) m
  unfold primeRamanujan subsetExponential nonzeroSet
  by_cases hm : m = 0
  · subst m
    simp [ZMod.card]
  · rw [if_neg hm]
    rw [if_neg hm] at hfull
    have hzeroTerm : stdAddChar (m * (0 : ZMod N)) = 1 := by simp
    rw [hfull, hzeroTerm] at hsplit
    linear_combination hsplit

/-- The full collision sum equals its restriction to nonzero residues when
the word omits zero. -/
theorem multiplicativeCollision_eq_nonzeroSet [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N)
    (hzero : word 0 = none) :
    multiplicativeCollision word a =
      subsetCollision word (nonzeroSet N) a := by
  classical
  unfold multiplicativeCollision subsetCollision nonzeroSet
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun r : ZMod N => sameBinKernel word r (a * r))
    (Finset.mem_univ 0)
  have hkernel : sameBinKernel word 0 (a * 0) = 0 := by
    simp [sameBinKernel_eq_indicator, hzero]
  rw [hkernel, add_zero] at hsplit
  exact hsplit.symm

/-- Exact Ramanujan-weighted two-dimensional collision identity. -/
theorem ramanujan_collision_identity [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N)
    (hzero : word 0 = none) :
    multiplicativeCollision word a =
      ((N : ℂ)⁻¹) ^ 2 * ∑ k : ZMod N, ∑ k' : ZMod N,
        crossSpectrum word k k' * primeRamanujan N (k + a * k') := by
  rw [multiplicativeCollision_eq_nonzeroSet word a hzero]
  exact subsetCollision_formula word (nonzeroSet N) a

/-- The Ramanujan identity and the line-slice identity are the same collision
count. -/
theorem ramanujan_identity_eq_line_slice [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hzero : word 0 = none) (hinv : a * aInv = 1) :
    ((N : ℂ)⁻¹) ^ 2 * ∑ k : ZMod N, ∑ k' : ZMod N,
        crossSpectrum word k k' * primeRamanujan N (k + a * k') =
      (N : ℂ)⁻¹ * ∑ k : ZMod N,
        crossSpectrum word k (-aInv * k) := by
  rw [← ramanujan_collision_identity word a hzero,
    ← multiplicative_slice word a aInv hinv]

/-! ## The normalized phase gate -/

/-- Complex mass remaining after phase cancellation along one spectral line. -/
noncomputable def sliceSum [NeZero N]
    (word : ZMod N → Option (Fin κ)) (aInv : ZMod N) : ℂ :=
  ∑ k : ZMod N, crossSpectrum word k (-aInv * k)

/-- Unsigned spectral mass along the same line. -/
noncomputable def phaseMass [NeZero N]
    (word : ZMod N → Option (Fin κ)) (aInv : ZMod N) : ℝ :=
  ∑ k : ZMod N, ∑ d : Fin κ,
    ‖binFourier word d k‖ * ‖binFourier word d (-aInv * k)‖

/-- Fraction of unsigned line mass surviving phase cancellation. -/
noncomputable def phaseGate [NeZero N]
    (word : ZMod N → Option (Fin κ)) (aInv : ZMod N) : ℝ :=
  ‖sliceSum word aInv‖ / phaseMass word aInv

/-- Exact collision count in natural numbers. -/
def collisionCount [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N) : ℕ :=
  ∑ r : ZMod N,
    if word r = word (a * r) ∧ word r ≠ none then 1 else 0

theorem multiplicativeCollision_eq_collisionCount [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N) :
    multiplicativeCollision word a = (collisionCount word a : ℂ) := by
  unfold multiplicativeCollision collisionCount
  simp_rw [sameBinKernel_eq_indicator]
  push_cast
  rfl

/-- The selected spectral line is exactly `N` times the integer collision
count. -/
theorem sliceSum_eq_collisionCount [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) :
    sliceSum word aInv = (N : ℂ) * collisionCount word a := by
  have hslice := multiplicative_slice word a aInv hinv
  rw [multiplicativeCollision_eq_collisionCount] at hslice
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hc : (collisionCount word a : ℂ) = sliceSum word aInv / N := by
    simpa [sliceSum, div_eq_inv_mul, mul_comm] using hslice
  have hmul := (eq_div_iff hN).mp hc
  simpa [mul_comm] using hmul.symm

/-- Triangle inequality for the phase gate denominator. -/
theorem norm_sliceSum_le_phaseMass [NeZero N]
    (word : ZMod N → Option (Fin κ)) (aInv : ZMod N) :
    ‖sliceSum word aInv‖ ≤ phaseMass word aInv := by
  classical
  unfold sliceSum phaseMass crossSpectrum
  calc
    ‖∑ k : ZMod N, ∑ d : Fin κ,
        binFourier word d k * binFourier word d (-aInv * k)‖ ≤
      ∑ k : ZMod N, ‖∑ d : Fin κ,
        binFourier word d k * binFourier word d (-aInv * k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k : ZMod N, ∑ d : Fin κ,
        ‖binFourier word d k * binFourier word d (-aInv * k)‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact norm_sum_le _ _
    _ = ∑ k : ZMod N, ∑ d : Fin κ,
        ‖binFourier word d k‖ * ‖binFourier word d (-aInv * k)‖ := by
      simp only [norm_mul]

/-- Multiplication by the selected inverse, with the manuscript's sign, is a
frequency permutation. -/
def lineFrequencyEquiv [NeZero N]
    (a aInv : ZMod N) (hinv : a * aInv = 1) : ZMod N ≃ ZMod N where
  toFun k := -aInv * k
  invFun k := -a * k
  left_inv k := by
    calc
      -a * (-aInv * k) = (a * aInv) * k := by ring
      _ = k := by rw [hinv, one_mul]
  right_inv k := by
    calc
      -aInv * (-a * k) = (a * aInv) * k := by ring
      _ = k := by rw [hinv, one_mul]

/-- Parseval mass of all bin Fourier coordinates. -/
theorem total_binFourier_norm_sq [NeZero N]
    (word : ZMod N → Option (Fin κ)) :
    ∑ k : ZMod N, ∑ d : Fin κ, ‖binFourier word d k‖ ^ 2 =
      (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
  calc
    (∑ k : ZMod N, ∑ d : Fin κ, ‖binFourier word d k‖ ^ 2) =
        ∑ k : ZMod N, (spectralPower word k).re := by
      apply Finset.sum_congr rfl
      intro k _
      exact (spectralPower_re_eq_sum_norm_sq word k).symm
    _ = (∑ k : ZMod N, spectralPower word k).re := by
      exact (Complex.re_sum (s := Finset.univ)
        (fun k : ZMod N => spectralPower word k)).symm
    _ = ((N : ℂ) * ∑ d : Fin κ, (binSet word d).card).re := by
      rw [total_spectralPower]
    _ = (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
      norm_num

/-- The line permutation preserves the second squared-norm total. -/
theorem total_binFourier_norm_sq_line [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) :
    ∑ k : ZMod N, ∑ d : Fin κ,
        ‖binFourier word d (-aInv * k)‖ ^ 2 =
      (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
  calc
    (∑ k : ZMod N, ∑ d : Fin κ,
        ‖binFourier word d (-aInv * k)‖ ^ 2) =
      ∑ k : ZMod N, ∑ d : Fin κ, ‖binFourier word d k‖ ^ 2 := by
        apply Fintype.sum_equiv (lineFrequencyEquiv a aInv hinv)
        intro k
        rfl
    _ = (N : ℝ) * ∑ d : Fin κ, (binSet word d).card :=
      total_binFourier_norm_sq word

/-- Cauchy--Schwarz and Parseval bound the unsigned line mass by the total
assigned Fourier mass. -/
theorem phaseMass_le_total [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) :
    phaseMass word aInv ≤
      (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
  classical
  let f : ZMod N × Fin κ → ℝ := fun kd => ‖binFourier word kd.2 kd.1‖
  let g : ZMod N × Fin κ → ℝ := fun kd =>
    ‖binFourier word kd.2 (-aInv * kd.1)‖
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (ZMod N × Fin κ)) f g
  have hf : ∑ kd : ZMod N × Fin κ, f kd ^ 2 =
      (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
    rw [Fintype.sum_prod_type]
    exact total_binFourier_norm_sq word
  have hg : ∑ kd : ZMod N × Fin κ, g kd ^ 2 =
      (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
    rw [Fintype.sum_prod_type]
    exact total_binFourier_norm_sq_line word a aInv hinv
  have hnonneg : 0 ≤ (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
    apply mul_nonneg
    · exact Nat.cast_nonneg N
    · exact Nat.cast_nonneg _
  unfold phaseMass
  calc
    (∑ k : ZMod N, ∑ d : Fin κ,
        ‖binFourier word d k‖ * ‖binFourier word d (-aInv * k)‖) =
      ∑ kd : ZMod N × Fin κ, f kd * g kd := by
        rw [Fintype.sum_prod_type]
    _ ≤
        √(∑ kd : ZMod N × Fin κ, f kd ^ 2) *
          √(∑ kd : ZMod N × Fin κ, g kd ^ 2) := by
      simpa using hcs
    _ = √((N : ℝ) * ∑ d : Fin κ, (binSet word d).card) *
          √((N : ℝ) * ∑ d : Fin κ, (binSet word d).card) := by
      rw [hf, hg]
    _ = (N : ℝ) * ∑ d : Fin κ, (binSet word d).card := by
      exact Real.mul_self_sqrt hnonneg

/-! ## Exact gate bounds and zero criterion -/

/-- Number of residues assigned to a digit coordinate. -/
def assignedMass [NeZero N]
    (word : ZMod N → Option (Fin κ)) : ℕ :=
  ∑ d : Fin κ, (binSet word d).card

/-- The zero-frequency contribution is a lower bound for the unsigned phase
mass. -/
theorem zeroModeSquareMass_le_phaseMass [NeZero N]
    (word : ZMod N → Option (Fin κ)) (aInv : ZMod N) :
    (∑ d : Fin κ, ((binSet word d).card : ℝ) ^ 2) ≤
      phaseMass word aInv := by
  classical
  unfold phaseMass
  have hterm :
      (∑ d : Fin κ, ((binSet word d).card : ℝ) ^ 2) =
        ∑ d : Fin κ,
          ‖binFourier word d (0 : ZMod N)‖ *
            ‖binFourier word d (-aInv * (0 : ZMod N))‖ := by
    simp [binFourier_zero, pow_two]
  rw [hterm]
  apply Finset.single_le_sum (s := Finset.univ) (a := (0 : ZMod N))
    (f := fun k : ZMod N => ∑ d : Fin κ,
      ‖binFourier word d k‖ * ‖binFourier word d (-aInv * k)‖)
  · intro k _
    positivity
  · simp

/-- A nonempty digit partition gives a strictly positive gate denominator. -/
theorem phaseMass_pos_of_assigned [NeZero N]
    (word : ZMod N → Option (Fin κ)) (aInv : ZMod N)
    (hmass : 0 < assignedMass word) :
    0 < phaseMass word aInv := by
  have hpoint (d : Fin κ) :
      ((binSet word d).card : ℝ) ≤ ((binSet word d).card : ℝ) ^ 2 := by
    have hn : (binSet word d).card = 0 ∨ 1 ≤ (binSet word d).card := by omega
    rcases hn with hn | hn
    · simp [hn]
    · have hnR : (1 : ℝ) ≤ ((binSet word d).card : ℝ) := by
        exact_mod_cast hn
      have hmul : 0 ≤ ((binSet word d).card : ℝ) *
          (((binSet word d).card : ℝ) - 1) := by positivity
      nlinarith
  have hsum : (assignedMass word : ℝ) ≤
      ∑ d : Fin κ, ((binSet word d).card : ℝ) ^ 2 := by
    unfold assignedMass
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun d _ => hpoint d
  have hpositive : 0 < (assignedMass word : ℝ) := by exact_mod_cast hmass
  exact lt_of_lt_of_le hpositive
    (hsum.trans (zeroModeSquareMass_le_phaseMass word aInv))

/-- The norm of the surviving line mass is exactly `N` times the natural
collision count. -/
theorem norm_sliceSum_eq_collisionCount [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) :
    ‖sliceSum word aInv‖ =
      (N : ℝ) * collisionCount word a := by
  rw [sliceSum_eq_collisionCount word a aInv hinv]
  norm_num

/-- Exact upper and lower phase-gate bounds. -/
theorem phaseGate_bounds [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) (hmass : 0 < assignedMass word) :
    (collisionCount word a : ℝ) / assignedMass word ≤
        phaseGate word aInv ∧
      phaseGate word aInv ≤ 1 := by
  have hphasePos := phaseMass_pos_of_assigned word aInv hmass
  have hassignedPos : (0 : ℝ) < assignedMass word := by
    exact_mod_cast hmass
  have hcap : phaseMass word aInv ≤
      (N : ℝ) * assignedMass word := by
    simpa [assignedMass] using phaseMass_le_total word a aInv hinv
  have hnorm := norm_sliceSum_eq_collisionCount word a aInv hinv
  constructor
  · unfold phaseGate
    rw [hnorm]
    apply (div_le_div_iff₀ hassignedPos hphasePos).2
    calc
      (collisionCount word a : ℝ) * phaseMass word aInv ≤
          (collisionCount word a : ℝ) *
            ((N : ℝ) * assignedMass word) := by
        exact mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg _)
      _ = ((N : ℝ) * collisionCount word a) * assignedMass word := by
        ring
  · unfold phaseGate
    exact (div_le_one hphasePos).2 (norm_sliceSum_le_phaseMass word aInv)

/-- The gate vanishes exactly at collision-free multipliers. -/
theorem phaseGate_eq_zero_iff [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) (hmass : 0 < assignedMass word) :
    phaseGate word aInv = 0 ↔ collisionCount word a = 0 := by
  have hphaseNe : phaseMass word aInv ≠ 0 :=
    ne_of_gt (phaseMass_pos_of_assigned word aInv hmass)
  unfold phaseGate
  rw [div_eq_zero_iff]
  simp only [hphaseNe, or_false, norm_eq_zero]
  rw [sliceSum_eq_collisionCount word a aInv hinv]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp [hN]

/-- Every positive collision count gives the discrete lower gate gap. -/
theorem phaseGate_ge_reciprocal_of_collision [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) (hmass : 0 < assignedMass word)
    (hcollision : 0 < collisionCount word a) :
    (assignedMass word : ℝ)⁻¹ ≤ phaseGate word aInv := by
  have hlower := (phaseGate_bounds word a aInv hinv hmass).1
  have hone : (1 : ℝ) ≤ collisionCount word a := by exact_mod_cast hcollision
  have hmassNonneg : (0 : ℝ) ≤ assignedMass word := Nat.cast_nonneg _
  calc
    (assignedMass word : ℝ)⁻¹ = 1 / assignedMass word := by
      rw [one_div]
    _ ≤ (collisionCount word a : ℝ) / assignedMass word := by
      exact div_le_div_of_nonneg_right hone hmassNonneg
    _ ≤ phaseGate word aInv := hlower

/-- At the identity line, unsigned and surviving mass agree exactly. -/
theorem phaseGate_one [NeZero N]
    (word : ZMod N → Option (Fin κ))
    (hmass : 0 < assignedMass word) :
    phaseGate word 1 = 1 := by
  have hnormNeg (d : Fin κ) (k : ZMod N) :
      ‖binFourier word d (-k)‖ = ‖binFourier word d k‖ := by
    rw [← star_binFourier]
    simp
  have hphase : phaseMass word 1 = (N : ℝ) * assignedMass word := by
    unfold phaseMass
    simp only [one_mul, neg_mul, hnormNeg, ← pow_two]
    simpa [assignedMass] using total_binFourier_norm_sq word
  have hslice : sliceSum word 1 =
      (N : ℂ) * assignedMass word := by
    unfold sliceSum
    simp only [neg_mul, one_mul]
    simp_rw [crossSpectrum_antidiagonal]
    simpa [assignedMass] using total_spectralPower word
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hmassR : (0 : ℝ) < assignedMass word := by exact_mod_cast hmass
  have hdenom : (N : ℝ) * assignedMass word ≠ 0 := by
    exact ne_of_gt (mul_pos hNpos hmassR)
  have hnorm : ‖(N : ℂ) * (assignedMass word : ℂ)‖ =
      (N : ℝ) * assignedMass word := by
    norm_num
  unfold phaseGate
  rw [hphase, hslice]
  rw [hnorm, div_self hdenom]

/-- Collision freedom is exactly binwise disjointness under multiplication. -/
theorem collisionCount_eq_zero_iff_bins_disjoint [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N) :
    collisionCount word a = 0 ↔
      ∀ d : Fin κ, ∀ r ∈ binSet word d, a * r ∉ binSet word d := by
  classical
  unfold collisionCount
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h d r hr hra
    have hs := h r (Finset.mem_univ r)
    simp only [ite_eq_right_iff, one_ne_zero, imp_false] at hs
    apply hs
    simp only [binSet, Finset.mem_filter, Finset.mem_univ, true_and] at hr hra
    exact ⟨hr.trans hra.symm, by simp [hr]⟩
  · intro h r _
    by_cases hmatch : word r = word (a * r) ∧ word r ≠ none
    · obtain ⟨d, hd⟩ : ∃ d, word r = some d := by
        cases hw : word r with
        | none => exact False.elim (hmatch.2 hw)
        | some d =>
            refine ⟨d, ?_⟩
            simp_all
      have hr : r ∈ binSet word d := by simp [binSet, hd]
      have har : a * r ∈ binSet word d := by
        simp [binSet, ← hmatch.1, hd]
      exact False.elim (h d r hr har)
    · simp [hmatch]

/-! ## Intrinsic prime specialization -/

theorem prime_assignedMass {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p] :
    assignedMass (primeDigitWord b p hb hp) = p - 1 := by
  exact primeDigitWord_total_bin_size hb hp

/-- The complete phase-gate theorem for the intrinsic prime digit word. -/
theorem prime_phaseGate_certificate {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (a aInv : ZMod p) (hinv : a * aInv = 1) :
    (collisionCount (primeDigitWord b p hb hp.pos) a : ℝ) /
        ((p - 1 : ℕ) : ℝ) ≤
        phaseGate (primeDigitWord b p hb hp.pos) aInv ∧
      phaseGate (primeDigitWord b p hb hp.pos) aInv ≤ 1 ∧
      (phaseGate (primeDigitWord b p hb hp.pos) aInv = 0 ↔
        collisionCount (primeDigitWord b p hb hp.pos) a = 0) ∧
      phaseGate (primeDigitWord b p hb hp.pos) 1 = 1 ∧
      (0 < collisionCount (primeDigitWord b p hb hp.pos) a →
        ((p - 1 : ℕ) : ℝ)⁻¹ ≤
          phaseGate (primeDigitWord b p hb hp.pos) aInv) := by
  have hmass : 0 < assignedMass (primeDigitWord b p hb hp.pos) := by
    rw [prime_assignedMass hb hp.pos]
    exact Nat.sub_pos_of_lt hp.one_lt
  have hbounds := phaseGate_bounds
    (primeDigitWord b p hb hp.pos) a aInv hinv hmass
  have hzero := phaseGate_eq_zero_iff
    (primeDigitWord b p hb hp.pos) a aInv hinv hmass
  have hone := phaseGate_one (primeDigitWord b p hb hp.pos) hmass
  constructor
  · simpa [prime_assignedMass hb hp.pos] using hbounds.1
  constructor
  · exact hbounds.2
  constructor
  · exact hzero
  constructor
  · exact hone
  · intro hcollision
    simpa [prime_assignedMass hb hp.pos] using
      phaseGate_ge_reciprocal_of_collision
        (primeDigitWord b p hb hp.pos) a aInv hinv hmass hcollision

/-! ## Singleton-bin collision law -/

theorem assignedMass_eq_assignedCount [NeZero N]
    (word : ZMod N → Option (Fin κ)) :
    assignedMass word =
      ∑ r : ZMod N, if word r ≠ none then 1 else 0 := by
  classical
  unfold assignedMass binSet
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  cases hr : word r with
  | none => simp
  | some d => simp

theorem collisionCount_one [NeZero N]
    (word : ZMod N → Option (Fin κ)) :
    collisionCount word 1 = assignedMass word := by
  rw [assignedMass_eq_assignedCount]
  unfold collisionCount
  apply Finset.sum_congr rfl
  intro r _
  simp

theorem primeDigitWord_injective_on_assigned {b p : ℕ}
    (hb : 0 < b) (hp : 0 < p) [NeZero p]
    (hdp : DigitPartitioning b p) {r s : ZMod p}
    (heq : primeDigitWord b p hb hp r = primeDigitWord b p hb hp s)
    (hrAssigned : primeDigitWord b p hb hp r ≠ none) :
    r = s := by
  obtain ⟨d, hrd⟩ : ∃ d, primeDigitWord b p hb hp r = some d := by
    cases hr : primeDigitWord b p hb hp r with
    | none => exact False.elim (hrAssigned hr)
    | some d =>
        refine ⟨d, ?_⟩
        simp_all
  have hsd : primeDigitWord b p hb hp s = some d := by
    rw [← heq]
    exact hrd
  have hrData := (primeDigitWord_some_iff hb hp).mp hrd
  have hsData := (primeDigitWord_some_iff hb hp).mp hsd
  apply ZMod.val_injective
  exact hdp (ZMod.val_pos.mpr hrData.1) r.val_lt
    (ZMod.val_pos.mpr hsData.1) s.val_lt (hrData.2.trans hsData.2.symm)

/-- Digit-partitioning makes every nonidentity multiplier collision-free. -/
theorem prime_collisionCount_eq_zero_of_digitPartitioning {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (hdp : DigitPartitioning b p) {a : ZMod p} (ha : a ≠ 1) :
    collisionCount (primeDigitWord b p hb hp.pos) a = 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  unfold collisionCount
  rw [Finset.sum_eq_zero_iff]
  intro r _
  by_cases hmatch :
      primeDigitWord b p hb hp.pos r =
          primeDigitWord b p hb hp.pos (a * r) ∧
        primeDigitWord b p hb hp.pos r ≠ none
  · have hremainder := primeDigitWord_injective_on_assigned
      hb hp.pos hdp hmatch.1 hmatch.2
    have hr : r ≠ 0 := by
      intro hrzero
      subst r
      exact hmatch.2 (primeDigitWord_zero b p hb hp.pos)
    have har : a * r = 1 * r := by simpa using hremainder.symm
    have : a = 1 := mul_right_cancel₀ hr har
    exact False.elim (ha this)
  · simp [hmatch]

/-- Exact singleton-bin collision profile. -/
theorem prime_singleton_collision_profile {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) [NeZero p]
    (hdp : DigitPartitioning b p) (a : ZMod p) :
    collisionCount (primeDigitWord b p hb hp.pos) a =
      if a = 1 then p - 1 else 0 := by
  by_cases ha : a = 1
  · subst a
    rw [if_pos rfl, collisionCount_one, prime_assignedMass hb hp.pos]
  · rw [if_neg ha]
    exact prime_collisionCount_eq_zero_of_digitPartitioning hb hp hdp ha

/-! ## Euclidean coarse data -/

/-- The exact zero-mode square mass forced by a two-length Euclidean bin
word. -/
theorem euclidean_bin_square_mass
    {b q r : ℕ} (n : Fin b → ℕ)
    (hlength : ∀ d, n d = q ∨ n d = q + 1)
    (hlarge :
      (Finset.univ.filter fun d : Fin b => n d = q + 1).card = r - 1) :
    ∑ d : Fin b, n d ^ 2 = b * q ^ 2 + (2 * q + 1) * (r - 1) := by
  classical
  let large := Finset.univ.filter fun d : Fin b => n d = q + 1
  have hpoint (d : Fin b) :
      n d ^ 2 = q ^ 2 + if d ∈ large then 2 * q + 1 else 0 := by
    rcases hlength d with hq | hq
    · have hd : d ∉ large := by simp [large, hq]
      simp [hq, hd]
    · have hd : d ∈ large := by simp [large, hq]
      simp [hq, hd]
      ring
  calc
    (∑ d : Fin b, n d ^ 2) =
        ∑ d : Fin b, (q ^ 2 + if d ∈ large then 2 * q + 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      exact hpoint d
    _ = b * q ^ 2 + large.card * (2 * q + 1) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite]
      simp [large]
    _ = b * q ^ 2 + (2 * q + 1) * (r - 1) := by
      rw [hlarge]
      ring

/-- Euclidean division gives the exact rational identity underlying the
continued-fraction tail. -/
theorem euclidean_tail_identity {p b q r : ℕ}
    (hb : 0 < b) (hr : 0 < r) (hdivision : p = b * q + r) :
    (p : ℚ) / b = q + 1 / ((b : ℚ) / r) := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [hdivision]
  push_cast
  field_simp

end NField.Alignment.PhaseFilteredRamanujan
