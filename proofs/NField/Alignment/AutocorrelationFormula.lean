/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.SpectralPower
import NField.Alignment.CrossAlignmentMatrix
import NField.Alignment.ThreeTier

/-!
# The two-dimensional same-bin transform

Reusable formal core for the Lean companion to "The Autocorrelation Formula".
The definitions use the same intrinsic `Option (Fin κ)` digit encoding as the
spectral-power companion.  Residues carrying `none` are outside the digit
partition, so the prime word omits residue zero exactly as in the manuscript.
-/

namespace NField.Alignment.AutocorrelationFormula

open scoped BigOperators
open ZMod
open NField.Alignment.SpectralPower
open NField.CollisionDefinition

variable {N κ : ℕ}

/-! ## The equality kernel and its two-dimensional transform -/

/-- Complex-valued indicator of one digit bin. -/
def binIndicator [NeZero N]
    (word : ZMod N → Option (Fin κ)) (d : Fin κ) (r : ZMod N) : ℂ :=
  if word r = some d then 1 else 0

/-- The equality kernel of the digit partition. -/
def sameBinKernel [NeZero N]
    (word : ZMod N → Option (Fin κ)) (r s : ZMod N) : ℂ :=
  ∑ d, binIndicator word d r * binIndicator word d s

/-- The coordinate sum is exactly the indicator that two residues carry the
same declared digit.  Two omitted residues do not count as a match. -/
theorem sameBinKernel_eq_indicator [NeZero N]
    (word : ZMod N → Option (Fin κ)) (r s : ZMod N) :
    sameBinKernel word r s =
      if word r = word s ∧ word r ≠ none then 1 else 0 := by
  classical
  cases hr : word r with
  | none => simp [sameBinKernel, binIndicator, hr]
  | some d =>
      cases hs : word s with
      | none => simp [sameBinKernel, binIndicator, hr, hs]
      | some e =>
          by_cases hde : d = e
          · subst e
            simp [sameBinKernel, binIndicator, hr, hs]
          · simp [sameBinKernel, binIndicator, hr, hs, hde]

/-- The phase-sensitive two-dimensional transform of the bin coordinates. -/
noncomputable def crossSpectrum [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k k' : ZMod N) : ℂ :=
  ∑ d, binFourier word d k * binFourier word d k'

/-- A bin Fourier coefficient is the transform of its one-hot indicator. -/
theorem binFourier_eq_indicator_sum [NeZero N]
    (word : ZMod N → Option (Fin κ)) (d : Fin κ) (k : ZMod N) :
    binFourier word d k =
      ∑ r : ZMod N, stdAddChar (-(r * k)) * binIndicator word d r := by
  classical
  unfold binFourier setFourier binSet binIndicator
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]

/-- The cross-spectrum is exactly the two-dimensional Fourier transform of
the equality kernel. -/
theorem crossSpectrum_eq_kernel_transform [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k k' : ZMod N) :
    crossSpectrum word k k' =
      ∑ r : ZMod N, ∑ s : ZMod N,
        sameBinKernel word r s *
          stdAddChar (-(r * k) - (s * k')) := by
  classical
  simp only [crossSpectrum, binFourier_eq_indicator_sum, sameBinKernel]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro d _
  rw [show -(r * k) - s * k' = -(r * k) + -(s * k') by ring,
    AddChar.map_add_eq_mul]
  ring

/-- The two-dimensional transform written as two successive standard DFTs. -/
theorem crossSpectrum_eq_dft_dft [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k k' : ZMod N) :
    crossSpectrum word k k' =
      𝓕 (fun r : ZMod N =>
        𝓕 (fun s : ZMod N => sameBinKernel word r s) k') k := by
  rw [crossSpectrum_eq_kernel_transform]
  simp only [ZMod.dft_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [show -(r * k) - s * k' = -(r * k) + -(s * k') by ring,
    AddChar.map_add_eq_mul]
  ring

/-- Applying inverse DFTs in both variables recovers the same-bin kernel. -/
theorem inverse_crossSpectrum [NeZero N]
    (word : ZMod N → Option (Fin κ)) (r s : ZMod N) :
    𝓕⁻ (fun k' : ZMod N =>
      𝓕⁻ (fun k : ZMod N => crossSpectrum word k k') r) s =
        sameBinKernel word r s := by
  have houter (k' : ZMod N) :
      𝓕⁻ (fun k : ZMod N => crossSpectrum word k k') r =
        𝓕 (fun s : ZMod N => sameBinKernel word r s) k' := by
    have hfun : (fun k : ZMod N => crossSpectrum word k k') =
        𝓕 (fun r : ZMod N =>
          𝓕 (fun s : ZMod N => sameBinKernel word r s) k') := by
      funext k
      exact crossSpectrum_eq_dft_dft word k k'
    rw [hfun, LinearEquiv.symm_apply_apply]
  simp_rw [houter]
  rw [LinearEquiv.symm_apply_apply]

/-- Pointwise two-dimensional inversion with both normalization factors
visible. -/
theorem sameBinKernel_eq_inverse_sum [NeZero N]
    (word : ZMod N → Option (Fin κ)) (r s : ZMod N) :
    sameBinKernel word r s =
      (N : ℂ)⁻¹ * ∑ k' : ZMod N, stdAddChar (k' * s) *
        ((N : ℂ)⁻¹ * ∑ k : ZMod N,
          stdAddChar (k * r) * crossSpectrum word k k') := by
  have h := inverse_crossSpectrum word r s
  rw [ZMod.invDFT_apply] at h
  simp only [smul_eq_mul] at h
  simp_rw [ZMod.invDFT_apply] at h
  simp only [smul_eq_mul] at h
  exact h.symm

/-! ## Symmetries and the vanishing total -/

theorem sameBinKernel_symmetric [NeZero N]
    (word : ZMod N → Option (Fin κ)) (r s : ZMod N) :
    sameBinKernel word r s = sameBinKernel word s r := by
  simp only [sameBinKernel]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem crossSpectrum_symmetric [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k k' : ZMod N) :
    crossSpectrum word k k' = crossSpectrum word k' k := by
  simp only [crossSpectrum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Reversing one frequency conjugates a real bin indicator transform. -/
theorem star_binFourier [NeZero N]
    (word : ZMod N → Option (Fin κ)) (d : Fin κ) (x : ZMod N) :
    starRingEnd ℂ (binFourier word d x) = binFourier word d (-x) := by
  simp only [binFourier, setFourier, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [starRingEnd_apply, neg_neg, mul_neg] using
    (AddChar.map_neg_eq_conj (stdAddChar (N := N)) (-(r * x))).symm

/-- Conjugation reverses both frequencies for every real digit partition. -/
theorem star_crossSpectrum [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k k' : ZMod N) :
    starRingEnd ℂ (crossSpectrum word k k') =
      crossSpectrum word (-k) (-k') := by
  classical
  simp only [crossSpectrum, map_sum, map_mul, star_binFourier]

/-- A complement-reflection invariant kernel makes the transform invariant
under simultaneous frequency negation. -/
theorem crossSpectrum_neg_of_kernel_neg [NeZero N]
    (word : ZMod N → Option (Fin κ))
    (hneg : ∀ r s, sameBinKernel word (-r) (-s) =
      sameBinKernel word r s) (k k' : ZMod N) :
    crossSpectrum word (-k) (-k') = crossSpectrum word k k' := by
  rw [crossSpectrum_eq_kernel_transform,
    crossSpectrum_eq_kernel_transform]
  apply Fintype.sum_equiv (Equiv.neg (ZMod N))
  intro r
  apply Fintype.sum_equiv (Equiv.neg (ZMod N))
  intro s
  simp only [Equiv.neg_apply, hneg]
  congr 1
  congr 1
  all_goals ring

/-- Under complement reflection every cross-spectrum entry is real. -/
theorem crossSpectrum_isReal_of_kernel_neg [NeZero N]
    (word : ZMod N → Option (Fin κ))
    (hneg : ∀ r s, sameBinKernel word (-r) (-s) =
      sameBinKernel word r s) (k k' : ZMod N) :
    starRingEnd ℂ (crossSpectrum word k k') = crossSpectrum word k k' := by
  rw [star_crossSpectrum, crossSpectrum_neg_of_kernel_neg word hneg]

/-- Radix complement in the intrinsic prime digit encoding. -/
theorem primeDigitWord_digit_neg {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p]
    (r : ZMod p) (hr : r ≠ 0) :
    digitBin b p (-r).val = b - 1 - digitBin b p r.val := by
  have hrpos : 0 < r.val := ZMod.val_pos.mpr hr
  have hrlt : r.val < p := r.val_lt
  have hnd : ¬p ∣ b * r.val := by
    intro h
    rcases hp.dvd_mul.mp h with hbase | hresidue
    · exact hpb hbase
    · exact (Nat.not_dvd_of_pos_of_lt hrpos hrlt) hresidue
  rw [ZMod.neg_val, if_neg hr]
  unfold digitBin
  exact NField.Alignment.ThreeTier.digit_complement
    b p r.val hb hp.pos hrpos hrlt hnd

/-- The actual prime digit kernel is invariant under simultaneous residue
negation.  This is the complement-reflection input used by the paper. -/
theorem primeDigitWord_kernel_neg {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p]
    (r s : ZMod p) :
    sameBinKernel (primeDigitWord b p hb hp.pos) (-r) (-s) =
      sameBinKernel (primeDigitWord b p hb hp.pos) r s := by
  by_cases hr : r = 0
  · subst r
    simp [sameBinKernel_eq_indicator, primeDigitWord_zero]
  by_cases hs : s = 0
  · subst s
    simp [sameBinKernel_eq_indicator, primeDigitWord_zero]
  have hnr : -r ≠ 0 := neg_ne_zero.mpr hr
  have hns : -s ≠ 0 := neg_ne_zero.mpr hs
  have hdr := primeDigitWord_digit_neg hb hp hpb r hr
  have hds := primeDigitWord_digit_neg hb hp hpb s hs
  rw [sameBinKernel_eq_indicator, sameBinKernel_eq_indicator]
  have hnoner : primeDigitWord b p hb hp.pos r ≠ none := by
    simp [primeDigitWord, hr]
  have hnones : primeDigitWord b p hb hp.pos s ≠ none := by
    simp [primeDigitWord, hs]
  have hnonenr : primeDigitWord b p hb hp.pos (-r) ≠ none := by
    simp [primeDigitWord, hnr]
  have hnonens : primeDigitWord b p hb hp.pos (-s) ≠ none := by
    simp [primeDigitWord, hns]
  have hdrlt : digitBin b p r.val < b :=
    digitBin_lt_base hb hp.pos r.val_lt
  have hdslt : digitBin b p s.val < b :=
    digitBin_lt_base hb hp.pos s.val_lt
  have heq :
      primeDigitWord b p hb hp.pos (-r) =
          primeDigitWord b p hb hp.pos (-s) ↔
        primeDigitWord b p hb hp.pos r =
          primeDigitWord b p hb hp.pos s := by
    simp only [primeDigitWord, dif_neg hr, dif_neg hs, dif_neg hnr,
      dif_neg hns, Option.some.injEq, Fin.mk.injEq]
    rw [hdr, hds]
    constructor <;> omega
  simp [heq, hnoner, hnonenr]

/-- Complement reflection makes the intrinsic prime cross-spectrum real and
symmetric. -/
theorem prime_crossSpectrum_real_symmetric {b p : ℕ}
    (hb : 0 < b) (hp : Nat.Prime p) (hpb : ¬p ∣ b) [NeZero p]
    (k k' : ZMod p) :
    starRingEnd ℂ
        (crossSpectrum (primeDigitWord b p hb hp.pos) k k') =
          crossSpectrum (primeDigitWord b p hb hp.pos) k k' ∧
      crossSpectrum (primeDigitWord b p hb hp.pos) k k' =
        crossSpectrum (primeDigitWord b p hb hp.pos) k' k := by
  exact ⟨crossSpectrum_isReal_of_kernel_neg _
      (primeDigitWord_kernel_neg hb hp hpb) k k',
    crossSpectrum_symmetric _ k k'⟩

/-- If zero is omitted, the complete two-dimensional transform has total
zero exactly as in the manuscript. -/
theorem crossSpectrum_total_eq_zero [NeZero N]
    (word : ZMod N → Option (Fin κ)) (hzero : word 0 = none) :
    ∑ k : ZMod N, ∑ k' : ZMod N, crossSpectrum word k k' = 0 := by
  have hkernel : sameBinKernel word 0 0 = 0 := by
    simp [sameBinKernel, binIndicator, hzero]
  have hsum (k' : ZMod N) :
      ∑ k : ZMod N, crossSpectrum word k k' =
        (N : ℂ) * 𝓕 (fun s : ZMod N => sameBinKernel word 0 s) k' := by
    have hfun : (fun k : ZMod N => crossSpectrum word k k') =
        𝓕 (fun r : ZMod N =>
          𝓕 (fun s : ZMod N => sameBinKernel word r s) k') := by
      funext k
      exact crossSpectrum_eq_dft_dft word k k'
    rw [hfun, ← ZMod.dft_apply_zero, ZMod.dft_dft]
    simp
  rw [Finset.sum_comm]
  simp_rw [hsum]
  rw [← Finset.mul_sum, ← ZMod.dft_apply_zero, ZMod.dft_dft]
  simp [hkernel]

/-! ## Multiplicative line slices -/

/-- The exact same-digit mass selected by multiplication by `a`. -/
def multiplicativeCollision [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N) : ℂ :=
  ∑ r : ZMod N, sameBinKernel word r (a * r)

/-- Orthogonality of the standard additive character, in the precise form
used by the line-slice proof. -/
theorem sum_stdAddChar_mul [NeZero N] (x : ZMod N) :
    ∑ k : ZMod N, stdAddChar (x * k) =
      if x = 0 then (N : ℂ) else 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N hx)

/-- Exact Fourier line-slice identity.  The explicit inverse witness avoids
hiding a field or primality assumption: the theorem holds over every cyclic
ring whenever `a` is a unit. -/
theorem multiplicative_slice [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a aInv : ZMod N)
    (hinv : a * aInv = 1) :
    multiplicativeCollision word a =
      (N : ℂ)⁻¹ * ∑ k : ZMod N,
        crossSpectrum word k (-aInv * k) := by
  classical
  have hcondition (r s : ZMod N) :
      -r + s * aInv = 0 ↔ s = a * r := by
    constructor
    · intro h
      have hsr : s * aInv = r := by linear_combination h
      calc
        s = s * (a * aInv) := by rw [hinv, mul_one]
        _ = a * (s * aInv) := by ring
        _ = a * r := by rw [hsr]
    · intro h
      rw [h]
      calc
        -r + a * r * aInv = -r + r * (a * aInv) := by ring
        _ = 0 := by rw [hinv]; ring
  rw [multiplicativeCollision]
  simp_rw [crossSpectrum_eq_kernel_transform]
  symm
  calc
    (N : ℂ)⁻¹ *
        ∑ k : ZMod N, ∑ r : ZMod N, ∑ s : ZMod N,
          sameBinKernel word r s *
            stdAddChar (-(r * k) - s * (-aInv * k)) =
      (N : ℂ)⁻¹ *
        ∑ r : ZMod N, ∑ s : ZMod N,
          sameBinKernel word r s *
            ∑ k : ZMod N, stdAddChar ((-r + s * aInv) * k) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      congr 1
      ring
    _ = (N : ℂ)⁻¹ *
        ∑ r : ZMod N, ∑ s : ZMod N,
          sameBinKernel word r s *
            (if s = a * r then (N : ℂ) else 0) := by
      simp_rw [sum_stdAddChar_mul, hcondition]
    _ = ∑ r : ZMod N, sameBinKernel word r (a * r) := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
      rw [show (∑ x : ZMod N,
          sameBinKernel word x (a * x) * (N : ℂ)) =
          (N : ℂ) * ∑ x : ZMod N,
            sameBinKernel word x (a * x) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring]
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- The slice at the identity multiplier is the antidiagonal spectral power. -/
theorem crossSpectrum_antidiagonal [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k : ZMod N) :
    crossSpectrum word k (-k) = spectralPower word k := by
  classical
  simp only [crossSpectrum, spectralPower]
  apply Finset.sum_congr rfl
  intro d _
  rw [← star_binFourier]
  ring

/-! ## Orbit aggregation and individual-orbit readout -/

/-- Collision contribution from a chosen residue orbit or arbitrary subset. -/
def subsetCollision [NeZero N]
    (word : ZMod N → Option (Fin κ))
    (S : Finset (ZMod N)) (a : ZMod N) : ℂ :=
  ∑ r ∈ S, sameBinKernel word r (a * r)

/-- Exponential sum of a chosen residue orbit. -/
noncomputable def subsetExponential [NeZero N]
    (S : Finset (ZMod N)) (m : ZMod N) : ℂ :=
  ∑ r ∈ S, stdAddChar (m * r)

/-- Exact readout for one chosen orbit or residue subset.  For an actual
multiplicative coset, `subsetExponential` is the subgroup exponential sum in
the manuscript. -/
theorem subsetCollision_formula [NeZero N]
    (word : ZMod N → Option (Fin κ))
    (S : Finset (ZMod N)) (a : ZMod N) :
    subsetCollision word S a =
      ((N : ℂ)⁻¹) ^ 2 * ∑ k : ZMod N, ∑ k' : ZMod N,
        crossSpectrum word k k' * subsetExponential S (k + a * k') := by
  classical
  unfold subsetCollision subsetExponential
  simp_rw [sameBinKernel_eq_inverse_sum]
  simp only [Finset.mul_sum]
  let F := fun (k k' r : ZMod N) =>
    ((N : ℂ)⁻¹) ^ 2 *
      (crossSpectrum word k k' * stdAddChar ((k + a * k') * r))
  have hswap :
      (∑ k : ZMod N, ∑ k' : ZMod N, ∑ r ∈ S, F k k' r) =
        ∑ r ∈ S, ∑ k' : ZMod N, ∑ k : ZMod N, F k k' r := by
    calc
      (∑ k : ZMod N, ∑ k' : ZMod N, ∑ r ∈ S, F k k' r) =
          ∑ k : ZMod N, ∑ r ∈ S, ∑ k' : ZMod N, F k k' r := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
      _ = ∑ r ∈ S, ∑ k : ZMod N, ∑ k' : ZMod N, F k k' r := by
            rw [Finset.sum_comm]
      _ = ∑ r ∈ S, ∑ k' : ZMod N, ∑ k : ZMod N, F k k' r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_comm]
  change (∑ r ∈ S, ∑ k' : ZMod N, ∑ k : ZMod N,
      (N : ℂ)⁻¹ * (stdAddChar (k' * (a * r)) *
        ((N : ℂ)⁻¹ * (stdAddChar (k * r) * crossSpectrum word k k')))) =
    ∑ k : ZMod N, ∑ k' : ZMod N, ∑ r ∈ S, F k k' r
  rw [hswap]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k' _
  apply Finset.sum_congr rfl
  intro k _
  unfold F
  rw [show (k + a * k') * r = k * r + k' * (a * r) by ring,
    AddChar.map_add_eq_mul]
  ring

/-- Splitting the residue set into disjoint named pieces splits the aggregate
collision count into the corresponding orbit contributions. -/
theorem collision_aggregation [NeZero N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (word : ZMod N → Option (Fin κ)) (orbitOf : ZMod N → ι)
    (a : ZMod N) :
    multiplicativeCollision word a =
      ∑ c : ι, subsetCollision word
        (Finset.univ.filter fun r => orbitOf r = c) a := by
  classical
  unfold multiplicativeCollision subsetCollision
  symm
  calc
    (∑ c : ι, ∑ r ∈ Finset.univ.filter (fun r => orbitOf r = c),
        sameBinKernel word r (a * r)) =
      ∑ c : ι, ∑ r : ZMod N,
        if orbitOf r = c then sameBinKernel word r (a * r) else 0 := by
          simp_rw [Finset.sum_filter]
    _ = ∑ r : ZMod N, ∑ c : ι,
        if orbitOf r = c then sameBinKernel word r (a * r) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ r : ZMod N, sameBinKernel word r (a * r) := by
          apply Finset.sum_congr rfl
          intro r _
          simp

/-! ## Full remainder orbits -/

/-- Nonzero residues, the state space visited by a primitive remainder orbit. -/
abbrev NonzeroResidue (N : ℕ) := {r : ZMod N // r ≠ 0}

/-- The aggregate multiplicative collision count restricted to nonzero
residues. -/
def nonzeroMultiplicativeCollision [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N) : ℂ :=
  ∑ r : NonzeroResidue N, sameBinKernel word r.val (a * r.val)

/-- Omitting residue zero makes the full and nonzero collision sums equal. -/
theorem multiplicativeCollision_eq_nonzero [NeZero N]
    (word : ZMod N → Option (Fin κ)) (a : ZMod N)
    (hzero : word 0 = none) :
    multiplicativeCollision word a = nonzeroMultiplicativeCollision word a := by
  unfold multiplicativeCollision nonzeroMultiplicativeCollision
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun r : ZMod N =>
    sameBinKernel word r (a * r)) 0]
  simp [sameBinKernel, binIndicator, hzero]

/-- Autocorrelation read directly from a cyclic enumeration of every nonzero
residue. -/
def fullOrbitAutocorrelation {G : Type*} [Fintype G] [AddCommGroup G]
    [NeZero N] (word : ZMod N → Option (Fin κ))
    (orbit : G ≃ NonzeroResidue N) (lag : G) : ℂ :=
  ∑ t : G, sameBinKernel word (orbit t).val (orbit (t + lag)).val

/-- The primitive-root hypothesis is used only through its consequence that
the cyclic remainder map enumerates every nonzero residue and advances by the
lag multiplier. -/
theorem fullOrbitAutocorrelation_eq_collision
    {G : Type*} [Fintype G] [AddCommGroup G] [NeZero N]
    (word : ZMod N → Option (Fin κ)) (orbit : G ≃ NonzeroResidue N)
    (lag : G) (a : ZMod N) (hzero : word 0 = none)
    (hmotion : ∀ t, (orbit (t + lag)).val = a * (orbit t).val) :
    fullOrbitAutocorrelation word orbit lag =
      multiplicativeCollision word a := by
  rw [multiplicativeCollision_eq_nonzero word a hzero]
  unfold fullOrbitAutocorrelation nonzeroMultiplicativeCollision
  apply Fintype.sum_equiv orbit
  intro t
  rw [hmotion]

/-- The paper's autocorrelation formula, with the primitive-root content
factored into the explicit full-orbit parametrization and motion law. -/
theorem fullOrbit_autocorrelation_slice
    {G : Type*} [Fintype G] [AddCommGroup G] [NeZero N]
    (word : ZMod N → Option (Fin κ)) (orbit : G ≃ NonzeroResidue N)
    (lag : G) (a aInv : ZMod N) (hzero : word 0 = none)
    (hmotion : ∀ t, (orbit (t + lag)).val = a * (orbit t).val)
    (hinv : a * aInv = 1) :
    fullOrbitAutocorrelation word orbit lag =
      (N : ℂ)⁻¹ * ∑ k : ZMod N,
        crossSpectrum word k (-aInv * k) := by
  rw [fullOrbitAutocorrelation_eq_collision word orbit lag a hzero hmotion]
  exact multiplicative_slice word a aInv hinv

/-! ## Cyclic word energies and the decimal-seven certificate -/

/-- The exact cyclic equality autocorrelation used for a remainder word. -/
def cyclicDigitAutocorrelation {L : ℕ}
    (word : ZMod L → Option (Fin κ)) [NeZero L] (lag : ZMod L) : ℕ :=
  additiveCollision word lag

/-- Fourier transformation of cyclic autocorrelation gives the nonnegative
sum of coordinate magnitudes, retaining all phase before the sum is taken. -/
theorem cyclic_autocorrelation_transform {L : ℕ} [NeZero L]
    (word : ZMod L → Option (Fin κ)) (j : ZMod L) :
    𝓕 (fun lag => (cyclicDigitAutocorrelation word lag : ℂ)) j =
      spectralPower word j :=
  dft_additiveCollision word j

/-- Spectral power is visibly a sum of squared complex norms. -/
theorem spectralPower_eq_sum_norm_sq [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k : ZMod N) :
    spectralPower word k =
      ∑ d : Fin κ, ((‖binFourier word d k‖ ^ 2 : ℝ) : ℂ) := by
  simp [spectralPower, Complex.conj_mul']

theorem spectralPower_re_eq_sum_norm_sq [NeZero N]
    (word : ZMod N → Option (Fin κ)) (k : ZMod N) :
    (spectralPower word k).re =
      ∑ d : Fin κ, ‖binFourier word d k‖ ^ 2 := by
  rw [spectralPower_eq_sum_norm_sq]
  simp [pow_two, Complex.mul_re]

/-- The normalized cyclic harmonic energy is real and nonnegative. -/
theorem cyclic_harmonic_energy_nonnegative {L : ℕ} [NeZero L]
    (word : ZMod L → Option (Fin κ)) (j : ZMod L) :
    0 ≤ (((L : ℂ)⁻¹ *
      𝓕 (fun lag => (cyclicDigitAutocorrelation word lag : ℂ)) j).re) := by
  rw [cyclic_autocorrelation_transform, Complex.mul_re,
    spectralPower_re_eq_sum_norm_sq]
  norm_num
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro d _
    positivity

/-- The decimal repetend modulo seven in cyclic remainder order. -/
def decimalSevenWord : Fin 6 → Fin 10 :=
  ![1, 4, 2, 8, 5, 7]

/-- The word `142857` agrees with itself at all six places only at zero lag
and at no place at every nonzero cyclic lag. -/
theorem decimalSevenAutocorrelation_certificate :
    ∀ lag : Fin 6,
      NField.Alignment.CrossAlignmentMatrix.crossCorrelation
          decimalSevenWord decimalSevenWord lag =
        if lag = 0 then 6 else 0 := by
  decide

end NField.Alignment.AutocorrelationFormula
