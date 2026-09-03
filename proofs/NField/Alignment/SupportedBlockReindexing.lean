/-
Author: Alexander S. Petty
-/

import NField.Alignment.SupportedBlockSpectrum
import NField.Alignment.SynchronizedCrossAlignment

/-!
# Reindexing supported lifts by synchronized residue blocks

This module constructs the literal permutation between positive proper
numerators below `p * s` and the terminating plus nonterminating block index.
It then identifies the synchronized matrix with the direct sum of all-ones
blocks under the digit-partitioning hypotheses.
-/

namespace NField.Alignment.SupportedBlockReindexing

open scoped BigOperators
open NField.Alignment
open NField.Alignment.CoherenceDecomposition
open NField.Alignment.CrossAlignmentMatrix
open NField.Alignment.SynchronizedCrossAlignment
open NField.Alignment.ThreeTier

/-- Natural numerator represented by a supported-block coordinate. -/
def supportedBlockNumeratorValue {p s : ℕ} : SupportedBlockIndex p s → ℕ
  | Sum.inl i => p * (i.val + 1)
  | Sum.inr ci => p * ci.2.val + (ci.1.val + 1)

theorem supportedBlockNumeratorValue_pos {p s : ℕ} (hp : 0 < p)
    (i : SupportedBlockIndex p s) : 0 < supportedBlockNumeratorValue i := by
  cases i with
  | inl i => simp [supportedBlockNumeratorValue, hp]
  | inr ci => simp [supportedBlockNumeratorValue]

theorem supportedBlockNumeratorValue_lt {p s : ℕ} (hp : 0 < p)
    (i : SupportedBlockIndex p s) : supportedBlockNumeratorValue i < p * s := by
  cases i with
  | inl i =>
      have hi : i.val + 1 < s := by omega
      exact Nat.mul_lt_mul_of_pos_left hi hp
  | inr ci =>
      have hc : ci.1.val + 1 < p := by omega
      have hi : ci.2.val + 1 ≤ s := by omega
      calc
        p * ci.2.val + (ci.1.val + 1) < p * ci.2.val + p :=
          Nat.add_lt_add_left hc _
        _ = p * (ci.2.val + 1) := by ring
        _ ≤ p * s := Nat.mul_le_mul_left p hi

/-- The actual positive proper numerator attached to a block coordinate. -/
def supportedBlockNumerator {p s : ℕ} (hp : 0 < p)
    (i : SupportedBlockIndex p s) : ProperNumerator (p * s) :=
  ⟨supportedBlockNumeratorValue i - 1, by
    have hpos := supportedBlockNumeratorValue_pos hp i
    have hlt := supportedBlockNumeratorValue_lt hp i
    omega⟩

@[simp] theorem numeratorValue_supportedBlockNumerator
    {p s : ℕ} (hp : 0 < p) (i : SupportedBlockIndex p s) :
    numeratorValue (supportedBlockNumerator hp i) =
      supportedBlockNumeratorValue i := by
  unfold numeratorValue supportedBlockNumerator
  exact Nat.sub_add_cancel (supportedBlockNumeratorValue_pos hp i)

/-- Distinct block coordinates give distinct literal numerators. -/
theorem supportedBlockNumeratorValue_injective {p s : ℕ} (hp : 0 < p) :
    Function.Injective
      (supportedBlockNumeratorValue : SupportedBlockIndex p s → ℕ) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [supportedBlockNumeratorValue] at hij
          have h := Nat.eq_of_mul_eq_mul_left hp hij
          exact congrArg Sum.inl (Fin.ext (Nat.add_right_cancel h))
      | inr cj =>
          have hc : cj.1.val + 1 < p := by omega
          have hmod := congrArg (fun z => z % p) hij
          simp [supportedBlockNumeratorValue, Nat.add_mod,
            Nat.mod_eq_of_lt hc] at hmod
  | inr ci =>
      cases j with
      | inl j =>
          have hc : ci.1.val + 1 < p := by omega
          have hmod := congrArg (fun z => z % p) hij
          simp [supportedBlockNumeratorValue, Nat.add_mod,
            Nat.mod_eq_of_lt hc] at hmod
      | inr cj =>
          have hci : ci.1.val + 1 < p := by omega
          have hcj : cj.1.val + 1 < p := by omega
          have hmod := congrArg (fun z => z % p) hij
          simp [supportedBlockNumeratorValue, Nat.add_mod,
            Nat.mod_eq_of_lt hci, Nat.mod_eq_of_lt hcj] at hmod
          have hcEq : ci.1 = cj.1 := Fin.ext hmod
          apply congrArg Sum.inr
          apply Prod.ext hcEq
          apply Fin.ext
          simp only [supportedBlockNumeratorValue] at hij
          have hmul : p * ci.2.val = p * cj.2.val := by omega
          exact Nat.eq_of_mul_eq_mul_left hp hmul

/-- The block-coordinate map into proper numerators is injective. -/
theorem supportedBlockNumerator_injective {p s : ℕ} (hp : 0 < p) :
    Function.Injective (supportedBlockNumerator (s := s) hp) := by
  intro i j hij
  apply supportedBlockNumeratorValue_injective hp
  simpa using congrArg numeratorValue hij

/-- The block index and the proper-numerator index have the same exact finite
cardinality. -/
theorem supportedBlockIndex_card {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    Fintype.card (SupportedBlockIndex p s) =
      Fintype.card (ProperNumerator (p * s)) := by
  simp only [SupportedBlockIndex, ProperNumerator, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_prod]
  rw [Nat.sub_mul, one_mul]
  have hsp : s ≤ p * s := by
    simpa [one_mul] using Nat.mul_le_mul_right s hp
  omega

/-- Exact permutation from synchronized block coordinates to literal positive
proper numerators. -/
noncomputable def supportedBlockEquivProperNumerator
    {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    SupportedBlockIndex p s ≃ ProperNumerator (p * s) :=
  Equiv.ofBijective (supportedBlockNumerator hp)
    ((Fintype.bijective_iff_injective_and_card
      (supportedBlockNumerator hp)).2
        ⟨supportedBlockNumerator_injective hp,
          supportedBlockIndex_card hp hs⟩)

@[simp] theorem supportedBlockEquivProperNumerator_apply
    {p s : ℕ} (hp : 0 < p) (hs : 0 < s)
    (i : SupportedBlockIndex p s) :
    supportedBlockEquivProperNumerator hp hs i =
      supportedBlockNumerator hp i := by
  simp [supportedBlockEquivProperNumerator]

/-- The rough-residue digit after clearing is the ordinary prime digit
started from the cleared numerator residue. -/
theorem periodicDigit_eq_digitAt_mul_clearing
    (b p u k position : ℕ) :
    periodicDigit b p u (k % p) position =
      digitAt b p ((k * u) % p) position := by
  unfold periodicDigit periodicResidue digitAt
  congr 1
  calc
    ((b ^ position * u) * (k % p)) % p =
        ((b ^ position * u) * k) % p :=
      NField.CollisionDefinition.transportedRemainder_mod_right
        p (b ^ position * u) k
    _ = (b ^ position * (k * u)) % p := by ring_nf
    _ = (b ^ position * ((k * u) % p)) % p :=
      (NField.CollisionDefinition.transportedRemainder_mod_right
        p (b ^ position) (k * u)).symm

/-- Under digit partitioning, two nonterminating proper numerators have equal
literal synchronized digits exactly when their rough residues agree. -/
theorem clearedPairMatchAt_iff_same_residue
    {b p s D : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hs : 0 < s) (hD : s ∣ b ^ D)
    (i j : ProperNumerator (p * s))
    (hi : ¬p ∣ numeratorValue i) (hj : ¬p ∣ numeratorValue j)
    (position : ℕ) :
    clearedPairMatchAt b (p * s) D i j position ↔
      numeratorValue i % p = numeratorValue j % p := by
  have hu := prime_coprime_clearingCofactor hp hpb hD
  have hri : numeratorValue i % p ≠ 0 := by
    exact mt Nat.dvd_of_mod_eq_zero hi
  have hrj : numeratorValue j % p ≠ 0 := by
    exact mt Nat.dvd_of_mod_eq_zero hj
  have hsync := synchronizedPairAlignedAtPosition_iff_same_residue
    hp hpb hdp hu (j := numeratorValue i) (k := numeratorValue j)
      (position := position)
  unfold clearedPairMatchAt
  rw [clearedDigit_eq_periodicDigit hs hD,
    clearedDigit_eq_periodicDigit hs hD,
    periodicDigit_eq_digitAt_mul_clearing,
    periodicDigit_eq_digitAt_mul_clearing]
  simpa [synchronizedPairAlignedAtPosition, hri, hrj] using hsync

/-- Exact full-window digit count in the digit-partitioning supported lift. -/
theorem clearedPairMatchCount_of_digitPartitioning
    {b p s D L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hs : 0 < s) (hD : s ∣ b ^ D)
    (i j : ProperNumerator (p * s))
    (hi : ¬p ∣ numeratorValue i) (hj : ¬p ∣ numeratorValue j) :
    clearedPairMatchCount b (p * s) D L i j =
      if numeratorValue i % p = numeratorValue j % p then L else 0 := by
  classical
  unfold clearedPairMatchCount
  simp_rw [clearedPairMatchAt_iff_same_residue hp hpb hdp hs hD i j hi hj]
  by_cases hres : numeratorValue i % p = numeratorValue j % p
  · simp [hres]
  · simp [hres]

/-- Real form of the exact all-ones block matrix. -/
noncomputable def supportedBlockMatrixReal (p s : ℕ) :
    Matrix (SupportedBlockIndex p s) (SupportedBlockIndex p s) ℝ :=
  (supportedBlockMatrix p s).map (Rat.castHom ℝ)

/-- The literal synchronized matrix of a digit-partitioning supported lift is
permutation-similar to the exact terminating and residue all-ones blocks. -/
theorem synchronizedCrossAlignmentMatrix_reindex_eq_supportedBlockMatrix
    {b p s D L : ℕ} (hp : Nat.Prime p) (hpb : ¬p ∣ b)
    (hdp : DigitPartitioning b p) (hs : 0 < s) (hD : s ∣ b ^ D)
    (hL : 0 < L) :
    Matrix.reindex (supportedBlockEquivProperNumerator hp.pos hs).symm
        (supportedBlockEquivProperNumerator hp.pos hs).symm
        (synchronizedCrossAlignmentMatrix b (p * s) p D L) =
      supportedBlockMatrixReal p s := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  simp only [supportedBlockEquivProperNumerator_apply]
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [synchronizedCrossAlignmentMatrix,
            supportedBlockMatrixReal, supportedBlockMatrix,
            supportedBlockNumeratorValue]
      | inr cj =>
          have hc : cj.1.val + 1 < p := by omega
          have hnon : ¬p ∣ p * cj.2.val + (cj.1.val + 1) := by
            rw [Nat.dvd_iff_mod_eq_zero]
            simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
          simp [synchronizedCrossAlignmentMatrix,
            supportedBlockMatrixReal, supportedBlockMatrix,
            supportedBlockNumeratorValue, hnon]
  | inr ci =>
      cases j with
      | inl j =>
          have hc : ci.1.val + 1 < p := by omega
          have hnon : ¬p ∣ p * ci.2.val + (ci.1.val + 1) := by
            rw [Nat.dvd_iff_mod_eq_zero]
            simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
          simp [synchronizedCrossAlignmentMatrix,
            supportedBlockMatrixReal, supportedBlockMatrix,
            supportedBlockNumeratorValue, hnon]
      | inr cj =>
          have hci : ci.1.val + 1 < p := by omega
          have hcj : cj.1.val + 1 < p := by omega
          have hni : ¬p ∣ p * ci.2.val + (ci.1.val + 1) := by
            rw [Nat.dvd_iff_mod_eq_zero]
            simp [Nat.add_mod, Nat.mod_eq_of_lt hci]
          have hnj : ¬p ∣ p * cj.2.val + (cj.1.val + 1) := by
            rw [Nat.dvd_iff_mod_eq_zero]
            simp [Nat.add_mod, Nat.mod_eq_of_lt hcj]
          have hni' : ¬p ∣ numeratorValue
              (supportedBlockNumerator hp.pos (Sum.inr ci)) := by
            simpa [supportedBlockNumeratorValue] using hni
          have hnj' : ¬p ∣ numeratorValue
              (supportedBlockNumerator hp.pos (Sum.inr cj)) := by
            simpa [supportedBlockNumeratorValue] using hnj
          unfold synchronizedCrossAlignmentMatrix
          rw [if_neg hni', if_neg hnj']
          rw [clearedPairMatchCount_of_digitPartitioning
            hp hpb hdp hs hD _ _ hni' hnj']
          by_cases hc : ci.1 = cj.1
          · simp [supportedBlockMatrixReal, supportedBlockMatrix,
              supportedBlockNumeratorValue, Nat.add_mod,
              Nat.mod_eq_of_lt hcj, hc, hL.ne']
          · have hcval : ci.1.val ≠ cj.1.val := by
              intro h
              exact hc (Fin.ext h)
            simp [supportedBlockMatrixReal, supportedBlockMatrix,
              supportedBlockNumeratorValue, Nat.add_mod,
              Nat.mod_eq_of_lt hci, Nat.mod_eq_of_lt hcj,
              hc, hcval]

end NField.Alignment.SupportedBlockReindexing
