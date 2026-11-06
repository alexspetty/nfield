/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealBernoulliBoundaryLimits
import NField.Alignment.ComplementaryHalfPacket

/-! # The literal real Dedekind Gram kernel and its half packet -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealDedekindGram
open scoped BigOperators Classical
open CollisionDedekindPairing RealBernoulliBoundaryLimits RademacherThreeTerm
  DedekindCollisionKernel ComplementaryPartition ComplementaryHalfPacket

def realGram (m r s : ℕ) : ℝ :=
  ∑ A ∈ Finset.range m,
    periodicSawtooth ((r : ℝ)*A/m)*periodicSawtooth ((s : ℝ)*A/m)

/-- Title: `The literal real Dedekind Gram kernel`. -/
theorem realGram_eq_arithmetic {m : ℕ} (hm : 0 < m) (r s : ℕ) :
    realGram m r s = (arithmeticCoefficientDedekindTerm r s m : ℝ) := by
  unfold realGram arithmeticCoefficientDedekindTerm
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Nat.cast_mul,← Nat.cast_mul,sawtooth_rational (r*A) m hm,
    sawtooth_rational (s*A) m hm]

/-- Title: `Real discrete pair correlation as a unit-ratio Dedekind sum`. -/
theorem realGram_eq_ratio {m r s : ℕ} (hm : 0 < m)
    (hr : r.Coprime m) (hs : s.Coprime m) :
    letI : NeZero m := ⟨hm.ne'⟩
    realGram m r s =
      (dedekindSum ((ZMod.unitOfCoprime s hs)*(ZMod.unitOfCoprime r hr)⁻¹)).re := by
  letI : NeZero m := ⟨hm.ne'⟩
  have h := congrArg Complex.re (arithmeticCoefficientDedekindTerm_eq_ratio hr hs)
  rw [realGram_eq_arithmetic hm]
  simpa only [coefficientDedekindTerm,Complex.ratCast_re,mul_comm] using h

theorem real_discrete_pair_correlation {m r s : ℕ} (hm : 0 < m)
    (hr : r.Coprime m) (hs : s.Coprime m) :
    letI : NeZero m := ⟨hm.ne'⟩
    (∑ A ∈ Finset.range m,
      periodicSawtooth ((r : ℝ)*A/m)*periodicSawtooth ((s : ℝ)*A/m))/(m : ℝ) =
      (dedekindSum ((ZMod.unitOfCoprime s hs)*(ZMod.unitOfCoprime r hr)⁻¹)).re/m := by
  letI : NeZero m := ⟨hm.ne'⟩
  change realGram m r s / m = _
  rw [realGram_eq_ratio hm hr hs]

/-- Title: `The partition packet as the literal real half Gram sum`. -/
theorem partition_packet_real_half {m X : ℕ} [NeZero X] (hm : 0 < m)
    (hX : 3 ≤ X) :
    (partitionPacket m X : ℝ) =
      ∑ k ∈ (Finset.Ico 1 X).filter (fun k => k.Coprime X ∧ 2*k<X),
        realGram m k (X-k) := by
  rw [partition_packet_half hX]
  unfold halfPartitionPacket
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  exact (realGram_eq_arithmetic hm k (X-k)).symm

end NField.Alignment.RealDedekindGram
