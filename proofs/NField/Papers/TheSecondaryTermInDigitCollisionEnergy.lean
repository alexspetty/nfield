/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.BernoulliAbelLimit
import NField.Alignment.BernoulliAbelPhase
import NField.Alignment.BernoulliAbelSeries
import NField.Alignment.BernoulliFourierIdentity
import NField.Alignment.BernoulliSmoothingFourier
import NField.Alignment.BernoulliSymmetricSmoothing
import NField.Alignment.BoundaryDistributionalDerivative
import NField.Alignment.BoundaryFourierCoefficients
import NField.Alignment.BoundaryJumpFlux
import NField.Alignment.CarrierDwellCounts
import NField.Alignment.CarrierPrefixPeriod
import NField.Alignment.CarrierTriangularIdentity
import NField.Alignment.ComplementaryHalfPacket
import NField.Alignment.ComplementaryHalfSums
import NField.Alignment.CotangentDedekindFormula
import NField.Alignment.CotangentGrid
import NField.Alignment.CotangentOrbitBound
import NField.Alignment.CyclicLogarithmicLadder
import NField.Alignment.DivisorHarmonicMain
import NField.Alignment.DivisorHyperbolaIdentity
import NField.Alignment.DivisorSawtoothIdentity
import NField.Alignment.DivisorSmoothingScales
import NField.Alignment.DivisorVoronoiEstimate
import NField.Alignment.DivisorWindowCount
import NField.Alignment.DivisorWindowPairing
import NField.Alignment.DivisorWindowResidue
import NField.Alignment.FejerSmallArc
import NField.Alignment.FiniteDifferenceEnergy
import NField.Alignment.FiniteDifferenceRows
import NField.Alignment.HalfPacketSignGeometry
import NField.Alignment.IntegerCotangentTransforms
import NField.Alignment.IntegerDedekindTransform
import NField.Alignment.IntegerFullTransformBound
import NField.Alignment.IntegerInversePrefix
import NField.Alignment.IntegerInverseResidue
import NField.Alignment.IntegerInverseSeriesLiteral
import NField.Alignment.IntegerNumeratorDescent
import NField.Alignment.IntegerSignedDamping
import NField.Alignment.IntegerTransformBounds
import NField.Alignment.JordanCapacityFormula
import NField.Alignment.KorolevRealCutoff
import NField.Alignment.KorolevShortRangeAsymptotic
import NField.Alignment.KorolevWeakRange
import NField.Alignment.MobiusLogarithmicMain
import NField.Alignment.PrimeSquareGridSeparation
import NField.Alignment.QuadraticWeakDerivative
import NField.Alignment.RealBernoulliBoundaryLimits
import NField.Alignment.RealBernoulliCapacityIntegral
import NField.Alignment.RealBernoulliJumpData
import NField.Alignment.RealBoundaryUniformCells
import NField.Alignment.RealCarrierGridAlias
import NField.Alignment.RealDedekindGram
import NField.Alignment.RealFractionalFirstMoment
import NField.Alignment.RealLogWeightedFractionalParts
import NField.Alignment.RealSaffariVaughanDistribution
import NField.Alignment.RealSawtoothDistribution
import NField.Alignment.RealSawtoothIntegralSymmetry
import NField.Alignment.RealSawtoothLimits
import NField.Alignment.RealSawtoothPairIntegral
import NField.Alignment.ReciprocalArcBlock
import NField.Alignment.ReciprocalDifferenceBound
import NField.Alignment.ReciprocalFloorSmoothing
import NField.Alignment.ReciprocalMomentEulerFactor
import NField.Alignment.ReciprocalMomentInfiniteSeries
import NField.Alignment.ReciprocalSawtoothGlobal
import NField.Alignment.ReciprocalSawtoothSmoothing
import NField.Alignment.ReciprocalSecondMoment
import NField.Alignment.ReciprocalSmoothedBlock
import NField.Alignment.ReciprocalSmoothingCutoff
import NField.Alignment.RemovedCarrierLogBound
import NField.Alignment.SecondaryCarrierExample
import NField.Alignment.SecondaryCarrierLogarithmicBounds
import NField.Alignment.SecondaryCollarBounds
import NField.Alignment.SecondaryCurvatureBounds
import NField.Alignment.SecondaryEulerHarmonicSeries
import NField.Alignment.SecondaryFiniteConsequences
import NField.Alignment.SecondaryLocalizationUnconditional
import NField.Alignment.SecondaryPrintedBounds
import NField.Alignment.SecondaryRealFractionalParts
import NField.Alignment.SecondaryRealStraightening
import NField.Alignment.SecondaryReservoirIntermediate
import NField.Alignment.SecondarySamplingAsymptotics
import NField.Alignment.SecondarySeriesConsequences
import NField.Alignment.SecondarySwitchingLedger
import NField.Alignment.SecondaryTermUnconditional
import NField.Alignment.SignedDivisorWindow
import NField.Alignment.SmoothingCoefficientSums
import NField.Alignment.SmoothingFiniteFrequency
import NField.Alignment.SmoothingSeriesBounds
import NField.Alignment.SquareLockAsymptoticScales
import NField.Alignment.SquareLockCountBound
import NField.Alignment.SquareLockCountScales
import NField.Alignment.SquareLockCutoffLimits
import NField.Alignment.SquareLockDivisorInjection
import NField.Alignment.SquareLockRemainingStrip
import NField.Alignment.SquareLockResidueArc
import NField.Alignment.TriangularAdditiveConvolution
import NField.Alignment.KorolevRangeEstimate
import NField.Alignment.KorolevCanonicalTruncatedPrefix
import NField.Alignment.KorolevUncutPrimeRectangle
import NField.Alignment.KorolevCanonicalSawtoothSlices
import NField.Alignment.KorolevSourceLogarithmicPartition
import NField.Alignment.KorolevBlockResidualVolume
import NField.Alignment.KorolevCanonicalInversePrefix
import NField.Alignment.KaratsubaSourceCancellation
import NField.Alignment.KaratsubaWindowMomentRange
import NField.Alignment.KorolevSourceWindowDensity
import NField.Alignment.KaratsubaProductPhase
import NField.Alignment.KaratsubaJointPopulation
import NField.Alignment.BernoulliCurvature
import NField.Alignment.CarrierJumpData
import NField.Alignment.CarrierSamplingReservoir
import NField.Alignment.CarrierStateSwitching
import NField.Alignment.CollisionBernoulliStraightening
import NField.Alignment.ComplementaryPartition
import NField.Alignment.CyclicCorrelationReservoir
import NField.Alignment.DedekindInverseResidueTransform
import NField.Alignment.InverseResiduePrefixCompletion
import NField.Alignment.InverseResidueHarmonicRangeSplit
import NField.Alignment.ExactSamplingReservoirBridge
import NField.Alignment.EndpointReservoirAlias
import NField.Alignment.EndpointReciprocityBridge
import NField.Alignment.GcdLcmCapacity
import NField.Alignment.PrimitiveAdditiveConvolution
import NField.Alignment.PrimeSecondaryCoefficient
import NField.Alignment.PrimeCarrierDamping
import NField.Alignment.SquareLockCarrierMass
import NField.Alignment.LiveCarrierDamping
import NField.Alignment.ReducedHarmonicMobius
import NField.Alignment.ReciprocalDivisorMomentBound
import NField.Alignment.SecondaryCapacityAnalyticInputs
import NField.Alignment.CompletedPrefixDivisorGrowth
import NField.Alignment.InverseAdditiveCompletion
import NField.Alignment.StepanovAuxiliary
import NField.Alignment.StepanovConstraintSpace
import NField.Alignment.StepanovPointCount
import NField.Alignment.KloostermanTraceSum
import NField.Alignment.KloostermanQuadraticLSeries
import NField.Alignment.KloostermanPrimePowerCoefficients
import NField.Alignment.KloostermanRootPowerAggregate
import NField.Alignment.KloostermanPrimeBound
import NField.Alignment.PrimePowerUnitFibers
import NField.Alignment.KloostermanEvenPrimePowerBound
import NField.Alignment.QuadraticAdditiveGauss
import NField.Alignment.CubeZeroUnitShift
import NField.Alignment.KloostermanOddPrimePowerBound
import NField.Alignment.PrimePowerContentReduction
import NField.Alignment.KloostermanGlobalBound
import NField.Alignment.KorolevFirstExclusion
import NField.Alignment.KorolevPrimeIntervals
import NField.Alignment.KorolevQuotientSieve
import NField.Alignment.KorolevMissingPrimeDecay
import NField.Alignment.KorolevSelectedPrimeCount
import NField.Alignment.KorolevSourceWindowCount
import NField.Alignment.KorolevLemmaA
import NField.Alignment.KaratsubaPrimeMoment
import NField.Alignment.KaratsubaScaledFourierMoment

/-!
# The Secondary Term in Digit-Collision Energy

## Coverage

The 35 proof-bearing statements and 194 displays are covered, including the
five analytic inputs, real-variable identities, endpoint cases and
signed-frequency formulas. Conditional signed damping, the sharpened capacity
premise and the three correlation implications retain their assumptions. The
proposed sampling limit remains open.

## Scope and assumptions

The five analytic inputs are proved. Conditional signed damping, the separate
sharpened-capacity premise and the three correlation implications retain their
stated assumptions. Endpoint cases and signed frequencies keep their original
parameter ranges. The proposed sampling limit remains an open question. The 36
rounded table cells have a separate computed reproduction; they are not Lean
interval certificates.
-/

namespace NField.Papers.TheSecondaryTermInDigitCollisionEnergy

open scoped BigOperators ZMod
open NField.Alignment.CarrierSamplingReservoir
open NField.Alignment.BernoulliCurvature
open NField.Alignment.CarrierJumpData
open NField.Alignment.CarrierStateSwitching
open NField.Alignment.CollisionBernoulliStraightening
open NField.Alignment.ComplementaryPartition
open NField.Alignment.CyclicCorrelationReservoir
open NField.Alignment.DedekindInverseResidueTransform
open NField.Alignment.InverseResiduePrefixCompletion
open NField.Alignment.InverseResidueHarmonicRangeSplit
open NField.Alignment.DedekindAbelRemainder
open NField.Alignment.DedekindFourierMoment
open NField.Alignment.GcdLcmCapacity
open NField.Alignment.ExactSamplingReservoirBridge
open NField.Alignment.EndpointReservoirAlias
open NField.Alignment.EndpointReciprocityBridge
open NField.Alignment.FloorStateSwitchingLedger
open NField.Alignment.PrimitiveAdditiveConvolution
open NField.Alignment.PrimeSecondaryCoefficient
open NField.Alignment.PrimeCarrierDamping
open NField.Alignment.PrimeSquareCubicEnergy
open NField.Alignment.SquareLockCarrierMass
open NField.Alignment.LiveCarrierDamping
open NField.Alignment.ReducedHarmonicMobius
open NField.Alignment.ReciprocalDivisorMomentBound
open NField.Alignment.SecondaryCapacityAnalyticInputs
open NField.Alignment.SecondaryCapacityLedger
open NField.Alignment.WeightedFractionalPartTransfer

open scoped Classical
open NField.Alignment.KorolevCanonicalPrimeSlices
open NField.Alignment.KorolevCanonicalPhaseSlices
open NField.Alignment.KorolevCanonicalSelectedSum
open NField.Alignment.KorolevLogarithmicPartition
open NField.Alignment.KorolevBlockResidualRange
open NField.Alignment.KaratsubaProductCutoffCompletion
open NField.Alignment.KorolevPrimeWindows
open NField.Alignment.CarryBoundarySpectra

open NField.Alignment
open NField.Alignment.KorolevCanonicalTruncatedPrefix
open NField.Alignment.KorolevWindowParameters
open NField.Alignment.KorolevPrimeIntervals
open NField.Alignment.DedekindReciprocity

/-- Manuscript Lemma `Floor-to-fractional response`. -/
theorem floor_to_fractional_response
    {p : ℕ} (hp : p.Prime) (a : ZMod (p ^ 2)) :
    collisionResponse p a = fractionalResponse hp a :=
  collisionResponse_eq_fractionalResponse hp a

/-- Manuscript Theorem `Collision-to-Bernoulli straightening`, including its
finite square-energy consequence. -/
theorem collision_to_bernoulli_straightening
    {p : ℕ} (hp : p.Prime) (A : ZMod (p ^ 2)) :
    collisionResponse p ((straighteningUnit p).val * A) =
        bernoulliBoundary hp A ∧
      collisionEnergy hp = bernoulliEnergy hp ∧
      collisionEnergy hp =
        NField.Alignment.PrimeCarryEnergyBridge.primeCarryEnergy hp :=
  ⟨NField.Alignment.CollisionBernoulliStraightening.collision_to_bernoulli_straightening hp A,
    collision_energy_eq_bernoulli_energy hp,
    NField.Alignment.ExactSamplingReservoirBridge.collisionEnergy_eq_primeCarryEnergy hp⟩

/-- Manuscript Lemma `Reduced-ratio capacity`. -/
theorem reduced_ratio_capacity (N : ℕ) :
    3 * continuousCapacity N =
      (N : ℝ) + 2 * ∑ k ∈ Finset.Icc 2 N,
        (((N / k : ℕ) : ℝ) / (k : ℝ)) * reducedHarmonicStar k :=
  NField.Alignment.SecondaryCapacityLedger.reduced_ratio_capacity N

/-- Manuscript Lemma `Coprime Euler sum`. -/
theorem coprime_euler_sum :
    Filter.Tendsto
      (fun N => ∑ ak ∈ NField.Alignment.CoprimeEulerMass.reducedEulerPairs N,
        NField.Alignment.CoprimeEulerMass.pairWeight ak)
      Filter.atTop (nhds 1) :=
  NField.Alignment.SecondaryCapacityLedger.coprime_euler_sum

/-- Manuscript Proposition `Exact continuous-defect ledger`. -/
theorem exact_continuous_defect_ledger (N : ℕ) :
    (N : ℝ) - continuousCapacity N =
      (2 / 3 : ℝ) * (N : ℝ) * reducedEulerTailMass N +
        (2 / 3 : ℝ) * fractionalFloorTerm N :=
  NField.Alignment.SecondaryCapacityLedger.exact_continuous_defect_ledger N

/-- Manuscript Lemma `Weighted fractional parts`. -/
theorem weighted_fractional_parts
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    WeightedFractionalPartsEstimate :=
  NField.Alignment.SecondaryCapacityAnalyticInputs.weighted_fractional_parts
    hSaffariVaughan

/-- Manuscript Lemma `Möbius reduction`. -/
theorem mobius_reduction
    (N : ℕ) :
    fractionalFloorTerm N = exactMobiusFractionalTransform N :=
  NField.Alignment.ReducedHarmonicMobius.mobius_reduction N

/-- Manuscript Proposition `Fractional-floor asymptotic`. -/
theorem fractional_floor_asymptotic
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound fractionalFloorTerm fractionalFloorMain
      secondaryCapacityRemainderScale :=
  NField.Alignment.SecondaryCapacityAnalyticInputs.fractional_floor_asymptotic
    hSaffariVaughan

/-- Manuscript Theorem `Continuous secondary coefficient`. -/
theorem continuous_secondary_coefficient
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound continuousCapacity continuousCapacityMain
      secondaryCapacityRemainderScale :=
  NField.Alignment.SecondaryCapacityAnalyticInputs.continuous_secondary_coefficient
    hSaffariVaughan

/-- Manuscript Corollary `Secondary term for the GCD and LCM sum`. -/
theorem secondary_term_for_gcd_lcm_sum
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    EventualErrorBound gcdLcmSquareSum gcdLcmSquareMain
        (fun N => 3 * secondaryCapacityRemainderScale N) ∧
      EventualErrorBound gcdLcmTriangularSum gcdLcmTriangularMain
        (fun N => (3 / 2 : ℝ) * secondaryCapacityRemainderScale N) :=
  NField.Alignment.SecondaryCapacityAnalyticInputs.secondary_term_for_gcd_lcm_sum
    hSaffariVaughan

/-- Manuscript Lemma `Jump data`. -/
theorem jump_data
    {N a k : ℕ} (hk : 0 < k) (hcop : a.Coprime k) (L : ℚ) :
    boundaryMidpoint N a k = cyclicPrefixResponse a k (N % k) ∧
      let T := cyclicPrefixResponse a k (N % k)
      let M : ℚ := (N / k : ℕ)
      (T - M) ^ 2 - (T + M) ^ 2 = -4 * M * T ∧
        2 * L * (T - M) - 2 * L * (T + M) = -4 * L * M :=
  squared_jump_data hk hcop L

/-- Manuscript Lemma `Periodic jump aliasing`, derived from the exact finite
reciprocity bridge with no manuscript-specific input left as a hypothesis. -/
theorem periodic_jump_aliasing
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    bernoulliEnergy hp / (p : ℝ) ^ 2 - continuousCapacity (p - 1) =
      -(((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2) -
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 +
        2 * (boundarySlope p : ℝ) *
          (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4 :=
  NField.Alignment.EndpointReciprocityBridge.periodic_jump_aliasing hp hpodd

/-- Manuscript Theorem `Exact endpoint-reservoir alias formula`. -/
theorem exact_endpoint_reservoir_alias_formula
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    samplingDefect hp =
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        4 * (jumpPhaseReservoir p : ℝ) / (p : ℝ) ^ 2 -
        2 * (boundarySlope p : ℝ) *
          (carrierBernoulliCurvature p : ℝ) / (p : ℝ) ^ 4 :=
  NField.Alignment.EndpointReciprocityBridge.exact_endpoint_reservoir_alias_formula
    hp hpodd

/-- Manuscript Proposition `Bernoulli-curvature evaluation`. -/
theorem bernoulli_curvature_evaluation
    {p : ℕ} (hp : p.Prime) :
    carrierBernoulliCurvature p = closedCarrierBernoulliCurvature p ∧
      |carrierBernoulliCurvature p| ≤
        ((p - 1 : ℕ) : ℚ) / 6 +
          ((p - 1 : ℕ) : ℚ) * harmonic (p - 1) / 6 :=
  ⟨NField.Alignment.BernoulliCurvature.bernoulli_curvature_evaluation hp,
    abs_carrierBernoulliCurvature_le hp⟩

/-- Manuscript Lemma `Discrete pair correlation`. -/
theorem discrete_pair_correlation
    {m : ℕ} [NeZero m] (r s : (ZMod m)ˣ) :
    discretePairCorrelation r s =
      (m : ℂ)⁻¹ * NField.Alignment.DedekindCollisionKernel.dedekindSum (s * r⁻¹) :=
  NField.Alignment.CarrierSamplingReservoir.discrete_pair_correlation r s

/-- Manuscript Theorem `Exact sampling-reservoir bridge`. -/
theorem exact_sampling_reservoir_bridge
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    samplingDefect hp =
      ((p - 1 : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2 -
        (2 / (3 * (p : ℝ) ^ 4) : ℝ) *
          (((p - 1 : ℕ) : ℝ) + elementaryRatioReservoir p) -
        lowerModulusReservoir p / (p : ℝ) ^ 2 :=
  NField.Alignment.ExactSamplingReservoirBridge.exact_sampling_reservoir_bridge
    hp hpodd

/-- Manuscript Lemma `First absolute moment`. -/
theorem first_absolute_moment
    {k : ℕ} [NeZero k] (hk : 0 < k) :
    dedekindFirstMoment k ≤
      (k : ℝ) * (harmonic k : ℝ) ^ 2 / 4 :=
  NField.Alignment.CarrierSamplingReservoir.first_absolute_moment hk

/-- Manuscript Lemma `One-carrier bound`. -/
theorem one_carrier_bound
    {k b : ℕ} [NeZero k] (hk : 2 ≤ k) (hkb : k < b)
    (β : (ZMod k)ˣ) :
    ‖∑ a ∈ Finset.Ico (k + 1) b,
        (((b - 1) / a : ℕ) : ℝ) • residueDedekindSequence β a‖ ≤
      4 * (((b - 1) / (k + 1) : ℕ) : ℝ) *
        ((k : ℝ) * (harmonic k : ℝ) ^ 2 / 4) :=
  NField.Alignment.CarrierSamplingReservoir.one_carrier_bound hk hkb β

/-- Manuscript Proposition `Unconditional sampling bound`. -/
theorem unconditional_sampling_bound
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    |samplingDefect hp| ≤
      30 * (1 + Real.log (p : ℝ)) ^ 2 :=
  NField.Alignment.ExactSamplingReservoirBridge.abs_samplingDefect_le_log_sq
    hp hpodd

/-- Manuscript Lemma `Exact additive transform`. -/
theorem exact_additive_transform
    {K : ℕ} (hK : 2 ≤ K) (t : ℕ) :
    FullTransformSeriesConverges K t ∧
      fullDedekindTransform K t / (K : ℂ) =
        fullTransformSeriesSide K t ∧
      unitDedekindTransform K t = unitTransformMobiusSide K t :=
  NField.Alignment.DedekindInverseResidueTransform.exact_additive_transform
    hK t

/-- Manuscript Lemma `Exact numerator descent`. -/
theorem exact_numerator_descent
    {q r : ℕ} :
    let c := r.gcd q
    let Q := q / c
    (Q = 1 → inverseSawSeries q r = 0) ∧
      (2 ≤ Q → inverseSawSeries q r = numeratorDescentSide q r) ∧
      (2 ≤ Q → ‖inverseSawSeries q r‖ ≤
        reciprocalDivisorSum q * inverseSawUnitMaximum Q) := by
  dsimp only
  exact ⟨
    (NField.Alignment.DedekindInverseResidueTransform.exact_numerator_descent
      (q := q) (r := r)).1,
    (NField.Alignment.DedekindInverseResidueTransform.exact_numerator_descent
      (q := q) (r := r)).2,
    exact_numerator_descent_bound⟩

/-- Manuscript Lemma `Completed inverse prefixes`. -/
theorem completed_inverse_prefixes
    (hcompletion : WeilEstermannCompletionInputs) :
    CompletedInversePrefixEstimate :=
  NField.Alignment.InverseResiduePrefixCompletion.completed_inverse_prefixes
    hcompletion

/-- Manuscript Lemma `Inverse-residue harmonic bound`, derived from the
source-level Korolev, Weil--Estermann, and standard divisor-growth inputs. -/
theorem inverse_residue_harmonic_bound
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth) :
    InverseResidueHarmonicEstimate :=
  NField.Alignment.DedekindInverseResidueTransform.inverse_residue_harmonic_bound
    (korolevAmbientInverseResidueEstimate_of_partials
      (uniformInverseSawPartialHarmonicEstimate hKorolev
        (completed_inverse_prefixes hcompletion) hdivisorGrowth))

/-- Manuscript Proposition `Uniform additive transform bound`. -/
theorem uniform_additive_transform_bound
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth) :
    UniformAdditiveTransformEstimate :=
  NField.Alignment.DedekindInverseResidueTransform.uniform_additive_transform_bound
    (korolevAmbientInverseResidueEstimate_of_partials
      (uniformInverseSawPartialHarmonicEstimate hKorolev
        (completed_inverse_prefixes hcompletion) hdivisorGrowth))

/-- Manuscript Lemma `Bounded reciprocal-divisor moments`. -/
theorem bounded_reciprocal_divisor_moments
    : BoundedReciprocalDivisorMoments :=
  NField.Alignment.ReciprocalDivisorMomentBound.bounded_reciprocal_divisor_moments

/-- Manuscript Theorem `All-prime carrier damping`. -/
theorem all_prime_carrier_damping
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth) :
    PrimeUniformBound lowerModulusReservoir
        logarithmicCarrierReservoirScale ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ p, p.Prime → p ≠ 2 →
          |primeSamplingDefect p| ≤
            C * (1 + logarithmicCarrierSamplingScale p) :=
  NField.Alignment.PrimeCarrierDamping.all_prime_carrier_damping_from_analytic_inputs
    (korolevAmbientInverseResidueEstimate_of_partials
      (uniformInverseSawPartialHarmonicEstimate hKorolev
        (completed_inverse_prefixes hcompletion) hdivisorGrowth))

/-- Manuscript Theorem `Square-lock localization`. -/
theorem square_lock_localization
    (hcount : SquareLockCountEstimate) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ p C, p.Prime → 1 ≤ C → 2 * C ≤ p →
        squareLockCollarMass p C ≤
          constant *
            (((C : ℝ) / (p : ℝ)) * (Real.log (2 * p)) ^ 3 +
              Real.rpow p (-1 / 3 : ℝ) *
                (Real.log (2 * p)) ^ 3) :=
  NField.Alignment.SquareLockCarrierMass.square_lock_localization
    hcount

/-- Manuscript Corollary `Two localization scales`. -/
theorem two_localization_scales
    (hcount : SquareLockCountEstimate)
    {p : ℕ} (hp : p.Prime)
    (hfineOne : 1 ≤ fineSquareLockCutoff p)
    (hfineHalf : 2 * fineSquareLockCutoff p ≤ p)
    (hcoefficientOne : 1 ≤ coefficientSquareLockCutoff p)
    (hcoefficientHalf : 2 * coefficientSquareLockCutoff p ≤ p) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      squareLockCollarMass p (fineSquareLockCutoff p) ≤
        constant *
          (((fineSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ) *
              (Real.log (2 * p)) ^ 3 +
            Real.rpow p (-1 / 3 : ℝ) * (Real.log (2 * p)) ^ 3) ∧
      squareLockCollarMass p (coefficientSquareLockCutoff p) ≤
        constant *
          (((coefficientSquareLockCutoff p : ℕ) : ℝ) / (p : ℝ) *
              (Real.log (2 * p)) ^ 3 +
            Real.rpow p (-1 / 3 : ℝ) * (Real.log (2 * p)) ^ 3) :=
  NField.Alignment.SquareLockCarrierMass.two_localization_scales
    hcount hp hfineOne hfineHalf hcoefficientOne hcoefficientHalf

/-- The switching ledger for any selected finite carrier family. -/
theorem selected_carrier_switching_ledger
    {p N : ℕ} (hp : p.Prime) (hN : 3 ≤ N)
    (carriers : Finset ℕ)
    (hcarriers : ∀ k ∈ carriers, 2 ≤ k ∧ k < p) :
    dwellBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) =
      ∑ X ∈ Finset.Icc 3 N,
        carrierDwell N X *
          (selectedCarrierFresh p carriers X : ℝ) ∧
    quadraticBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) =
      ∑ X ∈ Finset.Icc 3 N,
        carrierDwell N X *
          ((carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2 +
            2 * carrierStateBurdenReal p carriers (X - 1) *
              (carrierStateBurdenReal p carriers X -
                carrierStateBurdenReal p carriers (X - 1))) ∧
    (let J := fun X =>
        carrierStateBurdenReal p carriers (X - 1) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) +
          (1 / 2 : ℝ) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2;
      (∑ X ∈ Finset.Icc 3 N,
          carrierDwell N X * positivePart (J X)) =
        (∑ X ∈ Finset.Icc 3 N,
          carrierDwell N X * negativePart (J X)) +
        quadraticBurden N (carrierDwell N)
          (carrierStateBurdenReal p carriers) / 2) :=
  NField.Alignment.CarrierStateSwitching.exact_carrier_switching_ledger
    hp hN carriers hcarriers

/-- Manuscript Proposition `Exact switching ledger`, including the previously
missing first equality with the actual smaller-modulus Rademacher reservoir. -/
theorem exact_switching_ledger
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    let carriers := fullCarrierSet p
    (∑ k ∈ Finset.range p, modulusKSlice p k).re =
        dwellBurden (p - 1) (carrierDwell (p - 1))
          (carrierStateBurdenReal p carriers) ∧
    dwellBurden (p - 1) (carrierDwell (p - 1))
        (carrierStateBurdenReal p carriers) =
      carrierFamilyFreshMass p carriers ∧
    quadraticBurden (p - 1) (carrierDwell (p - 1))
        (carrierStateBurdenReal p carriers) =
      ∑ X ∈ Finset.Icc 3 (p - 1),
        carrierDwell (p - 1) X *
          ((carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2 +
            2 * carrierStateBurdenReal p carriers (X - 1) *
              (carrierStateBurdenReal p carriers X -
                carrierStateBurdenReal p carriers (X - 1))) ∧
    (let J := fun X =>
        carrierStateBurdenReal p carriers (X - 1) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) +
          (1 / 2 : ℝ) *
            (carrierStateBurdenReal p carriers X -
              carrierStateBurdenReal p carriers (X - 1)) ^ 2;
      (∑ X ∈ Finset.Icc 3 (p - 1),
          carrierDwell (p - 1) X * positivePart (J X)) =
        (∑ X ∈ Finset.Icc 3 (p - 1),
          carrierDwell (p - 1) X * negativePart (J X)) +
        quadraticBurden (p - 1) (carrierDwell (p - 1))
          (carrierStateBurdenReal p carriers) / 2) := by
  dsimp only
  have hN : 3 ≤ p - 1 := by omega
  have hcarriers : ∀ k ∈ fullCarrierSet p, 2 ≤ k ∧ k < p := by
    intro k hk
    have hkdata := Finset.mem_Icc.mp hk
    exact ⟨hkdata.1, by omega⟩
  have hledger :=
    NField.Alignment.CarrierStateSwitching.exact_carrier_switching_ledger
      hp hN (fullCarrierSet p) hcarriers
  have hmass := fullCarrierFreshMass_eq_modulusKSlices hp
  have hlinearMass :
      dwellBurden (p - 1) (carrierDwell (p - 1))
          (carrierStateBurdenReal p (fullCarrierSet p)) =
        carrierFamilyFreshMass p (fullCarrierSet p) := by
    simpa [carrierFamilyFreshMass] using hledger.1
  exact ⟨hmass.symm.trans hlinearMass.symm,
    hlinearMass, hledger.2.1, hledger.2.2⟩

/-- Manuscript identity `Stored-burden variance`, on the actual carrier
prefixes and floor dwell weights. -/
theorem stored_burden_variance
    {p N : ℕ} (hN : 3 ≤ N) (carriers : Finset ℕ) :
    let total := ∑ X ∈ Finset.Icc 3 N,
      (carrierDwell N X - carrierDwell N (X + 1)) *
        carrierStateBurdenReal p carriers X
    let mean := total / carrierDwell N 3
    total ^ 2 / carrierDwell N 3 +
        ∑ X ∈ Finset.Icc 3 N,
          (carrierDwell N X - carrierDwell N (X + 1)) *
            (carrierStateBurdenReal p carriers X - mean) ^ 2 =
      quadraticBurden N (carrierDwell N)
        (carrierStateBurdenReal p carriers) :=
  carrier_burden_variance_identity hN carriers

/-- Manuscript's exact negative-current characterization. -/
theorem negative_switching_current_criterion
    (p : ℕ) (carriers : Finset ℕ) (X : ℕ) :
    let stored := carrierStateBurdenReal p carriers (X - 1)
    let fresh := carrierStateBurdenReal p carriers X - stored
    stored * fresh + (1 / 2 : ℝ) * fresh ^ 2 < 0 ↔
      stored * fresh < 0 ∧ |fresh| < 2 * |stored| :=
  carrier_switching_current_neg_iff p carriers X

/-- Manuscript Proposition `Complementary-partition identity`. -/
theorem complementary_partition_identity
    {p X : ℕ} [NeZero X] (hp : p.Prime) (hX : 3 ≤ X) (hXp : X < p) :
    freshCarrierSum (p ^ 2) X =
      ((p ^ 2 : ℕ) : ℚ) / (12 * (X : ℚ)) * reducedHarmonic X +
        ((X : ℚ) * reducedHarmonic X - (X.totient : ℚ)) /
          (12 * (((p ^ 2 : ℕ) : ℚ))) -
        (X.totient : ℚ) / 8 - partitionPacket (p ^ 2) X :=
  NField.Alignment.ComplementaryPartition.complementary_partition_identity
    hp hX hXp

/-- Manuscript Corollary `Primitive additive convolution`. -/
theorem primitive_additive_convolution
    {p : ℕ} (hp : p.Prime) :
    (∀ X, 0 < X → X < p →
      fullAdditiveConvolution p X =
        ∑ d ∈ X.divisors, primitiveAdditiveConvolution p d) ∧
    (∀ X, 0 < X → X < p →
      primitiveAdditiveConvolution p X =
        ∑ d ∈ X.divisors,
          (ArithmeticFunction.moebius d : ℚ) *
            fullAdditiveConvolution p (X / d)) :=
  NField.Alignment.PrimitiveAdditiveConvolution.primitive_additive_convolution hp

/-- Manuscript Proposition `Live-sector damping`. -/
theorem live_sector_damping
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth)
    (hcount : SquareLockCountEstimate) :
    CarrierFamilyPrimeEventualBound liveCarrierSet
      logarithmicCarrierReservoirScale :=
  NField.Alignment.LiveCarrierDamping.live_sector_damping_from_analytic_inputs
    (korolevAmbientInverseResidueEstimate_of_partials
      (uniformInverseSawPartialHarmonicEstimate hKorolev
        (completed_inverse_prefixes hcompletion) hdivisorGrowth)) hcount

/-- Manuscript Problem `Signed carrier damping`.  This is deliberately a
proposition, not a claimed theorem. -/
def signed_carrier_damping_problem : Prop :=
  SignedDedekindCarrierDamping

/-- Manuscript Theorem `Sampling theorem conditional on signed damping`. -/
theorem sampling_conditional_on_signed_damping
    (hsigned : SignedDedekindCarrierDamping) :
    PrimeUniformBound primeSamplingDefect (fun p => Real.log p) :=
  NField.Alignment.LiveCarrierDamping.sampling_conditional_on_signed_damping
    hsigned

/-- The stronger error term in the manuscript's final corollary under signed
carrier damping. -/
theorem finite_secondary_coefficient_under_signed_damping
    (hSaffariVaughan : SaffariVaughanDistributionEstimate)
    (hsigned : SignedDedekindCarrierDamping) :
    PrimeEventualErrorBound primeCollisionEnergy
      primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primeContinuousScale p) :=
  NField.Alignment.PrimeSecondaryCoefficient.finite_secondary_coefficient_under_log_sampling
    (NField.Alignment.SecondaryCapacityAnalyticInputs.continuous_secondary_coefficient
      hSaffariVaughan)
    (sampling_conditional_on_signed_damping hsigned)

/-- The manuscript's final `p² log p` conclusion when continuous capacity is
also supplied with a logarithmic remainder. -/
theorem finite_secondary_coefficient_under_log_capacity_and_signed_damping
    (hcapacity : EventualErrorBound continuousCapacity continuousCapacityMain
      (fun N => Real.log N))
    (hsigned : SignedDedekindCarrierDamping) :
    PrimeEventualErrorBound primeCollisionEnergy
      primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * Real.log p) :=
  NField.Alignment.PrimeSecondaryCoefficient.finite_secondary_coefficient_under_log_capacity_and_sampling
    hcapacity (sampling_conditional_on_signed_damping hsigned)

/-- Manuscript Proposition `Cyclic correlation ladder`. -/
theorem cyclic_correlation_ladder
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hquadratic : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤
        k * harmonic k ^ 2)
    (hlinear : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤
        k * harmonic k)
    (hbounded : ∀ k, 2 ≤ k → k ≤ p - 1 →
      |cyclicCorrelation k ((p - 1) % k) (p ^ 2)| ≤ k) :
    |samplingDefect hp| ≤
        cyclicSamplingEnvelope p (fun k => k * harmonic k ^ 2) ∧
      |samplingDefect hp| ≤
        cyclicSamplingEnvelope p (fun k => k * harmonic k) ∧
      |samplingDefect hp| ≤
        cyclicSamplingEnvelope p (fun k => k) :=
  NField.Alignment.CyclicCorrelationReservoir.cyclic_correlation_ladder
    hp hpodd hquadratic hlinear hbounded

/-- Manuscript Corollary `Finite secondary coefficient`.  Both analytic
chains start at their source-level published estimates. -/
theorem finite_secondary_coefficient
    (hSaffariVaughan : SaffariVaughanDistributionEstimate)
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs)
    (hdivisorGrowth : StandardCompletedPrefixDivisorGrowth) :
    PrimeEventualErrorBound primeCollisionEnergy
      primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primePrintedSamplingScale p) :=
  NField.Alignment.PrimeSecondaryCoefficient.finite_secondary_coefficient_printed
    (NField.Alignment.SecondaryCapacityAnalyticInputs.continuous_secondary_coefficient
      hSaffariVaughan)
    (NField.Alignment.PrimeCarrierDamping.primeSamplingDefect_strict_bound_from_analytic_inputs
      (korolevAmbientInverseResidueEstimate_of_partials
        (uniformInverseSawPartialHarmonicEstimate hKorolev
          (completed_inverse_prefixes hcompletion) hdivisorGrowth)))

/-- The standard divisor bounds following `eq:completed-inverse-prefix`:
the exact completion scale costs any positive power beyond the square root. -/
theorem completed_prefix_scale_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ threshold : ℕ, ∀ q, threshold ≤ q →
      completedInversePrefixScale q ≤ C * (q : ℝ) ^ (1 / 2 + ε) :=
  NField.Alignment.CompletedPrefixDivisorGrowth.completed_prefix_scale_small_power ε hε

/-- SEC-04, with no divisor-growth assumption. -/
theorem standard_completed_prefix_divisor_growth :
    StandardCompletedPrefixDivisorGrowth :=
  NField.Alignment.CompletedPrefixDivisorGrowth.standard_completed_prefix_divisor_growth

/-- The final assertion of `Completed inverse prefixes`, still conditional
on the source-level Weil--Estermann estimate, uniformly in r and X. -/
theorem completed_inverse_prefixes_small_power
    (hcompletion : WeilEstermannCompletionInputs) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ q r X,
      threshold ≤ q → 2 ≤ q → r.Coprime q → 1 ≤ X → X ≤ q →
      |inverseResiduePrefix q r X| ≤ C * (q : ℝ) ^ (1 / 2 + ε) :=
  NField.Alignment.CompletedPrefixDivisorGrowth.completed_inverse_prefix_small_power
    (completed_inverse_prefixes hcompletion) ε hε

/-- `lem:inverse-harmonic` after discharging SEC-04; SEC-02 and SEC-03 remain. -/
theorem inverse_residue_harmonic_bound_from_two_inputs
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs) :
    InverseResidueHarmonicEstimate :=
  inverse_residue_harmonic_bound hKorolev hcompletion standard_completed_prefix_divisor_growth

/-- `prop:uniform-transform` after discharging SEC-04. -/
theorem uniform_additive_transform_bound_from_two_inputs
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs) :
    UniformAdditiveTransformEstimate :=
  uniform_additive_transform_bound hKorolev hcompletion standard_completed_prefix_divisor_growth

/-- `thm:all-prime-damping` after discharging SEC-04. -/
theorem all_prime_carrier_damping_from_two_inputs
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs) :
    PrimeUniformBound lowerModulusReservoir logarithmicCarrierReservoirScale ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime → p ≠ 2 →
        |primeSamplingDefect p| ≤ C * (1 + logarithmicCarrierSamplingScale p) :=
  all_prime_carrier_damping hKorolev hcompletion standard_completed_prefix_divisor_growth

/-- `prop:live-sector-damping` after discharging SEC-04. The separate
square-lock counting hypothesis SEC-05 is still required. -/
theorem live_sector_damping_without_divisor_input
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs)
    (hcount : SquareLockCountEstimate) :
    CarrierFamilyPrimeEventualBound liveCarrierSet logarithmicCarrierReservoirScale :=
  live_sector_damping hKorolev hcompletion standard_completed_prefix_divisor_growth hcount

/-- `cor:inherit` with SEC-04 proved. The exact printed conclusion is
unchanged; only Saffari--Vaughan, Korolev and Weil--Estermann remain inputs. -/
theorem finite_secondary_coefficient_from_three_inputs
    (hSaffariVaughan : SaffariVaughanDistributionEstimate)
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcompletion : WeilEstermannCompletionInputs) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primePrintedSamplingScale p) :=
  finite_secondary_coefficient hSaffariVaughan hKorolev hcompletion
    standard_completed_prefix_divisor_growth

/-- Exact finite completion underlying `lem:completed-inverse-prefix`.
Every frequency, including zero, is present. -/
theorem inverse_additive_completion {q : ℕ} [NeZero q]
    (r X : ℕ) (j : ZMod q) :
    inverseAdditivePrefix q r X j = (q : ℂ)⁻¹ *
      ∑ t : ZMod q, ZMod.stdAddChar t *
        NField.Alignment.SpectralPower.intervalFourier q X (-t) *
        NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t :=
  NField.Alignment.InverseAdditiveCompletion.inverse_additive_prefix_completion r X j

/-- Literal complete Kloosterman sum used by the finite completion. -/
theorem complete_inverse_kloosterman_sum {q : ℕ} [NeZero q]
    (r : ℕ) (j t : ZMod q) :
    NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t =
      ∑ u : (ZMod q)ˣ,
        ZMod.stdAddChar (j * ((r : ZMod q) * u⁻¹.val) - u.val * t) :=
  NField.Alignment.InverseAdditiveCompletion.complete_inverse_sum_eq_units r j t

/-- The zero completion mode is a complete unit-character sum. -/
theorem complete_inverse_zero_mode {q : ℕ} [NeZero q]
    (r : ℕ) (j : ZMod q) :
    NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j 0 =
      ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (j * ((r : ZMod q) * u.val)) :=
  NField.Alignment.InverseAdditiveCompletion.complete_inverse_sum_zero r j

/-- Completion with the exact zero-mode cost `X/q` retained. -/
theorem inverse_additive_completion_bound {q : ℕ} [NeZero q]
    (hq : 0 < q) (r X : ℕ) (j : ZMod q) {U : ℝ} (hU : 0 ≤ U)
    (hcomplete : ∀ t : ZMod q,
      ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ U) :
    ‖inverseAdditivePrefix q r X j‖ ≤ U * ((X : ℝ) / q + (harmonic q : ℝ)) :=
  NField.Alignment.InverseAdditiveCompletion.inverse_additive_prefix_norm_of_complete
    hq r X j hU hcomplete

/-- SEC-03's incomplete estimate follows from its genuine complete-sum
source bound. The source bound is not proved by this reduction. -/
theorem weil_estermann_prefix_from_complete_sums
    (hcomplete : NField.Alignment.InverseAdditiveCompletion.CompleteInverseSumEstimate) :
    WeilEstermannInversePrefixEstimate :=
  NField.Alignment.InverseAdditiveCompletion.weil_estermann_prefix_of_complete hcomplete

/-- Same printed `cor:inherit` conclusion, now starting the completion
chain at complete Kloosterman sums. All three source inputs remain explicit. -/
theorem finite_secondary_coefficient_from_complete_sums
    (hSaffariVaughan : SaffariVaughanDistributionEstimate)
    (hKorolev : KorolevInverseFractionRangeEstimate)
    (hcomplete : NField.Alignment.InverseAdditiveCompletion.CompleteInverseSumEstimate) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primePrintedSamplingScale p) :=
  finite_secondary_coefficient_from_three_inputs hSaffariVaughan hKorolev
    (weil_estermann_prefix_from_complete_sums hcomplete)

/-- Linear Hasse quotient and degree bound for positive-degree f; Harcos Lemma 10 supporting SEC-03. -/
theorem stepanov_hasse_factor {R : Type*} [CommRing R] [IsDomain R]
    (f : Polynomial R) (hdeg : 1 ≤ f.natDegree) {n k : ℕ} (hk : k ≤ n) :
    ∃ Q : Polynomial R →ₗ[R] Polynomial R, ∀ g : Polynomial R,
      Polynomial.hasseDeriv k (g * f ^ n) = Q g * f ^ (n-k) ∧
      (Q g).natDegree + k ≤ g.natDegree + k * f.natDegree :=
  NField.Alignment.HasseDerivativeFactor.hasse_factor_linear_degree f hdeg hk

/-- Exact equivalence between Hasse vanishing and root-factor divisibility in every characteristic. -/
theorem stepanov_root_multiplicity {R : Type*} [CommRing R]
    (p : Polynomial R) (a : R) (n : ℕ) :
    (Polynomial.X - Polynomial.C a) ^ n ∣ p ↔ ∀ k < n, (Polynomial.hasseDeriv k p).eval a = 0 :=
  NField.Alignment.HasseRootCount.pow_X_sub_C_dvd_iff_hasse_eval_eq_zero p a n

/-- Distinct-root count times prescribed multiplicity is bounded by the degree of a nonzero polynomial. -/
theorem stepanov_root_count {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (hp : p ≠ 0) (s : Finset R) (n : ℕ)
    (hvanish : ∀ a ∈ s, ∀ k < n, (Polynomial.hasseDeriv k p).eval a = 0) :
    s.card * n ≤ p.natDegree :=
  NField.Alignment.HasseRootCount.card_mul_order_le_natDegree p hp s n hvanish

/-- Below q, evaluation of the Hasse derivative of g*X^(j*q) equals D_k(g)(a)*a^j. -/
theorem stepanov_frobenius_derivative {K : Type*} [Field K] [Fintype K]
    (g : Polynomial K) (a : K) (j : ℕ) {k : ℕ} (hkq : k < Fintype.card K) :
    (Polynomial.hasseDeriv k (g * Polynomial.X ^ (j * Fintype.card K))).eval a =
      (Polynomial.hasseDeriv k g).eval a * a ^ j :=
  NField.Alignment.HasseFiniteField.hasse_mul_X_pow_mul_card_eval g a j hkq

/-- Exact quotient-constraint formula for the two-family auxiliary polynomial. -/
theorem stepanov_auxiliary_derivative {K : Type*} [Field K] [Fintype K]
    (f : Polynomial K) (hf : f ≠ 0) (r s : ℕ → Polynomial K) (ell d J : ℕ)
    (a : K) {k : ℕ} (hk : k ≤ ell) (hkq : k < Fintype.card K) :
    (Polynomial.hasseDeriv k (NField.Alignment.StepanovAuxiliary.auxiliary f r s ell d J)).eval a =
      (f.eval a) ^ (ell-k) * ∑ j ∈ Finset.range J,
        ((NField.Alignment.HasseDerivativeFactor.quotientMap f hf ell k (r j)).eval a +
          (NField.Alignment.HasseDerivativeFactor.quotientMap f hf (ell+d) k (s j)).eval a * (f.eval a)^d) * a^j :=
  NField.Alignment.StepanovAuxiliary.auxiliary_hasse_eval f hf r s ell d J a hk hkq

/-- Root count from explicit vanishing constraints and an explicit nonzero auxiliary polynomial; neither existence nor nonvanishing is proved here. -/
theorem stepanov_auxiliary_root_bound {K : Type*} [Field K] [Fintype K]
    (f : Polynomial K) (hf : f ≠ 0) (r s : ℕ → Polynomial K) (ell d J n : ℕ)
    (hn : n ≤ ell + 1) (hnq : n ≤ Fintype.card K) (points : Finset K)
    (haux : NField.Alignment.StepanovAuxiliary.auxiliary f r s ell d J ≠ 0)
    (hconstraints : ∀ a ∈ points, ∀ k < n,
      (∑ j ∈ Finset.range J,
        ((NField.Alignment.HasseDerivativeFactor.quotientMap f hf ell k (r j)).eval a +
          (NField.Alignment.HasseDerivativeFactor.quotientMap f hf (ell+d) k (s j)).eval a * (f.eval a)^d) * a^j) = 0) :
    points.card * n ≤ (NField.Alignment.StepanovAuxiliary.auxiliary f r s ell d J).natDegree :=
  NField.Alignment.StepanovAuxiliary.card_mul_order_le_auxiliary_degree f hf r s ell d J n hn hnq points haux hconstraints

/-- Degree of the actual auxiliary polynomial from coefficient-degree bounds, including J=0. -/
theorem stepanov_auxiliary_degree {K : Type*} [Field K] [Fintype K]
    (f : Polynomial K) (r s : ℕ → Polynomial K) (ell d J R : ℕ)
    (hr : ∀ j < J, (r j).natDegree ≤ R)
    (hs : ∀ j < J, (s j).natDegree ≤ R) :
    (NField.Alignment.StepanovAuxiliary.auxiliary f r s ell d J).natDegree ≤
      R + (ell+d) * f.natDegree + (J-1) * Fintype.card K :=
  NField.Alignment.StepanovAuxiliaryDegree.auxiliary_natDegree_le f r s ell d J R hr hs

/-- Degree of each homogeneous derivative constraint; the bound retains k*(deg f-1). -/
theorem stepanov_constraint_degree {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (r s : ℕ → Polynomial K) (ell d J k R : ℕ) (value : K) (hk : k ≤ ell)
    (hr : ∀ j < J, (r j).natDegree ≤ R)
    (hs : ∀ j < J, (s j).natDegree ≤ R) :
    (NField.Alignment.StepanovAuxiliaryDegree.constraint f hf r s ell d J k value).natDegree ≤
      R + k * (f.natDegree-1) + (J-1) :=
  NField.Alignment.StepanovAuxiliaryDegree.constraint_natDegree_le f hf hdeg r s ell d J k R value hk hr hs

/-- Auxiliary nonvanishing from a nonzero bounded coefficient family, nonzero f(0), odd field size, and f nonsquare over the algebraic closure. -/
theorem stepanov_auxiliary_nonvanishing {K : Type*} [Field K] [Fintype K]
    (f : Polynomial K) (r s : ℕ → Polynomial K) (ell d J : ℕ)
    (hd : 2*d+1 = Fintype.card K) (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (hr : ∀ j < J, 2*(r j).natDegree + f.natDegree < Fintype.card K)
    (hs : ∀ j < J, 2*(s j).natDegree + f.natDegree < Fintype.card K)
    (hne : ∃ j < J, r j ≠ 0 ∨ s j ≠ 0) : NField.Alignment.StepanovAuxiliary.auxiliary f r s ell d J ≠ 0 :=
  NField.Alignment.StepanovNonvanishing.auxiliary_ne_zero f r s ell d J hd hf0 hns hr hs hne

/-- Exact scalar equation count ell*(R+J)+(ell*(ell-1)/2)*(m-1). -/
theorem stepanov_constraint_equation_count (ell R J m : ℕ) :
    (∑ k : Fin ell, (R+J+k.val*(m-1))) =
      ell*(R+J) + (ell*(ell-1)/2)*(m-1) :=
  NField.Alignment.StepanovConstraintSpace.equation_count ell R J m

/-- A nonzero bounded family satisfying every polynomial constraint exists when its variable count exceeds its equation count. -/
theorem stepanov_nonzero_constraint_solution {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (ell d J R : ℕ) (hJ : 0 < J) (value : K)
    (hdim : (∑ k : Fin ell, (R+J+k.val*(f.natDegree-1))) < 2*J*(R+1)) :
    ∃ r s : ℕ → Polynomial K,
      (∀ j < J, (r j).natDegree ≤ R) ∧
      (∀ j < J, (s j).natDegree ≤ R) ∧
      (∃ j < J, r j ≠ 0 ∨ s j ≠ 0) ∧
      ∀ k < ell, NField.Alignment.StepanovAuxiliaryDegree.constraint f hf r s ell d J k value = 0 :=
  NField.Alignment.StepanovConstraintSpace.exists_nonzero_constraint_solution f hf hdeg ell d J R hJ value hdim

/-- Actual root-count bound from numerical dimension and degree conditions, with coefficient existence and auxiliary nonvanishing proved; parameter optimization remains. -/
theorem stepanov_root_bound_from_dimension_count {K : Type*} [Field K] [Fintype K]
    (f : Polynomial K) (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (ell d J R : ℕ) (hJ : 0 < J) (value : K) (points : Finset K)
    (hd : 2*d+1 = Fintype.card K) (hell : ell ≤ Fintype.card K)
    (hf0 : f.eval 0 ≠ 0)
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (hR : 2*R + f.natDegree < Fintype.card K)
    (hdim : (∑ k : Fin ell, (R+J+k.val*(f.natDegree-1))) < 2*J*(R+1))
    (hpoints : ∀ a ∈ points, f.eval a = 0 ∨ (f.eval a)^d = value) :
    points.card * ell ≤ R + (ell+d)*f.natDegree + (J-1)*Fintype.card K :=
  NField.Alignment.StepanovConstraintSpace.card_mul_order_bound f hf hdeg ell d J R hJ value points hd hell hf0 hns hR hdim hpoints

/-- The exact rounded parameters give strictly more coefficient variables than scalar constraints. -/
theorem stepanov_rounded_dimension_inequality (q m : ℕ) (hm : 3 ≤ m) (hmq : 6*m < q) :
    (∑ k : Fin (NField.Alignment.StepanovParameters.order q),
      (NField.Alignment.StepanovParameters.coefficientDegree q m + NField.Alignment.StepanovParameters.blockCount q m (NField.Alignment.StepanovParameters.order q) + k.val*(m-1))) <
      2*NField.Alignment.StepanovParameters.blockCount q m (NField.Alignment.StepanovParameters.order q)*(NField.Alignment.StepanovParameters.coefficientDegree q m+1) :=
  NField.Alignment.StepanovParameters.rounded_dimension_inequality q m hm hmq

/-- Optimizes the degree-based root bound with ell=ceil(sqrt(q)) and the exact integer block cutoff. -/
theorem stepanov_rounded_root_bound (q m d N : ℕ) (hm : 3 ≤ m) (hmq : 6*m < q)
    (hd : 2*d+1 = q)
    (hbound : N*NField.Alignment.StepanovParameters.order q ≤ NField.Alignment.StepanovParameters.coefficientDegree q m + (NField.Alignment.StepanovParameters.order q+d)*m +
      (NField.Alignment.StepanovParameters.blockCount q m (NField.Alignment.StepanovParameters.order q)-1)*q) :
    (N : ℝ) < (q : ℝ)/2 + 2*m*NField.Alignment.StepanovParameters.order q :=
  NField.Alignment.StepanovParameters.rounded_card_bound q m d N hm hmq hd hbound

/-- Bounds a selected root/power-value set; translation removes any assumption on f(0). -/
theorem stepanov_selected_point_bound {K : Type*} [Field K] [Fintype K]
    (f : Polynomial K) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree < Fintype.card K)
    (hodd : Odd (Fintype.card K))
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K))))
    (value : K) (points : Finset K)
    (hpoints : ∀ a ∈ points,
      f.eval a = 0 ∨ (f.eval a)^((Fintype.card K-1)/2) = value) :
    (points.card : ℝ) < (Fintype.card K : ℝ)/2 +
      2*f.natDegree*NField.Alignment.StepanovParameters.order (Fintype.card K) :=
  NField.Alignment.StepanovSelectedPointBound.selected_point_bound f hm hmq hodd hns value points hpoints

/-- Two-sided quadratic-character sum bound from the positive and negative classes. -/
theorem stepanov_quadratic_character_sum_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree < Fintype.card K)
    (hodd : Odd (Fintype.card K))
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K)))) :
    |∑ x : K, (quadraticChar K (f.eval x) : ℝ)| <
      4*f.natDegree*NField.Alignment.StepanovParameters.order (Fintype.card K) :=
  NField.Alignment.StepanovPointCount.quadratic_character_sum_bound f hm hmq hodd hns

/-- The actual number of pairs (x,y) with y^2=f(x) equals q plus the quadratic-character sum. -/
theorem stepanov_point_count_identity {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) (hchar : ringChar K ≠ 2) :
    (NField.Alignment.StepanovPointCount.pointCount f : ℝ) = Fintype.card K + ∑ x : K, (quadraticChar K (f.eval x) : ℝ) :=
  NField.Alignment.StepanovPointCount.pointCount_eq_card_add_character_sum f hchar

/-- Proves |N-q|<4*m*ceil(sqrt(q)) for odd q, degree m>=3, q>=6m and f nonsquare over the algebraic closure. -/
theorem stepanov_point_count_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) (hm : 3 ≤ f.natDegree) (hmq : 6*f.natDegree ≤ Fintype.card K)
    (hodd : Odd (Fintype.card K))
    (hns : ¬ IsSquare (f.map (algebraMap K (AlgebraicClosure K)))) :
    |(NField.Alignment.StepanovPointCount.pointCount f : ℝ) - Fintype.card K| <
      4*f.natDegree*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) :=
  NField.Alignment.StepanovPointCount.point_count_bound f hm hmq hodd hns

/-- The actual polynomial (X^p-X)^2-4ab has degree 2p. -/
theorem kloosterman_curve_degree {K : Type*} [Field K]
    (p : ℕ) (hp : 1 < p) (a b : K) :
    (NField.Alignment.KloostermanCurve.curvePolynomial p a b).natDegree = 2*p :=
  NField.Alignment.KloostermanCurve.curvePolynomial_natDegree p hp a b

/-- An explicit Bezout identity proves separability in characteristic p when ab and 2 are nonzero. -/
theorem kloosterman_curve_separable {K : Type*} [Field K]
    (p : ℕ) [CharP K p] (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    (NField.Alignment.KloostermanCurve.curvePolynomial p a b).Separable :=
  NField.Alignment.KloostermanCurve.curvePolynomial_separable p a b hab h2

/-- The actual curve polynomial is nonsquare over the algebraic closure. -/
theorem kloosterman_curve_nonsquare {K : Type*} [Field K]
    (p : ℕ) [CharP K p] (hp : 1 < p) (a b : K)
    (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    ¬IsSquare ((NField.Alignment.KloostermanCurve.curvePolynomial p a b).map (algebraMap K (AlgebraicClosure K))) :=
  NField.Alignment.KloostermanCurve.curvePolynomial_not_isSquare_map p hp a b hab h2

/-- The actual curve count satisfies |N-q|<8p*ceil(sqrt(q)) for odd q>=12p. -/
theorem kloosterman_curve_point_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [CharP K p] (hp : 1 < p) (a b : K) (hab : a*b ≠ 0)
    (hodd : Odd (Fintype.card K)) (hq : 12*p ≤ Fintype.card K) :
    |(NField.Alignment.StepanovPointCount.pointCount (NField.Alignment.KloostermanCurve.curvePolynomial p a b) : ℝ)-Fintype.card K| <
      8*p*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) :=
  NField.Alignment.KloostermanCurve.curve_point_count_bound p hp a b hab hodd hq

/-- The equation x^p-x=v is solvable exactly when the actual trace to ZMod p is zero. -/
theorem artin_schreier_solvable_iff_trace_zero {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (v : K) :
    (∃ x : K, x^p-x = v) ↔ Algebra.trace (ZMod p) K v = 0 :=
  NField.Alignment.ArtinSchreierTrace.exists_artinSchreier_iff_trace_zero p v

/-- Each trace-zero fiber has exactly p points; every other fiber is empty. -/
theorem artin_schreier_fiber_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (v : K) :
    (Finset.univ.filter (fun x : K => x^p-x = v)).card =
      if Algebra.trace (ZMod p) K v = 0 then p else 0 :=
  NField.Alignment.ArtinSchreierTrace.artinSchreier_fiber_card p v

/-- The actual curve count is p times the count of nonzero t with trace(at+b/t)=0. -/
theorem kloosterman_curve_trace_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    NField.Alignment.StepanovPointCount.pointCount (NField.Alignment.KloostermanCurve.curvePolynomial p a b) = p*NField.Alignment.KloostermanCurvePoints.traceZeroCount p a b :=
  NField.Alignment.KloostermanCurvePoints.curve_pointCount_eq_trace p a b hab h2

/-- The sum of actual trace Kloosterman sums over every prime-field frequency equals the curve count. -/
theorem kloosterman_trace_sum_curve_identity {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    (∑ m : ZMod p, NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m) =
      (NField.Alignment.StepanovPointCount.pointCount (NField.Alignment.KloostermanCurve.curvePolynomial p a b) : ℂ) :=
  NField.Alignment.KloostermanTraceSum.sum_traceKloosterman_eq_curve_count p a b hab h2

/-- The zero frequency is exactly q-1. -/
theorem kloosterman_trace_zero_frequency {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (a b : K) :
    NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b 0 = (Fintype.card K : ℂ)-1 :=
  NField.Alignment.KloostermanTraceSum.traceKloosterman_zero p a b

/-- The nonzero-frequency sum minus one equals N-q, with the affine correction retained. -/
theorem kloosterman_nonzero_trace_identity {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (h2 : (2:K) ≠ 0) :
    (∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m)-1 =
      (NField.Alignment.StepanovPointCount.pointCount (NField.Alignment.KloostermanCurve.curvePolynomial p a b) : ℂ)-Fintype.card K :=
  NField.Alignment.KloostermanTraceSum.nonzero_trace_sum_sub_one p a b hab h2

/-- Bounds the norm of the exact nonzero-frequency aggregate minus one; it does not bound individual sums. -/
theorem kloosterman_trace_aggregate_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (a b : K) (hab : a*b ≠ 0) (hodd : Odd (Fintype.card K))
    (hq : 12*p ≤ Fintype.card K) :
    ‖(∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m)-1‖ <
      8*p*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) :=
  NField.Alignment.KloostermanTraceSum.nonzero_trace_sum_bound p a b hab hodd hq

/-- Identifies the original prime-modulus completion sum with m=1, a=-t and b=j*r. -/
theorem complete_inverse_trace_identity (p : ℕ) [Fact p.Prime]
    (r : ℕ) (j t : ZMod p) :
    NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t =
      NField.Alignment.KloostermanTraceSum.traceKloostermanSum p (-t) (j*r) 1 :=
  NField.Alignment.KloostermanTraceSum.complete_inverse_eq_traceKloosterman p r j t

/-- The normalized source character is multiplicative on all polynomials, including zero constant terms. -/
theorem kloosterman_polynomial_character_mul (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f g : Polynomial (ZMod p)) :
    NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m (f*g) =
      NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m f * NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m g :=
  NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter_mul p a b m f g

/-- Every actual polynomial-character value has norm at most one. -/
theorem kloosterman_polynomial_character_norm (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f : Polynomial (ZMod p)) :
    ‖NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m f‖ ≤ 1 :=
  NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter_norm_le_one p a b m f

/-- The value on X-t is the actual inverse additive phase, with t=0 handled. -/
theorem kloosterman_polynomial_character_linear (p : ℕ) [Fact p.Prime]
    (a b m t : ZMod p) :
    NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m (Polynomial.X-Polynomial.C t) = if t=0 then 0 else
      ZMod.stdAddChar (m*(a*t+b/t)) :=
  NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter_X_sub_C p a b m t

/-- A proved equivalence identifies the sum over actual monic polynomials with all lower coefficient vectors. -/
theorem kloosterman_monic_coefficient_sum (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) :
    NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient p a b m n = ∑ c : Fin n → ZMod p,
      NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m (NField.Alignment.KloostermanMonicCoefficients.polynomialFromCoefficients n c) :=
  NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient_eq_sum_coefficients p a b m n

/-- The degree-zero coefficient is one. -/
theorem kloosterman_lseries_coefficient_zero (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient p a b m 0 = 1 :=
  NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient_zero p a b m

/-- The degree-one coefficient is the actual prime-field Kloosterman sum. -/
theorem kloosterman_lseries_coefficient_one (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient p a b m 1 = NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m :=
  NField.Alignment.KloostermanCoefficientEvaluation.degreeCoefficient_one p a b m

/-- The degree-two coefficient is p when a, b and m are nonzero. -/
theorem kloosterman_lseries_coefficient_two (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient p a b m 2 = (p : ℂ) :=
  NField.Alignment.KloostermanCoefficientEvaluation.degreeCoefficient_two p a b m ha hb hm

/-- Every coefficient in degree at least three vanishes by translating one actual coefficient coordinate. -/
theorem kloosterman_lseries_higher_coefficients (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hm : m ≠ 0) (n : ℕ) (hn : 3≤n) :
    NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient p a b m n = 0 :=
  NField.Alignment.KloostermanCoefficientEvaluation.degreeCoefficient_eq_zero_of_three_le p a b m ha hm n hn

/-- The actual monic-polynomial formal L-series equals 1+S_m*T+p*T^2. -/
theorem kloosterman_formal_lseries_quadratic (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m = (NField.Alignment.KloostermanQuadraticLSeries.quadraticLPolynomial p a b m : PowerSeries ℂ) :=
  NField.Alignment.KloostermanQuadraticLSeries.formalLSeries_eq_quadratic p a b m ha hb hm

/-- Constructs reciprocal roots with sum -S_m and product p, factoring the actual quadratic polynomial. -/
theorem kloosterman_quadratic_factors (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    ∃ α β : ℂ, α+β = -NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m ∧ α*β = p ∧
      NField.Alignment.KloostermanQuadraticLSeries.quadraticLPolynomial p a b m =
        (1-Polynomial.C α*Polynomial.X)*(1-Polynomial.C β*Polynomial.X) :=
  NField.Alignment.KloostermanQuadraticLSeries.exists_quadratic_factors p a b m

/-- The actual formal L-series factors as (1-alpha*T)*(1-beta*T); no root-modulus estimate is asserted. -/
theorem kloosterman_formal_lseries_factors (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    ∃ α β : ℂ, α+β = -NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m ∧ α*β = p ∧
      NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
        (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X) :=
  NField.Alignment.KloostermanQuadraticLSeries.formalLSeries_factors p a b m ha hb hm

/-- The algebraic root-power recurrence; equality to extension-field sums remains open. -/
theorem kloosterman_root_power_sum_recurrence (S P α β : ℂ)
    (hs : α+β = -S) (hp : α*β=P) (n : ℕ) :
    α^(n+2)+β^(n+2) = -S*(α^(n+1)+β^(n+1))-P*(α^n+β^n) :=
  NField.Alignment.KloostermanQuadraticLSeries.root_power_sum_recurrence S P α β hs hp n

/-- The actual monic polynomial character is the product over its normalized monic irreducible factors, with multiplicity. -/
theorem kloosterman_character_irreducible_factors (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (f : Polynomial (ZMod p)) (hf : f.Monic) :
    NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m f =
      ((UniqueFactorizationMonoid.normalizedFactors f).map (NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m)).prod :=
  NField.Alignment.KloostermanMonicFactorization.character_normalizedFactors p a b m f hf

/-- The actual degree coefficient is reindexed by the proved degree-preserving unique-factorization equivalence. -/
theorem kloosterman_coefficient_factorization_sum (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) :
    NField.Alignment.KloostermanMonicCoefficients.degreeCoefficient p a b m n =
      ∑ s : NField.Alignment.KloostermanMonicFactorization.FactorizationDegree (ZMod p) n,
        (s.val.map (NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m)).prod :=
  NField.Alignment.KloostermanMonicFactorization.degreeCoefficient_eq_factorization_sum p a b m n

/-- Removing a new monic irreducible subtracts its character times the sifted coefficient in the complementary degree. -/
theorem kloosterman_sifted_coefficient_remove_factor (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (Polynomial (ZMod p)))
    (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k)
    (g : Polynomial (ZMod p)) (hg : g.Monic) (hi : Irreducible g) (hgs : g ∉ s)
    (n : ℕ) :
    NField.Alignment.KloostermanSiftedSeries.siftedCoefficient p a b m (insert g s) (g.natDegree+n) =
      NField.Alignment.KloostermanSiftedSeries.siftedCoefficient p a b m s (g.natDegree+n) -
        NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m g * NField.Alignment.KloostermanSiftedSeries.siftedCoefficient p a b m s n :=
  NField.Alignment.KloostermanSiftedSeries.siftedCoefficient_insert_shift p a b m s hs g hg hi hgs n

/-- The exact formal-series identity for removing one irreducible Euler factor, including zero character values. -/
theorem kloosterman_sifted_series_remove_factor (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (Polynomial (ZMod p)))
    (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k)
    (g : Polynomial (ZMod p)) (hg : g.Monic) (hi : Irreducible g) (hgs : g ∉ s) :
    NField.Alignment.KloostermanSiftedSeries.siftedSeries p a b m (insert g s) =
      NField.Alignment.KloostermanSiftedSeries.eulerFactor p a b m g * NField.Alignment.KloostermanSiftedSeries.siftedSeries p a b m s :=
  NField.Alignment.KloostermanSiftedSeries.siftedSeries_insert p a b m s hs g hg hi hgs

/-- Removing a finite set of actual monic irreducibles multiplies the actual L-series by their Euler factors. -/
theorem kloosterman_sifted_finite_product (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (s : Finset (Polynomial (ZMod p)))
    (hs : ∀ k ∈ s, k.Monic ∧ Irreducible k) :
    NField.Alignment.KloostermanSiftedSeries.siftedSeries p a b m s =
      (∏ g ∈ s, NField.Alignment.KloostermanSiftedSeries.eulerFactor p a b m g) *
        NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m :=
  NField.Alignment.KloostermanSiftedSeries.siftedSeries_eq_finite_product p a b m s hs

/-- The Euler product through degree N times the actual L-series is one in degree zero and zero through degree N. -/
theorem kloosterman_finite_euler_coefficients (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (N n : ℕ) (hn : n≤N) :
    PowerSeries.coeff n
      (NField.Alignment.KloostermanFiniteEulerProduct.finiteEulerDenominator p a b m N * NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m) =
        if n=0 then 1 else 0 :=
  NField.Alignment.KloostermanFiniteEulerProduct.coeff_finiteEulerDenominator_mul_LSeries p a b m N n hn

/-- The equivalent exact polynomial-truncation identity for every cutoff N. -/
theorem kloosterman_finite_euler_truncation (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (N : ℕ) :
    PowerSeries.trunc (N+1)
      (NField.Alignment.KloostermanFiniteEulerProduct.finiteEulerDenominator p a b m N * NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m) = 1 :=
  NField.Alignment.KloostermanFiniteEulerProduct.trunc_finiteEulerDenominator_mul_LSeries p a b m N

/-- The geometric inverse has exact coefficients at multiples of the positive degree, including zero weights. -/
theorem kloosterman_geometric_euler_inverse (w : ℂ) (d : ℕ) (hd : 0<d) :
    NField.Alignment.KloostermanFormalLogDerivative.geometricSeries w d = (1-PowerSeries.C w*PowerSeries.X^d : PowerSeries ℂ)⁻¹ :=
  NField.Alignment.KloostermanFormalLogDerivative.geometricSeries_eq_inverse w d hd

/-- An Euler factor contributes minus d times the n/d power of its character when d divides positive n, and zero otherwise. -/
theorem kloosterman_euler_log_derivative_coefficient (w : ℂ) (d : ℕ) (hd : 0<d)
    (n : ℕ) (hn : 0<n) :
    PowerSeries.coeff n (NField.Alignment.KloostermanFormalLogDerivative.logarithmicDerivative (1-PowerSeries.C w*PowerSeries.X^d)) =
      if d ∣ n then -(d:ℂ)*w^(n/d) else 0 :=
  NField.Alignment.KloostermanFormalLogDerivative.coeff_logarithmicDerivative_eulerFactor w d hd n hn

/-- The logarithmic derivative of the actual L-series has the proved weighted irreducible prime-power coefficient. -/
theorem kloosterman_lseries_prime_power_coefficient (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (n : ℕ) (hn : 0<n) :
    PowerSeries.coeff n (NField.Alignment.KloostermanFormalLogDerivative.logarithmicDerivative (NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m)) =
      NField.Alignment.KloostermanPrimePowerCoefficients.primePowerCoefficient p a b m n :=
  NField.Alignment.KloostermanPrimePowerCoefficients.coeff_logarithmicDerivative_LSeries p a b m n hn

/-- For factors of the actual L-series, the weighted irreducible sum equals the negative root-power sum. -/
theorem kloosterman_prime_power_root_identity (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (α β : ℂ)
    (hf : NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
      (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X))
    (n : ℕ) (hn : 0<n) :
    NField.Alignment.KloostermanPrimePowerCoefficients.primePowerCoefficient p a b m n = -(α^n+β^n) :=
  NField.Alignment.KloostermanPrimePowerCoefficients.primePowerCoefficient_eq_root_powers p a b m α β hf n hn

/-- Actual quadratic factors satisfy the prime-power identity at every positive degree, without assuming an extension-field trace formula. -/
theorem kloosterman_factors_all_prime_power_coefficients (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a≠0) (hb : b≠0) (hm : m≠0) :
    ∃ α β : ℂ, α+β = -NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m ∧
      α*β=p ∧
      NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
        (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X) ∧
      ∀ n : ℕ, 0<n → NField.Alignment.KloostermanPrimePowerCoefficients.primePowerCoefficient p a b m n = -(α^n+β^n) :=
  NField.Alignment.KloostermanPrimePowerCoefficients.exists_factors_primePowerCoefficients p a b m ha hb hm

/-- The actual minimal polynomial of a nonzero inverse is the normalized reverse polynomial. -/
theorem kloosterman_inverse_minpoly {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] (t : K) (ht : t≠0) :
    minpoly F t⁻¹ = (minpoly F t).reverse * Polynomial.C ((minpoly F t).coeff 0)⁻¹ :=
  NField.Alignment.KloostermanMinpolyTrace.minpoly_inverse t ht

/-- The inverse trace is minus the linear/constant coefficient ratio times the exact degree over the simple subfield. -/
theorem kloosterman_inverse_trace {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] (t : K) (ht : t≠0) :
    Algebra.trace F K t⁻¹ = (Module.finrank (IntermediateField.adjoin F {t}) K : F) *
      (-((minpoly F t).coeff 1/(minpoly F t).coeff 0)) :=
  NField.Alignment.KloostermanMinpolyTrace.trace_inverse t ht

/-- The traced inverse-additive phase equals the actual minimal-polynomial coefficient phase with the natural degree quotient. -/
theorem kloosterman_trace_phase_coefficients {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    (a b : ZMod p) (t : K) (ht : t≠0) :
    Algebra.trace (ZMod p) K
      (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t) =
      (Module.finrank (ZMod p) K / (minpoly (ZMod p) t).natDegree : ℕ) *
        (-a*(minpoly (ZMod p) t).nextCoeff-
          b*((minpoly (ZMod p) t).coeff 1/(minpoly (ZMod p) t).coeff 0)) :=
  NField.Alignment.KloostermanMinpolyCharacter.trace_inverse_phase p a b t ht

/-- Every nonzero root of an actual monic irreducible has exactly its prime-power character weight. -/
theorem kloosterman_irreducible_character_trace {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    (a b m : ZMod p) (g : (Polynomial (ZMod p))) (hg : g.Monic) (hi : Irreducible g)
    (t : K) (ht : t≠0) (hr : Polynomial.aeval t g=0) :
    NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m g ^ (Module.finrank (ZMod p) K / g.natDegree) =
      ZMod.stdAddChar (m*Algebra.trace (ZMod p) K
        (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t)) :=
  NField.Alignment.KloostermanMinpolyCharacter.irreducible_character_pow_eq_trace p a b m g hg hi t ht hr

open scoped Classical in
/-- The actual minimal-polynomial fiber has d elements if d divides the extension degree and zero otherwise, proved through finite-field embedding counts. -/
theorem kloosterman_minpoly_fiber_cardinality {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype K] (g : (Polynomial F)) (hg : g.Monic) (hi : Irreducible g) :
    Fintype.card {t : K // minpoly F t=g} =
      if g.natDegree ∣ Module.finrank F K then g.natDegree else 0 :=
  NField.Alignment.KloostermanMinpolyFibers.card_minpoly_fiber g hg hi

/-- The local character identity includes the zero element, whose minimal polynomial X has zero weight. -/
theorem kloosterman_zero_inclusive_character_weight {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
    (a b m : ZMod p) (t : K) :
    (if t=0 then 0 else ZMod.stdAddChar (m*Algebra.trace (ZMod p) K
      (algebraMap (ZMod p) K a*t+algebraMap (ZMod p) K b/t))) =
      NField.Alignment.KloostermanPolynomialCharacter.polynomialCharacter p a b m (minpoly (ZMod p) t) ^
        (Module.finrank (ZMod p) K / (minpoly (ZMod p) t).natDegree) :=
  NField.Alignment.KloostermanMinpolyFibers.element_character_eq_minpoly_weight p a b m t

/-- Grouping actual extension-field elements by minimal polynomial identifies the trace sum with the irreducible prime-power coefficient. -/
theorem kloosterman_extension_prime_power_identity {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] (a b m : ZMod p) :
    NField.Alignment.KloostermanTraceSum.traceKloostermanSum p (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) m =
      NField.Alignment.KloostermanPrimePowerCoefficients.primePowerCoefficient p a b m (Module.finrank (ZMod p) K) :=
  NField.Alignment.KloostermanExtensionTrace.traceKloostermanSum_eq_primePowerCoefficient p a b m

/-- Every finite extension trace sum equals the negative power sum of factors of the actual L-series. -/
theorem kloosterman_extension_root_power_identity {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) K] (a b m : ZMod p) (α β : ℂ)
    (hf : NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
      (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X)) :
    NField.Alignment.KloostermanTraceSum.traceKloostermanSum p (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) m =
      -(α^(Module.finrank (ZMod p) K)+β^(Module.finrank (ZMod p) K)) :=
  NField.Alignment.KloostermanExtensionTrace.traceKloostermanSum_eq_root_powers p a b m α β hf

/-- One pair of actual quadratic factors satisfies the trace identity in every finite extension. -/
theorem kloosterman_roots_all_extensions (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (ha : a≠0) (hb : b≠0) (hm : m≠0) :
    ∃ α β : ℂ, α+β = -NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m ∧ α*β=p ∧
      NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
        (1-PowerSeries.C α*PowerSeries.X)*(1-PowerSeries.C β*PowerSeries.X) ∧
      ∀ (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod p) K],
        NField.Alignment.KloostermanTraceSum.traceKloostermanSum p (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b) m =
          -(α^(Module.finrank (ZMod p) K)+β^(Module.finrank (ZMod p) K)) :=
  NField.Alignment.KloostermanExtensionTrace.exists_factors_all_extensions p a b m ha hb hm

/-- Actual reciprocal-root families are chosen once for all nonzero prime-field frequencies. -/
theorem kloosterman_frequency_root_families (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) :
    ∃ α β : ZMod p → ℂ, ∀ m : ZMod p, m≠0 →
      α m+β m = -NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m ∧ α m*β m=p ∧
      NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
        (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X) :=
  NField.Alignment.KloostermanRootPowerAggregate.exists_root_families p a b ha hb

/-- The literal curve point count equals q-1 minus the aggregate of actual reciprocal-root powers. -/
theorem kloosterman_curve_root_power_count {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [Algebra (ZMod p) K] (a b : ZMod p) (ha : a≠0) (hb : b≠0)
    (h2 : (2:K)≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    (NField.Alignment.StepanovPointCount.pointCount (NField.Alignment.KloostermanCurve.curvePolynomial p
      (algebraMap (ZMod p) K a) (algebraMap (ZMod p) K b)) : ℂ) =
      (Fintype.card K:ℂ)-1-
        ∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          (α m^(Module.finrank (ZMod p) K)+β m^(Module.finrank (ZMod p) K)) :=
  NField.Alignment.KloostermanRootPowerAggregate.curve_pointCount_eq_root_powers p a b ha hb h2 α β hf

/-- Stepanov bounds the norm of the actual root-power aggregate plus one under the stated odd-cardinality and field-size conditions. -/
theorem kloosterman_root_power_aggregate_bound {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [Algebra (ZMod p) K] (a b : ZMod p) (ha : a≠0) (hb : b≠0)
    (hodd : Odd (Fintype.card K)) (hq : 12*p≤Fintype.card K)
    (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    ‖(∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      (α m^(Module.finrank (ZMod p) K)+β m^(Module.finrank (ZMod p) K)))+1‖ <
      8*p*Nat.ceil (Real.sqrt (Fintype.card K : ℝ)) :=
  NField.Alignment.KloostermanRootPowerAggregate.root_power_aggregate_bound p a b ha hb hodd hq α β hf

/-- An eventual exponential bound on unweighted finite power sums bounds each individual root, with repetitions retained. -/
theorem finite_root_norm_of_power_sum_growth {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (R C : ℝ) (hR : 0<R)
    (h : ∀ᶠ n : ℕ in Filter.atTop, ‖∑ i, z i^n‖ ≤ C*R^n) :
    ∀ i, ‖z i‖≤R :=
  NField.Alignment.FinitePowerSumGrowth.norm_le_of_power_sum_growth z R C hR h

/-- Actual fields of cardinality p^n give eventual square-root exponential growth of the fixed reciprocal-root family for odd primes. -/
theorem kloosterman_eventual_root_power_growth (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ‖∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, (α m^n+β m^n)‖ ≤
        (16*p+1)*(Real.sqrt p)^n :=
  NField.Alignment.KloostermanRootModuli.eventual_root_power_growth p hp a b ha hb α β hf

/-- Every actual reciprocal root for nonzero frequency at an odd prime has modulus at most sqrt(p). -/
theorem kloosterman_root_norm_le (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    ∀ m : ZMod p, m≠0 → ‖α m‖≤Real.sqrt p ∧ ‖β m‖≤Real.sqrt p :=
  NField.Alignment.KloostermanRootModuli.root_norm_le p hp a b ha hb α β hf

/-- The exact product p forces both actual reciprocal-root moduli to equal sqrt(p) for odd primes and nonzero parameters. -/
theorem kloosterman_root_norm_eq (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → NField.Alignment.KloostermanQuadraticLSeries.formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X))
    (hprod : ∀ m : ZMod p, m≠0 → α m*β m=p) :
    ∀ m : ZMod p, m≠0 → ‖α m‖=Real.sqrt p ∧ ‖β m‖=Real.sqrt p :=
  NField.Alignment.KloostermanRootModuli.root_norm_eq p hp a b ha hb α β hf hprod

/-- The actual trace Kloosterman sum at an odd prime with all parameters nonzero is bounded by 2*sqrt(p). -/
theorem kloosterman_odd_prime_trace_bound (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b m : ZMod p) (ha : a≠0) (hb : b≠0) (hm : m≠0) :
    ‖NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m‖ ≤ 2*Real.sqrt p :=
  NField.Alignment.KloostermanRootModuli.prime_trace_sum_bound p hp a b m ha hb hm

/-- Inversion permutes the actual nonzero variables and exchanges the two trace-sum parameters. -/
theorem kloosterman_trace_parameter_swap {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (a b : K) (m : ZMod p) :
    NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m = NField.Alignment.KloostermanTraceSum.traceKloostermanSum p b a m :=
  NField.Alignment.KloostermanPrimeBound.trace_sum_swap p a b m

/-- At a prime, one zero parameter and nonzero remaining parameter and frequency give the exact value -1. -/
theorem kloosterman_prime_zero_parameter (p : ℕ) [Fact p.Prime]
    (a m : ZMod p) (ha : a≠0) (hm : m≠0) :
    NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a 0 m = -1 :=
  NField.Alignment.KloostermanPrimeBound.prime_trace_sum_zero_right p a m ha hm

/-- The triangle inequality bounds every prime-field trace sum by p-1, including characteristic two. -/
theorem kloosterman_prime_trivial_bound (p : ℕ) [Fact p.Prime] (a b m : ZMod p) :
    ‖NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m‖ ≤ (p:ℝ)-1 :=
  NField.Alignment.KloostermanPrimeBound.prime_trace_sum_trivial p a b m

/-- The prime-field square-root bound includes p=2 and one zero parameter, with nonzero character frequency. -/
theorem kloosterman_all_prime_trace_bound (p : ℕ) [Fact p.Prime]
    (a b m : ZMod p) (hab : a≠0 ∨ b≠0) (hm : m≠0) :
    ‖NField.Alignment.KloostermanTraceSum.traceKloostermanSum p a b m‖ ≤ 2*Real.sqrt p :=
  NField.Alignment.KloostermanPrimeBound.prime_trace_sum_bound_all p a b m hab hm

/-- The literal complete inverse sum has norm at most 2*sqrt(p) for all primes, coprime r, nonzero j and every completion frequency t, including zero. -/
theorem complete_inverse_sum_prime_bound (p : ℕ) [Fact p.Prime]
    (r : ℕ) (j t : ZMod p) (hr : r.Coprime p) (hj : j≠0) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 2*Real.sqrt p :=
  NField.Alignment.KloostermanPrimeBound.complete_inverse_sum_prime_bound p r j t hr hj

/-- The actual shifted unit has reciprocal u inverse minus d times u inverse squared when d squared is zero. -/
theorem square_zero_unit_inverse {R : Type*} [CommRing R] (u : Rˣ) (d : R) (hd : d^2=0) :
    (((NField.Alignment.SquareZeroUnitShift.shift u d hd)⁻¹ : Rˣ) : R) =
      ((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2 :=
  NField.Alignment.SquareZeroUnitShift.shift_inverse u d hd

/-- The inverse-additive phase changes exactly by its linear term under a square-zero increment. -/
theorem square_zero_inverse_phase_shift {R : Type*} [CommRing R] (a b : R) (u : Rˣ) (d : R) (hd : d^2=0) :
    NField.Alignment.SquareZeroUnitShift.phase a b (NField.Alignment.SquareZeroUnitShift.shift u d hd) = NField.Alignment.SquareZeroUnitShift.phase a b u+d*(a-b*((u⁻¹:Rˣ):R)^2) :=
  NField.Alignment.SquareZeroUnitShift.phase_shift a b u d hd

/-- The square of a unit clears the inverse in the exact critical equation. -/
theorem square_zero_critical_equivalence {R : Type*} [CommRing R] (a b c : R) (u : Rˣ) :
    c*(a-b*((u⁻¹:Rˣ):R)^2)=0 ↔ c*(a*(u:R)^2-b)=0 :=
  NField.Alignment.SquareZeroUnitShift.critical_iff a b c u

/-- Averaging actual unit translations and primitive character orthogonality gives the exact stationary filter in a finite ring. -/
theorem unit_sum_stationary_filter {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b c : R) (hc : c^2=0) :
    NField.Alignment.UnitSumStationaryPhase.unitSum ψ a b = ∑ u : Rˣ, if c*(a*(u:R)^2-b)=0 then ψ (NField.Alignment.SquareZeroUnitShift.phase a b u) else 0 :=
  NField.Alignment.UnitSumStationaryPhase.sum_eq_critical ψ hψ a b c hc

/-- The stationary unit count bounds the actual primitive-character unit sum. -/
theorem unit_sum_stationary_count_bound {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b c : R) (hc : c^2=0) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ψ a b‖ ≤
      ((Finset.univ.filter (fun u : Rˣ => c*(a*(u:R)^2-b)=0)).card:ℝ) :=
  NField.Alignment.UnitSumStationaryPhase.norm_le_critical_count ψ hψ a b c hc

/-- Absence of stationary units makes the literal unit exponential sum zero. -/
theorem unit_sum_zero_without_critical {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b c : R) (hc : c^2=0) (hcrit : ∀ u : Rˣ, c*(a*(u:R)^2-b)≠0) :
    NField.Alignment.UnitSumStationaryPhase.unitSum ψ a b = 0 :=
  NField.Alignment.UnitSumStationaryPhase.sum_eq_zero_of_no_critical ψ hψ a b c hc hcrit

/-- The literal completion sum is the unit phase with A=-t and B=j*r. -/
theorem complete_inverse_as_unit_sum {q : ℕ} [NeZero q]
    (r : ℕ) (j t : ZMod q) :
    NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t = NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar (-t) (j*r) :=
  NField.Alignment.KloostermanPrimePowerStationary.complete_inverse_eq_unitSum r j t

/-- The p^s increment has square zero modulo p^k when k<=2s. -/
theorem prime_power_increment_square_zero (p k s : ℕ) (hs : k≤2*s) :
    ((p : ZMod (p^k))^s)^2=0 :=
  NField.Alignment.KloostermanPrimePowerStationary.power_square_zero p k s hs

/-- Annihilation by p^s is exactly reduction to zero modulo p^(k-s), for s<=k. -/
theorem prime_power_annihilator_reduction (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (x : ZMod (p^k)) :
    (p : ZMod (p^k))^s*x=0 ↔ NField.Alignment.KloostermanPrimePowerStationary.reduction p k s x=0 :=
  NField.Alignment.KloostermanPrimePowerStationary.annihilator_iff_reduction_zero p k s hs x

/-- The cleared stationary equation is exactly the reduced quadratic congruence, without unit assumptions on phase parameters. -/
theorem prime_power_critical_congruence (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (a b : ZMod (p^k)) (u : (ZMod (p^k))ˣ) :
    (p : ZMod (p^k))^s*(a*(u:ZMod (p^k))^2-b)=0 ↔
      NField.Alignment.KloostermanPrimePowerStationary.reduction p k s a*(NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (u:ZMod (p^k)))^2=NField.Alignment.KloostermanPrimePowerStationary.reduction p k s b :=
  NField.Alignment.KloostermanPrimePowerStationary.critical_iff_reduced p k s hs a b u

/-- The original complete inverse sum equals its filtered unit sum at every prime power, retaining all j and t. -/
theorem complete_inverse_prime_power_stationary (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k)) :
    NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t =
      ∑ u : (ZMod (p^k))ˣ,
        if NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (-t)*(NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (u:ZMod (p^k)))^2=
            NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (j*r)
        then ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase (-t) (j*r) u) else 0 :=
  NField.Alignment.KloostermanPrimePowerStationary.complete_inverse_stationary p k s hs hk r j t

/-- Choosing s=ceil(k/2) discharges the stationary-filter exponent conditions for k>=1. -/
theorem complete_inverse_prime_power_half_stationary (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : 1≤k) (r : ℕ) (j t : ZMod (p^k)) :
    NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t =
      ∑ u : (ZMod (p^k))ˣ,
        if NField.Alignment.KloostermanPrimePowerStationary.reduction p k ((k+1)/2) (-t)*(NField.Alignment.KloostermanPrimePowerStationary.reduction p k ((k+1)/2) (u:ZMod (p^k)))^2=
            NField.Alignment.KloostermanPrimePowerStationary.reduction p k ((k+1)/2) (j*r)
        then ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase (-t) (j*r) u) else 0 :=
  NField.Alignment.KloostermanPrimePowerStationary.complete_inverse_half_stationary p k hk r j t

/-- Every unit modulo p^m has exactly p^(k-m) unit lifts modulo p^k for 1<=m<=k. -/
theorem prime_power_unit_lift_cardinality (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m ≤ k) (v : (ZMod (p^m))ˣ) :
    (Finset.univ.filter (fun u : (ZMod (p^k))ˣ =>
      ZMod.unitsMap (Nat.pow_dvd_pow p hmk) u=v)).card = p^(k-m) :=
  NField.Alignment.PrimePowerUnitFibers.card_unit_fiber p k m hm hmk v

open scoped Classical in
/-- Any predicate on the reduced units pulls back with the exact same prime-power multiplicity. -/
theorem prime_power_unit_preimage_cardinality (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m ≤ k) (P : (ZMod (p^m))ˣ → Prop) :
    (Finset.univ.filter (fun u : (ZMod (p^k))ˣ =>
      P (ZMod.unitsMap (Nat.pow_dvd_pow p hmk) u))).card =
      p^(k-m)*(Finset.univ.filter P).card :=
  NField.Alignment.PrimePowerUnitFibers.card_unit_preimage p k m hm hmk P

/-- The literal complete sum is bounded by p^s times the actual reduced quadratic unit-root count, for s<k<=2s. -/
theorem complete_inverse_prime_power_reduced_count_bound (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s<k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k)) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ (p:ℝ)^s*
      ((Finset.univ.filter (fun v : (ZMod (p^(k-s)))ˣ =>
        NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (-t)*(v:ZMod (p^(k-s)))^2=NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (j*r))).card:ℝ) :=
  NField.Alignment.PrimePowerUnitFibers.complete_inverse_norm_le_reduced_count p k s hs hk r j t

/-- Every square-map fiber in a finite cyclic commutative group has at most two elements. -/
theorem cyclic_square_fiber_count {G : Type*} [CommGroup G] [Fintype G]
    [DecidableEq G] [IsCyclic G] (v : G) :
    (Finset.univ.filter (fun u : G => u^2=v)).card ≤ 2 :=
  NField.Alignment.CyclicUnitQuadraticRoots.card_square_fiber_le_two v

/-- The actual quadratic unit-root set has at most two elements when the unit group is cyclic and at least one phase parameter is a unit. -/
theorem cyclic_quadratic_unit_count {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] [IsCyclic Rˣ] (a b : R) (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b)).card ≤ 2 :=
  NField.Alignment.CyclicUnitQuadraticRoots.card_quadratic_units_le_two a b hab

/-- Cyclicity of odd prime-power unit groups supplies the actual two-root bound at every exponent. -/
theorem odd_prime_power_quadratic_unit_count (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (m : ℕ) (a b : ZMod (p^m)) (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : (ZMod (p^m))ˣ => a*(u:ZMod (p^m))^2=b)).card ≤ 2 :=
  NField.Alignment.CyclicUnitQuadraticRoots.odd_prime_power_quadratic_count p hp m a b hab

/-- If precisely one phase parameter is a unit, there are no quadratic unit roots, without an odd-characteristic assumption. -/
theorem quadratic_unit_mismatch_no_roots {R : Type*} [CommRing R]
    (a b : R) (hab : (IsUnit a ∧ ¬IsUnit b) ∨ (¬IsUnit a ∧ IsUnit b)) :
    ∀ u : Rˣ, a*(u:R)^2≠b :=
  NField.Alignment.CyclicUnitQuadraticRoots.no_quadratic_units_of_unit_mismatch a b hab

/-- A unit reduced phase parameter bounds the actual complete sum by 2*p^s at odd primes. -/
theorem odd_prime_power_stationary_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (k s : ℕ) (hs : s<k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k))
    (hab : IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (-t)) ∨ IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (j*r))) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 2*(p:ℝ)^s :=
  NField.Alignment.KloostermanEvenPrimePowerBound.odd_prime_power_stationary_bound p hp k s hs hk r j t hab

/-- An original unit phase parameter supplies the required reduced-unit condition through the actual ring map. -/
theorem odd_prime_power_stationary_bound_of_unit (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (k s : ℕ) (hs : s<k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k))
    (hab : IsUnit (-t) ∨ IsUnit (j*r)) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 2*(p:ℝ)^s :=
  NField.Alignment.KloostermanEvenPrimePowerBound.odd_prime_power_stationary_bound_of_unit p hp k s hs hk r j t hab

/-- At every positive even exponent of an odd prime, the original complete inverse sum is bounded by twice the square root of the modulus when at least one phase parameter is a unit. -/
theorem odd_prime_even_exponent_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 0<h) (r : ℕ) (j t : ZMod (p^(2*h)))
    (hab : IsUnit (-t) ∨ IsUnit (j*r)) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h):ℕ):ℝ) :=
  NField.Alignment.KloostermanEvenPrimePowerBound.even_prime_power_bound p hp h hh r j t hab

/-- A unit frequency and the manuscript coprime multiplier give the even-exponent bound at every completion frequency, including zero. -/
theorem odd_prime_even_exponent_unit_frequency_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 0<h) (r : ℕ) (j t : ZMod (p^(2*h)))
    (hr : r.Coprime (p^(2*h))) (hj : IsUnit j) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h):ℕ):ℝ) :=
  NField.Alignment.KloostermanEvenPrimePowerBound.even_prime_power_bound_unit_frequency p hp h hh r j t hr hj

/-- Precisely one unit reduced phase parameter makes the original complete sum zero, including characteristic two. -/
theorem complete_inverse_reduced_unit_mismatch_zero (p : ℕ) [Fact p.Prime]
    (k s : ℕ) (hs : s≤k) (hk : k≤2*s) (r : ℕ) (j t : ZMod (p^k))
    (hab : (IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (-t)) ∧ ¬IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (j*r))) ∨
      (¬IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (-t)) ∧ IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction p k s (j*r)))) :
    NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t=0 :=
  NField.Alignment.KloostermanEvenPrimePowerBound.complete_inverse_zero_of_reduced_unit_mismatch p k s hs hk r j t hab

/-- The literal quadratic additive sum times its conjugate equals the field cardinality by exact primitive orthogonality. -/
theorem quadratic_additive_gauss_squared_identity {F : Type*} [Field F] [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (ha : a≠0) (h2 : (2:F)≠0) :
    NField.Alignment.QuadraticAdditiveGauss.quadraticSum ψ a b*(starRingEnd ℂ) (NField.Alignment.QuadraticAdditiveGauss.quadraticSum ψ a b) = Fintype.card F :=
  NField.Alignment.QuadraticAdditiveGauss.quadratic_sum_mul_conj ψ hψ a b ha h2

/-- The literal finite-field quadratic sum has norm sqrt(card(F)) for nonzero quadratic coefficient and characteristic not two. -/
theorem quadratic_additive_gauss_norm {F : Type*} [Field F] [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (ha : a≠0) (h2 : (2:F)≠0) :
    ‖NField.Alignment.QuadraticAdditiveGauss.quadraticSum ψ a b‖ = Real.sqrt (Fintype.card F:ℝ) :=
  NField.Alignment.QuadraticAdditiveGauss.norm_quadratic_sum ψ hψ a b ha h2

/-- The actual standard-character quadratic sum at an odd prime has norm sqrt(p) for every linear coefficient. -/
theorem odd_prime_quadratic_additive_gauss_norm (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (a b : ZMod p) (ha : a≠0) :
    ‖NField.Alignment.QuadraticAdditiveGauss.quadraticSum ZMod.stdAddChar a b‖=Real.sqrt p :=
  NField.Alignment.QuadraticAdditiveGauss.norm_prime_quadratic_sum p hp a b ha

/-- The actual shifted unit has its exact inverse expansion through degree two when the increment cubed is zero. -/
theorem cube_zero_unit_inverse {R : Type*} [CommRing R] (u : Rˣ) (d : R) (hd : d^3=0) :
    (((NField.Alignment.CubeZeroUnitShift.shift u d hd)⁻¹:Rˣ):R)=
      ((u⁻¹:Rˣ):R)-d*((u⁻¹:Rˣ):R)^2+d^2*((u⁻¹:Rˣ):R)^3 :=
  NField.Alignment.CubeZeroUnitShift.shift_inverse u d hd

/-- The inverse-additive phase retains the exact quadratic term under a cube-zero increment. -/
theorem cube_zero_inverse_phase_shift {R : Type*} [CommRing R] (a b : R) (u : Rˣ) (d : R) (hd : d^3=0) :
    NField.Alignment.SquareZeroUnitShift.phase a b (NField.Alignment.CubeZeroUnitShift.shift u d hd) =
      NField.Alignment.SquareZeroUnitShift.phase a b u+d*(a-b*((u⁻¹:Rˣ):R)^2)+
        d^2*(b*((u⁻¹:Rˣ):R)^3) :=
  NField.Alignment.CubeZeroUnitShift.phase_shift a b u d hd

/-- A p^h multiple has cube zero modulo p^(2h+1) for h>=1. -/
theorem odd_exponent_increment_cube_zero (p h : ℕ) (hh : 1≤h) (z : ZMod (p^(2*h+1))) :
    ((p:ZMod (p^(2*h+1)))^h*z)^3=0 :=
  NField.Alignment.CubeZeroUnitShift.power_cube_zero p h hh z

/-- The actual odd-exponent modulus satisfies the quadratic inverse-phase formula with the cube-zero condition discharged. -/
theorem odd_exponent_exact_quadratic_phase (p h : ℕ) (hh : 1≤h)
    (a b z : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ) :
    NField.Alignment.SquareZeroUnitShift.phase a b
      (NField.Alignment.CubeZeroUnitShift.shift u ((p:ZMod (p^(2*h+1)))^h*z) (NField.Alignment.CubeZeroUnitShift.power_cube_zero p h hh z)) =
    NField.Alignment.SquareZeroUnitShift.phase a b u+
      ((p:ZMod (p^(2*h+1)))^h*z)*(a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2)+
      ((p:ZMod (p^(2*h+1)))^h*z)^2*
        (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3) :=
  NField.Alignment.CubeZeroUnitShift.odd_exponent_phase_shift p h hh a b z u

/-- Multiplication by m embeds the smaller residue ring additively when m*n=q and m is nonzero. -/
theorem scaled_residue_lift_injective (m n q : ℕ) (hm : m≠0) (hq : m*n=q) :
    Function.Injective (NField.Alignment.ScaledResidueLift.scaledLift m n q hq) :=
  NField.Alignment.ScaledResidueLift.scaledLift_injective m n q hm hq

/-- The actual scaled lift preserves the standard additive character exactly. -/
theorem standard_character_scaled_lift (m n q : ℕ) [NeZero m] [NeZero n] [NeZero q]
    (hq : m*n=q) (z : ZMod n) :
    ZMod.stdAddChar (NField.Alignment.ScaledResidueLift.scaledLift m n q hq z)=ZMod.stdAddChar z :=
  NField.Alignment.ScaledResidueLift.stdAddChar_scaledLift m n q hq z

/-- A phase divisible by m has exactly the standard character modulo q/m. -/
theorem standard_character_scaled_phase (m n q : ℕ) [NeZero m] [NeZero n] [NeZero q]
    (hq : m*n=q) (x : ZMod q) :
    ZMod.stdAddChar ((m:ZMod q)*x) =
      ZMod.stdAddChar (ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n) x) :=
  NField.Alignment.ScaledResidueLift.stdAddChar_scaled_phase m n q hq x

/-- The explicit cube-zero unit lift belongs to the original reduction fiber. -/
theorem odd_exponent_unit_lift_reduces (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) (z : ZMod (p^(h+1))) :
    NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h (NField.Alignment.OddPrimePowerUnitLifts.unitLift p h hh u z)=NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u :=
  NField.Alignment.OddPrimePowerUnitLifts.unitLift_reduces p h hh u z

/-- Distinct additive residues give distinct unit lifts. -/
theorem odd_exponent_unit_lift_injective (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) : Function.Injective (NField.Alignment.OddPrimePowerUnitLifts.unitLift p h hh u) :=
  NField.Alignment.OddPrimePowerUnitLifts.unitLift_injective p h hh u

/-- The explicit bijection rewrites the actual sum over a unit-reduction fiber. -/
theorem odd_exponent_unit_fiber_sum (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (u : (ZMod (p^(2*h+1)))ˣ) (f : (ZMod (p^(2*h+1)))ˣ → ℂ) :
    (∑ v ∈ Finset.univ.filter (fun v => NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h v=NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u), f v) =
      ∑ z : ZMod (p^(h+1)), f (NField.Alignment.OddPrimePowerUnitLifts.unitLift p h hh u z) :=
  NField.Alignment.OddPrimePowerUnitLifts.sum_unit_fiber p h hh u f

/-- Every additive reduction fiber from modulus m*n to n has exactly m elements. -/
theorem residue_reduction_fiber_card (m n q : ℕ) [NeZero n] [NeZero q]
    (hq : m*n=q) (y : ZMod n) :
    (Finset.univ.filter (fun x : ZMod q =>
      ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n) x=y)).card=m :=
  NField.Alignment.ResidueReductionSum.card_reduction_fiber m n q hq y

/-- Pulling a sum back under residue reduction multiplies it by the exact fiber cardinality. -/
theorem residue_reduction_sum (m n q : ℕ) [NeZero n] [NeZero q]
    (hq : m*n=q) (f : ZMod n → ℂ) :
    (∑ x : ZMod q,
      f (ZMod.castHom (show n∣q from hq ▸ dvd_mul_left n m) (ZMod n) x)) =
        (m:ℂ)*∑ y : ZMod n, f y :=
  NField.Alignment.ResidueReductionSum.sum_reduction m n q hq f

/-- The actual lifted phase factors as its constant character times a prime-field quadratic character. -/
theorem odd_exponent_lift_character (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (a b ℓ : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hder : a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
      (p:ZMod (p^(2*h+1)))^h*ℓ) (z : ZMod (p^(h+1))) :
    ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b (NField.Alignment.OddPrimePowerUnitLifts.unitLift p h hh u z)) =
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b u)*ZMod.stdAddChar
        (NField.Alignment.OddPrimePowerFiberGauss.primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)*
          (NField.Alignment.OddPrimePowerFiberGauss.primeReduction p h z)^2+NField.Alignment.OddPrimePowerFiberGauss.primeReduction p (2*h) ℓ*NField.Alignment.OddPrimePowerFiberGauss.primeReduction p h z) :=
  NField.Alignment.OddPrimePowerFiberGauss.character_unitLift p h hh a b ℓ u hder z

/-- The actual unit-fiber sum equals its constant phase times p^h times the literal quadratic Gauss sum. -/
theorem odd_exponent_fiber_gauss_identity (p : ℕ) [Fact p.Prime] (h : ℕ) (hh : 1≤h)
    (a b ℓ : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hder : a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
      (p:ZMod (p^(2*h+1)))^h*ℓ) :
    (∑ v ∈ Finset.univ.filter (fun v => NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h v=NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u),
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b v)) =
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b u)*(p:ℂ)^h*
        NField.Alignment.QuadraticAdditiveGauss.quadraticSum ZMod.stdAddChar
          (NField.Alignment.OddPrimePowerFiberGauss.primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3))
          (NField.Alignment.OddPrimePowerFiberGauss.primeReduction p (2*h) ℓ) :=
  NField.Alignment.OddPrimePowerFiberGauss.sum_unit_fiber_eq_gauss p h hh a b ℓ u hder

/-- With explicit derivative factor and nonzero quadratic coefficient the actual fiber norm is p^h*sqrt(p). -/
theorem odd_exponent_fiber_gauss_norm (p : ℕ) [Fact p.Prime] (hp : p≠2) (h : ℕ) (hh : 1≤h)
    (a b ℓ : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hder : a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
      (p:ZMod (p^(2*h+1)))^h*ℓ)
    (hc : NField.Alignment.OddPrimePowerFiberGauss.primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)≠0) :
    ‖∑ v ∈ Finset.univ.filter (fun v => NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h v=NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u),
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b v)‖ = (p:ℝ)^h*Real.sqrt p :=
  NField.Alignment.OddPrimePowerFiberGauss.norm_unit_fiber p hp h hh a b ℓ u hder hc

/-- Zero after reduction implies an actual multiplicative factor in the original residue ring. -/
theorem residue_factor_of_zero_reduction (m q : ℕ) [NeZero q] (hm : m∣q)
    (x : ZMod q) (hx : ZMod.castHom hm (ZMod m) x=0) :
    ∃ z : ZMod q, x=(m:ZMod q)*z :=
  NField.Alignment.OddPrimePowerStationaryFiber.exists_factor_of_reduction_zero m q hm x hx

/-- The reduced stationary equation supplies the derivative factor, rather than assuming it. -/
theorem odd_stationary_derivative_factor (p : ℕ) [Fact p.Prime] (h : ℕ)
    (a b : ZMod (p^(2*h+1))) (u : (ZMod (p^(2*h+1)))ˣ)
    (hcrit : NField.Alignment.OddPrimePowerStationaryFiber.halfReduction p h a*(NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u:ZMod (p^h))^2=
      NField.Alignment.OddPrimePowerStationaryFiber.halfReduction p h b) :
    ∃ ℓ : ZMod (p^(2*h+1)),
      a-b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^2=
        (p:ZMod (p^(2*h+1)))^h*ℓ :=
  NField.Alignment.OddPrimePowerStationaryFiber.stationary_derivative_factor p h a b u hcrit

/-- A unit inverse-phase coefficient gives a nonzero prime-field quadratic coefficient. -/
theorem odd_stationary_quadratic_coefficient (p : ℕ) [Fact p.Prime] (h : ℕ)
    (b : ZMod (p^(2*h+1))) (hb : IsUnit b) (u : (ZMod (p^(2*h+1)))ˣ) :
    NField.Alignment.OddPrimePowerFiberGauss.primeReduction p (2*h) (b*((u⁻¹:(ZMod (p^(2*h+1)))ˣ):ZMod (p^(2*h+1)))^3)≠0 :=
  NField.Alignment.OddPrimePowerStationaryFiber.quadratic_coefficient_ne_zero p h b hb u

/-- The stationary equation and unit b discharge all auxiliary conditions for the exact fiber norm. -/
theorem odd_stationary_fiber_norm (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (a b : ZMod (p^(2*h+1))) (hb : IsUnit b)
    (u : (ZMod (p^(2*h+1)))ˣ)
    (hcrit : NField.Alignment.OddPrimePowerStationaryFiber.halfReduction p h a*(NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u:ZMod (p^h))^2=
      NField.Alignment.OddPrimePowerStationaryFiber.halfReduction p h b) :
    ‖∑ v ∈ Finset.univ.filter (fun v => NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h v=NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u),
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b v)‖ = (p:ℝ)^h*Real.sqrt p :=
  NField.Alignment.OddPrimePowerStationaryFiber.norm_stationary_fiber p hp h hh a b hb u hcrit

/-- The actual unit sum equals the sum of literal fibers over the reduced quadratic roots. -/
theorem odd_unit_sum_stationary_fibers (p : ℕ) [Fact p.Prime] (h : ℕ)
    (a b : ZMod (p^(2*h+1))) :
    NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b =
      ∑ v ∈ Finset.univ.filter (fun v : (ZMod (p^h))ˣ =>
        NField.Alignment.OddPrimePowerStationaryFiber.halfReduction p h a*(v:ZMod (p^h))^2=NField.Alignment.OddPrimePowerStationaryFiber.halfReduction p h b),
        ∑ u ∈ Finset.univ.filter (fun u => NField.Alignment.OddPrimePowerUnitLifts.unitReduction p h u=v),
          ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b u) :=
  NField.Alignment.KloostermanOddPrimePowerBound.unitSum_stationary_fibers p h a b

/-- At most two stationary classes give the actual unit sum norm at most 2*p^h*sqrt(p), for odd p, h>=1 and unit b. -/
theorem odd_unit_sum_square_root_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (a b : ZMod (p^(2*h+1))) (hb : IsUnit b) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖ ≤ 2*((p:ℝ)^h*Real.sqrt p) :=
  NField.Alignment.KloostermanOddPrimePowerBound.norm_unitSum_le p hp h hh a b hb

/-- The Gauss norm factor p^h*sqrt(p) is exactly sqrt(p^(2h+1)). -/
theorem odd_prime_power_square_root_factor (p h : ℕ) :
    (p:ℝ)^h*Real.sqrt p=Real.sqrt ((p^(2*h+1):ℕ):ℝ) :=
  NField.Alignment.KloostermanOddPrimePowerBound.odd_sqrt_factor p h

/-- The original complete inverse sum has norm at most 2*sqrt(p^(2h+1)) for odd p, h>=1 and unit j*r. -/
theorem odd_prime_odd_exponent_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (r : ℕ) (j t : ZMod (p^(2*h+1))) (hb : IsUnit (j*r)) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h+1):ℕ):ℝ) :=
  NField.Alignment.KloostermanOddPrimePowerBound.odd_prime_power_bound p hp h hh r j t hb

/-- Unit j and coprime r give the odd-exponent bound for every t, including zero. -/
theorem odd_prime_odd_exponent_unit_frequency_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (h : ℕ) (hh : 1≤h) (r : ℕ) (j t : ZMod (p^(2*h+1)))
    (hr : r.Coprime (p^(2*h+1))) (hj : IsUnit j) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 2*Real.sqrt ((p^(2*h+1):ℕ):ℝ) :=
  NField.Alignment.KloostermanOddPrimePowerBound.odd_prime_power_bound_unit_frequency p hp h hh r j t hr hj

/-- The square-map kernel modulo 2^(n+3) has at most four elements, using the order of 5. -/
theorem power_two_square_kernel_count (n : ℕ) :
    Nat.card (powMonoidHom (α := (ZMod (2^(n+3)))ˣ) 2).ker ≤ 4 :=
  NField.Alignment.TwoPowerUnitQuadraticRoots.square_kernel_card_le_four n

/-- Every unit square-map fiber modulo 2^m has at most four elements, including small exponents. -/
theorem power_two_square_fiber_count (m : ℕ) (v : (ZMod (2^m))ˣ) :
    (Finset.univ.filter (fun u : (ZMod (2^m))ˣ => u^2=v)).card ≤ 4 :=
  NField.Alignment.TwoPowerUnitQuadraticRoots.card_square_fiber_le_four m v

/-- A square-fiber bound transfers to the actual quadratic unit roots when at least one coefficient is a unit. -/
theorem quadratic_unit_count_of_square_fibers {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] (C : ℕ)
    (hsq : ∀ v : Rˣ, (Finset.univ.filter (fun u : Rˣ => u^2=v)).card≤C)
    (a b : R) (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : Rˣ => a*(u:R)^2=b)).card ≤ C :=
  NField.Alignment.TwoPowerUnitQuadraticRoots.card_quadratic_units_le_of_square_bound C hsq a b hab

/-- The actual quadratic unit-root set modulo 2^m has at most four elements under the unit condition. -/
theorem power_two_quadratic_unit_count (m : ℕ) (a b : ZMod (2^m))
    (hab : IsUnit a ∨ IsUnit b) :
    (Finset.univ.filter (fun u : (ZMod (2^m))ˣ => a*(u:ZMod (2^m))^2=b)).card ≤ 4 :=
  NField.Alignment.TwoPowerUnitQuadraticRoots.two_power_quadratic_count m a b hab

/-- The literal complete sum modulo 2^k is bounded by 4*2^s with the actual reduced-unit condition. -/
theorem power_two_stationary_bound (k s : ℕ) (hs : s<k) (hk : k≤2*s)
    (r : ℕ) (j t : ZMod (2^k))
    (hab : IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction 2 k s (-t)) ∨ IsUnit (NField.Alignment.KloostermanPrimePowerStationary.reduction 2 k s (j*r))) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 4*(2:ℝ)^s :=
  NField.Alignment.KloostermanTwoPowerBound.two_power_stationary_bound k s hs hk r j t hab

/-- The half-exponent loss at the fixed prime two is uniformly at most twice the square root. -/
theorem power_two_half_exponent_sqrt_bound (k : ℕ) :
    (2:ℝ)^((k+1)/2) ≤ 2*Real.sqrt ((2^k:ℕ):ℝ) :=
  NField.Alignment.KloostermanTwoPowerBound.half_power_le_two_sqrt k

/-- At k>=2, a unit phase parameter bounds the actual complete sum modulo 2^k by 8*sqrt(2^k). -/
theorem power_two_primitive_complete_bound (k : ℕ) (hk : 2≤k) (r : ℕ) (j t : ZMod (2^k))
    (hab : IsUnit (-t) ∨ IsUnit (j*r)) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 8*Real.sqrt ((2^k:ℕ):ℝ) :=
  NField.Alignment.KloostermanTwoPowerBound.two_power_bound k hk r j t hab

/-- Unit j and coprime r give the powers-of-two bound for every t. -/
theorem power_two_unit_frequency_bound (k : ℕ) (hk : 2≤k) (r : ℕ) (j t : ZMod (2^k))
    (hr : r.Coprime (2^k)) (hj : IsUnit j) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ 8*Real.sqrt ((2^k:ℕ):ℝ) :=
  NField.Alignment.KloostermanTwoPowerBound.two_power_bound_unit_frequency k hk r j t hr hj

/-- Inversion swaps the two parameters of the actual finite-ring unit sum. -/
theorem actual_unit_sum_parameter_swap {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (a b : R) : NField.Alignment.UnitSumStationaryPhase.unitSum ψ a b=NField.Alignment.UnitSumStationaryPhase.unitSum ψ b a :=
  NField.Alignment.PrimitivePrimePowerBound.unitSum_swap ψ a b

/-- At every prime, the literal unit sum has norm at most 2*sqrt(p) when either phase parameter is a unit. -/
theorem prime_unit_sum_bound (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hab : IsUnit a ∨ IsUnit b) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖ ≤ 2*Real.sqrt p :=
  NField.Alignment.PrimitivePrimePowerBound.prime_unitSum_bound p a b hab

/-- Every positive exponent of an odd prime has constant two for either unit phase parameter. -/
theorem odd_prime_all_exponents_unit_bound (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (k : ℕ) (hk : 1≤k) (a b : ZMod (p^k)) (hab : IsUnit a ∨ IsUnit b) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖ ≤ 2*Real.sqrt ((p^k:ℕ):ℝ) :=
  NField.Alignment.PrimitivePrimePowerBound.odd_prime_unitSum_bound p hp k hk a b hab

/-- Every positive exponent of two has a uniform constant eight for either unit phase parameter. -/
theorem power_two_all_exponents_unit_bound (k : ℕ) (hk : 1≤k)
    (a b : ZMod (2^k)) (hab : IsUnit a ∨ IsUnit b) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖ ≤ 8*Real.sqrt ((2^k:ℕ):ℝ) :=
  NField.Alignment.PrimitivePrimePowerBound.two_power_unitSum_bound k hk a b hab

/-- All positive prime-power exponents are covered, retaining constant two at odd primes and eight only at two. -/
theorem all_prime_power_primitive_unit_bound (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1≤k)
    (a b : ZMod (p^k)) (hab : IsUnit a ∨ IsUnit b) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖ ≤ (if p=2 then 8 else 2)*Real.sqrt ((p^k:ℕ):ℝ) :=
  NField.Alignment.PrimitivePrimePowerBound.prime_power_unitSum_bound p k hk a b hab

/-- Unit j and coprime r give the complete inverse-sum bound at every positive prime-power modulus and every t. -/
theorem all_prime_power_unit_frequency_bound (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : 1≤k) (r : ℕ) (j t : ZMod (p^k))
    (hr : r.Coprime (p^k)) (hj : IsUnit j) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖ ≤ (if p=2 then 8 else 2)*Real.sqrt ((p^k:ℕ):ℝ) :=
  NField.Alignment.PrimitivePrimePowerBound.complete_prime_power_bound_unit_frequency p k hk r j t hr hj

/-- Actual unit reduction from p^k to p^m pulls sums back with exactly p^(k-m) copies. -/
theorem prime_power_unit_reduction_sum (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (f : (ZMod (p^m))ˣ → ℂ) :
    (∑ u : (ZMod (p^k))ˣ, f (NField.Alignment.PrimePowerContentReduction.unitReduction p k m hmk u)) =
      (p:ℂ)^(k-m)*∑ v : (ZMod (p^m))ˣ, f v :=
  NField.Alignment.PrimePowerContentReduction.sum_unit_reduction p k m hm hmk f

/-- The actual phase commutes with ring and unit reduction. -/
theorem prime_power_actual_phase_reduction (p k m : ℕ) (hmk : m≤k)
    (a b : ZMod (p^k)) (u : (ZMod (p^k))ˣ) :
    NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk (NField.Alignment.SquareZeroUnitShift.phase a b u)=
      NField.Alignment.SquareZeroUnitShift.phase (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk a) (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk b)
        (NField.Alignment.PrimePowerContentReduction.unitReduction p k m hmk u) :=
  NField.Alignment.PrimePowerContentReduction.phase_reduction p k m hmk a b u

/-- A common factor p^(k-m) in both phase parameters gives exactly the standard character modulo p^m. -/
theorem prime_power_common_factor_character (p : ℕ) [Fact p.Prime] (k m : ℕ) (hmk : m≤k)
    (a b : ZMod (p^k)) (u : (ZMod (p^k))ˣ) :
    ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b) u)=
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk a) (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk b)
        (NField.Alignment.PrimePowerContentReduction.unitReduction p k m hmk u)) :=
  NField.Alignment.PrimePowerContentReduction.character_scaled_phase p k m hmk a b u

/-- The literal unit sum with specified common content equals p^(k-m) times the actual reduced sum. -/
theorem prime_power_exact_content_reduction (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k)) :
    NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)=
      (p:ℂ)^(k-m)*NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar
        (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk a) (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk b) :=
  NField.Alignment.PrimePowerContentReduction.unitSum_content_reduction p k m hm hmk a b

/-- The same exact multiplicity factors out of the actual norm. -/
theorem prime_power_exact_content_norm (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k)) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)‖=
      (p:ℝ)^(k-m)*‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar
        (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk a) (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk b)‖ :=
  NField.Alignment.PrimePowerContentReduction.norm_content_reduction p k m hm hmk a b

/-- A specified common factor and primitive reduced phase give the proved local estimate with all parameters retained. -/
theorem prime_power_specified_content_bound (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k))
    (hab : IsUnit (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk a) ∨ IsUnit (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk b)) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)‖≤
      (p:ℝ)^(k-m)*((if p=2 then 8 else 2)*Real.sqrt ((p^m:ℕ):ℝ)) :=
  NField.Alignment.PrimePowerContentReduction.content_bound p k m hm hmk a b hab

/-- The extracted-content factor has the exact form sqrt(p^k)*sqrt(p^(k-m)). -/
theorem prime_power_content_sqrt_factor (p k m : ℕ) (hmk : m≤k) :
    (p:ℝ)^(k-m)*Real.sqrt ((p^m:ℕ):ℝ)=
      Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt ((p^(k-m):ℕ):ℝ) :=
  NField.Alignment.PrimePowerContentReduction.sqrt_content_factor p k m hmk

/-- The actual sum with specified common content has the square-root bound, conditional only on the explicit reduced-unit condition. -/
theorem prime_power_content_square_root_bound (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hm : 1 ≤ m) (hmk : m≤k) (a b : ZMod (p^k))
    (hab : IsUnit (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk a) ∨ IsUnit (NField.Alignment.PrimePowerContentReduction.ringReduction p k m hmk b)) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar ((p:ZMod (p^k))^(k-m)*a) ((p:ZMod (p^k))^(k-m)*b)‖≤
      (if p=2 then 8 else 2)*Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt ((p^(k-m):ℕ):ℝ) :=
  NField.Alignment.PrimePowerContentReduction.content_bound_sqrt p k m hm hmk a b hab

/-- A nonunit at positive prime-power exponent has a prime-divisible canonical representative. -/
theorem nonunit_prime_divides_representative (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k)
    (x : ZMod (p^k)) (hx : ¬IsUnit x) : p∣x.val :=
  NField.Alignment.PrimePowerGcdDescent.prime_dvd_val_of_nonunit p k hk x hx

/-- The canonical quotient by p lies below the smaller modulus. -/
theorem prime_quotient_representative_range (p : ℕ) [Fact p.Prime] (k : ℕ) (x : ZMod (p^(k+1))) :
    x.val/p<p^k :=
  NField.Alignment.PrimePowerGcdDescent.quotient_val_lt p k x

/-- A prime-divisible residue equals p times its canonical quotient. -/
theorem exact_prime_quotient_factor (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) (hx : p∣x.val) :
    x=(p:ZMod (p^(k+1)))*(x.val/p:ZMod (p^(k+1))) :=
  NField.Alignment.PrimePowerGcdDescent.residue_eq_prime_mul_quotient p k x hx

/-- The reduced quotient has its exact canonical representative without wrapping. -/
theorem reduced_prime_quotient_representative (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) : (x.val/p:ZMod (p^k)).val=x.val/p :=
  NField.Alignment.PrimePowerGcdDescent.reduced_quotient_val p k x

/-- Canonical prime division gives the exact gcd recurrence. -/
theorem exact_prime_quotient_gcd (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) (hx : p∣x.val) :
    Nat.gcd x.val (p^(k+1))=p*Nat.gcd (x.val/p:ZMod (p^k)).val (p^k) :=
  NField.Alignment.PrimePowerGcdDescent.gcd_quotient p k x hx

/-- A nonzero prime-divisible residue forces a positive lower exponent. -/
theorem nonzero_nonunit_lower_exponent (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^(k+1))) (hx : x≠0) (hd : p∣x.val) : 1≤k :=
  NField.Alignment.PrimePowerGcdDescent.positive_lower_exponent p k x hx hd

/-- Removing a common prime factor gives an exact norm recurrence for the literal unit sum. -/
theorem actual_unit_sum_prime_descent (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1≤k)
    (a b : ZMod (p^(k+1))) (ha : p∣a.val) (hb : p∣b.val) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖=(p:ℝ)*
      ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar (a.val/p:ZMod (p^k)) (b.val/p:ZMod (p^k))‖ :=
  NField.Alignment.PrimePowerGcdDescent.norm_prime_descent p k hk a b ha hb

/-- The norm recurrence factor p agrees exactly with the two square-root factors. -/
theorem prime_gcd_square_root_scaling (p k g : ℕ) :
    (p:ℝ)*(Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt (g:ℝ))=
      Real.sqrt ((p^(k+1):ℕ):ℝ)*Real.sqrt ((p*g:ℕ):ℝ) :=
  NField.Alignment.PrimePowerGcdDescent.sqrt_gcd_descent_factor p k g

/-- The local estimate constant is at least one. -/
theorem prime_local_constant_lower_bound (p : ℕ) : 1≤NField.Alignment.PrimePowerGcdBound.localConstant p :=
  NField.Alignment.PrimePowerGcdBound.one_le_localConstant p

/-- The actual unit sum is bounded by the full modulus for all phase parameters. -/
theorem actual_unit_sum_trivial_bound (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖≤(q:ℝ) :=
  NField.Alignment.PrimePowerGcdBound.norm_unitSum_le_modulus q a b

/-- A zero inverse-phase coefficient satisfies the same gcd-shaped bound. -/
theorem zero_frequency_local_gcd_bound (q : ℕ) [NeZero q] (C : ℝ) (hC : 1≤C) (a : ZMod q) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a 0‖≤C*Real.sqrt (q:ℝ)*Real.sqrt (Nat.gcd (0:ZMod q).val q:ℝ) :=
  NField.Alignment.PrimePowerGcdBound.zero_right_gcd_bound q C hC a

/-- The full local estimate is proved for every exponent and arbitrary phase parameters, including zeros. -/
theorem all_prime_power_actual_gcd_bound (p : ℕ) [Fact p.Prime] (k : ℕ)
    (a b : ZMod (p^k)) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖≤
      NField.Alignment.PrimePowerGcdBound.localConstant p*Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt (Nat.gcd b.val (p^k):ℝ) :=
  NField.Alignment.PrimePowerGcdBound.prime_power_unitSum_gcd_bound p k a b

/-- Multiplication by an actual unit preserves the canonical representative gcd. -/
theorem frequency_gcd_invariant_under_unit (q : ℕ) [NeZero q] (x y : ZMod q) (hy : IsUnit y) :
    Nat.gcd (x*y).val q=Nat.gcd x.val q :=
  NField.Alignment.PrimePowerGcdBound.gcd_val_mul_unit q x y hy

/-- The manuscript coprime multiplier preserves the exact frequency gcd. -/
theorem frequency_gcd_invariant_under_coprime (q : ℕ) [NeZero q] (j : ZMod q) (r : ℕ) (hr : r.Coprime q) :
    Nat.gcd (j*r).val q=Nat.gcd j.val q :=
  NField.Alignment.PrimePowerGcdBound.gcd_val_mul_coprime q j r hr

/-- The original complete sum has the full prime-power gcd estimate, without a unit-frequency or nonzero-frequency hypothesis. -/
theorem complete_prime_power_full_gcd_bound (p : ℕ) [Fact p.Prime] (k : ℕ)
    (r : ℕ) (j t : ZMod (p^k)) (hr : r.Coprime (p^k)) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖≤
      NField.Alignment.PrimePowerGcdBound.localConstant p*Real.sqrt ((p^k:ℕ):ℝ)*Real.sqrt (Nat.gcd j.val (p^k):ℝ) :=
  NField.Alignment.PrimePowerGcdBound.complete_inverse_prime_power_gcd_bound p k r j t hr

/-- The left standard-character CRT twist is an actual unit. -/
theorem crt_left_character_twist_unit (m n : ℕ) (h : m.Coprime n) : IsUnit (NField.Alignment.KloostermanCRT.leftTwist m n) :=
  NField.Alignment.KloostermanCRT.leftTwist_isUnit m n h

/-- The right standard-character CRT twist is an actual unit. -/
theorem crt_right_character_twist_unit (m n : ℕ) (h : m.Coprime n) : IsUnit (NField.Alignment.KloostermanCRT.rightTwist m n) :=
  NField.Alignment.KloostermanCRT.rightTwist_isUnit m n h

/-- The standard additive character factors with the exact Bezout twists. -/
theorem standard_additive_character_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m*n)) :
    ZMod.stdAddChar x=
      ZMod.stdAddChar (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n x)*
      ZMod.stdAddChar (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n x) :=
  NField.Alignment.KloostermanCRT.standard_character_crt m n h x

/-- The left component of the actual CRT unit equivalence is the canonical reduction. -/
theorem crt_unit_equivalence_left_reduction (m n : ℕ) (h : m.Coprime n) (u : (ZMod (m*n))ˣ) :
    (NField.Alignment.KloostermanCRT.unitEquiv m n h u).1=ZMod.unitsMap (dvd_mul_right m n) u :=
  NField.Alignment.KloostermanCRT.unitEquiv_fst m n h u

/-- The right component of the actual CRT unit equivalence is the canonical reduction. -/
theorem crt_unit_equivalence_right_reduction (m n : ℕ) (h : m.Coprime n) (u : (ZMod (m*n))ˣ) :
    (NField.Alignment.KloostermanCRT.unitEquiv m n h u).2=ZMod.unitsMap (dvd_mul_left n m) u :=
  NField.Alignment.KloostermanCRT.unitEquiv_snd m n h u

/-- The original phase character equals the product of the two twisted local phase characters. -/
theorem actual_inverse_phase_character_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (a b : ZMod (m*n)) (u : (ZMod (m*n))ˣ) :
    ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase a b u)=
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n a)
        (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n b) (NField.Alignment.KloostermanCRT.unitEquiv m n h u).1)*
      ZMod.stdAddChar (NField.Alignment.SquareZeroUnitShift.phase (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n a)
        (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n b) (NField.Alignment.KloostermanCRT.unitEquiv m n h u).2) :=
  NField.Alignment.KloostermanCRT.phase_character_crt m n h a b u

/-- The literal complete unit sum factors exactly across coprime moduli. -/
theorem actual_unit_sum_crt_product (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (a b : ZMod (m*n)) :
    NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b=
      NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n a) (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n b)*
      NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n a) (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n b) :=
  NField.Alignment.KloostermanCRT.unitSum_crt m n h a b

/-- The exact CRT product also factors the actual norm. -/
theorem actual_unit_sum_crt_norm (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (a b : ZMod (m*n)) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖=
      ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n a) (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n b)‖*
      ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n a) (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n b)‖ :=
  NField.Alignment.KloostermanCRT.norm_unitSum_crt m n h a b

/-- The left character twist preserves the local frequency gcd, including zero. -/
theorem crt_left_twist_gcd_invariance (m n : ℕ) [NeZero m] (h : m.Coprime n) (b : ZMod (m*n)) :
    Nat.gcd (NField.Alignment.KloostermanCRT.leftTwist m n*NField.Alignment.KloostermanCRT.leftReduction m n b).val m=Nat.gcd (NField.Alignment.KloostermanCRT.leftReduction m n b).val m :=
  NField.Alignment.KloostermanCRT.left_twist_gcd m n h b

/-- The right character twist preserves the local frequency gcd, including zero. -/
theorem crt_right_twist_gcd_invariance (m n : ℕ) [NeZero n] (h : m.Coprime n) (b : ZMod (m*n)) :
    Nat.gcd (NField.Alignment.KloostermanCRT.rightTwist m n*NField.Alignment.KloostermanCRT.rightReduction m n b).val n=Nat.gcd (NField.Alignment.KloostermanCRT.rightReduction m n b).val n :=
  NField.Alignment.KloostermanCRT.right_twist_gcd m n h b

/-- The exceptional prime-two factor lies between one and four. -/
theorem crt_exceptional_factor_bounds (q : ℕ) : 1≤NField.Alignment.KloostermanGlobalBound.exceptionalFactor q ∧ NField.Alignment.KloostermanGlobalBound.exceptionalFactor q≤4 :=
  NField.Alignment.KloostermanGlobalBound.exceptionalFactor_bounds q

/-- The actual multiplicative divisor cost is nonnegative. -/
theorem global_divisor_cost_nonnegative (q : ℕ) : 0≤NField.Alignment.KloostermanGlobalBound.divisorCost q :=
  NField.Alignment.KloostermanGlobalBound.divisorCost_nonneg q

/-- Coprime factors incur the prime-two loss at most once. -/
theorem coprime_exceptional_factor_product (m n : ℕ) (h : m.Coprime n) :
    NField.Alignment.KloostermanGlobalBound.exceptionalFactor (m*n)=NField.Alignment.KloostermanGlobalBound.exceptionalFactor m*NField.Alignment.KloostermanGlobalBound.exceptionalFactor n :=
  NField.Alignment.KloostermanGlobalBound.exceptionalFactor_mul m n h

/-- The cost including the actual divisor count is multiplicative on coprime moduli. -/
theorem coprime_divisor_cost_product (m n : ℕ) (h : m.Coprime n) :
    NField.Alignment.KloostermanGlobalBound.divisorCost (m*n)=NField.Alignment.KloostermanGlobalBound.divisorCost m*NField.Alignment.KloostermanGlobalBound.divisorCost n :=
  NField.Alignment.KloostermanGlobalBound.divisorCost_mul m n h

/-- A modulus at least two has its two distinct endpoint divisors. -/
theorem two_endpoint_divisors (q : ℕ) (hq : 2≤q) : 2≤q.divisors.card :=
  NField.Alignment.KloostermanGlobalBound.two_le_card_divisors q hq

/-- The full local prime-power constant is absorbed by the multiplicative divisor cost. -/
theorem local_constant_absorbed_by_divisors (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k) :
    NField.Alignment.PrimePowerGcdBound.localConstant p≤NField.Alignment.KloostermanGlobalBound.divisorCost (p^k) :=
  NField.Alignment.KloostermanGlobalBound.localConstant_le_divisorCost p k hk

/-- Reduction preserves the gcd against the smaller modulus. -/
theorem frequency_gcd_under_residue_reduction (q d : ℕ) [NeZero q] (hd : d∣q) (x : ZMod q) :
    Nat.gcd (ZMod.castHom hd (ZMod d) x).val d=Nat.gcd x.val d :=
  NField.Alignment.KloostermanGlobalBound.gcd_reduction q d hd x

/-- Prime-power induction and exact CRT prove the actual gcd estimate at every positive modulus. -/
theorem all_moduli_actual_unit_sum_cost_bound (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖≤
      NField.Alignment.KloostermanGlobalBound.divisorCost q*Real.sqrt (q:ℝ)*Real.sqrt (Nat.gcd b.val q:ℝ) :=
  NField.Alignment.KloostermanGlobalBound.unitSum_divisorCost_bound q a b

/-- The literal unit sum has the full divisor/gcd estimate with absolute constant four. -/
theorem all_moduli_actual_unit_sum_bound (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖NField.Alignment.UnitSumStationaryPhase.unitSum ZMod.stdAddChar a b‖≤
      4*Real.sqrt (q:ℝ)*q.divisors.card*Real.sqrt (Nat.gcd b.val q:ℝ) :=
  NField.Alignment.KloostermanGlobalBound.unitSum_uniform_bound q a b

/-- The original complete inverse sum has exactly the manuscript divisor and frequency-gcd factors for all positive moduli. -/
theorem complete_inverse_sum_full_modulus_bound (q : ℕ) [NeZero q] (r : ℕ) (j t : ZMod q)
    (hr : r.Coprime q) :
    ‖NField.Alignment.InverseAdditiveCompletion.completeInverseSum r j t‖≤
      4*Real.sqrt (q:ℝ)*q.divisors.card*Real.sqrt (Nat.gcd j.val q:ℝ) :=
  NField.Alignment.KloostermanGlobalBound.complete_inverse_sum_bound q r j t hr

/-- The previously open full complete Kloosterman estimate is proved with constant four. -/
theorem complete_inverse_sum_estimate_proved : NField.Alignment.InverseAdditiveCompletion.CompleteInverseSumEstimate :=
  NField.Alignment.KloostermanGlobalBound.complete_inverse_sum_estimate

/-- SEC-03 is proved via exact finite completion, retaining the printed logarithm, gcd factor and all range conditions. -/
theorem weil_estermann_completion_inputs_proved :
    NField.Alignment.InverseResiduePrefixCompletion.WeilEstermannInversePrefixEstimate :=
  NField.Alignment.KloostermanGlobalBound.weil_estermann_inverse_prefix_estimate

/-- Manuscript `lem:completed-inverse-prefix` and its displayed envelope, with SEC-03 discharged. -/
theorem completed_inverse_prefixes_unconditional : CompletedInversePrefixEstimate :=
  completed_inverse_prefixes weil_estermann_completion_inputs_proved

/-- The lemma's final q^(1/2+o(1)) assertion, stated for every positive epsilon and with both inputs discharged. -/
theorem completed_inverse_prefixes_small_power_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ threshold : ℕ, ∀ q r X,
      threshold ≤ q → 2 ≤ q → r.Coprime q → 1 ≤ X → X ≤ q →
      |inverseResiduePrefix q r X| ≤ C * (q : ℝ) ^ (1 / 2 + ε) :=
  completed_inverse_prefixes_small_power weil_estermann_completion_inputs_proved ε hε

/-- The inverse harmonic estimate now requires only SEC-02 Korolev. -/
theorem inverse_residue_harmonic_bound_from_korolev
    (hKorolev : KorolevInverseFractionRangeEstimate) : InverseResidueHarmonicEstimate :=
  inverse_residue_harmonic_bound_from_two_inputs hKorolev weil_estermann_completion_inputs_proved

/-- The full additive transform now requires only SEC-02 Korolev. -/
theorem uniform_additive_transform_bound_from_korolev
    (hKorolev : KorolevInverseFractionRangeEstimate) : UniformAdditiveTransformEstimate :=
  uniform_additive_transform_bound_from_two_inputs hKorolev weil_estermann_completion_inputs_proved

/-- The carrier and sampling conclusions now require only SEC-02 Korolev. -/
theorem all_prime_carrier_damping_from_korolev
    (hKorolev : KorolevInverseFractionRangeEstimate) :
    PrimeUniformBound lowerModulusReservoir logarithmicCarrierReservoirScale ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime → p ≠ 2 →
        |primeSamplingDefect p| ≤ C * (1 + logarithmicCarrierSamplingScale p) :=
  all_prime_carrier_damping_from_two_inputs hKorolev weil_estermann_completion_inputs_proved

/-- The separate live-sector conclusion retains Korolev and the explicit SEC-05 count only. -/
theorem live_sector_damping_from_korolev_and_count
    (hKorolev : KorolevInverseFractionRangeEstimate) (hcount : SquareLockCountEstimate) :
    CarrierFamilyPrimeEventualBound liveCarrierSet logarithmicCarrierReservoirScale :=
  live_sector_damping_without_divisor_input hKorolev weil_estermann_completion_inputs_proved hcount

/-- The exact printed secondary expansion now has only SEC-01 and SEC-02 as main analytic inputs. -/
theorem finite_secondary_coefficient_from_two_inputs
    (hSaffariVaughan : SaffariVaughanDistributionEstimate)
    (hKorolev : KorolevInverseFractionRangeEstimate) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primePrintedSamplingScale p) :=
  finite_secondary_coefficient_from_three_inputs hSaffariVaughan hKorolev
    weil_estermann_completion_inputs_proved

/-- Actual smooth-number count at Q=exp(log x/log(log x)) is O(x/(log x*log(log x))), using the existing Rankin and Mertens proofs. -/
theorem korolev_smooth_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      NField.Alignment.HarperSmoothCount.smoothCount x (NField.Alignment.HarperRoundedCutoff.smoothCutoff x) ≤ C*(x/(Real.log x*Real.log (Real.log x))) :=
  NField.Alignment.KorolevSmoothCount.eventual_smoothCount_two_bound

/-- The discarded finite set is exactly the positive integers up to x with all prime factors at most Q or all prime factors greater than Q. -/
theorem korolev_first_exclusion_set {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ NField.Alignment.KorolevFirstExclusion.firstExclusionSet x ↔ 0 < n ∧ (n:ℝ) ≤ x ∧
      ((∀ p : ℕ, p.Prime → p ∣ n → (p:ℝ) ≤ NField.Alignment.HarperRoundedCutoff.smoothCutoff x) ∨
       (∀ p : ℕ, p.Prime → p ∣ n → NField.Alignment.HarperRoundedCutoff.smoothCutoff x < (p:ℝ))) :=
  NField.Alignment.KorolevFirstExclusion.firstExclusionSet_mem hx n

/-- The actual smooth/rough excluded set, restricted to integers coprime to any q, is uniformly O(x*log(log x)/log x). -/
theorem korolev_first_exclusion_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop, ∀ q : ℕ,
      (((NField.Alignment.KorolevFirstExclusion.firstExclusionSet x).filter (fun n => n.Coprime q)).card:ℝ) ≤
        C*(x*Real.log (Real.log x)/Real.log x) :=
  NField.Alignment.KorolevFirstExclusion.eventual_coprime_first_exclusion_bound

/-- Actual reciprocal prime sum on any real interval 2 <= u <= v has the explicit two-endpoint Mertens error. -/
theorem korolev_prime_interval_error {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    |(∑ p ∈ NField.Alignment.KorolevPrimeIntervals.intervalPrimes u v, (1 : ℝ) / p) -
      (Real.log (Real.log v) - Real.log (Real.log u))| ≤
        2 * NField.Alignment.KorolevPrimeIntervals.errorConstant / Real.log u :=
  NField.Alignment.KorolevPrimeIntervals.interval_reciprocal_error hu huv

/-- The same upper estimate holds after restricting primes to those coprime to any modulus. -/
theorem korolev_coprime_interval_upper (m : ℕ) {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ (NField.Alignment.KorolevPrimeIntervals.intervalPrimes u v).filter (fun p => p.Coprime m), (1 : ℝ) / p) ≤
      Real.log (Real.log v) - Real.log (Real.log u) + 2 * NField.Alignment.KorolevPrimeIntervals.errorConstant / Real.log u :=
  NField.Alignment.KorolevPrimeIntervals.coprime_interval_upper m hu huv

/-- For a positive modulus, the lower estimate subtracts at most log m/(u log u) for removed prime divisors. -/
theorem korolev_coprime_interval_lower {m : ℕ} (hm : 0 < m) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    Real.log (Real.log v) - Real.log (Real.log u) - 2 * NField.Alignment.KorolevPrimeIntervals.errorConstant / Real.log u -
      Real.log m / (u * Real.log u) ≤
        ∑ p ∈ (NField.Alignment.KorolevPrimeIntervals.intervalPrimes u v).filter (fun p => p.Coprime m), (1 : ℝ) / p :=
  NField.Alignment.KorolevPrimeIntervals.coprime_interval_lower hm hu huv

/-- For all sufficiently large Q, uniformly in x >= Q and 0 <= t <= x, the actual nontrivial rough count is at most 17*t*log x/(log Q)^2. -/
theorem korolev_rough_quotient_bound : ∀ᶠ Q : ℝ in Filter.atTop, ∀ x t : ℝ,
    Q ≤ x → 0 ≤ t → t ≤ x →
      ((NField.Alignment.KorolevQuotientSieve.nontrivialRoughSet t Q).card : ℝ) ≤ 17 * (t * Real.log x / (Real.log Q)^2) :=
  NField.Alignment.KorolevQuotientSieve.eventual_quotient_bound

/-- The actual rough counts at x/(l^2*w), summed over any finite positive factor set, obey the reciprocal-factor bound without a sieve error per factor. -/
theorem korolev_rough_factor_sum_bound : ∀ᶠ Q : ℝ in Filter.atTop, ∀ x : ℝ, Q ≤ x →
    ∀ l : ℕ, 0 < l → ∀ W : Finset ℕ, (∀ w ∈ W, 0 < w) →
      (∑ w ∈ W, ((NField.Alignment.KorolevQuotientSieve.nontrivialRoughSet (x / ((l : ℝ)^2 * w)) Q).card : ℝ)) ≤
        (17 * x * Real.log x / ((l : ℝ)^2 * (Real.log Q)^2)) *
          ∑ w ∈ W, (1 : ℝ) / w :=
  NField.Alignment.KorolevQuotientSieve.eventual_factor_sum_bound

/-- The actual reciprocal sum over allowed smooth factors loses exp(-sum 1/p) for a selected prime set, using the existing finite Euler product. -/
theorem korolev_allowed_reciprocal_bound {Q : ℝ} {S W : Finset ℕ}
    (hS : S ⊆ NField.Alignment.CollisionMertensInput.primesUpTo Q)
    (hW : ∀ w ∈ W, w ∈ Nat.factoredNumbers (NField.Alignment.CollisionMertensInput.primesUpTo Q \ S)) :
    (∑ w ∈ W, (1 : ℝ) / w) ≤
      NField.Alignment.CollisionMertensInput.inversePrimeProduct Q * Real.exp (-(∑ p ∈ S, (1 : ℝ) / p)) :=
  NField.Alignment.KorolevAllowedEulerProduct.allowed_reciprocal_bound hS hW

/-- The counted set is exactly the positive integers up to x divisible by none of the selected primes. -/
theorem korolev_missing_prime_set {x : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) (n : ℕ) :
    n ∈ NField.Alignment.KorolevMissingPrimeCount.avoidSet x S ↔ 0 < n ∧ (n : ℝ) ≤ x ∧ ∀ p ∈ S, ¬p ∣ n :=
  NField.Alignment.KorolevMissingPrimeCount.avoidSet_mem hx S n

/-- The canonical smooth/rough factorization injects the actual nonsmooth missing-prime set into the finite rough-factor sum. -/
theorem korolev_missing_factor_count {x Q : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    (NField.Alignment.KorolevMissingPrimeCount.nonsmoothAvoidSet x Q S).card ≤
      ∑ w ∈ NField.Alignment.KorolevMissingPrimeCount.allowedSmoothSet x Q S, (NField.Alignment.KorolevQuotientSieve.nontrivialRoughSet (x / (w : ℝ)) Q).card :=
  NField.Alignment.KorolevMissingPrimeCount.nonsmooth_avoid_count_le_factor_sum hx S

/-- At the exact cutoff, the actual missing-prime count has a uniform smooth error plus exponential reciprocal-mass bound, including any coprime restriction. -/
theorem korolev_missing_prime_cutoff_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ S : Finset ℕ, S ⊆ NField.Alignment.CollisionMertensInput.primesUpTo (NField.Alignment.HarperRoundedCutoff.smoothCutoff x) → ∀ m : ℕ,
      (((NField.Alignment.KorolevMissingPrimeCount.avoidSet x S).filter (fun n => n.Coprime m)).card : ℝ) ≤ C *
        (x / (Real.log x * Real.log (Real.log x)) + x * Real.log (Real.log x) *
          Real.exp (-(∑ p ∈ S, (1 : ℝ) / p))) :=
  NField.Alignment.KorolevMissingPrimeDecay.eventual_coprime_avoid_count_bound

/-- A stated reciprocal-mass lower bound gives logarithmic decay uniformly in the selected set, varying gamma, and modulus. The source-window mass condition remains open. -/
theorem korolev_missing_prime_decay_from_mass : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ S : Finset ℕ, S ⊆ NField.Alignment.CollisionMertensInput.primesUpTo (NField.Alignment.HarperRoundedCutoff.smoothCutoff x) → ∀ gamma error : ℝ,
      gamma * Real.log (Real.log x) - error ≤ ∑ p ∈ S, (1 : ℝ) / p → ∀ m : ℕ,
        (((NField.Alignment.KorolevMissingPrimeCount.avoidSet x S).filter (fun n => n.Coprime m)).card : ℝ) ≤ C *
          (x / (Real.log x * Real.log (Real.log x)) +
            x * Real.log (Real.log x) * (Real.exp error * (Real.log x)^(-gamma))) :=
  NField.Alignment.KorolevMissingPrimeDecay.eventual_avoid_count_of_mass

/-- The U/V endpoints agree exactly with the source power formulas for positive m and k >= 1. -/
theorem korolev_window_endpoints_source {m : ℝ} (hm : 0 < m) {k : ℕ} (hk : 1 ≤ k) :
    NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.log m) k = m ^ (1/(2*(k : ℝ)-1))/4 ∧
      NField.Alignment.KorolevPrimeWindows.lowerEndpoint (Real.log m) k = m ^ (1/(2*(k : ℝ)-1)-1/(4*(k : ℝ)^2-1)) :=
  NField.Alignment.KorolevSelectedPrimeCount.window_endpoints_source hm hk

/-- Actual reciprocal mass of the disjoint U/V prime windows, with finite size conditions and normalization and Mertens errors explicit. -/
theorem korolev_selected_window_mass {L : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hsize : 8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L) :
    (Real.log ((b : ℝ)+1)-Real.log a)/2 - NField.Alignment.KorolevWindowMass.lossConstant*((b : ℝ)+1)^2/L ≤
      ∑ p ∈ NField.Alignment.KorolevPrimeWindows.selectedPrimes L a b, (1 : ℝ)/p :=
  NField.Alignment.KorolevWindowMass.selected_mass_lower ha hab hsize

/-- Actual reciprocal mass of the contiguous U-endpoint interval, with finite size conditions and Mertens error explicit. -/
theorem korolev_contiguous_window_mass {L : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hsize : 8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L) :
    Real.log ((b : ℝ)+1)-Real.log a - 12*NField.Alignment.KorolevPrimeIntervals.errorConstant*((b : ℝ)+1)/L ≤
      ∑ p ∈ NField.Alignment.KorolevPrimeIntervals.intervalPrimes (NField.Alignment.KorolevPrimeWindows.upperEndpoint L (b+1)) (NField.Alignment.KorolevPrimeWindows.upperEndpoint L a), (1 : ℝ)/p :=
  NField.Alignment.KorolevWindowMass.contiguous_mass_lower ha hab hsize

/-- Actual missing-prime count for the disjoint window family, using the proved mass; retains explicit index, size and cutoff conditions. -/
theorem korolev_selected_window_avoid_count : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ (L : ℝ) (a b : ℕ), 1 ≤ a → a ≤ b →
      8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L → NField.Alignment.KorolevPrimeWindows.upperEndpoint L a ≤ NField.Alignment.HarperRoundedCutoff.smoothCutoff x → ∀ m : ℕ,
        (((NField.Alignment.KorolevMissingPrimeCount.avoidSet x (NField.Alignment.KorolevPrimeWindows.selectedPrimes L a b)).filter (fun n => n.Coprime m)).card : ℝ) ≤
          C * (x/(Real.log x * Real.log (Real.log x)) + x*Real.log (Real.log x) *
            Real.exp (NField.Alignment.KorolevWindowMass.lossConstant*((b : ℝ)+1)^2/L - (Real.log ((b : ℝ)+1)-Real.log a)/2)) :=
  NField.Alignment.KorolevSelectedPrimeCount.eventual_selected_avoid_count_bound

/-- Actual missing-prime count for the contiguous interval family, using the proved mass; retains explicit index, size and cutoff conditions. -/
theorem korolev_contiguous_window_avoid_count : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ (L : ℝ) (a b : ℕ), 1 ≤ a → a ≤ b →
      8*((b : ℝ)+1)^2*(Real.log 4+1) ≤ L → NField.Alignment.KorolevPrimeWindows.upperEndpoint L a ≤ NField.Alignment.HarperRoundedCutoff.smoothCutoff x → ∀ m : ℕ,
        (((NField.Alignment.KorolevMissingPrimeCount.avoidSet x (NField.Alignment.KorolevPrimeIntervals.intervalPrimes (NField.Alignment.KorolevPrimeWindows.upperEndpoint L (b+1))
          (NField.Alignment.KorolevPrimeWindows.upperEndpoint L a))).filter (fun n => n.Coprime m)).card : ℝ) ≤
          C * (x/(Real.log x * Real.log (Real.log x)) + x*Real.log (Real.log x) *
            Real.exp (12*NField.Alignment.KorolevPrimeIntervals.errorConstant*((b : ℝ)+1)/L -
              (Real.log ((b : ℝ)+1)-Real.log a))) :=
  NField.Alignment.KorolevSelectedPrimeCount.eventual_contiguous_avoid_count_bound

/-- The four scales agree exactly with the source epsilon, log x and gamma power formulas. -/
theorem korolev_source_scale_correspondence (C m x : ℝ) (hL : 0 < Real.log m)
    (hY : 0 < Real.log x) (hu : Real.log (Real.log x) ≠ 0) :
    NField.Alignment.KorolevSourceScales.pStart (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (1/(2*(Real.log x/Real.log m)))*(Real.log x)^(2*NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) ∧
    NField.Alignment.KorolevSourceScales.pStop (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (1/(2*(Real.log x/Real.log m)))*(Real.log x)^(4*NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) ∧
    NField.Alignment.KorolevSourceScales.qStart (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (2/(Real.log x/Real.log m)^2)*(Real.log x)^(8*NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) ∧
    NField.Alignment.KorolevSourceScales.qStop (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) =
      (2/(Real.log x/Real.log m)^2)*(Real.log x)^(10*NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) :=
  NField.Alignment.KorolevSourceWindowCount.source_scale_correspondence C m x hL hY hu

/-- Actual ceil/floor indices satisfy all four defining endpoint comparisons uniformly in the logarithmic source range. -/
theorem korolev_source_endpoint_definitions (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in Filter.atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.pFirst v u c) ≤ Real.exp (NField.Alignment.KorolevSourceScales.pThreshold v u c)/4 ∧
        Real.exp (NField.Alignment.KorolevSourceScales.pThreshold v u c)/4 < NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.pFirst v u c-1)) ∧
      (Real.exp (Real.exp (u-4*NField.Alignment.KorolevSourceScales.gain v u c))/4 ≤ NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.pLast v u c+1) ∧
        NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.pLast v u c+1+1) < Real.exp (Real.exp (u-4*NField.Alignment.KorolevSourceScales.gain v u c))/4) ∧
      (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.qFirst v u c) ≤ Real.exp (NField.Alignment.KorolevSourceScales.qThreshold v u c)/4 ∧
        Real.exp (NField.Alignment.KorolevSourceScales.qThreshold v u c)/4 < NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.qFirst v u c-1)) ∧
      (Real.exp (Real.exp (2*u-v-10*NField.Alignment.KorolevSourceScales.gain v u c)/4)/4 ≤ NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.qLast v u c) ∧
        NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.qLast v u c+1) < Real.exp (Real.exp (2*u-v-10*NField.Alignment.KorolevSourceScales.gain v u c)/4)/4) :=
  NField.Alignment.KorolevSourceCoordinates.eventual_endpoint_definitions c hc

/-- Both actual index families satisfy size, order, cutoff, logarithmic gain and Mertens error bounds throughout the source range. -/
theorem korolev_source_window_conditions (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in Filter.atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      NField.Alignment.KorolevWindowParameters.WindowConditions (Real.exp v) (Real.exp (Real.exp u/u)) (NField.Alignment.KorolevSourceScales.gain v u c)
        (NField.Alignment.KorolevWindowParameters.pFirst v u c) (NField.Alignment.KorolevWindowParameters.pLast v u c) ∧
      NField.Alignment.KorolevWindowParameters.WindowConditions (Real.exp v) (Real.exp (Real.exp u/u)) (NField.Alignment.KorolevSourceScales.gain v u c)
        (NField.Alignment.KorolevWindowParameters.qFirst v u c) (NField.Alignment.KorolevWindowParameters.qLast v u c) :=
  NField.Alignment.KorolevWindowParameters.eventual_window_conditions c hc

/-- Both actual prime-family mass lower bounds hold uniformly with absolute additive errors; no finite size or cutoff input remains. -/
theorem korolev_source_window_mass (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ v : ℝ in Filter.atTop,
    ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v →
      NField.Alignment.KorolevSourceScales.gain v u c-Real.log 4/2-1 ≤
        ∑ p ∈ NField.Alignment.KorolevPrimeWindows.selectedPrimes (Real.exp v) (NField.Alignment.KorolevWindowParameters.pFirst v u c) (NField.Alignment.KorolevWindowParameters.pLast v u c), (1 : ℝ)/p ∧
      2*NField.Alignment.KorolevSourceScales.gain v u c-Real.log 4-1 ≤
        ∑ p ∈ NField.Alignment.KorolevPrimeIntervals.intervalPrimes
          (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.qLast v u c+1))
          (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.exp v) (NField.Alignment.KorolevWindowParameters.qFirst v u c)), (1 : ℝ)/p :=
  NField.Alignment.KorolevWindowParameters.eventual_source_mass_bounds c hc

/-- Both actual missing-prime counts have uniform logarithmic-coordinate decay; the smooth remainder is absorbed. -/
theorem korolev_logarithmic_window_counts (c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ v : ℝ in Filter.atTop,
      ∀ u : ℝ, (4/5)*v+5*Real.log v ≤ u → u ≤ v → ∀ m : ℕ,
        (((NField.Alignment.KorolevMissingPrimeCount.avoidSet (Real.exp (Real.exp u)) (NField.Alignment.KorolevParameterCount.pPrimes v u c)).filter (fun n => n.Coprime m)).card : ℝ) ≤
          K*Real.exp (Real.exp u)*u*Real.exp (-NField.Alignment.KorolevSourceScales.gain v u c) ∧
        (((NField.Alignment.KorolevMissingPrimeCount.avoidSet (Real.exp (Real.exp u)) (NField.Alignment.KorolevParameterCount.qPrimes v u c)).filter (fun n => n.Coprime m)).card : ℝ) ≤
          K*Real.exp (Real.exp u)*u*Real.exp (-NField.Alignment.KorolevSourceScales.gain v u c) :=
  NField.Alignment.KorolevParameterCount.eventual_window_missing_counts c hc

/-- The actual printed m,x length range implies the logarithmic parameter range. -/
theorem korolev_source_log_range {m x : ℝ} (hm : 0 < m) (hL : 1 < Real.log m)
    (hlo : Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x)
    (hhi : x ≤ m^(4/7 : ℝ)) :
    0 < x ∧ 0 < Real.log x ∧
      (4/5)*Real.log (Real.log m)+5*Real.log (Real.log (Real.log m)) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log m) :=
  NField.Alignment.KorolevSourceWindowCount.source_log_range hm hL hlo hhi

/-- The exponential gain is exactly the negative source-gamma power of log x. -/
theorem korolev_source_decay {C m x : ℝ} (hx : 0 < Real.log x)
    (hu : Real.log (Real.log x) ≠ 0) :
    Real.exp (-NField.Alignment.KorolevSourceScales.gain (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)) =
      (Real.log x)^(-NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) :=
  NField.Alignment.KorolevSourceWindowCount.source_decay_identity hx hu

/-- In the original source length range, both selected-prime exclusions are O(x log(log x)/(log x)^gamma), uniformly in x and coprime restriction. -/
theorem korolev_source_window_counts (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℝ in Filter.atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ modulus : ℕ,
        (((NField.Alignment.KorolevMissingPrimeCount.avoidSet x (NField.Alignment.KorolevSourceWindowCount.sourcePPrimes C m x)).filter (fun n => n.Coprime modulus)).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) ∧
        (((NField.Alignment.KorolevMissingPrimeCount.avoidSet x (NField.Alignment.KorolevSourceWindowCount.sourceQPrimes C m x)).filter (fun n => n.Coprime modulus)).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) :=
  NField.Alignment.KorolevSourceWindowCount.eventual_source_window_counts C hC

/-- In the original source range, both selected families contain primes, with log x < q < p. -/
theorem korolev_selected_primes_large_distinct (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℝ in Filter.atTop,
    ∀ x : ℝ, Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ p ∈ NField.Alignment.KorolevSourceWindowCount.sourcePPrimes C m x, ∀ q ∈ NField.Alignment.KorolevSourceWindowCount.sourceQPrimes C m x,
        p.Prime ∧ q.Prime ∧ Real.log x < (q : ℝ) ∧ q < p :=
  NField.Alignment.KorolevPrimeSeparation.eventual_source_prime_properties C hC

/-- The actual exception set consists exactly of positive n <= x divisible by some l^2 with l > y. -/
theorem korolev_large_square_set {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) :
    n ∈ NField.Alignment.KorolevLargeSquares.largeSquareSet x y ↔ 0 < n ∧ (n : ℝ) ≤ x ∧ ∃ l : ℕ, y < (l : ℝ) ∧ l^2 ∣ n :=
  NField.Alignment.KorolevLargeSquares.largeSquareSet_mem hx y n

/-- The actual large-square exception count is at most 2*x/y, uniformly after coprime restriction. -/
theorem korolev_large_square_count {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (m : ℕ) :
    (((NField.Alignment.KorolevLargeSquares.largeSquareSet x y).filter (fun n => n.Coprime m)).card : ℝ) ≤ 2*x/y :=
  NField.Alignment.KorolevLargeSquares.coprime_large_square_count hx hy m

/-- Outside the actual three-set union, n=l^2*p*q*h with small l, distinct selected primes and squarefree p*q*h. -/
theorem korolev_squarefree_representation {x : ℝ} (hx : 0 ≤ x) {P Q : Finset ℕ}
    (hprimes : ∀ p ∈ P, ∀ q ∈ Q, p.Prime ∧ q.Prime ∧ Real.log x < (q : ℝ) ∧ q < p)
    {n : ℕ} (hn : 0 < n) (hnx : (n : ℝ) ≤ x) (hout : n ∉ NField.Alignment.KorolevSquarefreeRepresentation.exceptionSet x P Q) :
    NField.Alignment.KorolevSquarefreeRepresentation.HasSelectedRepresentation x P Q n :=
  NField.Alignment.KorolevSquarefreeRepresentation.representation_outside_exception hx hprimes hn hnx hout

/-- Membership in the contiguous selected family is exactly membership in one indexed U interval. -/
theorem korolev_contiguous_interval_membership {L : ℝ} (hL : 0 ≤ L) {a b q : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    q ∈ NField.Alignment.KorolevPrimeIntervals.intervalPrimes (NField.Alignment.KorolevPrimeWindows.upperEndpoint L (b+1)) (NField.Alignment.KorolevPrimeWindows.upperEndpoint L a) ↔
      ∃ s : ℕ, a ≤ s ∧ s ≤ b ∧ q.Prime ∧
        NField.Alignment.KorolevPrimeWindows.upperEndpoint L (s+1) < (q : ℝ) ∧ (q : ℝ) ≤ NField.Alignment.KorolevPrimeWindows.upperEndpoint L s :=
  NField.Alignment.KorolevSquarefreeRepresentation.contiguous_interval_membership hL ha hab

/-- The selected representation supplies literal source interval indices, endpoints and nonzero Mobius value. -/
theorem korolev_source_representation_witness {C m x : ℝ} (hL : 0 < Real.log m)
    (hqa : 1 ≤ NField.Alignment.KorolevWindowParameters.qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))
    (hqab : NField.Alignment.KorolevWindowParameters.qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤
      NField.Alignment.KorolevWindowParameters.qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C))
    {n : ℕ} (hn : NField.Alignment.KorolevSquarefreeRepresentation.HasSelectedRepresentation x (NField.Alignment.KorolevSourceWindowCount.sourcePPrimes C m x) (NField.Alignment.KorolevSourceWindowCount.sourceQPrimes C m x) n) :
    NField.Alignment.KorolevLemmaA.SourceRepresentation C m x n :=
  NField.Alignment.KorolevLemmaA.source_representation_of_selected hL hqa hqab hn

/-- The actual exception union has the source gamma decay, and every retained integer has the literal representation; an absolute constant replaces the uncertified printed 60. -/
theorem korolev_source_representation (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℝ in Filter.atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ modulus : ℕ,
        (((NField.Alignment.KorolevSquarefreeRepresentation.exceptionSet x (NField.Alignment.KorolevSourceWindowCount.sourcePPrimes C m x) (NField.Alignment.KorolevSourceWindowCount.sourceQPrimes C m x)).filter
          (fun n => n.Coprime modulus)).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) ∧
        ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x → n.Coprime modulus →
          n ∉ NField.Alignment.KorolevSquarefreeRepresentation.exceptionSet x (NField.Alignment.KorolevSourceWindowCount.sourcePPrimes C m x) (NField.Alignment.KorolevSourceWindowCount.sourceQPrimes C m x) →
          NField.Alignment.KorolevLemmaA.SourceRepresentation C m x n :=
  NField.Alignment.KorolevLemmaA.eventual_source_representation C hC

/-- The actual count of coprime positive integers failing the literal source representation has the stated gamma decay. -/
theorem korolev_actual_representation_failure_count (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℝ in Filter.atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ m^(4/7 : ℝ) → ∀ modulus : ℕ,
        ((NField.Alignment.KorolevLemmaA.failureSet C m x modulus).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-NField.Alignment.KorolevSourceWindowCount.sourceGamma C m x) :=
  NField.Alignment.KorolevLemmaA.eventual_actual_failure_count C hC

/-- In the short range, equal prime reciprocal sums differ only by a permutation of positions. -/
theorem karatsuba_prime_reciprocal_rigidity {P : Finset ℕ} {m k : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m)
    (u v : NField.Alignment.KaratsubaPrimeMoment.PrimeTuple P k)
    (heq : NField.Alignment.KaratsubaPrimeMoment.reciprocalSum m (fun i => (u i).val) =
      NField.Alignment.KaratsubaPrimeMoment.reciprocalSum m (fun i => (v i).val)) :
    ∃ e : Equiv.Perm (Fin k), ∀ i, v (e i) = u i := by
  have hc := NField.Alignment.KaratsubaPrimeMoment.tupleCount_eq_of_reciprocalSum_eq hX
    (fun i => (u i).val) (fun i => (v i).val)
    (fun i => hprime _ (u i).property) (fun i => hprime _ (v i).property)
    (fun i => hcop _ (u i).property) (fun i => hcop _ (v i).property)
    (fun i => hlower _ (u i).property) (fun i => hlower _ (v i).property)
    (fun i => hupper _ (u i).property) (fun i => hupper _ (v i).property) hsize heq
  obtain ⟨e, he⟩ := NField.Alignment.KaratsubaPrimeMoment.exists_perm_of_tupleCount_eq _ _ hc
  exact ⟨e, fun i => Subtype.ext (he i)⟩

/-- The actual ordered-pair count is at most k! times the kth power of the prime population. -/
theorem karatsuba_prime_reciprocal_moment_count {P : Finset ℕ} {m k : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2 * k - 1) < m) :
    (Finset.univ.filter (fun uv :
      NField.Alignment.KaratsubaPrimeMoment.PrimeTuple P k ×
        NField.Alignment.KaratsubaPrimeMoment.PrimeTuple P k =>
      NField.Alignment.KaratsubaPrimeMoment.reciprocalSum m (fun i => (uv.2 i).val) =
        NField.Alignment.KaratsubaPrimeMoment.reciprocalSum m (fun i => (uv.1 i).val))).card ≤
      k.factorial * P.card ^ k := by
  rw [← NField.Alignment.KaratsubaPrimeMoment.reciprocalCollisionCount_eq_pair_count]
  exact NField.Alignment.KaratsubaPrimeMoment.reciprocalCollisionCount_le
    hX hprime hcop hlower hupper hsize

/-- The actual prime exponential sum has an exact ordered-tuple even moment. -/
theorem karatsuba_prime_even_moment (P : Finset ℕ) (m k : ℕ) [NeZero m] :
    (∑ a : ZMod m, ‖NField.Alignment.KaratsubaFourierMoment.primeExponentialSum P m a‖ ^ (2*k)) =
      (m : ℝ) * NField.Alignment.KaratsubaPrimeMoment.reciprocalCollisionCount P m k :=
  NField.Alignment.KaratsubaFourierMoment.prime_norm_even_moment P m k

/-- The short-range even moment at any scaled frequency retains the exact gcd cost. -/
theorem karatsuba_scaled_prime_even_moment {P : Finset ℕ} {m k : ℕ} [NeZero m] {X : ℝ}
    (hX : 1 ≤ X) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m)
    (hlower : ∀ p ∈ P, k < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hsize : (k : ℝ) * X ^ (2*k-1) < m) (a : ZMod m) :
    (∑ t : ZMod m,
      ‖NField.Alignment.KaratsubaFourierMoment.primeExponentialSum P m (t*a)‖ ^ (2*k)) ≤
        (m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k)) :=
  NField.Alignment.KaratsubaScaledFourierMoment.scaled_prime_norm_moment_le
    hX hprime hcop hlower hupper hsize a

/-- The finite bilinear prime sum obeys a power bound with both actual populations and the exact frequency gcd. -/
theorem karatsuba_bilinear_power_bound {P Q : Finset ℕ} {m s k L U : ℕ}
    [NeZero m] {X Y : ℝ} (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hL : ∀ q ∈ Q, L < q) (hU : ∀ q ∈ Q, q ≤ U)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime) (hPc : ∀ p ∈ P, p.Coprime m)
    (hPl : ∀ p ∈ P, k < p) (hPu : ∀ p ∈ P, (p : ℝ) ≤ X)
    (hPs : (k : ℝ)*X^(2*k-1) < m)
    (hY : 1 ≤ Y) (hQ : ∀ q ∈ Q, q.Prime) (hQc : ∀ q ∈ Q, q.Coprime m)
    (hQl : ∀ q ∈ Q, s < q) (hQu : ∀ q ∈ Q, (q : ℝ) ≤ Y)
    (hQs : (s : ℝ)*Y^(2*s-1) < m) (a b : ZMod m) :
    ‖NField.Alignment.KaratsubaBilinearReduction.bilinearPrimeSum P Q a b‖ ^ (2*s*k) ≤
      (((P.card : ℝ) ^ (s-1)) ^ k * ((Q.card : ℝ) ^ s) ^ (k-1)) ^ 2 *
        (((s.factorial * Q.card ^ s : ℕ) : ℝ) *
          (((s*(U-L) : ℕ) : ℝ) *
            ((m : ℝ) * (a.val.gcd m * (k.factorial * P.card ^ k))))) :=
  NField.Alignment.KaratsubaJointPopulation.bilinear_power_bound hs hk hL hU
    hX hP hPc hPl hPu hPs hY hQ hQc hQl hQu hQs a b

/-- The bilinear sum is the literal inverse-product character sum over ordered prime pairs. -/
theorem karatsuba_ordered_product_phase {P Q : Finset ℕ} {m : ℕ} [NeZero m]
    (hP : ∀ p ∈ P, p.Coprime m) (hQ : ∀ q ∈ Q, q.Coprime m) (a b : ZMod m) :
    NField.Alignment.KaratsubaBilinearReduction.bilinearPrimeSum P Q a b =
      ∑ p : {p // p ∈ P}, ∑ q : {q // q ∈ Q},
        ZMod.stdAddChar (a * ((p.val*q.val : ℕ) : ZMod m)⁻¹ +
          b * ((p.val*q.val : ℕ) : ZMod m)) :=
  NField.Alignment.KaratsubaProductPhase.bilinear_eq_ordered_inverse_sum hP hQ a b

/-- The actual coprime prime populations obey a uniform lower bound throughout the paper's full modulus and shorter-sum range. -/
theorem korolev_source_prime_population (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in Filter.atTop,
    ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k : ℕ, 1 ≤ k →
        (k ≤ NField.Alignment.KorolevWindowParameters.pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ∨
          k ≤ NField.Alignment.KorolevWindowParameters.qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C)) →
        NField.Alignment.KorolevPrimeWindows.lowerEndpoint (Real.log m) k / (8*(k : ℝ)) ≤
          (((NField.Alignment.KorolevPrimeWindows.windowPrimes (Real.log m) k).filter (fun p => p.Coprime m)).card : ℝ) ∧
        NField.Alignment.KorolevPrimeWindows.lowerEndpoint (Real.log m) k / (8*(k : ℝ)) ≤
          (((NField.Alignment.KorolevPrimeIntervals.intervalPrimes (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.log m) (k+1))
            (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.log m) k)).filter (fun p => p.Coprime m)).card : ℝ) :=
  NField.Alignment.KorolevSourceWindowDensity.eventual_source_population_nat C hC

/-- The literal source upper endpoint satisfies the strict reciprocal-moment size condition. -/
theorem karatsuba_source_window_moment_range {M : ℝ} (hM : 0 < M) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ)*(NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.log M) k)^(2*k-1) < M :=
  NField.Alignment.KaratsubaWindowMomentRange.upperEndpoint_short_moment hM hk

/-- The actual source-window bilinear sum has uniform exponential power decay with its exact frequency gcd. -/
theorem karatsuba_source_bilinear_power_bound (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in Filter.atTop,
    ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
        NField.Alignment.KorolevWindowParameters.pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
        k ≤ NField.Alignment.KorolevWindowParameters.pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        NField.Alignment.KorolevWindowParameters.qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
        s ≤ NField.Alignment.KorolevWindowParameters.qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        ∀ a b : ZMod m,
          (‖NField.Alignment.KaratsubaBilinearReduction.bilinearPrimeSum (NField.Alignment.KaratsubaSourceWindows.pPrimes m k) (NField.Alignment.KaratsubaSourceWindows.qPrimes m s) a b‖ /
            (((NField.Alignment.KaratsubaSourceWindows.pPrimes m k).card : ℝ)*((NField.Alignment.KaratsubaSourceWindows.qPrimes m s).card : ℝ)))^(2*s*k) ≤
              (a.val.gcd m : ℝ)*Real.exp (-Real.log m/(48*(k : ℝ)^2)) :=
  NField.Alignment.KaratsubaSourceCancellation.eventual_source_bilinear_power_bound C hC

/-- The normalized source-window bilinear norm has uniform exponential decay for every coprime inverse frequency. -/
theorem karatsuba_source_bilinear_coprime_bound (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in Filter.atTop,
    ∀ [NeZero m], ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
        NField.Alignment.KorolevWindowParameters.pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
        k ≤ NField.Alignment.KorolevWindowParameters.pLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        NField.Alignment.KorolevWindowParameters.qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
        s ≤ NField.Alignment.KorolevWindowParameters.qLast (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) →
        ∀ a b : ZMod m, a.val.Coprime m →
          ‖NField.Alignment.KaratsubaBilinearReduction.bilinearPrimeSum (NField.Alignment.KaratsubaSourceWindows.pPrimes m k) (NField.Alignment.KaratsubaSourceWindows.qPrimes m s) a b‖ /
            (((NField.Alignment.KaratsubaSourceWindows.pPrimes m k).card : ℝ)*((NField.Alignment.KaratsubaSourceWindows.qPrimes m s).card : ℝ)) ≤
              Real.exp (-Real.log m/(96*(s : ℝ)*(k : ℝ)^3)) :=
  NField.Alignment.KaratsubaSourceCancellation.eventual_source_bilinear_bound C hC

/-- The actual centered inverse-residue prefix is exactly the canonical selected-factor sum plus its actual failure-set contribution. -/
theorem korolev_canonical_inverse_prefix {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hX : 1 ≤ X) :
    NField.Alignment.DedekindInverseResidueTransform.inverseResiduePrefix q r X = NField.Alignment.KorolevCanonicalInversePrefix.canonicalPrefix P Q q r X +
      ∑ n ∈ NField.Alignment.KorolevCanonicalSelectedSum.failure (X : ℝ) P Q q, (NField.Alignment.DedekindReciprocity.rationalSawtooth (r*NField.Alignment.DedekindInverseResidueTransform.inverseResidue n q) q : ℝ) :=
  NField.Alignment.KorolevCanonicalInversePrefix.prefix_eq_canonical_add_failure hP hQ hdis q r X hX

/-- The omitted part of the centered inverse-residue prefix costs at most one half per failed selected representation. -/
theorem korolev_canonical_prefix_remainder {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hq : 0 < q) (hX : 1 ≤ X) :
    |NField.Alignment.DedekindInverseResidueTransform.inverseResiduePrefix q r X - NField.Alignment.KorolevCanonicalInversePrefix.canonicalPrefix P Q q r X| ≤
      ((NField.Alignment.KorolevCanonicalSelectedSum.failure (X : ℝ) P Q q).card : ℝ)/2 :=
  NField.Alignment.KorolevCanonicalInversePrefix.prefix_remainder_bound hP hQ hdis q r X hq hX

/-- The actual selected-representation failures have the uniform source gamma decay; no exception predicate enters the canonical sum. -/
theorem korolev_selected_representation_failure_count (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ M : ℝ in Filter.atTop, ∀ x : ℝ,
      Real.exp ((Real.log M)^(4/5 : ℝ)*(Real.log (Real.log M))^5) ≤ x →
      x ≤ M^(4/7 : ℝ) → ∀ m : ℕ,
        ((NField.Alignment.KorolevCanonicalSelectedSum.failure x (NField.Alignment.KorolevSourceWindowCount.sourcePPrimes C M x) (NField.Alignment.KorolevSourceWindowCount.sourceQPrimes C M x) m).card : ℝ) ≤
          K*x*Real.log (Real.log x)*(Real.log x)^(-NField.Alignment.KorolevSourceWindowCount.sourceGamma C M x) :=
  NField.Alignment.KorolevCanonicalSelectedSum.eventual_failure_count C hC

/-- The actual inverse-residue prefix has an exact block-dependent residual truncation and its actual omitted set. -/
theorem korolev_truncated_inverse_prefix {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hX : 1 ≤ X)
    (lp lq : ℝ) {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hPI : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQI : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    inverseResiduePrefix q r X = truncatedPrefix P Q q r X lp lq Dp Dq A +
      ∑ n ∈ failure (X : ℝ) P Q q, (rationalSawtooth (r*inverseResidue n q) q : ℝ) :=
  NField.Alignment.KorolevCanonicalTruncatedPrefix.prefix_eq_truncated_add_failure hP hQ hdis q r X hX lp lq hA hDp hDq hPI hQI

/-- Exact residual truncation preserves the half-per-failure prefix remainder bound. -/
theorem korolev_truncated_prefix_remainder {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hdis : Disjoint P Q) (q r X : ℕ) (hq : 0 < q) (hX : 1 ≤ X)
    (lp lq : ℝ) {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq)
    (hPI : P = KorolevPrimeIntervals.intervalPrimes (Real.exp lp) (Real.exp (lp+Dp)))
    (hQI : Q = KorolevPrimeIntervals.intervalPrimes (Real.exp lq) (Real.exp (lq+Dq))) :
    |inverseResiduePrefix q r X - truncatedPrefix P Q q r X lp lq Dp Dq A| ≤
      ((failure (X : ℝ) P Q q).card : ℝ)/2 :=
  NField.Alignment.KorolevCanonicalTruncatedPrefix.prefix_truncated_remainder_bound hP hQ hdis q r X hq hX lp lq hA hDp hDq hPI hQI

/-- Every prime product in the full uncut source rectangle is below the modulus throughout the source range. -/
theorem korolev_uncut_source_rectangle (C : ℝ) (hC : 1 ≤ C) : ∀ᶠ m : ℕ in Filter.atTop,
    ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k s : ℕ,
      NField.Alignment.KorolevWindowParameters.pFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ k →
      NField.Alignment.KorolevWindowParameters.qFirst (Real.log (Real.log m)) (Real.log (Real.log x)) (Real.log C) ≤ s →
      ∀ p ∈ NField.Alignment.KorolevPrimeWindows.windowPrimes (Real.log m) k,
      ∀ q ∈ NField.Alignment.KorolevPrimeIntervals.intervalPrimes (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.log m) (s+1)) (NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.log m) s),
        p*q < m :=
  NField.Alignment.KorolevUncutPrimeRectangle.eventual_source_rectangle C hC

/-- The coupled product cutoff costs at most one plus the harmonic sum against the full shifted bilinear family. -/
theorem karatsuba_product_cutoff_harmonic_bound (P Q : Finset ℕ) {m : ℕ} [NeZero m]
    (l h X : ℕ) (hl : 0 < l) (hh : 0 < h) (a b : ZMod m)
    (hrect : ∀ p ∈ P, ∀ q ∈ Q, p*q < m) {B : ℝ}
    (hbound : ∀ c : ZMod m, ‖KaratsubaBilinearReduction.bilinearPrimeSum P Q a (b+c)‖ ≤ B) :
    ‖productCutoffSum P Q l h X a b‖ ≤ (1+(harmonic m : ℝ))*B :=
  NField.Alignment.KaratsubaProductCutoffCost.norm_productCutoffSum_le_harmonic P Q l h X hl hh a b hrect hbound

/-- The actual canonical sawtooth slice reduces to the frequency-dependent completed bilinear bounds. -/
theorem korolev_canonical_sawtooth_slice_bound {m : ℕ} [NeZero m]
    (P Q P₀ Q₀ : Finset ℕ) (l h X r : ℕ)
    (hlpos : 0 < l) (hhpos : 0 < h) (hl : l.Coprime m) (hh : h.Coprime m)
    (hrect : ∀ p ∈ P₀, ∀ q ∈ Q₀, p*q < m) (B : ZMod m → ℝ)
    (hbound : ∀ j c : ZMod m,
      ‖KaratsubaBilinearReduction.bilinearPrimeSum (canonicalDomain P P₀ h m) (canonicalDomain Q Q₀ h m)
        ((j*(r : ZMod m))*((l^2*h : ℕ) : ZMod m)⁻¹) c‖ ≤ B j) :
    ‖primeSliceOn P Q P₀ Q₀ l h X m
      (fun n => ((rationalSawtooth (r*inverseResidue n m) m : ℚ) : ℂ))‖ ≤
      (1+(harmonic m : ℝ))/(m : ℝ) *
        ∑ j : ZMod m, ‖ZMod.dft (centeredSawtooth : ZMod m → ℂ) j‖ * B j :=
  NField.Alignment.KorolevCanonicalSawtoothSlices.norm_sawtooth_slice_le P Q P₀ Q₀ l h X r hlpos hhpos hl hh hrect B hbound

/-- Unit numerator and square-residual scalings preserve each original sawtooth frequency gcd exactly. -/
theorem korolev_sawtooth_frequency_gcd {m l h r : ℕ} [NeZero m] (j : ZMod m)
    (hl : l.Coprime m) (hh : h.Coprime m) (hr : r.Coprime m) :
    (((j*(r : ZMod m))*((l^2*h : ℕ) : ZMod m)⁻¹).val).gcd m = j.val.gcd m :=
  NField.Alignment.KorolevCanonicalSawtoothSlices.sawtooth_frequency_gcd j hl hh hr

/-- Actual coprime populations of the logarithmic blocks have their uniform lower bounds throughout the source range. -/
theorem korolev_source_logarithmic_block_population (C : ℝ) (hC : 1 ≤ C) (A : ℝ)
    (hA : 1 ≤ A) (herror : 8*KorolevPrimeIntervals.errorConstant ≤ A) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ x : ℝ,
      Real.exp ((Real.log m)^(4/5 : ℝ)*(Real.log (Real.log m))^5) ≤ x →
      x ≤ (m : ℝ)^(4/7 : ℝ) → ∀ k : ℕ, 1 ≤ k →
      (k ≤ KorolevWindowParameters.pLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C) ∨
       k ≤ KorolevWindowParameters.qLast (Real.log (Real.log m))
        (Real.log (Real.log x)) (Real.log C)) →
      ∀ l D : ℝ, NField.Alignment.KorolevPrimeWindows.upperEndpoint (Real.log m) (k+1) ≤ Real.exp l → A ≤ D → ∀ i : ℕ,
      NField.Alignment.KorolevLogarithmicPartition.point l D A i * NField.Alignment.KorolevLogarithmicPartition.width D A / (4*Real.log (NField.Alignment.KorolevLogarithmicPartition.point l D A (i+1))) ≤
        (((NField.Alignment.KorolevLogarithmicPartition.block l D A i).filter (fun p => p.Coprime m)).card : ℝ) :=
  by simpa using NField.Alignment.KorolevSourceLogarithmicPartition.eventual_partition_population_nat C hC A hA herror

/-- The exact residual support cancels the two block populations at a fixed endpoint-ratio cost. -/
theorem karatsuba_block_residual_population_cost (l X : ℕ) (hl : 0 < l) (lp lq : ℝ)
    {Dp Dq A : ℝ} (hA : 0 < A) (hDp : A ≤ Dp) (hDq : A ≤ Dq) (i j : ℕ) :
    ((block lp Dp A i).card : ℝ) * ((block lq Dq A j).card : ℝ) *
      (residualBound l X (point lp Dp A i) (point lq Dq A j) : ℝ) ≤
        Real.exp (4*A) * (X : ℝ) / (l : ℝ)^2 :=
  NField.Alignment.KorolevBlockResidualVolume.residual_population_cost l X hl lp lq hA hDp hDq i j


/-- The published arbitrary-modulus inverse-fraction range estimate, with all analytic inputs discharged. -/
theorem korolev_inverse_fraction_range_estimate : KorolevInverseFractionRangeEstimate :=
  NField.Alignment.KorolevRangeEstimate.korolev_range_estimate

/-- The inverse-residue harmonic estimate with Korolev and completion both proved. -/
theorem inverse_residue_harmonic_bound_unconditional : InverseResidueHarmonicEstimate :=
  inverse_residue_harmonic_bound_from_korolev korolev_inverse_fraction_range_estimate

/-- The full uniform additive transform estimate with its source estimates proved. -/
theorem uniform_additive_transform_bound_unconditional : UniformAdditiveTransformEstimate :=
  uniform_additive_transform_bound_from_korolev korolev_inverse_fraction_range_estimate

/-- All-prime carrier damping and its sampling consequence with the inverse-residue input discharged. -/
theorem all_prime_carrier_damping_unconditional :
    PrimeUniformBound lowerModulusReservoir logarithmicCarrierReservoirScale ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, p.Prime → p ≠ 2 →
        |primeSamplingDefect p| ≤ C * (1 + logarithmicCarrierSamplingScale p) :=
  all_prime_carrier_damping_from_korolev korolev_inverse_fraction_range_estimate

/-- The live-sector estimate retains only the separate square-lock counting input. -/
theorem live_sector_damping_from_count (hcount : SquareLockCountEstimate) :
    CarrierFamilyPrimeEventualBound liveCarrierSet logarithmicCarrierReservoirScale :=
  live_sector_damping_from_korolev_and_count korolev_inverse_fraction_range_estimate hcount

/-- The printed secondary expansion retains only Saffari-Vaughan as its main analytic input. -/
theorem finite_secondary_coefficient_from_saffari_vaughan
    (hSaffariVaughan : SaffariVaughanDistributionEstimate) :
    PrimeEventualErrorBound primeCollisionEnergy primeDisplayedSecondaryMain
      (fun p => (p : ℝ) ^ 2 * primePrintedSamplingScale p) :=
  finite_secondary_coefficient_from_two_inputs hSaffariVaughan korolev_inverse_fraction_range_estimate

end NField.Papers.TheSecondaryTermInDigitCollisionEnergy

-- Additional source-titled results; the publisher reads compiler references.
#check NField.Alignment.BernoulliAbelLimit.bernoulli_one_symmetric_abel
#check NField.Alignment.BernoulliAbelSeries.abel_hasSum
#check NField.Alignment.BernoulliFourierIdentity.bernoulli_two_fourier
#check NField.Alignment.BoundaryDistributionalDerivative.boundary_distributional_second_derivative
#check NField.Alignment.BoundaryFourierCoefficients.boundary_fourier_jump_formula
#check NField.Alignment.CarrierDwellCounts.floor_state_count
#check NField.Alignment.CarrierDwellCounts.floor_state_upper_count
#check NField.Alignment.CarrierTriangularIdentity.triangular_carrier_identity
#check NField.Alignment.CarrierTriangularIdentity.literal_collar_triangular_identity
#check NField.Alignment.ComplementaryHalfPacket.partition_packet_half
#check NField.Alignment.ComplementaryHalfSums.reciprocal_half_sum
#check NField.Alignment.ComplementaryHalfSums.ratio_half_sum
#check NField.Alignment.CotangentDedekindFormula.arithmetic_dedekind_cotangent
#check NField.Alignment.CotangentGrid.cotangent_circular_bound
#check NField.Alignment.CotangentOrbitBound.cot_mass_logarithmic
#check NField.Alignment.CotangentOrbitBound.unit_cotangent_orbit_bound
#check NField.Alignment.CyclicLogarithmicLadder.quadratic_correlation_rung
#check NField.Alignment.CyclicLogarithmicLadder.logarithmic_correlation_rung
#check NField.Alignment.CyclicLogarithmicLadder.bounded_correlation_rung
#check NField.Alignment.DivisorVoronoiEstimate.divisor_error_isBigO
#check NField.Alignment.DivisorWindowCount.prime_square_divisor_window_bound
#check NField.Alignment.HalfPacketSignGeometry.half_packet_no_opposite
#check NField.Alignment.IntegerCotangentTransforms.integer_series_cotangent
#check NField.Alignment.IntegerCotangentTransforms.integer_inverse_cotangent_identity
#check NField.Alignment.IntegerCotangentTransforms.integer_full_cotangent
#check NField.Alignment.IntegerDedekindTransform.integer_additive_transform
#check NField.Alignment.IntegerDedekindTransform.integer_unit_mobius
#check NField.Alignment.IntegerFullTransformBound.integer_full_transform_bound
#check NField.Alignment.IntegerInversePrefix.completed_integer_real_prefixes
#check NField.Alignment.IntegerInversePrefix.completed_integer_real_prefixes_small_power
#check NField.Alignment.IntegerInverseResidue.integer_inverse_series_tendsto
#check NField.Alignment.IntegerInverseSeriesLiteral.integer_literal_series_tendsto
#check NField.Alignment.IntegerNumeratorDescent.integer_numerator_descent
#check NField.Alignment.IntegerNumeratorDescent.integer_numerator_descent_bound
#check NField.Alignment.IntegerSignedDamping.signed_damping_iff_integer_intervals
#check NField.Alignment.IntegerSignedDamping.sampling_under_integer_signed_damping
#check NField.Alignment.IntegerSignedDamping.secondary_under_integer_signed_damping
#check NField.Alignment.IntegerSignedDamping.secondary_under_sharp_capacity_and_integer_signed_damping
#check NField.Alignment.IntegerTransformBounds.integer_inverse_harmonic_bound
#check NField.Alignment.IntegerTransformBounds.integer_uniform_transform_bound
#check NField.Alignment.JordanCapacityFormula.capacity_jordan_formula
#check NField.Alignment.KorolevRealCutoff.korolev_real_cutoff
#check NField.Alignment.KorolevShortRangeAsymptotic.short_range_isLittleO
#check NField.Alignment.MobiusLogarithmicMain.mobius_log_main_bound
#check NField.Alignment.PrimeSquareGridSeparation.nonzero_grid_halfJump
#check NField.Alignment.PrimeSquareGridSeparation.boundary_derivative_on_grid
#check NField.Alignment.RealBernoulliBoundaryLimits.rational_boundary_limits
#check NField.Alignment.RealBernoulliBoundaryLimits.origin_boundary_limits
#check NField.Alignment.RealBernoulliCapacityIntegral.integral_capacity_eq_continuous_capacity
#check NField.Alignment.RealBernoulliCapacityIntegral.integral_capacity_secondary_coefficient
#check NField.Alignment.RealBernoulliJumpData.rational_square_jump_limits
#check NField.Alignment.RealBernoulliJumpData.origin_square_jump_limits
#check NField.Alignment.RealCarrierGridAlias.actual_periodic_jump_aliasing
#check NField.Alignment.RealCarrierGridAlias.actual_endpoint_reservoir_alias
#check NField.Alignment.RealDedekindGram.realGram_eq_arithmetic
#check NField.Alignment.RealDedekindGram.realGram_eq_ratio
#check NField.Alignment.RealDedekindGram.partition_packet_real_half
#check NField.Alignment.RealFractionalFirstMoment.real_first_moment_error
#check NField.Alignment.RealLogWeightedFractionalParts.log_weighted_fractional_parts
#check NField.Alignment.RealSaffariVaughanDistribution.normalized_real_distribution
#check NField.Alignment.RealSawtoothDistribution.sawtooth_distribution
#check NField.Alignment.RealSawtoothPairIntegral.sawtooth_pair_integral
#check NField.Alignment.ReciprocalMomentEulerFactor.local_euler_factor
#check NField.Alignment.ReciprocalMomentInfiniteSeries.third_moment_infinite_majorant
#check NField.Alignment.ReciprocalSawtoothGlobal.floor_global_log_bound
#check NField.Alignment.RemovedCarrierLogBound.full_live_difference
#check NField.Alignment.RemovedCarrierLogBound.removed_carrier_log_bound
#check NField.Alignment.SecondaryCarrierExample.displacement
#check NField.Alignment.SecondaryCarrierExample.coefficient_cutoff
#check NField.Alignment.SecondaryCarrierExample.floor_residues
#check NField.Alignment.SecondaryCarrierExample.collar_values
#check NField.Alignment.SecondaryCarrierExample.collar_sign_and_sum
#check NField.Alignment.SecondaryCarrierLogarithmicBounds.integer_carrier_prefix_log_bound
#check NField.Alignment.SecondaryCarrierLogarithmicBounds.one_carrier_log_bound
#check NField.Alignment.SecondaryCarrierLogarithmicBounds.absolute_carrier_sum_log_bound
#check NField.Alignment.SecondaryCollarBounds.slice_re_eq_prefix_layers
#check NField.Alignment.SecondaryCollarBounds.small_displacement_reservoir_bound
#check NField.Alignment.SecondaryCollarBounds.absolute_collar_own_logarithm
#check NField.Alignment.SecondaryCurvatureBounds.curvature_log_bound
#check NField.Alignment.SecondaryCurvatureBounds.scaled_curvature_log_bound
#check NField.Alignment.SecondaryCurvatureBounds.endpoint_alias_log_remainder
#check NField.Alignment.SecondaryEulerHarmonicSeries.harmonic_reciprocal_square_has_sum
#check NField.Alignment.SecondaryEulerHarmonicSeries.coprime_euler_harmonic_identity
#check NField.Alignment.SecondaryFiniteConsequences.bounded_reciprocal_divisor_moments
#check NField.Alignment.SecondaryFiniteConsequences.elementary_reservoir_log_bound
#check NField.Alignment.SecondaryFiniteConsequences.sampling_correction_bound
#check NField.Alignment.SecondaryFiniteConsequences.primitive_convolution_eq_packet
#check NField.Alignment.SecondaryLocalizationUnconditional.square_lock_localization
#check NField.Alignment.SecondaryLocalizationUnconditional.live_sector_damping
#check NField.Alignment.SecondaryLocalizationUnconditional.finite_secondary_coefficient_under_signed_damping
#check NField.Alignment.SecondaryPrintedBounds.one_carrier_harmonic_bound
#check NField.Alignment.SecondaryPrintedBounds.first_absolute_moment_logarithmic
#check NField.Alignment.SecondaryPrintedBounds.one_carrier_quadratic_logarithmic
#check NField.Alignment.SecondaryPrintedBounds.sampling_bound_printed
#check NField.Alignment.SecondaryPrintedBounds.sampling_bound_quadratic_logarithmic
#check NField.Alignment.SecondaryRealFractionalParts.mobius_reduction
#check NField.Alignment.SecondaryRealFractionalParts.weighted_fractional_parts
#check NField.Alignment.SecondaryRealStraightening.real_collision_straightening
#check NField.Alignment.SecondaryRealStraightening.real_sampled_energy
#check NField.Alignment.SecondaryReservoirIntermediate.elementary_reservoir_intermediate
#check NField.Alignment.SecondaryReservoirIntermediate.elementary_upper_sum_quadratic_logarithmic
#check NField.Alignment.SecondarySamplingAsymptotics.sampling_defect_isLittleO_log_square
#check NField.Alignment.SecondarySeriesConsequences.coprime_euler_series
#check NField.Alignment.SecondarySeriesConsequences.reduced_euler_tail_series
#check NField.Alignment.SecondarySeriesConsequences.logarithmic_reciprocal_square_summable
#check NField.Alignment.SecondarySeriesConsequences.gcd_lcm_logarithmic_error
#check NField.Alignment.SecondarySwitchingLedger.exact_selected_ledger
#check NField.Alignment.SecondarySwitchingLedger.fresh_collision_all_states
#check NField.Alignment.SecondarySwitchingLedger.selected_linear_ledger
#check NField.Alignment.SecondaryTermUnconditional.weighted_fractional_parts
#check NField.Alignment.SecondaryTermUnconditional.fractional_floor_asymptotic
#check NField.Alignment.SecondaryTermUnconditional.continuous_secondary_coefficient
#check NField.Alignment.SecondaryTermUnconditional.secondary_term_for_gcd_lcm_square
#check NField.Alignment.SecondaryTermUnconditional.secondary_term_for_gcd_lcm_triangular
#check NField.Alignment.SecondaryTermUnconditional.finite_secondary_coefficient
#check NField.Alignment.SignedDivisorWindow.signed_divisor_window_bound
#check NField.Alignment.SquareLockAsymptoticScales.collarMass_tendsto_zero
#check NField.Alignment.SquareLockAsymptoticScales.collarMass_isLittleO_log_square
#check NField.Alignment.SquareLockCountBound.square_lock_count_estimate
#check NField.Alignment.SquareLockCutoffLimits.fine_collar_tendsto_zero
#check NField.Alignment.SquareLockCutoffLimits.coefficient_collar_isLittleO_log_square
#check NField.Alignment.SquareLockCutoffLimits.coefficient_collar_isBigO_log
#check NField.Alignment.SquareLockDivisorInjection.centered_residue_divisor_lock
#check NField.Alignment.SquareLockDivisorInjection.carrier_count_le_signed_divisor_count
#check NField.Alignment.SquareLockRemainingStrip.remaining_carrier_strip
#check NField.Alignment.SquareLockRemainingStrip.remaining_floor_levels
#check NField.Alignment.TriangularAdditiveConvolution.primitive_lifetime_triangle
#check NField.Alignment.SaffariVaughanDistribution.saffari_vaughan_distribution
