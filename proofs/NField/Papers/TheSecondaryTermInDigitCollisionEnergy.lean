/-
Author: Alexander S. Petty
-/

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

/-!
# The Secondary Term in Digit-Collision Energy

Reader-facing declaration map for every named mathematical object in the
manuscript. Exact finite identities already closed by this companion are
proved in theorem-object modules. Analytic source estimates are explicit
hypotheses of the declarations that consume them; the finite reductions,
limit passages, and final assembly are proved here without unchecked
declarations.

There are 40 checked theorem declarations and one explicitly open problem.
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

end NField.Papers.TheSecondaryTermInDigitCollisionEnergy
