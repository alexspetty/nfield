/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.UnityNativeWeights
import NField.Alignment.UnityNativeHilbert
import NField.Alignment.UnityNativeProjection
import NField.Alignment.UnityNativeCopies
import NField.Alignment.UnityNativeDilation
import NField.Alignment.UnityPrimitiveProbability
import NField.Alignment.UnityTransportedFit
import NField.Alignment.UnityMixedCarries
import NField.Alignment.UnityFiniteGram
import NField.Alignment.UnityGramPseudoinverse
import NField.Alignment.UnityStableCorrection
import NField.Alignment.UnityCumulativeCapture
import NField.Alignment.UnityNativeIsometry
import NField.Alignment.UnityProjectionBands
import NField.Alignment.UnityPrescribedDetectors
import NField.Alignment.UnityDetectorBandCost
import NField.Alignment.UnityGramCosts
import NField.Alignment.UnityVanishingCost
import NField.Alignment.UnityScalarCertificates
import NField.Alignment.UnitySelectedDetectors
import NField.Alignment.UnityDetectorHorizon
import NField.Alignment.UnityDetectorResponse

/-!
# Unity, Refinement, and Signed Capture

This is a partial companion for both published editions. It contains the
actual reciprocal-weight Hilbert model, primitive mass, integer copying,
mixed carries, finite projection and pseudoinverse gain, uncertain-reading
corrections, the prescribed shallow detector, its full signed terminal
response, all stated uniform detector costs and scalar certificates, and
the conditional cumulative-capture theorems.

The Wold/spine and arithmetic-detail claims, clock and mask formulas,
packet estimates and classical analytic equivalences are unfinished.
The website has the sufficient packet criterion; Zenodo Version 2 adds
its converse. Neither direction is claimed completed here. The stated
cumulative-capture lower bounds and packet-growth condition remain open.
This index does not establish whole-paper completion or the Riemann hypothesis.
Reader labels are owned by the source declarations selected below.
-/

namespace NField.Papers.UnityRefinementAndSignedCapture

#check NField.Alignment.UnityNativeWeights.weights_tsum
#check NField.Alignment.UnityNativeWeights.copy_block_weight
#check NField.Alignment.UnityNativeHilbert.inner_eq_weighted
#check NField.Alignment.UnityNativeHilbert.norm_sq_eq_weighted
#check NField.Alignment.UnityNativeHilbert.unity_norm_sq
#check NField.Alignment.UnityNativeProjection.unity_not_mem_clockSpace
#check NField.Alignment.UnityNativeProjection.deficit_pos
#check NField.Alignment.UnityNativeProjection.residual_inner_unity
#check NField.Alignment.UnityNativeProjection.fitted_energy
#check NField.Alignment.UnityNativeProjection.deficit_difference
#check NField.Alignment.UnityNativeProjection.deficit_antitone
#check NField.Alignment.UnityNativeProjection.capacity_difference
#check NField.Alignment.UnityNativeProjection.deficit_le_candidate
#check NField.Alignment.UnityNativeCopies.copy_norm_sq
#check NField.Alignment.UnityNativeCopies.copy_inner
#check NField.Alignment.UnityNativeCopies.copy_copy
#check NField.Alignment.UnityNativeDilation.copy_clock
#check NField.Alignment.UnityNativeDilation.copy_clockSpace
#check NField.Alignment.UnityNativeDilation.copy_mean
#check NField.Alignment.UnityNativeDilation.boundary_norm_sq
#check NField.Alignment.UnityNativeDilation.unity_boundary_copy
#check NField.Alignment.UnityPrimitiveProbability.kernel_total
#check NField.Alignment.UnityPrimitiveProbability.first_coordinate_one_mass
#check NField.Alignment.UnityPrimitiveProbability.unity_conditional_weight
#check NField.Alignment.UnityPrimitiveProbability.period_weighted_kernel
#check NField.Alignment.UnityPrimitiveProbability.period_mass_conservation
#check NField.Alignment.UnityPrimitiveProbability.probability_split_defect
#check NField.Alignment.UnityPrimitiveProbability.kernel_antidiagonal
#check NField.Alignment.UnityTransportedFit.transported_energy
#check NField.Alignment.UnityTransportedFit.transported_gain
#check NField.Alignment.UnityTransportedFit.residual_dilation
#check NField.Alignment.UnityMixedCarries.rowCarry_range
#check NField.Alignment.UnityMixedCarries.mixed_carry_reconstruction
#check NField.Alignment.UnityMixedCarries.resolved_clock_error
#check NField.Alignment.UnityMixedCarries.resolved_clock_error_range
#check NField.Alignment.UnityFiniteGram.gram_apply
#check NField.Alignment.UnityFiniteGram.gram_quadratic
#check NField.Alignment.UnityFiniteGram.jointGain_rayleigh
#check NField.Alignment.UnityGramPseudoinverse.gram_pseudo_gram
#check NField.Alignment.UnityGramPseudoinverse.pseudo_gram_pseudo
#check NField.Alignment.UnityGramPseudoinverse.gram_pseudo_symmetric
#check NField.Alignment.UnityGramPseudoinverse.jointGain_eq_pseudoinverse
#check NField.Alignment.UnityGramPseudoinverse.pseudoinverse_native_gain
#check NField.Alignment.UnityStableCorrection.stable_joint_gain
#check NField.Alignment.UnityStableCorrection.corrected_fit_mem
#check NField.Alignment.UnityStableCorrection.stable_native_correction
#check NField.Alignment.UnityCumulativeCapture.capacity_telescope
#check NField.Alignment.UnityCumulativeCapture.total_gain_budget
#check NField.Alignment.UnityCumulativeCapture.actual_probe_capture
#check NField.Alignment.UnityCumulativeCapture.actual_fractional_capture
#check NField.Alignment.UnityNativeIsometry.scaledCopy_value
#check NField.Alignment.UnityNativeIsometry.rootDetail_norm_sq
#check NField.Alignment.UnityNativeIsometry.rootDetail_value
#check NField.Alignment.UnityNativeIsometry.conditioned_norm_le
#check NField.Alignment.UnityNativeIsometry.residual_conditioned_reading
#check NField.Alignment.UnityNativeIsometry.scaledCopy_comp
#check NField.Alignment.UnityNativeIsometry.scaledCopy_clockSpace
#check NField.Alignment.UnityNativeIsometry.scaledCopy_clock
#check NField.Alignment.UnityNativeIsometry.binary_iterate
#check NField.Alignment.UnityProjectionBands.projectedEnergy_mono
#check NField.Alignment.UnityProjectionBands.band_orthogonal
#check NField.Alignment.UnityProjectionBands.band_energy
#check NField.Alignment.UnityPrescribedDetectors.detector_admitted
#check NField.Alignment.UnityPrescribedDetectors.detector_cost
#check NField.Alignment.UnityPrescribedDetectors.capture_eq_jointGain
#check NField.Alignment.UnityPrescribedDetectors.capture_le_native_gain
#check NField.Alignment.UnityPrescribedDetectors.prescribedFit_mem
#check NField.Alignment.UnityPrescribedDetectors.prescribedFit_energy
#check NField.Alignment.UnityPrescribedDetectors.prescribed_capacity_step
#check NField.Alignment.UnityPrescribedDetectors.prescribed_capture_recovery
#check NField.Alignment.UnityDetectorBandCost.coarseCutoff_two
#check NField.Alignment.UnityDetectorBandCost.full_band_cost_bound
#check NField.Alignment.UnityDetectorBandCost.selected_band_cost_sharp
#check NField.Alignment.UnityDetectorBandCost.totalCost_le_two
#check NField.Alignment.UnityDetectorBandCost.totalCost_sharp
#check NField.Alignment.UnityGramCosts.gramMatrix_trace
#check NField.Alignment.UnityGramCosts.largestEigenvalue_le_trace
#check NField.Alignment.UnityGramCosts.readings_cost
#check NField.Alignment.UnityGramCosts.prescribed_uniform_cost
#check NField.Alignment.UnityGramCosts.prescribed_half_lower
#check NField.Alignment.UnityVanishingCost.root_energy_tendsto
#check NField.Alignment.UnityVanishingCost.selected_cost_tendsto_zero
#check NField.Alignment.UnityVanishingCost.totalCost_tendsto_zero
#check NField.Alignment.UnityVanishingCost.detectorTrace_tendsto_zero
#check NField.Alignment.UnityScalarCertificates.prescribed_certificate_chain
#check NField.Alignment.UnityScalarCertificates.prescribed_rayleigh
#check NField.Alignment.UnitySelectedDetectors.selected_uniform_cost
#check NField.Alignment.UnityDetectorHorizon.horizon_integer_ceiling
#check NField.Alignment.UnityDetectorHorizon.eligible_nonempty
#check NField.Alignment.UnityDetectorResponse.pullback_eq_iterate
#check NField.Alignment.UnityDetectorResponse.pulled_residual_orthogonal
#check NField.Alignment.UnityDetectorResponse.prescribed_terminal_response
#check NField.Alignment.UnityDetectorResponse.binary_clock_lift

end NField.Papers.UnityRefinementAndSignedCapture
