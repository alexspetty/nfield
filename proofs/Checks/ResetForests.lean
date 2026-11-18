/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Papers.SamplingDefectAndResetForests
import Lean.Util.CollectAxioms
/-!
# Axiom check for selected reset-forest results

This explicit list covers the principal identities, coordinate constructions,
forest bounds and conditional cost criteria. Each entry must be a theorem.
Only Lean's standard `propext`, `Classical.choice` and `Quot.sound` axioms are
allowed. In particular, `sorryAx` or an additional mathematical axiom fails the
check. This check does not remove any hypothesis from a theorem statement.
-/

open Lean Elab Command

private def resetForestStatements : Array Name := #[
  ``NField.ResetForests.AbsoluteForestWork.polynomial_forest_absolute_any_exponent,
  ``NField.ResetForests.SignedForestWork.polynomial_signed_and_restoration_any_exponent,
  ``NField.ResetForests.SignedForestWork.forest_remainder_identity,
  ``NField.ResetForests.SignedForestWork.polynomial_forest_remainder,
  ``NField.ResetForests.SignedForestWork.polynomial_forest_half_rate_iff,
  ``NField.ResetForests.SourceMetrics.both_prime_square_grams_posDef,
  ``NField.ResetForests.FibreReconstruction.complete_fibre_map_injective,
  ``NField.ResetForests.FibreReconstruction.continuous_fibre_reconstruction,
  ``NField.ResetForests.FibreReconstruction.sampled_fibre_reconstruction,
  ``NField.ResetForests.FibreTraces.reduced_reset_limits_and_jump,
  ``NField.ResetForests.FibreTraces.coherent_fibre_endpoint_limits,
  ``NField.ResetForests.GramDecomposition.collision_energy_complete_readings,
  ``NField.ResetForests.GramDecomposition.complete_gram_sector_split,
  ``NField.ResetForests.GramDecomposition.collision_energy_unit_sector,
  ``NField.ResetForests.PrimitiveCoordinates.primitive_basis_apply,
  ``NField.ResetForests.PrimitiveCoordinates.primitive_field_gram,
  ``NField.ResetForests.PrimitiveCoordinates.continuous_incidence_factorization,
  ``NField.ResetForests.PrimitiveCoordinates.primitive_torus_projection,
  ``NField.ResetForests.QuadraticResponse.full_source_reset_identity,
  ``NField.ResetForests.QuadraticResponse.coherent_complete_reset_identity,
  ``NField.ResetForests.QuadraticResponse.full_sampling_fderiv,
  ``NField.ResetForests.Core.reflected_source_word_integer,
  ``NField.ResetForests.Core.folded_word_third,
  ``NField.ResetForests.Core.common_sampling_phase,
  ``NField.ResetForests.CenteredPhase.centered_joint_clock,
  ``NField.ResetForests.CarryWork.prime_carry_clock_identity,
  ``NField.ResetForests.ClockRows.complete_clock_row_estimate,
  ``NField.ResetForests.ClockRows.complete_clock_binary_source,
  ``NField.ResetForests.PhasePopulations.raw_clock_divisor_bound,
  ``NField.ResetForests.PhasePopulations.complete_clock_interior_half_power,
  ``NField.ResetForests.PhasePopulations.reset_load_tail_real,
  ``NField.ResetForests.ResetGrid.reset_grid_estimate,
  ``NField.ResetForests.Core.incoming_and_triple_budget,
  ``NField.ResetForests.AbsoluteForestWork.whole_forest_absolute_estimate,
  ``NField.ResetForests.ReturnWindows.growing_window_absolute,
  ``NField.ResetForests.ReturnWindows.growing_window_sampling,
  ``NField.ResetForests.ReturnWindows.growing_window_half_rate_iff,
  ``NField.ResetForests.Core.collapse_reset_mass,
  ``NField.ResetForests.Core.reset_mass_injective,
  ``NField.ResetForests.Core.collapse_source_unique,
  ``NField.ResetForests.Core.collapse_idempotent,
  ``NField.ResetForests.ResetMasks.forest_matrix_inverse,
  ``NField.ResetForests.ResetMasks.forest_inverse_matrix,
  ``NField.ResetForests.ResetMasks.coherent_basis_coordinates,
  ``NField.ResetForests.ResetMasks.reset_mask_complement,
  ``NField.ResetForests.ResetMasks.reset_mask_compose,
  ``NField.ResetForests.ResetMasks.ordered_clock_entry,
  ``NField.ResetForests.ResetMasks.masked_boundary_full_split,
  ``NField.ResetForests.ResetMasks.masked_boundary_complement,
  ``NField.ResetForests.SignedForestWork.other_forest_restoration_identity,
  ``NField.ResetForests.ReturnWindows.growing_signed_and_restoration,
  ``NField.ResetForests.ReturnWindows.polynomial_binary_remainder,
  ``NField.ResetForests.LoadedWords.retained_clock_word_partition,
  ``NField.ResetForests.CompletePackets.packet_fringe_normalized_small_power,
  ``NField.ResetForests.CompletePackets.complete_packet_reading_half_power,
  ``NField.ResetForests.PacketCycles.complete_packet_half_rate_iff,
  ``NField.ResetForests.PacketCycles.labelled_word_period_first,
  ``NField.ResetForests.BranchTransport.actual_measure_branch_connection,
  ``NField.ResetForests.BranchTransport.actual_measure_potential_transport,
  ``NField.ResetForests.BranchTransport.actual_measure_midpoint_transport,
  ``NField.ResetForests.BranchTransport.actual_clock_strip_identity,
  ``NField.ResetForests.PacketQueries.complete_packet_record_rank_signature,
  ``NField.ResetForests.PacketQueries.complete_packet_record_minimal,
  ``NField.ResetForests.PacketQueries.complete_packet_quadratic_record_minimal,
  ``NField.ResetForests.RecordGeometry.complete_record_query,
  ``NField.ResetForests.RecordGeometry.complete_query_blocks_unique,
  ``NField.ResetForests.RecordGeometry.actual_source_query_blocks_unique,
  ``NField.ResetForests.RecordGeometry.record_lift_unique_minimum,
  ``NField.ResetForests.RecordGeometry.entering_lift_unique_minimum,
  ``NField.ResetForests.RecordGeometry.complete_record_energy,
  ``NField.ResetForests.SeedRecord.seed_complete_query_rank_signature,
  ``NField.ResetForests.SeedRecord.seed_complete_coherent_work,
  ``NField.ResetForests.SeedRecord.seed_native_interior_work,
  ``NField.ResetForests.SeedRecord.seed_actual_complete_packet,
  ``NField.ResetForests.Core.weighted_prime_square_identity,
  ``NField.ResetForests.PrefixGeometry.actual_source_coherent_work,
  ``NField.ResetForests.PrefixGeometry.actual_prefix_full_detector_formula,
  ``NField.ResetForests.PrefixGeometry.actual_compressed_cost_formula,
  ``NField.ResetForests.PrefixGeometry.compressed_increment_cost_formula,
  ``NField.ResetForests.PrefixGeometry.readout_is_metric_projection,
  ``NField.ResetForests.PrefixGeometry.actual_dyadic_prefix_partition,
  ``NField.ResetForests.PrefixGeometry.prefix_increment_energy,
  ``NField.ResetForests.PrefixGeometry.prefix_complete_source_energy,
  ``NField.ResetForests.Core.signed_cost_loss,
  ``NField.ResetForests.Core.grouped_cost_decrease,
  ``NField.ResetForests.CostCriteria.sufficient_half_power_criterion,
  ``NField.ResetForests.CostCriteria.entire_packet_half_power_criterion,
  ``NField.ResetForests.CostCriteria.dyadic_band_half_power_criterion,
  ``NField.ResetForests.CostCriteria.source_energy_cubic_limit,
  ``NField.ResetForests.RefinedBounds.corrected_error_literal,
  ``NField.ResetForests.RefinedBounds.corrected_half_power_iff,
  ``NField.ResetForests.RefinedBounds.sample_error_quarter_power,
  ``NField.ResetForests.RefinedBounds.corrected_carry_quarter_power,
  ``NField.ResetForests.RefinedBounds.diagonal_mass_cubic_limit,
  ``NField.ResetForests.RefinedBounds.off_diagonal_mass_cubic_limit,
  ``NField.ResetForests.RefinedBounds.curvature_log_isBigO,
  ``NField.ResetForests.RefinedBounds.normalized_load_tail_log_bound,
  ``NField.ResetForests.RefinedBounds.dyadic_local_half_power_criterion,
  ``NField.ResetForests.RefinedBounds.one_final_prefix_cost
]

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in resetForestStatements do
    match env.find? theoremName with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected a theorem: {theoremName}"
    for axiomName in ← collectAxioms theoremName do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {theoremName}"
  logInfo m!"Checked {resetForestStatements.size} selected reset-forest theorems; only standard Lean axioms occur."
