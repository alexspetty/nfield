/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.ResetForests.CostRealization61
import NField.ResetForests.FiniteCostLoss
import NField.ResetForests.OpeningRates
import NField.ResetForests.LeadingMass
import NField.ResetForests.LogRemainders
import NField.ResetForests.DyadicLocal
/-!
# The Sampling Defect and Reset Forests

Formal companion to Alexander S. Petty's
*The Sampling Defect and Reset Forests*,
https://doi.org/10.5281/zenodo.24282329.

## Coverage

The imported modules give the complete reset identity, positive energy forms,
fibre and source coordinates, and the absolute and signed bounds on controlled
reset forests. They retain the complete sampled field, its mixed work and its
complementary reset reading. The polynomial-height forest estimates improve
on the quarter-power sampling bound within those forests.

The later modules give packet partitions, ordered boundary work, the complete
quadratic record, entering-source decompositions, readout projections and
signed coarsening costs.

The exact four-clock example, leading-mass limits and logarithmic remainder
bounds are included.

## Scope and assumptions

The corresponding bound for the full complementary reading remains open.
The sufficient half-power criteria retain the required cost-growth hypotheses.
Query uniqueness concerns the specified symmetric representatives. The local
cost criterion uses the specified dyadic cuts; it does not assert a bound for
arbitrary partitions. All hypotheses are stated in the individual Lean
declarations. `check-reset-forests.sh` builds this companion and checks the
axioms of an explicit selection of its principal results.
-/
