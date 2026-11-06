/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.RealReciprocalPrefixEstimate
import NField.Alignment.SaffariVaughanReciprocalTransfer

/-! # The weighted Saffari–Vaughan distribution estimate

The strict fractional-part threshold, integer endpoints, and printed
logarithmic exponent are retained. The real reciprocal estimate is proved
by the preceding finite moment, Fourier, and parameter modules.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.SaffariVaughanDistribution
open WeightedFractionalPartTransfer RealReciprocalPrefixEstimate
  ReciprocalLogComparison SaffariVaughanReciprocalTransfer

/-- Title: `Weighted fractional-part distribution`. -/
theorem saffari_vaughan_distribution : SaffariVaughanDistributionEstimate := by
  obtain ⟨C,hC,hR⟩ := reciprocal_prefix_estimate
  exact saffari_vaughan_of_reciprocal C prefixDecay hC.le prefixDecay_pos
    prefixDecay_le_one hR

end NField.Alignment.SaffariVaughanDistribution
