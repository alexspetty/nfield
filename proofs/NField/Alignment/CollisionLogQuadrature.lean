/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Strict logarithm bounds for the harmonic remainder

Both error functions vanish at zero and have explicitly positive rational
derivatives. These local inequalities are not a conductor-expansion claim.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionLogQuadrature

def trapezoidLog (t : ℝ) : ℝ := t/2+t/(2*(1+t))
def correctionLog (t : ℝ) : ℝ := (t^2-(t/(1+t))^2)/12
def upperLogGap (t : ℝ) : ℝ := trapezoidLog t-Real.log (1+t)
def lowerLogGap (t : ℝ) : ℝ := Real.log (1+t)-trapezoidLog t+correctionLog t

theorem upperLogGap_hasDerivAt (t : ℝ) (ht : 0≤t) :
    HasDerivAt upperLogGap (t^2/(2*(1+t)^2)) t := by
  have h1 : 1+t≠0 := by positivity
  have h2 : 2*(1+t)≠0 := by positivity
  have hi := hasDerivAt_id t
  have hs := hi.const_add 1
  have hr := (hi.div_const 2).add (hi.div (hs.const_mul 2) h2)
  have he := hr.sub (hs.log h1)
  unfold upperLogGap trapezoidLog
  convert! he using 1
  dsimp
  field_simp
  ring

theorem lowerLogGap_hasDerivAt (t : ℝ) (ht : 0≤t) :
    HasDerivAt lowerLogGap (t^4/(6*(1+t)^3)) t := by
  have h1 : 1+t≠0 := by positivity
  have h2 : 2*(1+t)≠0 := by positivity
  have hi := hasDerivAt_id t
  have hs := hi.const_add 1
  have hr := (hi.div_const 2).add (hi.div (hs.const_mul 2) h2)
  have hc := ((hi.pow 2).sub ((hi.div hs h1).pow 2)).div_const 12
  have he := ((hs.log h1).sub hr).add hc
  unfold lowerLogGap trapezoidLog correctionLog
  convert! he using 1
  dsimp
  field_simp
  ring

theorem upperLogGap_strictMonoOn : StrictMonoOn upperLogGap (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro t ht
    exact (upperLogGap_hasDerivAt t ht).continuousAt.continuousWithinAt
  · intro t ht
    have hp : 0<t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    rw [(upperLogGap_hasDerivAt t hp.le).deriv]
    positivity

theorem lowerLogGap_strictMonoOn : StrictMonoOn lowerLogGap (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro t ht
    exact (lowerLogGap_hasDerivAt t ht).continuousAt.continuousWithinAt
  · intro t ht
    have hp : 0<t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    rw [(lowerLogGap_hasDerivAt t hp.le).deriv]
    positivity

theorem log_lt_trapezoid {t : ℝ} (ht : 0<t) : Real.log (1+t)<trapezoidLog t := by
  have he := upperLogGap_strictMonoOn (show (0 : ℝ)∈Set.Ici 0 from by simp) ht.le ht
  have hz : upperLogGap 0=0 := by norm_num [upperLogGap,trapezoidLog]
  rw [hz,upperLogGap] at he
  linarith

theorem trapezoid_sub_correction_lt_log {t : ℝ} (ht : 0<t) :
    trapezoidLog t-correctionLog t<Real.log (1+t) := by
  have he := lowerLogGap_strictMonoOn (show (0 : ℝ)∈Set.Ici 0 from by simp) ht.le ht
  have hz : lowerLogGap 0=0 := by norm_num [lowerLogGap,trapezoidLog,correctionLog]
  rw [hz,lowerLogGap] at he
  linarith

end NField.Alignment.CollisionLogQuadrature
