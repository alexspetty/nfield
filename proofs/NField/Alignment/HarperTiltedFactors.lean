/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTiltedMeasure

/-!
# The actual normalized Euler-factor densities

Each prime-coordinate energy has a positive finite integral. Independence
factors the full second moment into those integrals, identifying their
product with the already proved exact reciprocal-prime product. Hence the
actual global density is exactly the product of normalized local densities.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperTiltedFactors
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter SteinhausMoment HarperRandomEulerProduct
  HarperEulerSecondMoment HarperTiltedMeasure HarperSmoothCount CollisionMertensInput

def localEnergy (q : ℕ) (s : ℂ) (z : UnitAddCircle) : ℝ :=
  ‖(1-fourier 1 z/(q : ℂ)^s)⁻¹‖^2
def localMass (q : ℕ) (s : ℂ) : ℝ := ∫ z, localEnergy q s z ∂AddCircle.haarAddCircle
def localDensity (q : ℕ) (s : ℂ) (z : UnitAddCircle) : ℝ :=
  localEnergy q s z / localMass q s

theorem localEnergy_measurable (q : ℕ) (s : ℂ) : Measurable (localEnergy q s) :=
  ((measurable_const.sub ((fourier 1).continuous.measurable.div_const _)).inv.norm).pow_const 2

theorem localTerm_norm {q : ℕ} (hq : q ≠ 0) (s : ℂ) (z : UnitAddCircle) :
    ‖fourier 1 z/(q : ℂ)^s‖ = (q : ℝ)^(-s.re) := by
  have hz : ‖fourier (T := 1) 1 z‖ = 1 := Circle.norm_coe _
  rw [norm_div, hz, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hq),
    Real.rpow_neg (Nat.cast_nonneg q)]
  exact one_div _

theorem localTerm_norm_lt_one {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re)
    (z : UnitAddCircle) : ‖fourier 1 z/(q : ℂ)^s‖ < 1 := by
  rw [localTerm_norm hq.ne_zero]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq.one_lt) (by linarith)

theorem localDenominator_ne_zero {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re)
    (z : UnitAddCircle) : 1-fourier 1 z/(q : ℂ)^s ≠ 0 := by
  intro h
  have he := (sub_eq_zero.mp h).symm
  have hb := localTerm_norm_lt_one hq hs z
  rw [he, norm_one] at hb
  exact (lt_irrefl (1 : ℝ)) hb

theorem localEnergy_pos {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re)
    (z : UnitAddCircle) : 0 < localEnergy q s z :=
  pow_pos (norm_pos_iff.mpr (inv_ne_zero (localDenominator_ne_zero hq hs z))) 2

theorem localEnergy_bound {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re)
    (z : UnitAddCircle) : localEnergy q s z ≤ ((1-(q : ℝ)^(-s.re))⁻¹)^2 := by
  have hr : 0 < 1-(q : ℝ)^(-s.re) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq.one_lt) (by linarith))
  have hn : 1-(q : ℝ)^(-s.re) ≤ ‖1-fourier 1 z/(q : ℂ)^s‖ := by
    simpa only [norm_one, localTerm_norm hq.ne_zero] using
      norm_sub_norm_le (1 : ℂ) (fourier 1 z/(q : ℂ)^s)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hr hn

theorem localEnergy_integrable {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re) :
    Integrable (localEnergy q s) AddCircle.haarAddCircle := by
  apply Integrable.of_bound (localEnergy_measurable q s).aestronglyMeasurable
    (((1-(q : ℝ)^(-s.re))⁻¹)^2)
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_of_nonneg (localEnergy_pos hq hs z).le]
    exact localEnergy_bound hq hs z)

theorem localMass_pos {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re) :
    0 < localMass q s := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (localEnergy_pos hq hs z).le)
    (localEnergy_integrable hq hs)).mpr
  have he : Function.support (localEnergy q s) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (localEnergy_pos hq hs z)
  rw [he, measure_univ]
  exact zero_lt_one

theorem localDensity_measurable (q : ℕ) (s : ℂ) : Measurable (localDensity q s) :=
  (localEnergy_measurable q s).div_const _

theorem localDensity_pos {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re)
    (z : UnitAddCircle) : 0 < localDensity q s z :=
  div_pos (localEnergy_pos hq hs z) (localMass_pos hq hs)

theorem localDensity_integrable {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re) :
    Integrable (localDensity q s) AddCircle.haarAddCircle :=
  (localEnergy_integrable hq hs).div_const _

theorem localDensity_integral {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re) :
    (∫ z, localDensity q s z ∂AddCircle.haarAddCircle) = 1 := by
  unfold localDensity
  rw [integral_div, ← localMass, div_self (ne_of_gt (localMass_pos hq hs))]

theorem localEnergy_phase_integral (q : ℕ) (s : ℂ) :
    (∫ ω, localEnergy q s (ω q) ∂phaseMeasure) = localMass q s := by
  rw [← integral_map (measurable_pi_apply q).aemeasurable
    (localEnergy_measurable q s).aestronglyMeasurable, phaseMeasure, Measure.infinitePi_map_eval]
  rfl

theorem eulerEnergy_eq_prod (P : ℝ) (s : ℂ) (ω : PhaseSpace) :
    ‖eulerProduct P s ω‖^2 = ∏ q ∈ primesUpTo P, localEnergy q s (ω q) := by
  unfold eulerProduct
  rw [norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro q hq
  rw [steinhaus_prime (primesUpTo_mem.mp hq).1]
  rfl

theorem localMass_product (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    (∏ q ∈ primesUpTo P, localMass q s) = shiftedProduct P (2*s.re) := by
  have hi : iIndepFun (fun q (ω : PhaseSpace) => localEnergy q s (ω q)) phaseMeasure :=
    iIndepFun_infinitePi (fun q => localEnergy_measurable q s)
  have hI := hi.precomp (g := fun q : primesUpTo P => q.val) Subtype.val_injective
  have h := hI.integral_fun_prod_eq_prod_integral (fun q =>
      ((localEnergy_measurable q.val s).comp (measurable_pi_apply q.val)).aestronglyMeasurable)
  have hp (ω : PhaseSpace) : (∏ q : primesUpTo P, localEnergy q.val s (ω q.val)) =
      ∏ q ∈ primesUpTo P, localEnergy q s (ω q) :=
    (primesUpTo P).prod_coe_sort (fun q => localEnergy q s (ω q))
  have hp' : (∏ q : primesUpTo P, ∫ ω, localEnergy q.val s (ω q.val) ∂phaseMeasure) =
      ∏ q ∈ primesUpTo P, ∫ ω, localEnergy q s (ω q) ∂phaseMeasure :=
    (primesUpTo P).prod_coe_sort (fun q => ∫ ω, localEnergy q s (ω q) ∂phaseMeasure)
  simp_rw [hp] at h
  rw [hp'] at h
  simp_rw [localEnergy_phase_integral] at h
  rw [← h]
  simp_rw [← eulerEnergy_eq_prod]
  exact eulerProduct_second_moment P hs

theorem energyDensity_eq_prod (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    energyDensity P s ω = ∏ q ∈ primesUpTo P, localDensity q s (ω q) := by
  simp only [localDensity, Finset.prod_div_distrib]
  rw [localMass_product P hs, ← eulerEnergy_eq_prod]
  rfl

end NField.Alignment.HarperTiltedFactors
