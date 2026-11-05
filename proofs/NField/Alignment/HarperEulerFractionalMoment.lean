/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperLocalExponentialMoment

/-!
# The actual Euler-product 11/5 moment and extreme samples

Independent prime coordinates factor the exponential expectation. The exact
local leading coefficient 121/100 is retained; the cubic errors sum to a
fixed constant. The proved Mertens estimate then gives the uniform actual
11/5 moment bound O(log(P)^(121/100)). The exact extreme-energy reduction
therefore yields O(log(P)^(99/100)), uniformly in frequency and at the
rounded conditioning samples. No moment growth estimate is assumed.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperEulerFractionalMoment
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Asymptotics SteinhausMoment HarperRandomEulerProduct HarperEulerIntegral
  HarperEulerLogComparison HarperModerateSamples HarperLocalExponentialMoment
  CollisionMertensInput HarperSmoothDivisor HarperConditioningFrequencies HarperRoundedCutoff

def exponentialProduct (P t : ℝ) (ω : PhaseSpace) : ℝ :=
  ∏ q ∈ primesUpTo P, Real.exp (localArgument q t ω)
def cubicPrimeMajorant : ℝ := ∑' n : ℕ, (n : ℝ)^(-(3/2 : ℝ))
def momentConstant : ℝ :=
  Real.exp ((11/5 : ℝ)*logRemainderConstant)*Real.exp (localErrorConstant*cubicPrimeMajorant)

theorem momentConstant_pos : 0 < momentConstant := by
  unfold momentConstant
  positivity

theorem exponentialProduct_eq_exp (P t : ℝ) (ω : PhaseSpace) :
    exponentialProduct P t ω = Real.exp ((11/5 : ℝ)*quadraticPrimeSum P t ω) := by
  unfold exponentialProduct quadraticPrimeSum
  rw [Complex.re_sum, Finset.mul_sum, Real.exp_sum]
  rfl

theorem exponentialProduct_measurable (P t : ℝ) : Measurable (exponentialProduct P t) :=
  Finset.measurable_prod _ (fun q _ => Real.continuous_exp.measurable.comp (localArgument_measurable q t))

theorem exponentialProduct_bound (P t : ℝ) (ω : PhaseSpace) :
    exponentialProduct P t ω ≤ Real.exp 4 ^ (primesUpTo P).card := by
  unfold exponentialProduct
  calc
    _ ≤ ∏ _q ∈ primesUpTo P, Real.exp 4 := by
      apply Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le)
      intro q hq
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans
        (localArgument_abs_le_four (primesUpTo_mem.mp hq).1 t ω))
    _ = _ := by simp

theorem exponentialProduct_integrable (P t : ℝ) : Integrable (exponentialProduct P t) phaseMeasure := by
  apply Integrable.of_bound (exponentialProduct_measurable P t).aestronglyMeasurable
    (Real.exp 4 ^ (primesUpTo P).card)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg (by unfold exponentialProduct; positivity)]
  exact exponentialProduct_bound P t ω

theorem exponentialProduct_expectation (P t : ℝ) :
    (∫ ω, exponentialProduct P t ω ∂phaseMeasure) =
      ∏ q ∈ primesUpTo P, ∫ ω, Real.exp (localArgument q t ω) ∂phaseMeasure := by
  let s := primesUpTo P
  let g : s → {q : ℕ // q.Prime} := fun q => ⟨q.val,(primesUpTo_mem.mp q.property).1⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun q : {q : ℕ // q.Prime} => q.val) h
  have hI := prime_values_independent.precomp (g := g) hg
  let f (q : s) (z : ℂ) : ℝ :=
    Real.exp ((11/5 : ℝ)*(z/(q.val : ℂ)^(linePoint (1/2) t)+
      (z/(q.val : ℂ)^(linePoint (1/2) t))^2/2).re)
  have hf (q : s) : Measurable (f q) := by
    exact Real.continuous_exp.measurable.comp ((Complex.continuous_re.measurable.comp
      ((measurable_id.div_const _).add (((measurable_id.div_const _).pow_const 2).div_const 2))).const_mul _)
  have h := hI.integral_fun_prod_comp (f := f)
    (fun q => (steinhaus_measurable q.val).aemeasurable) (fun q => (hf q).aestronglyMeasurable)
  change (∫ ω, ∏ q : s, Real.exp (localArgument q.val t ω) ∂phaseMeasure) =
    ∏ q : s, ∫ ω, Real.exp (localArgument q.val t ω) ∂phaseMeasure at h
  have hp (ω : PhaseSpace) : (∏ q : s, Real.exp (localArgument q.val t ω)) =
      exponentialProduct P t ω := s.prod_coe_sort (fun q => Real.exp (localArgument q t ω))
  have hp' : (∏ q : s, ∫ ω, Real.exp (localArgument q.val t ω) ∂phaseMeasure) =
      ∏ q ∈ primesUpTo P, ∫ ω, Real.exp (localArgument q t ω) ∂phaseMeasure :=
    s.prod_coe_sort (fun q => ∫ ω, Real.exp (localArgument q t ω) ∂phaseMeasure)
  simp_rw [hp] at h
  rw [hp'] at h
  exact h

theorem exponentialProduct_expectation_exp_bound (P t : ℝ) :
    (∫ ω, exponentialProduct P t ω ∂phaseMeasure) ≤
      Real.exp ((121/100 : ℝ)*(∑ q ∈ primesUpTo P, (q : ℝ)⁻¹)+
        localErrorConstant*(∑ q ∈ primesUpTo P, (q : ℝ)^(-(3/2 : ℝ)))) := by
  rw [exponentialProduct_expectation]
  calc
    _ ≤ ∏ q ∈ primesUpTo P, Real.exp ((121/100 : ℝ)*(q : ℝ)⁻¹+
        localErrorConstant*(q : ℝ)^(-(3/2 : ℝ))) := by
      apply Finset.prod_le_prod (fun q _ => integral_nonneg (fun ω => (Real.exp_pos _).le))
      intro q hq
      exact local_exponential_mean_exp_bound (primesUpTo_mem.mp hq).1 t
    _ = _ := by rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem exp_inverse_prime_bound {q : ℕ} (hq : q.Prime) :
    Real.exp ((q : ℝ)⁻¹) ≤ (1-(q : ℝ)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hpos : 0 < 1-(q : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hq1)
  apply (Real.le_log_iff_exp_le (inv_pos.mpr hpos)).mp
  rw [Real.log_inv]
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

theorem exp_prime_reciprocal_sum_bound (P : ℝ) :
    Real.exp (∑ q ∈ primesUpTo P, (q : ℝ)⁻¹) ≤ inversePrimeProduct P := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
    (fun q hq => exp_inverse_prime_bound (primesUpTo_mem.mp hq).1)

theorem cubic_prime_sum_bound (P : ℝ) :
    (∑ q ∈ primesUpTo P, (q : ℝ)^(-(3/2 : ℝ))) ≤ cubicPrimeMajorant :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ) < -1)).sum_le_tsum _
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem exponentialProduct_expectation_bound (P t : ℝ) :
    (∫ ω, exponentialProduct P t ω ∂phaseMeasure) ≤
      (inversePrimeProduct P)^(121/100 : ℝ)*Real.exp (localErrorConstant*cubicPrimeMajorant) := by
  calc
    _ ≤ Real.exp ((121/100 : ℝ)*(∑ q ∈ primesUpTo P, (q : ℝ)⁻¹)+
        localErrorConstant*(∑ q ∈ primesUpTo P, (q : ℝ)^(-(3/2 : ℝ)))) :=
      exponentialProduct_expectation_exp_bound P t
    _ ≤ Real.exp ((121/100 : ℝ)*(∑ q ∈ primesUpTo P, (q : ℝ)⁻¹)+
        localErrorConstant*cubicPrimeMajorant) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (cubic_prime_sum_bound P) localErrorConstant_pos.le)
    _ = (Real.exp (∑ q ∈ primesUpTo P, (q : ℝ)⁻¹))^(121/100 : ℝ)*
        Real.exp (localErrorConstant*cubicPrimeMajorant) := by
      rw [Real.exp_add, mul_comm (121/100 : ℝ), Real.exp_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Real.exp_pos _).le (exp_prime_reciprocal_sum_bound P) (by norm_num))
      (Real.exp_pos _).le

theorem eulerProduct_moment_point_bound (P t : ℝ) (ω : PhaseSpace) :
    ‖eulerProduct P (linePoint (1/2) t) ω‖^(11/5 : ℝ) ≤
      Real.exp ((11/5 : ℝ)*logRemainderConstant)*exponentialProduct P t ω := by
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (eulerProduct_critical_ne_zero P t ω)),
    exponentialProduct_eq_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp (log_eulerProduct_quadratic_bound P t ω)).2
  linarith

theorem eulerProduct_moment_prime_product_bound (P t : ℝ) :
    (∫ ω, ‖eulerProduct P (linePoint (1/2) t) ω‖^(11/5 : ℝ) ∂phaseMeasure) ≤
      momentConstant*(inversePrimeProduct P)^(121/100 : ℝ) := by
  calc
    _ ≤ ∫ ω, Real.exp ((11/5 : ℝ)*logRemainderConstant)*exponentialProduct P t ω ∂phaseMeasure :=
      integral_mono (norm_rpow_integrable P t (by norm_num))
        ((exponentialProduct_integrable P t).const_mul _) (eulerProduct_moment_point_bound P t)
    _ = Real.exp ((11/5 : ℝ)*logRemainderConstant)*
        (∫ ω, exponentialProduct P t ω ∂phaseMeasure) := integral_const_mul _ _
    _ ≤ Real.exp ((11/5 : ℝ)*logRemainderConstant)*
        ((inversePrimeProduct P)^(121/100 : ℝ)*Real.exp (localErrorConstant*cubicPrimeMajorant)) :=
      mul_le_mul_of_nonneg_left (exponentialProduct_expectation_bound P t) (Real.exp_pos _).le
    _ = _ := by unfold momentConstant; ring

theorem eventual_eulerProduct_moment_log_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ t : ℝ, (∫ ω, ‖eulerProduct P (linePoint (1/2) t) ω‖^(11/5 : ℝ) ∂phaseMeasure) ≤
      C*(Real.log P)^(121/100 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := inversePrimeProduct_isBigO_log.exists_pos
  refine ⟨momentConstant*C^(121/100 : ℝ),mul_pos momentConstant_pos (Real.rpow_pos_of_pos hC _),?_⟩
  filter_upwards [hb.bound,Real.tendsto_log_atTop.eventually_gt_atTop 0] with P hp hlog
  rw [Real.norm_of_nonneg (inversePrimeProduct_pos _).le,Real.norm_of_nonneg hlog.le] at hp
  intro t
  calc
    _ ≤ momentConstant*(inversePrimeProduct P)^(121/100 : ℝ) := eulerProduct_moment_prime_product_bound P t
    _ ≤ momentConstant*(C*Real.log P)^(121/100 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (inversePrimeProduct_pos P).le hp (by norm_num)) momentConstant_pos.le
    _ = _ := by rw [Real.mul_rpow hC.le hlog.le]; ring

theorem eventual_extremeEnergy_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ t : ℝ, (∫ ω, extremeEnergy P t ω ∂phaseMeasure) ≤ C*(Real.log P)^(99/100 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_eulerProduct_moment_log_bound
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [hb,Real.tendsto_log_atTop.eventually_ge_atTop 1] with P hm hlog
  have hpos : 0 < Real.log P := lt_of_lt_of_le zero_lt_one hlog
  intro t
  have he : (Real.log P)^(-(11/50 : ℝ))*(Real.log P)^(121/100 : ℝ) =
      (Real.log P)^(99/100 : ℝ) := by rw [← Real.rpow_add hpos]; norm_num
  have hlo : (Real.log P)^(-(11/5 : ℝ)) ≤ (Real.log P)^(99/100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  calc
    _ ≤ (Real.log P)^(-(11/50 : ℝ))*
        (∫ ω, ‖eulerProduct P (linePoint (1/2) t) ω‖^(11/5 : ℝ) ∂phaseMeasure)+
          (Real.log P)^(-(11/5 : ℝ)) := extremeEnergy_expectation_bound hpos t
    _ ≤ (Real.log P)^(-(11/50 : ℝ))*(C*(Real.log P)^(121/100 : ℝ))+
        (Real.log P)^(99/100 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left (hm t) (Real.rpow_nonneg hpos.le _)) hlo
    _ = _ := by rw [mul_left_comm,he]; ring

theorem eventual_actual_extremeEnergy_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ k : Fin (factorCount x),
      (∫ ω, extremeEnergy (primeCutoff x) (frequency x k) ω ∂phaseMeasure) ≤
        C*(cutoffLog x)^(99/100 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := eventual_extremeEnergy_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [primeCutoff_tendsto.eventually hb] with x h
  intro k
  simpa only [log_primeCutoff] using h (frequency x k)

end NField.Alignment.HarperEulerFractionalMoment
