/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperWeightedCharacteristic

/-!
# Characteristic functions of actual finite prime-range logarithms

Under the actual critical weighted law, logarithms from active prime
coordinates give an exact product characteristic function. Contractive
product comparison sums the proved local errors. The Gaussian product is
identified with its exact summed mean and variance. Frequencies may vary
with the prime and the finite range may be empty.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperPrimeRangeCharacteristic
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter SteinhausMoment HarperTiltedMeasure
  HarperTiltedCoordinates HarperEulerIntegral HarperEulerLogComparison HarperTiltedLogBounds
  HarperCharacteristicTaylor HarperGaussianFactor HarperWeightedCharacteristic CollisionMertensInput

def rangeLog (S : Finset ℕ) (t : ℕ → ℝ) (ω : PhaseSpace) : ℝ :=
  ∑ q ∈ S, primeLog q (t q) ω
def rangeCharacteristic (P : ℝ) (S : Finset ℕ) (t : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∫ ω, phaseExponential u (rangeLog S t ω) ∂tiltedMeasure P (linePoint (1/2) 0)
def rangeMean (S : Finset ℕ) (t : ℕ → ℝ) : ℝ :=
  ∑ q ∈ S, Real.cos (t q*Real.log q)/q
def rangeVariance (S : Finset ℕ) : ℝ := ∑ q ∈ S, (q : ℝ)⁻¹/2
def rangeGaussian (S : Finset ℕ) (t : ℕ → ℝ) (u : ℝ) : ℂ :=
  Complex.exp ((u*rangeMean S t : ℝ)*Complex.I-(u^2*rangeVariance S/2 : ℝ))

theorem contractive_product_norm {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) : ‖∏ i ∈ S, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) hf

theorem contractive_product_difference {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) (hg : ∀ i ∈ S, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ S, f i)-(∏ i ∈ S, g i)‖ ≤ ∑ i ∈ S, ‖f i-g i‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfS : ∀ i ∈ S, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS : ∀ i ∈ S, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga := hg a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have he : f a*(∏ i ∈ S, f i)-g a*(∏ i ∈ S, g i) =
        (f a-g a)*(∏ i ∈ S, f i)+g a*((∏ i ∈ S, f i)-(∏ i ∈ S, g i)) := by ring
    rw [he]
    calc
      _ ≤ ‖(f a-g a)*(∏ i ∈ S, f i)‖+‖g a*((∏ i ∈ S, f i)-(∏ i ∈ S, g i))‖ := norm_add_le _ _
      _ = ‖f a-g a‖*‖∏ i ∈ S, f i‖+‖g a‖*‖(∏ i ∈ S, f i)-(∏ i ∈ S, g i)‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖f a-g a‖*1+1*(∑ i ∈ S, ‖f i-g i‖) := add_le_add
        (mul_le_mul_of_nonneg_left (contractive_product_norm S f hfS) (norm_nonneg _))
        (mul_le_mul hga (ih hfS hgS) (norm_nonneg _) (by norm_num))
      _ = _ := by ring

theorem phaseExponential_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) (u : ℝ) :
    phaseExponential u (∑ i ∈ S, f i) = ∏ i ∈ S, phaseExponential u (f i) := by
  have he : (((u*∑ i ∈ S, f i : ℝ) : ℂ)*Complex.I) =
      ∑ i ∈ S, (((u*f i : ℝ) : ℂ)*Complex.I) := by
    rw [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
  rw [phaseExponential, he, Complex.exp_sum]
  rfl

theorem rangeLog_measurable (S : Finset ℕ) (t : ℕ → ℝ) : Measurable (rangeLog S t) :=
  Finset.measurable_sum S (fun q _ => primeLog_measurable q (t q))

theorem primePhase_functions_independent (P : ℝ) (S : Finset ℕ) (hS : S ⊆ primesUpTo P)
    (t : ℕ → ℝ) (u : ℝ) :
    iIndepFun (fun (q : S) (ω : PhaseSpace) => phaseExponential u (primeLog q (t q) ω))
      (tiltedMeasure P (linePoint (1/2) 0)) := by
  let f : ℕ → UnitAddCircle → ℂ := fun q z =>
    phaseExponential u (logFactor (fourier 1 z/(q : ℂ)^(linePoint (1/2) (t q))))
  have hf (q : ℕ) : Measurable (f q) := (phaseExponential_measurable u).comp
    (((measurable_const.sub ((fourier 1).continuous.measurable.div_const _)).inv.norm).log)
  have hi := (coordinates_independent P (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])).comp f hf
  have h := hi.precomp (g := fun q : S => q.val) Subtype.val_injective
  have he : (fun (q : S) (ω : PhaseSpace) => phaseExponential u (primeLog q (t q) ω)) =
      (fun (q : S) (ω : PhaseSpace) => f q (ω q)) := by
    funext q ω
    simp only [f, primeLog, primeTerm, steinhaus_prime (primesUpTo_mem.mp (hS q.property)).1]
    rfl
  rw [he]
  exact h

theorem rangeCharacteristic_product (P : ℝ) (S : Finset ℕ) (hS : S ⊆ primesUpTo P)
    (t : ℕ → ℝ) (u : ℝ) :
    rangeCharacteristic P S t u = ∏ q ∈ S, localCharacteristic P q (t q) u := by
  letI := tiltedMeasure_probability P (show 0 < (linePoint (1/2) 0).re by norm_num [linePoint])
  have hi := primePhase_functions_independent P S hS t u
  have h := hi.integral_fun_prod_eq_prod_integral (fun q =>
    ((phaseExponential_measurable u).comp (primeLog_measurable q (t q))).aestronglyMeasurable)
  have he (ω : PhaseSpace) :
      (∏ q : S, phaseExponential u (primeLog q (t q) ω)) =
      ∏ q ∈ S, phaseExponential u (primeLog q (t q) ω) :=
    S.prod_coe_sort (fun q => phaseExponential u (primeLog q (t q) ω))
  have he' : (∏ q : S, localCharacteristic P q (t q) u) =
      ∏ q ∈ S, localCharacteristic P q (t q) u :=
    S.prod_coe_sort (fun q => localCharacteristic P q (t q) u)
  simp_rw [he] at h
  change (∫ ω, ∏ q ∈ S, phaseExponential u (primeLog q (t q) ω)
    ∂tiltedMeasure P (linePoint (1/2) 0)) = (∏ q : S, localCharacteristic P q (t q) u) at h
  rw [he'] at h
  unfold rangeCharacteristic rangeLog
  simp_rw [phaseExponential_sum]
  exact h

theorem rangeGaussian_product (S : Finset ℕ) (t : ℕ → ℝ) (u : ℝ) :
    rangeGaussian S t u = ∏ q ∈ S, gaussianFactor q (Real.cos (t q*Real.log q)) u := by
  have he (q : ℕ) : gaussianExponent q (Real.cos (t q*Real.log q)) u =
      ((u*(Real.cos (t q*Real.log q)/q) : ℝ) : ℂ)*Complex.I-
        ((u^2/2*((q : ℝ)⁻¹/2) : ℝ) : ℂ) := by
    unfold gaussianExponent
    push_cast
    ring
  simp only [gaussianFactor]
  rw [← Complex.exp_sum]
  simp_rw [he]
  unfold rangeGaussian rangeMean rangeVariance
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum,
    ← Finset.mul_sum, ← Complex.ofReal_sum, ← Finset.mul_sum]
  push_cast
  ring

theorem rangeCharacteristic_gaussian_error (P : ℝ) (S : Finset ℕ) (hS : S ⊆ primesUpTo P)
    (t : ℕ → ℝ) {u : ℝ} (hu : ∀ q ∈ S, |u| ≤ Real.sqrt q) :
    ‖rangeCharacteristic P S t u-rangeGaussian S t u‖ ≤
      comparisonConstant*(|u|+|u|^3)*(∑ q ∈ S, (q : ℝ)^(-(3/2 : ℝ))) := by
  rw [rangeCharacteristic_product P S hS t u, rangeGaussian_product]
  calc
    _ ≤ ∑ q ∈ S, ‖localCharacteristic P q (t q) u-gaussianFactor q (Real.cos (t q*Real.log q)) u‖ :=
      contractive_product_difference S _ _ (fun q _ => localCharacteristic_norm_le_one P q (t q) u)
        (fun q _ => gaussianFactor_norm_le_one (Nat.cast_nonneg q) _ _)
    _ ≤ ∑ q ∈ S, comparisonConstant*(|u|+|u|^3)*(q : ℝ)^(-(3/2 : ℝ)) :=
      Finset.sum_le_sum (fun q hq => localCharacteristic_gaussian_error P (hS hq) (t q) (hu q hq))
    _ = _ := by rw [Finset.mul_sum]

end NField.Alignment.HarperPrimeRangeCharacteristic
