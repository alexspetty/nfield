/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A concrete Steinhaus probability model

Take independent normalized Haar phases, indexed by the natural numbers.
Only prime coordinates enter the multiplicative function. Keeping the
unused coordinates is harmless and gives one fixed probability space for
every integer cutoff.
-/

set_option autoImplicit false

namespace NField.Alignment.SteinhausMoment

open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory

abbrev PhaseSpace := ℕ → UnitAddCircle

noncomputable def phaseMeasure : Measure PhaseSpace :=
  Measure.infinitePi (fun _ : ℕ => AddCircle.haarAddCircle)

instance : IsProbabilityMeasure phaseMeasure := by
  unfold phaseMeasure
  infer_instance

noncomputable def phase (p : ℕ) (k : ℤ) (ω : PhaseSpace) : ℂ :=
  fourier k (ω p)

theorem phase_measurable (p : ℕ) (k : ℤ) : Measurable (phase p k) :=
  (fourier k).continuous.measurable.comp (measurable_pi_apply p)

theorem phase_norm (p : ℕ) (k : ℤ) (ω : PhaseSpace) : ‖phase p k ω‖ = 1 :=
  Circle.norm_coe _

theorem haar_phase_integral (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) =
      if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · subst k
    simp
  · rw [if_neg hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk (by norm_num))

theorem phase_integral (p : ℕ) (k : ℤ) :
    (∫ ω, phase p k ω ∂phaseMeasure) = if k=0 then 1 else 0 := by
  calc
    _ = ∫ x : UnitAddCircle, fourier k x
        ∂(phaseMeasure.map (fun ω => ω p)) :=
      (integral_map (measurable_pi_apply p).aemeasurable
        (fourier k).continuous.aestronglyMeasurable).symm
    _ = ∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle := by
      rw [phaseMeasure, Measure.infinitePi_map_eval]
    _ = _ := haar_phase_integral k

theorem phases_independent (k : ℕ → ℤ) :
    iIndepFun (fun p => phase p (k p)) phaseMeasure := by
  exact iIndepFun_infinitePi (X := fun p => fourier (k p))
    (fun p => (fourier (k p)).continuous.measurable)

theorem phase_product_integral (s : Finset ℕ) (k : ℕ → ℤ) :
    (∫ ω, ∏ p ∈ s, phase p (k p) ω ∂phaseMeasure) =
      ∏ p ∈ s, if k p=0 then (1 : ℂ) else 0 := by
  have hI := (phases_independent k).precomp (g := fun p : s => p.val) Subtype.val_injective
  have h := hI.integral_fun_prod_eq_prod_integral
    (fun p => (phase_measurable p.val (k p.val)).aestronglyMeasurable)
  have hprod (ω : PhaseSpace) :
      (∏ p : s, phase p.val (k p.val) ω) = ∏ p ∈ s, phase p (k p) ω :=
    s.prod_coe_sort (fun p => phase p (k p) ω)
  have hprod' : (∏ p : s, if k p.val=0 then (1 : ℂ) else 0) =
      ∏ p ∈ s, if k p=0 then (1 : ℂ) else 0 :=
    s.prod_coe_sort (fun p => if k p=0 then (1 : ℂ) else 0)
  simp_rw [phase_integral, hprod] at h
  rw [hprod'] at h
  exact h

/-- The Steinhaus multiplicative function, extended by zero at zero. -/
noncomputable def steinhaus (n : ℕ) (ω : PhaseSpace) : ℂ :=
  if n=0 then 0 else ∏ p ∈ n.primeFactors, phase p (n.factorization p : ℤ) ω

@[simp] theorem steinhaus_zero (ω : PhaseSpace) : steinhaus 0 ω = 0 := by
  simp [steinhaus]

@[simp] theorem steinhaus_one (ω : PhaseSpace) : steinhaus 1 ω = 1 := by
  simp [steinhaus]

theorem steinhaus_measurable (n : ℕ) : Measurable (steinhaus n) := by
  classical
  change Measurable (fun ω => steinhaus n ω)
  by_cases hn : n=0
  · subst n
    simp only [steinhaus_zero]
    exact measurable_const
  · simp only [steinhaus, if_neg hn]
    exact Finset.measurable_prod _ (fun p _ => phase_measurable p _)

theorem steinhaus_norm {n : ℕ} (hn : n≠0) (ω : PhaseSpace) :
    ‖steinhaus n ω‖ = 1 := by
  simp [steinhaus, hn, norm_prod, phase_norm]

theorem steinhaus_norm_le (n : ℕ) (ω : PhaseSpace) : ‖steinhaus n ω‖ ≤ 1 := by
  by_cases hn : n=0
  · simp [hn]
  · exact (steinhaus_norm hn ω).le

theorem steinhaus_integrable (n : ℕ) : Integrable (steinhaus n) phaseMeasure :=
  Integrable.of_bound (steinhaus_measurable n).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (steinhaus_norm_le n))

theorem factorization_eq_zero_of_not_mem {n p : ℕ} (hp : p ∉ n.primeFactors) :
    n.factorization p=0 := by
  exact Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)

/-- A larger finite prime set gives the same product: the extra exponents vanish. -/
theorem steinhaus_eq_product {n : ℕ} (hn : n≠0) (s : Finset ℕ)
    (hs : n.primeFactors ⊆ s) (ω : PhaseSpace) :
    steinhaus n ω = ∏ p ∈ s, phase p (n.factorization p : ℤ) ω := by
  rw [steinhaus, if_neg hn]
  exact Finset.prod_subset hs (fun p _ hp => by
    simp [factorization_eq_zero_of_not_mem hp, phase])

theorem steinhaus_prime {p : ℕ} (hp : p.Prime) (ω : PhaseSpace) :
    steinhaus p ω = phase p 1 ω := by
  simp [steinhaus, hp.ne_zero, hp.primeFactors, hp.factorization]

/-- Independent uniform circle values, stated on the actual prime index type. -/
theorem prime_values_independent :
    iIndepFun (fun p : {p : ℕ // p.Prime} => steinhaus p.val) phaseMeasure := by
  have h := (phases_independent (fun _ => 1)).precomp
    (g := fun p : {p : ℕ // p.Prime} => p.val) Subtype.val_injective
  have heq : (fun p : {p : ℕ // p.Prime} => steinhaus p.val) =
      (fun p : {p : ℕ // p.Prime} => phase p.val 1) := by
    funext p ω
    exact steinhaus_prime p.property ω
  rw [heq]
  exact h

/-- Every prime value has the pushforward of normalized circle Haar measure. -/
theorem prime_value_law {p : ℕ} (hp : p.Prime) :
    phaseMeasure.map (steinhaus p) =
      (AddCircle.haarAddCircle : Measure UnitAddCircle).map (fourier 1) := by
  have heq : steinhaus p = (fourier (T := 1) 1) ∘ (fun ω : PhaseSpace => ω p) := by
    funext ω
    exact steinhaus_prime hp ω
  rw [heq, ← Measure.map_map (fourier 1).continuous.measurable (measurable_pi_apply p),
    phaseMeasure, Measure.infinitePi_map_eval]

theorem steinhaus_mul (m n : ℕ) (ω : PhaseSpace) :
    steinhaus (m*n) ω = steinhaus m ω * steinhaus n ω := by
  classical
  by_cases hm : m=0
  · simp [hm]
  by_cases hn : n=0
  · simp [hn]
  let s := m.primeFactors ∪ n.primeFactors
  rw [steinhaus_eq_product (mul_ne_zero hm hn) s (by
    rw [Nat.primeFactors_mul hm hn]),
    steinhaus_eq_product hm s Finset.subset_union_left,
    steinhaus_eq_product hn s Finset.subset_union_right,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  simp only [Nat.factorization_mul hm hn, Finsupp.add_apply, Nat.cast_add,
    phase, fourier_add]

noncomputable def steinhausHom (ω : PhaseSpace) : ℕ →*₀ ℂ where
  toFun := fun n => steinhaus n ω
  map_zero' := steinhaus_zero ω
  map_one' := steinhaus_one ω
  map_mul' := fun m n => steinhaus_mul m n ω

theorem steinhaus_pow (n k : ℕ) (ω : PhaseSpace) :
    steinhaus (n^k) ω = steinhaus n ω ^ k :=
  (steinhausHom ω).map_pow n k

theorem steinhaus_prod {ι : Type*} (s : Finset ι) (a : ι → ℕ) (ω : PhaseSpace) :
    steinhaus (∏ i ∈ s, a i) ω = ∏ i ∈ s, steinhaus (a i) ω :=
  map_prod (steinhausHom ω) a s

theorem steinhaus_pair_integrable (u v : ℕ) :
    Integrable (fun ω => steinhaus u ω * star (steinhaus v ω)) phaseMeasure := by
  have hstar : Measurable (fun ω => star (steinhaus v ω)) :=
    Complex.continuous_conj.measurable.comp (steinhaus_measurable v)
  apply Integrable.of_bound
    ((steinhaus_measurable u).mul hstar).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro ω
  change ‖steinhaus u ω * star (steinhaus v ω)‖ ≤ 1
  rw [norm_mul, norm_star]
  exact mul_le_one₀ (steinhaus_norm_le u ω) (norm_nonneg _) (steinhaus_norm_le v ω)

theorem steinhaus_pair_product {u v : ℕ} (hu : u≠0) (hv : v≠0) (ω : PhaseSpace) :
    steinhaus u ω * star (steinhaus v ω) =
      ∏ p ∈ u.primeFactors ∪ v.primeFactors,
        phase p ((u.factorization p : ℤ)-(v.factorization p : ℤ)) ω := by
  classical
  rw [steinhaus_eq_product hu _ Finset.subset_union_left,
    steinhaus_eq_product hv _ Finset.subset_union_right, star_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  simp only [phase, sub_eq_add_neg, fourier_add, fourier_neg, starRingEnd_apply]

/-- Exact diagonal orthogonality, proved for the constructed probability model. -/
theorem steinhaus_orthogonality {u v : ℕ} (hu : u≠0) (hv : v≠0) :
    (∫ ω, steinhaus u ω * star (steinhaus v ω) ∂phaseMeasure) =
      if u=v then 1 else 0 := by
  classical
  simp_rw [steinhaus_pair_product hu hv]
  rw [phase_product_integral]
  by_cases huv : u=v
  · simp [huv]
  · rw [if_neg huv]
    have hex : ∃ p, u.factorization p ≠ v.factorization p := by
      by_contra! h
      exact huv (Nat.factorization_inj hu hv (Finsupp.ext h))
    obtain ⟨p, hp⟩ := hex
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨p, ?_, ?_⟩
    · by_contra hs
      have hs' := Finset.notMem_union.mp hs
      exact hp ((factorization_eq_zero_of_not_mem hs'.1).trans
        (factorization_eq_zero_of_not_mem hs'.2).symm)
    · have hne : (u.factorization p : ℤ)-(v.factorization p : ℤ) ≠ 0 := by
        intro h
        exact hp (Int.ofNat_inj.mp (sub_eq_zero.mp h))
      simp [hne]

/-- Linear extension of orthogonality to a finite, complex weighted pairing. -/
theorem finite_pairing_integral (s t : Finset ℕ) (c : ℕ → ℕ → ℂ)
    (hs : ∀ u ∈ s, u≠0) (ht : ∀ v ∈ t, v≠0) :
    (∫ ω, ∑ u ∈ s, ∑ v ∈ t,
      c u v * (steinhaus u ω * star (steinhaus v ω)) ∂phaseMeasure) =
      ∑ u ∈ s, ∑ v ∈ t, c u v * (if u=v then 1 else 0) := by
  have hI (u v : ℕ) : Integrable
      (fun ω => c u v * (steinhaus u ω * star (steinhaus v ω))) phaseMeasure :=
    (steinhaus_pair_integrable u v).const_mul _
  rw [integral_finsetSum s (fun u _ => integrable_finsetSum t (fun v _ => hI u v))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum t (fun v _ => hI u v)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul, steinhaus_orthogonality (hs u hu) (ht v hv)]

theorem polynomial_pair_expansion (s t : Finset ℕ) (c d : ℕ → ℂ) (ω : PhaseSpace) :
    (∑ u ∈ s, c u * steinhaus u ω) * star (∑ v ∈ t, d v * steinhaus v ω) =
      ∑ u ∈ s, ∑ v ∈ t, (c u * star (d v)) *
        (steinhaus u ω * star (steinhaus v ω)) := by
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem polynomial_pair_integrable (s t : Finset ℕ) (c d : ℕ → ℂ) :
    Integrable (fun ω => (∑ u ∈ s, c u * steinhaus u ω) *
      star (∑ v ∈ t, d v * steinhaus v ω)) phaseMeasure := by
  simp_rw [polynomial_pair_expansion]
  exact integrable_finsetSum s (fun u _ => integrable_finsetSum t
    (fun v _ => (steinhaus_pair_integrable u v).const_mul _))

/-- The mixed second moment of any two finite Dirichlet polynomials. -/
theorem polynomial_pair_integral (s t : Finset ℕ) (c d : ℕ → ℂ)
    (hs : ∀ u ∈ s, u≠0) (ht : ∀ v ∈ t, v≠0) :
    (∫ ω, (∑ u ∈ s, c u * steinhaus u ω) *
      star (∑ v ∈ t, d v * steinhaus v ω) ∂phaseMeasure) =
      ∑ u ∈ s, ∑ v ∈ t, (c u * star (d v)) * (if u=v then 1 else 0) := by
  simp_rw [polynomial_pair_expansion]
  exact finite_pairing_integral s t _ hs ht

theorem self_pair_eq_norm_sq (z : ℂ) : z * star z = (‖z‖^2 : ℝ) := by
  exact (Complex.mul_conj z).trans (congrArg (fun r : ℝ => (r : ℂ))
    (Complex.normSq_eq_norm_sq z))

/-- The exact L2 norm of a finite Steinhaus Dirichlet polynomial. -/
theorem polynomial_second_moment (s : Finset ℕ) (c : ℕ → ℂ)
    (hs : ∀ u ∈ s, u≠0) :
    (∫ ω, ‖∑ u ∈ s, c u * steinhaus u ω‖^2 ∂phaseMeasure) =
      ∑ u ∈ s, ‖c u‖^2 := by
  classical
  have h := polynomial_pair_integral s s c c hs hs
  have hsum : (∑ u ∈ s, ∑ v ∈ s,
      (c u * star (c v)) * (if u=v then (1 : ℂ) else 0)) =
      ∑ u ∈ s, c u * star (c u) := by
    apply Finset.sum_congr rfl
    intro u hu
    simp [mul_ite, hu]
  rw [hsum] at h
  simp_rw [self_pair_eq_norm_sq] at h
  rw [integral_complex_ofReal] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.re_sum] using hre

end NField.Alignment.SteinhausMoment
