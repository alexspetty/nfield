/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.HarperTiltedFactors
import NField.Alignment.SteinhausFiniteTilt

/-!
# Prime-coordinate laws and independence under Euler-energy weighting

The actual Euler-energy weighted law equals the infinite product of its
normalized prime-coordinate laws and the untouched Haar laws. Finite
marginals, cancellation of unused cutoff factors and independence of
disjoint coordinate blocks follow for this measure, not a replacement model.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.HarperTiltedCoordinates
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Filter SteinhausMoment SteinhausCoordinates
  SteinhausFiniteTilt HarperTiltedMeasure HarperTiltedFactors CollisionMertensInput

def coordinateDensity (P : ℝ) (s : ℂ) (q : ℕ) (z : UnitAddCircle) : ℝ≥0∞ :=
  if q ∈ primesUpTo P then ENNReal.ofReal (localDensity q s z) else 1
def coordinateLaw (P : ℝ) (s : ℂ) (q : ℕ) : Measure UnitAddCircle :=
  AddCircle.haarAddCircle.withDensity (coordinateDensity P s q)

theorem coordinateDensity_measurable (P : ℝ) (s : ℂ) (q : ℕ) :
    Measurable (coordinateDensity P s q) := by
  unfold coordinateDensity
  split_ifs
  · exact (localDensity_measurable q s).ennreal_ofReal
  · exact measurable_const

theorem coordinateDensity_integral (P : ℝ) {s : ℂ} (hs : 0 < s.re) (q : ℕ) :
    (∫⁻ z, coordinateDensity P s q z ∂AddCircle.haarAddCircle) = 1 := by
  by_cases hq : q ∈ primesUpTo P
  · have hp := (primesUpTo_mem.mp hq).1
    simp only [coordinateDensity, if_pos hq]
    rw [← ofReal_integral_eq_lintegral_ofReal (localDensity_integrable hp hs)
      (Eventually.of_forall (fun z => (localDensity_pos hp hs z).le)), localDensity_integral hp hs]
    norm_num
  · simp [coordinateDensity, hq]

theorem coordinateLaw_probability (P : ℝ) {s : ℂ} (hs : 0 < s.re) (q : ℕ) :
    IsProbabilityMeasure (coordinateLaw P s q) := by
  constructor
  rw [coordinateLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, coordinateDensity_integral P hs q]

theorem energyDensity_ennreal_product (P : ℝ) {s : ℂ} (hs : 0 < s.re) (ω : PhaseSpace) :
    ENNReal.ofReal (energyDensity P s ω) = ∏ q ∈ primesUpTo P, coordinateDensity P s q (ω q) := by
  rw [energyDensity_eq_prod P hs, ENNReal.ofReal_prod_of_nonneg
    (fun q hq => (localDensity_pos (primesUpTo_mem.mp hq).1 hs _).le)]
  exact Finset.prod_congr rfl (fun q hq => by simp only [coordinateDensity, if_pos hq])

theorem tiltedMeasure_eq_product (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    tiltedMeasure P s = Measure.infinitePi (coordinateLaw P s) := by
  unfold tiltedMeasure
  simp_rw [energyDensity_ennreal_product P hs]
  exact finite_density_product_law (primesUpTo P) (coordinateDensity P s)
    (coordinateDensity_measurable P s) (coordinateDensity_integral P hs)
    (fun q hq z => by simp only [coordinateDensity, if_neg hq])

theorem coordinate_law (P : ℝ) {s : ℂ} (hs : 0 < s.re) (q : ℕ) :
    (tiltedMeasure P s).map (fun ω => ω q) = coordinateLaw P s q := by
  letI := fun q => coordinateLaw_probability P hs q
  rw [tiltedMeasure_eq_product P hs, Measure.infinitePi_map_eval]

theorem unused_coordinate_law (P : ℝ) (s : ℂ) {q : ℕ} (hq : q ∉ primesUpTo P) :
    coordinateLaw P s q = AddCircle.haarAddCircle := by
  have he : coordinateDensity P s q = fun _ => 1 := by
    funext z
    exact if_neg hq
  unfold coordinateLaw
  rw [he, withDensity_const, one_smul]

theorem coordinates_independent (P : ℝ) {s : ℂ} (hs : 0 < s.re) :
    iIndepFun (fun q (ω : PhaseSpace) => ω q) (tiltedMeasure P s) := by
  letI := fun q => coordinateLaw_probability P hs q
  rw [tiltedMeasure_eq_product P hs]
  exact iIndepFun_infinitePi (X := fun _ (z : UnitAddCircle) => z) (fun _ => measurable_id)

theorem finite_coordinate_law (P : ℝ) {s : ℂ} (hs : 0 < s.re) (S : Finset ℕ) :
    (tiltedMeasure P s).map S.restrict = Measure.pi (fun q : S => coordinateLaw P s q) := by
  letI := fun q => coordinateLaw_probability P hs q
  rw [tiltedMeasure_eq_product P hs, Measure.infinitePi_map_restrict]

theorem finite_coordinate_cutoff_eq (P Q : ℝ) {s : ℂ} (hs : 0 < s.re) (S : Finset ℕ)
    (hPQ : ∀ q ∈ S, q ∈ primesUpTo P ↔ q ∈ primesUpTo Q) :
    (tiltedMeasure P s).map S.restrict = (tiltedMeasure Q s).map S.restrict := by
  rw [finite_coordinate_law P hs, finite_coordinate_law Q hs]
  congr 1
  funext q
  unfold coordinateLaw
  congr 1
  funext z
  simp only [coordinateDensity, hPQ q q.property]

theorem integral_finite_coordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : ℝ) {s : ℂ} (hs : 0 < s.re) (S : Finset ℕ) (f : (S → UnitAddCircle) → E)
    (hf : Measurable f) :
    (∫ ω, f (S.restrict ω) ∂tiltedMeasure P s) =
      ∫ z, f z ∂Measure.pi (fun q : S => coordinateLaw P s q) := by
  rw [← integral_map (Finset.measurable_restrict S).aemeasurable hf.aestronglyMeasurable,
    finite_coordinate_law P hs]

theorem integral_cutoff_locality (P Q : ℝ) {s : ℂ} (hs : 0 < s.re) {S : Finset ℕ}
    {f : PhaseSpace → ℂ} (hf : Measurable f) (hS : DependsOn S f)
    (hPQ : ∀ q ∈ S, q ∈ primesUpTo P ↔ q ∈ primesUpTo Q) :
    (∫ ω, f ω ∂tiltedMeasure P s) = ∫ ω, f ω ∂tiltedMeasure Q s := by
  have hm := hf.comp (extendCoordinates_measurable S)
  have hp := integral_map (μ := tiltedMeasure P s) (Finset.measurable_restrict S).aemeasurable hm.aestronglyMeasurable
  have hq := integral_map (μ := tiltedMeasure Q s) (Finset.measurable_restrict S).aemeasurable hm.aestronglyMeasurable
  have he (ω : PhaseSpace) : f (extendCoordinates S (S.restrict ω)) = f ω :=
    dependsOn_factorization hS ω
  simp only [Function.comp_apply, he] at hp hq
  rw [← hp, ← hq, finite_coordinate_cutoff_eq P Q hs S hPQ]

theorem disjoint_blocks_independent (P : ℝ) {s : ℂ} (hs : 0 < s.re) {S T : Finset ℕ}
    (hST : Disjoint S T) :
    IndepFun (fun ω : PhaseSpace => S.restrict ω) (fun ω : PhaseSpace => T.restrict ω)
      (tiltedMeasure P s) :=
  (coordinates_independent P hs).indepFun_finset S T hST (fun q => measurable_pi_apply q)

theorem disjoint_block_functions_independent {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (P : ℝ) {s : ℂ} (hs : 0 < s.re) {S T : Finset ℕ} (hST : Disjoint S T)
    {f : (S → UnitAddCircle) → E} {g : (T → UnitAddCircle) → F}
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun ω : PhaseSpace => f (S.restrict ω)) (fun ω : PhaseSpace => g (T.restrict ω))
      (tiltedMeasure P s) := (disjoint_blocks_independent P hs hST).comp hf hg

theorem independent_of_disjoint_coordinates (P : ℝ) {s : ℂ} (hs : 0 < s.re)
    {S T : Finset ℕ} (hST : Disjoint S T) {f g : PhaseSpace → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hS : DependsOn S f) (hT : DependsOn T g) :
    IndepFun f g (tiltedMeasure P s) := by
  have h := disjoint_block_functions_independent P hs hST
    (hf.comp (extendCoordinates_measurable S)) (hg.comp (extendCoordinates_measurable T))
  have he : (fun ω : PhaseSpace => (f ∘ extendCoordinates S) (S.restrict ω)) = f :=
    funext (dependsOn_factorization hS)
  have he' : (fun ω : PhaseSpace => (g ∘ extendCoordinates T) (T.restrict ω)) = g :=
    funext (dependsOn_factorization hT)
  rwa [he, he'] at h

theorem integral_mul_disjoint (P : ℝ) {s : ℂ} (hs : 0 < s.re)
    {S T : Finset ℕ} (hST : Disjoint S T) {f g : PhaseSpace → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hS : DependsOn S f) (hT : DependsOn T g) :
    (∫ ω, f ω*g ω ∂tiltedMeasure P s) =
      (∫ ω, f ω ∂tiltedMeasure P s)*(∫ ω, g ω ∂tiltedMeasure P s) :=
  (independent_of_disjoint_coordinates P hs hST hf hg hS hT).integral_fun_mul_eq_mul_integral
    hf.aestronglyMeasurable hg.aestronglyMeasurable

theorem block_coordinates_independent {ι : Type*} (P : ℝ) {s : ℂ} (hs : 0 < s.re)
    (S : ι → Finset ℕ) (hST : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepFun (fun i (ω : PhaseSpace) => (S i).restrict ω) (tiltedMeasure P s) := by
  letI := fun q => coordinateLaw_probability P hs q
  letI := tiltedMeasure_probability P hs
  let idx : ((i : ι) × S i) → ℕ := fun a => a.2.val
  have hinj : Function.Injective idx := by
    rintro ⟨i,qi⟩ ⟨j,qj⟩ he
    change qi.val = qj.val at he
    have hij : i = j := by
      by_contra hn
      exact Finset.disjoint_left.mp (hST hn) qi.property (he.symm ▸ qj.property)
    subst j
    congr 1
    exact Subtype.ext he
  let pull : PhaseSpace → ((i : ι) × S i) → UnitAddCircle := fun ω a => ω (idx a)
  have hm : Measurable pull := measurable_pi_lambda _ (fun a => measurable_pi_apply (idx a))
  have hmap : (tiltedMeasure P s).map (fun ω i => (S i).restrict ω) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun q : S i => coordinateLaw P s q)) := by
    calc
      _ = ((tiltedMeasure P s).map pull).map
          (MeasurableEquiv.piCurry (fun i (_ : S i) => UnitAddCircle)) := by
        rw [Measure.map_map (MeasurableEquiv.piCurry _).measurable hm]
        rfl
      _ = _ := by
        rw [tiltedMeasure_eq_product P hs,
          Measure.map_infinitePi_infinitePi_of_inj hinj]
        exact Measure.infinitePi_map_piCurry (fun i (q : S i) => coordinateLaw P s q)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => (S i).measurable_restrict), hmap]
  congr 1
  funext i
  symm
  rw [tiltedMeasure_eq_product P hs]
  exact Measure.map_infinitePi_infinitePi_of_inj (f := fun q : S i => q.val) Subtype.val_injective

theorem block_functions_independent {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (P : ℝ) {s : ℂ} (hs : 0 < s.re) (S : ι → Finset ℕ)
    (hST : Pairwise (fun i j => Disjoint (S i) (S j)))
    (f : ∀ i, (S i → UnitAddCircle) → E i) (hf : ∀ i, Measurable (f i)) :
    iIndepFun (fun i (ω : PhaseSpace) => f i ((S i).restrict ω)) (tiltedMeasure P s) :=
  (block_coordinates_independent P hs S hST).comp f hf

end NField.Alignment.HarperTiltedCoordinates
