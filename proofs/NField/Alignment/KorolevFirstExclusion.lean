/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KorolevSmoothCount
import NField.Alignment.HarperSieveBound

/-!
# First smooth/rough exclusion in Korolev's prime-factor decomposition

At Q = exp(log x / log(log x)), the already proved Selberg sieve gives
an explicit rough count. Its Q^4 error is eventually at most sqrt(x).
Combining this with the strengthened Rankin bound controls the literal
union of smooth and rough integers by O(x log(log x) / log x), uniformly
after restriction to any modulus's coprime integers. This is only step
2 of Lemma A; the two selected prime-factor windows are not proved here.
-/

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.KorolevFirstExclusion
open scoped BigOperators Topology
open Filter HarperSmoothCount HarperRoundedCutoff HarperSmoothCountDecay
  HarperSmoothRough HarperIntervalSieve HarperSieveBound KorolevSmoothCount
  HarperSmoothDivisor CollisionMertensInput

def roughSet (x y : ℝ) : Finset ℕ :=
  (intervalSupport 0 x).filter (fun n => n.Coprime (primeBase y))

def firstExclusionSet (x : ℝ) : Finset ℕ :=
  smoothSet x (smoothCutoff x) ∪ roughSet x (smoothCutoff x)

/-- Coprimality with the full prime base means every prime factor is larger. -/
theorem coprime_primeBase_iff (n : ℕ) (y : ℝ) :
    n.Coprime (primeBase y) ↔ ∀ p : ℕ, p.Prime → p ∣ n → y < (p:ℝ) := by
  constructor
  · intro hc p hp hpn
    by_contra h
    have hd : p ∣ primeBase y := (prime_dvd_primeBase hp).mpr
      (primesUpTo_mem.mpr ⟨hp,le_of_not_gt h⟩)
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hpn hd)
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpn hpb
    have hle := (primesUpTo_mem.mp ((prime_dvd_primeBase hp).mp hpb)).2
    exact (not_le_of_gt (h p hp hpn)) hle

theorem roughSet_mem {x y : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ roughSet x y ↔ 0 < n ∧ (n:ℝ) ≤ x ∧
      ∀ p : ℕ, p.Prime → p ∣ n → y < (p:ℝ) := by
  rw [roughSet,Finset.mem_filter,intervalSupport_mem (by norm_num) hx,
    coprime_primeBase_iff]
  simp only [Nat.cast_pos, and_assoc]

/-- Exact finite-set correspondence with the two prime-factor classes
removed at the source's first smooth/rough exclusion. -/
theorem firstExclusionSet_mem {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ firstExclusionSet x ↔ 0 < n ∧ (n:ℝ) ≤ x ∧
      ((∀ p : ℕ, p.Prime → p ∣ n → (p:ℝ) ≤ smoothCutoff x) ∨
       (∀ p : ℕ, p.Prime → p ∣ n → smoothCutoff x < (p:ℝ))) := by
  rw [firstExclusionSet,Finset.mem_union,smoothSet_mem,roughSet_mem hx,
    smoothIntegers_mem]
  constructor
  · rintro (⟨hn,hx,_,hp⟩ | ⟨hn,hx,hp⟩)
    · exact ⟨hn,hx,Or.inl hp⟩
    · exact ⟨hn,hx,Or.inr hp⟩
  · rintro ⟨hn,hx,hp|hp⟩
    · exact Or.inl ⟨hn,hx,hn.ne',hp⟩
    · exact Or.inr ⟨hn,hx,hp⟩

theorem eventual_cutoff_fourth_le_sqrt : ∀ᶠ x : ℝ in atTop,
    (smoothCutoff x)^4 ≤ Real.sqrt x := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 8]
    with x hx hu
  dsimp only [Function.comp_apply] at hu
  have hx0 : 0 ≤ x := by linarith
  rw [smoothCutoff, ← Real.rpow_mul_natCast hx0, Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have hl : 0 < Real.log (Real.log x) := by linarith
  have he : (1/Real.log (Real.log x))*4 = 4/Real.log (Real.log x) := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  exact (div_le_iff₀ hl).mpr (by linarith)

theorem eventual_sqrt_le_first_scale : ∀ᶠ x : ℝ in atTop,
    Real.sqrt x ≤ x*Real.log (Real.log x)/Real.log x := by
  have hb := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  filter_upwards [hb, eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with x hlog hx hu
  dsimp only [Function.comp_apply] at hu
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hlog' : Real.log x ≤ Real.sqrt x := by
    simpa only [Real.norm_of_nonneg hl.le, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _),
      one_mul, Real.sqrt_eq_rpow] using hlog
  apply (le_div_iff₀ hl).mpr
  calc
    Real.sqrt x * Real.log x ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hlog' (Real.sqrt_nonneg _)
    _ = x := Real.mul_self_sqrt hx0
    _ ≤ x*Real.log (Real.log x) := by nlinarith

/-- The existing Selberg bound at the literal Korolev cutoff. -/
theorem eventual_rough_count_bound : ∀ᶠ x : ℝ in atTop,
    ((roughSet x (smoothCutoff x)).card:ℝ) ≤
      3*(x*Real.log (Real.log x)/Real.log x) := by
  filter_upwards [eventual_cutoff_fourth_le_sqrt, eventual_sqrt_le_first_scale,
    smoothCutoff_tendsto.eventually_ge_atTop 2, eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with x herr hsqrt hQ hx hu
  dsimp only [Function.comp_apply] at hu
  have h := rough_interval_bound (a := 0) (b := x) (by norm_num) (by linarith) hQ
  change ((roughSet x (smoothCutoff x)).card:ℝ) ≤
    2*(x-0)/Real.log (smoothCutoff x)+(smoothCutoff x)^4 at h
  rw [sub_zero, log_smoothCutoff (by linarith)] at h
  have he : 2*x/(Real.log x/Real.log (Real.log x)) =
      2*(x*Real.log (Real.log x)/Real.log x) := by field_simp
  rw [he] at h
  linarith

/-- Literal union of the two discarded classes, with an absolute constant. -/
theorem eventual_first_exclusion_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ((firstExclusionSet x).card:ℝ) ≤ C*(x*Real.log (Real.log x)/Real.log x) := by
  obtain ⟨C,hC,hsm⟩ := eventual_smoothCount_two_bound
  refine ⟨C+3,by positivity,?_⟩
  filter_upwards [hsm,eventual_rough_count_bound,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with x hsm hr hx hu
  dsimp only [Function.comp_apply] at hu
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hscale : x/(Real.log x*Real.log (Real.log x)) ≤
      x*Real.log (Real.log x)/Real.log x := by
    rw [← div_div]
    calc
      x/Real.log x/Real.log (Real.log x) ≤ x/Real.log x :=
        (div_le_iff₀ (by linarith : 0<Real.log (Real.log x))).mpr
          (by nlinarith [div_nonneg hx0 hl.le])
      _ ≤ x/Real.log x*Real.log (Real.log x) := by nlinarith [div_nonneg hx0 hl.le]
      _ = _ := by ring
  have hs := hsm.trans (mul_le_mul_of_nonneg_left hscale hC.le)
  have hc : ((firstExclusionSet x).card:ℝ) ≤
      smoothCount x (smoothCutoff x)+((roughSet x (smoothCutoff x)).card:ℝ) := by
    unfold firstExclusionSet smoothCount
    exact_mod_cast Finset.card_union_le (smoothSet x (smoothCutoff x))
      (roughSet x (smoothCutoff x))
  nlinarith

/-- The same bound is uniform after restricting to the actual coprime
summation set for any modulus. -/
theorem eventual_coprime_first_exclusion_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ q : ℕ,
      (((firstExclusionSet x).filter (fun n => n.Coprime q)).card:ℝ) ≤
        C*(x*Real.log (Real.log x)/Real.log x) := by
  obtain ⟨C,hC,h⟩ := eventual_first_exclusion_bound
  refine ⟨C,hC,h.mono ?_⟩
  intro x hx q
  exact (show (((firstExclusionSet x).filter (fun n => n.Coprime q)).card:ℝ) ≤
      ((firstExclusionSet x).card:ℝ) by exact_mod_cast Finset.card_filter_le _ _).trans hx

end NField.Alignment.KorolevFirstExclusion
