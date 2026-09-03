/-
Author: Alexander S. Petty
-/

import NField.Alignment.CarryBoundarySpectra
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The first odd Dirichlet special value

This module closes the analytic endpoint needed to identify the finite first
Bernoulli sum of a primitive odd Dirichlet character with its genuine
Mathlib `LFunction` value at one.  The endpoint is proved rather than assumed.
-/

namespace NField.Alignment.SawtoothLValue

open scoped BigOperators ComplexConjugate Topology ZMod
open Filter Finset
open NField.Alignment.CarryBoundarySpectra
open NField.Alignment.CollisionCharacterStructure

/-! ## A quantitative Dirichlet tail bound -/

private theorem norm_sum_range_smul_le
    {f : ℕ → ℝ} {z : ℕ → ℂ} {C : ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hfanti : Antitone f)
    (hC : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ C) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, f i • z i‖ ≤ C * f 0 := by
  rw [Finset.sum_range_by_parts]
  calc
    ‖f (n - 1) • ∑ i ∈ Finset.range n, z i -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖
        ≤ ‖f (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
            ‖∑ i ∈ Finset.range (n - 1),
              (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖ :=
          norm_sub_le _ _
    _ ≤ f (n - 1) * C +
          ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * C := by
      gcongr
      · rw [norm_smul, Real.norm_of_nonneg (hf0 _)]
        exact mul_le_mul_of_nonneg_left (hC n) (hf0 _)
      · calc
          ‖∑ i ∈ Finset.range (n - 1),
              (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖
              ≤ ∑ i ∈ Finset.range (n - 1),
                  ‖(f (i + 1) - f i) •
                    ∑ j ∈ Finset.range (i + 1), z j‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * C := by
            gcongr with i hi
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr (hfanti (Nat.le_succ i))),
              neg_sub]
            exact mul_le_mul_of_nonneg_left (hC (i + 1))
              (sub_nonneg.mpr (hfanti (Nat.le_succ i)))
    _ = C * f 0 := by
      rw [← Finset.sum_mul]
      rw [show (∑ i ∈ Finset.range (n - 1), (f i - f (i + 1))) =
          -(∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i)) by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring]
      rw [Finset.sum_range_sub, mul_comm (f (n - 1)) C]
      ring

/-! ## The conditionally convergent first sine series -/

private theorem norm_geometric_partial_sum_le
    {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z ^ (k + 1)‖ ≤ 2 / ‖z - 1‖ := by
  rw [show (∑ k ∈ Finset.range n, z ^ (k + 1)) =
      z * ∑ k ∈ Finset.range n, z ^ k by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ']]
  rw [geom_sum_eq hz]
  rw [norm_mul, norm_div]
  have hsub : ‖z ^ n - 1‖ ≤ ‖z‖ ^ n + 1 := by
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ ^ n + 1 := by rw [norm_pow, norm_one]
  rw [hzNorm, one_pow] at hsub
  norm_num at hsub
  rw [hzNorm, one_mul]
  exact div_le_div_of_nonneg_right hsub (norm_nonneg _)

private theorem norm_harmonic_geometric_tail_le
    {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n,
        z ^ (m + i + 1) / ((m + i + 1 : ℕ) : ℂ) ^ (σ : ℂ)‖ ≤
      (2 / ‖z - 1‖) / (m + 1 : ℝ) := by
  let f : ℕ → ℝ := fun i => (m + i + 1 : ℝ) ^ (-σ)
  let w : ℕ → ℂ := fun i => z ^ (m + i + 1)
  have hf0 : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (by positivity) _
  have hfanti : Antitone f := by
    intro i j hij
    have hij' : m + i + 1 ≤ m + j + 1 := by omega
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast hij') (neg_nonpos.mpr (zero_le_one.trans hσ))
  have hw (r : ℕ) : ‖∑ i ∈ Finset.range r, w i‖ ≤ 2 / ‖z - 1‖ := by
    change ‖∑ i ∈ Finset.range r, z ^ (m + i + 1)‖ ≤ _
    rw [show (∑ i ∈ Finset.range r, z ^ (m + i + 1)) =
        z ^ m * ∑ i ∈ Finset.range r, z ^ (i + 1) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show m + i + 1 = m + (i + 1) by omega, pow_add]]
    rw [norm_mul, norm_pow, hzNorm, one_pow, one_mul]
    exact norm_geometric_partial_sum_le hzNorm hz r
  have hbound := norm_sum_range_smul_le hf0 hfanti hw n
  have hterms :
      (∑ i ∈ Finset.range n, f i • w i) =
        ∑ i ∈ Finset.range n,
          z ^ (m + i + 1) /
            ((m + i + 1 : ℕ) : ℂ) ^ (σ : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    change (((m + i + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) *
      z ^ (m + i + 1) = _
    rw [show (((m + i + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) =
        ((m + i + 1 : ℝ) : ℂ) ^ ((-σ : ℝ) : ℂ) by
          exact Complex.ofReal_cpow (by positivity) (-σ)]
    rw [show ((-σ : ℝ) : ℂ) = -((σ : ℝ) : ℂ) by norm_num]
    rw [Complex.cpow_neg]
    have hcast : (((m + i + 1 : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ)) =
        (((m + i + 1 : ℕ) : ℂ) ^ ((σ : ℝ) : ℂ)) := by
      congr 1
      norm_num
    rw [div_eq_mul_inv]
    rw [hcast]
    ring
  rw [hterms] at hbound
  refine hbound.trans ?_
  have hC : 0 ≤ 2 / ‖z - 1‖ := div_nonneg (by positivity) (norm_nonneg _)
  have hbase : (1 : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hpow : (m + 1 : ℝ) ^ (-σ) ≤ (m + 1 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (neg_le_neg hσ)
  have hminusOne : (m + 1 : ℝ) ^ (-1 : ℝ) = (m + 1 : ℝ)⁻¹ := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num,
      Real.rpow_neg (by positivity), Real.rpow_one]
  rw [hminusOne] at hpow
  calc
    (2 / ‖z - 1‖) * f 0 =
        (2 / ‖z - 1‖) * (m + 1 : ℝ) ^ (-σ) := by simp [f]
    _ ≤ (2 / ‖z - 1‖) * (m + 1 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = (2 / ‖z - 1‖) / (m + 1 : ℝ) := by
      simp only [div_eq_mul_inv]

private theorem first_harmonic_geometric_cauchy
    {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1) :
    CauchySeq fun n =>
      ∑ k ∈ Finset.range n, (1 / ((k + 1 : ℕ) : ℝ)) • z ^ (k + 1) := by
  apply Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
  · intro a b hab
    simp only [one_div]
    gcongr
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n
    exact norm_geometric_partial_sum_le hzNorm hz n

private theorem harmonic_geometric_powerSeries
    {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun k : ℕ => u ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      (-Complex.log (1 - u)) := by
  have hlog := (Complex.hasSum_taylorSeries_log (z := -u) (by simpa using hu)).neg
  have hshift := (hasSum_nat_add_iff (f := fun n : ℕ =>
    -((-1 : ℂ) ^ (n + 1) * (-u) ^ n / (n : ℂ))) 1).2 (by
      simpa using hlog)
  have hterms (n : ℕ) :
      -((-1 : ℂ) ^ (n + 1 + 1) * (-u) ^ (n + 1) /
          ((n + 1 : ℕ) : ℂ)) =
        u ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
    rw [neg_pow]
    ring_nf
    rw [show n * 2 = 2 * n by omega, pow_mul]
    norm_num
  have hresult := hshift.congr_fun fun n => (hterms n).symm
  simpa only [sub_eq_add_neg] using hresult

private theorem one_sub_mem_slitPlane
    {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  change 0 < 1 - z.re
  have hrele : z.re ≤ 1 := by
    calc
      z.re ≤ ‖z‖ := Complex.re_le_norm z
      _ = 1 := hzNorm
  have hrene : z.re ≠ 1 := by
    intro hre
    have hsq := Complex.sq_norm z
    rw [hzNorm, Complex.normSq_apply, hre] at hsq
    have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
    apply hz
    apply Complex.ext
    · simpa using hre
    · simpa using him
  have hrelt : z.re < 1 := lt_of_le_of_ne hrele hrene
  linarith

/-- The ordered harmonic geometric series has its principal-log endpoint.
This is the Abel-limit statement needed at the conditionally convergent
boundary; it deliberately uses ordered partial sums rather than `tsum`. -/
theorem tendsto_harmonic_geometric
    {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1) :
    Tendsto (fun n =>
      ∑ k ∈ Finset.range n,
        z ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) atTop
      (𝓝 (-Complex.log (1 - z))) := by
  have hc := first_harmonic_geometric_cauchy hzNorm hz
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hL' : Tendsto (fun n =>
      ∑ k ∈ Finset.range n,
        z ^ (k + 1) / ((k + 1 : ℕ) : ℂ)) atTop (𝓝 L) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using hL
  have hAbel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL'
  let F : ℂ → ℂ := fun w =>
    ∑' n : ℕ, (z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * w ^ n
  let G : ℂ → ℂ := fun w => -Complex.log (1 - z * w) / w
  have hFG : F =ᶠ[((𝓝[<] (1 : ℝ)).map Complex.ofReal)] G := by
    change ∀ᶠ w in ((𝓝[<] (1 : ℝ)).map Complex.ofReal), F w = G w
    rw [Filter.eventually_map]
    have hlt : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 :=
      self_mem_nhdsWithin
    have hpos : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
      (eventually_gt_nhds zero_lt_one).filter_mono inf_le_left
    filter_upwards [hlt, hpos] with r hrlt hrpos
    have hur : ‖z * (r : ℂ)‖ < 1 := by
      rw [norm_mul, hzNorm, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hrpos]
      exact hrlt
    have hseries := harmonic_geometric_powerSeries hur
    unfold F G
    rw [← hseries.tsum_eq]
    rw [div_eq_mul_inv]
    calc
      (∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * (r : ℂ) ^ n) =
          ∑' n : ℕ, ((z * (r : ℂ)) ^ (n + 1) /
            ((n + 1 : ℕ) : ℂ)) * (r : ℂ)⁻¹ := by
              apply tsum_congr
              intro n
              push_cast
              field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hrpos.ne']
              ring
      _ = (∑' n : ℕ, (z * (r : ℂ)) ^ (n + 1) /
            ((n + 1 : ℕ) : ℂ)) * (r : ℂ)⁻¹ := by
              rw [tsum_mul_right]
  have hG : Tendsto G (((𝓝[<] (1 : ℝ)).map Complex.ofReal))
      (𝓝 (-Complex.log (1 - z))) := by
    rw [Filter.tendsto_map'_iff]
    have hinner : ContinuousAt (fun w : ℂ => 1 - z * w) 1 := by fun_prop
    have hmem : 1 - z * (1 : ℂ) ∈ Complex.slitPlane := by
      simpa using one_sub_mem_slitPlane hzNorm hz
    have hlog : ContinuousAt (fun w : ℂ => Complex.log (1 - z * w)) 1 :=
      hinner.clog hmem
    have hquot : ContinuousAt (fun w : ℂ => -Complex.log (1 - z * w) / w) 1 := by
      exact hlog.neg.div continuousAt_id one_ne_zero
    have hofReal : Tendsto Complex.ofReal (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left inf_le_left
    simpa [G] using hquot.tendsto.comp hofReal
  have hAbelF : Tendsto F (((𝓝[<] (1 : ℝ)).map Complex.ofReal)) (𝓝 L) := by
    simpa [F] using hAbel
  have hAbelG : Tendsto G (((𝓝[<] (1 : ℝ)).map Complex.ofReal)) (𝓝 L) :=
    hAbelF.congr' hFG
  have hnebot : NeBot (((𝓝[<] (1 : ℝ)).map Complex.ofReal)) := by infer_instance
  have hEq : L = -Complex.log (1 - z) := tendsto_nhds_unique hAbelG hG
  simpa [hEq] using hL'

/-! ## Identification with the continued exponential zeta value -/

/-- At a nonzero rational point of the additive circle, Mathlib's analytically
continued exponential zeta value at one is the ordered principal-log
endpoint. -/
theorem expZeta_one_eq_neg_log
    {N : ℕ} [NeZero N] (j : ZMod N) (hj : j ≠ 0) :
    HurwitzZeta.expZeta (ZMod.toAddCircle j) 1 =
      -Complex.log (1 - ZMod.stdAddChar j) := by
  let a : ℝ := j.val / N
  let z : ℂ := ZMod.stdAddChar j
  have hzNorm : ‖z‖ = 1 := by
    dsimp [z]
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hz : z ≠ 1 := by
    intro h
    apply hj
    apply ZMod.injective_stdAddChar
    simpa [z] using h
  have hza : z = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
    dsimp [z, a]
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
    push_cast
    congr 1
    ring
  let P : ℝ → ℕ → ℂ := fun σ n =>
    ∑ k ∈ Finset.range n,
      z ^ (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ)
  let L : ℂ := -Complex.log (1 - z)
  have hPone : Tendsto (P 1) atTop (𝓝 L) := by
    simpa [P, L] using tendsto_harmonic_geometric hzNorm hz
  have hseries {σ : ℝ} (hσ : 1 < σ) :
      HasSum (fun k : ℕ =>
        z ^ (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ))
        (HurwitzZeta.expZeta (ZMod.toAddCircle j) (σ : ℂ)) := by
    have hraw := HurwitzZeta.hasSum_expZeta_of_one_lt_re a
      (s := (σ : ℂ)) (by simpa using hσ)
    have hpoint : (a : UnitAddCircle) = ZMod.toAddCircle j := by
      rw [ZMod.toAddCircle_apply]
    have hσ0 : (σ : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (zero_lt_one.trans hσ))
    have hshift := (hasSum_nat_add_iff (f := fun n : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ)) /
        (n : ℂ) ^ (σ : ℂ)) 1).2 (by
          simpa [hpoint, hσ0] using hraw)
    refine hshift.congr_fun fun k => ?_
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((k + 1 : ℕ) : ℂ) =
        ((k + 1 : ℕ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) by ring,
      Complex.exp_nat_mul, ← hza]
  have htail {σ : ℝ} (hσ : 1 < σ) (m : ℕ) :
      ‖HurwitzZeta.expZeta (ZMod.toAddCircle j) (σ : ℂ) - P σ m‖ ≤
        (2 / ‖z - 1‖) / (m + 1 : ℝ) := by
    let t : ℕ → ℂ := fun k =>
      z ^ (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ)
    have hs : HasSum t (HurwitzZeta.expZeta
        (ZMod.toAddCircle j) (σ : ℂ)) := by
      simpa [t] using hseries hσ
    have htailSum : HasSum (fun k => t (k + m))
        (HurwitzZeta.expZeta (ZMod.toAddCircle j) (σ : ℂ) - P σ m) := by
      have hPm : P σ m = ∑ i ∈ Finset.range m, t i := by rfl
      rw [hPm]
      apply (hasSum_nat_add_iff m).2
      simpa only [sub_add_cancel] using hs
    have htend := htailSum.tendsto_sum_nat.norm
    apply le_of_tendsto htend
    exact Eventually.of_forall fun n => by
      simpa [t, add_assoc, add_comm, add_left_comm, P] using
        norm_harmonic_geometric_tail_le hzNorm hz hσ.le m n
  have hcontinued : Tendsto
      (fun σ : ℝ => HurwitzZeta.expZeta
        (ZMod.toAddCircle j) (σ : ℂ)) (𝓝[>] 1) (𝓝 L) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hthird : 0 < ε / 3 := by positivity
    have htailZero : Tendsto (fun m : ℕ =>
        (2 / ‖z - 1‖) / (m + 1 : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_assoc] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
          (2 / ‖z - 1‖)
    have hsmallTail : ∀ᶠ m : ℕ in atTop,
        (2 / ‖z - 1‖) / (m + 1 : ℝ) < ε / 3 :=
      (Metric.tendsto_nhds.1 htailZero (ε / 3) hthird) |>.mono fun m hm => by
        have hnonneg : 0 ≤ (2 / ‖z - 1‖) / (m + 1 : ℝ) :=
          div_nonneg (div_nonneg (by positivity) (norm_nonneg _)) (by positivity)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hm
        exact hm
    have hsmallBoundary : ∀ᶠ m : ℕ in atTop,
        dist (P 1 m) L < ε / 3 :=
      (Metric.tendsto_nhds.1 hPone (ε / 3) hthird)
    obtain ⟨m, hmTail, hmBoundary⟩ :=
      (hsmallTail.and hsmallBoundary).exists
    have hhead : Tendsto (fun σ : ℝ => P σ m) (𝓝[>] 1) (𝓝 (P 1 m)) := by
      apply tendsto_finsetSum
      intro k hk
      have hcont : ContinuousAt (fun σ : ℝ =>
          z ^ (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ)) 1 := by
        have hpow : ContinuousAt (fun σ : ℝ =>
            ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ)) 1 :=
          (continuousAt_const_cpow (by exact_mod_cast Nat.succ_ne_zero k)).comp
            Complex.continuous_ofReal.continuousAt
        exact continuousAt_const.div hpow
          (by
            norm_num [Complex.cpow_one]
            exact Nat.cast_add_one_ne_zero k)
      exact hcont.tendsto.mono_left inf_le_left
    have hheadSmall : ∀ᶠ σ : ℝ in 𝓝[>] 1,
        dist (P σ m) (P 1 m) < ε / 3 :=
      (Metric.tendsto_nhds.1 hhead (ε / 3) hthird)
    filter_upwards [self_mem_nhdsWithin, hheadSmall] with σ hσ hσhead
    rw [Set.mem_Ioi] at hσ
    calc
      dist (HurwitzZeta.expZeta (ZMod.toAddCircle j) (σ : ℂ)) L
          ≤ dist (HurwitzZeta.expZeta (ZMod.toAddCircle j) (σ : ℂ)) (P σ m) +
              dist (P σ m) (P 1 m) + dist (P 1 m) L := by
            exact dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
        have hfirst :
            dist (HurwitzZeta.expZeta (ZMod.toAddCircle j) (σ : ℂ)) (P σ m) <
              ε / 3 :=
          lt_of_le_of_lt (by simpa [dist_eq_norm] using htail hσ m) hmTail
        exact add_lt_add (add_lt_add hfirst hσhead) hmBoundary
      _ = ε := by ring
  have hanalytic : Tendsto
      (fun σ : ℝ => HurwitzZeta.expZeta
        (ZMod.toAddCircle j) (σ : ℂ)) (𝓝[>] 1)
      (𝓝 (HurwitzZeta.expZeta (ZMod.toAddCircle j) 1)) := by
    have hdiff := HurwitzZeta.differentiableAt_expZeta
      (ZMod.toAddCircle j) 1 (Or.inr (ZMod.toAddCircle_eq_zero.not.mpr hj))
    exact hdiff.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.tendsto 1).mono_left inf_le_left)
  have hEq := tendsto_nhds_unique hanalytic hcontinued
  simpa [L, z] using hEq

private theorem one_sub_exp_two_pi_mul_I_factor (a : ℝ) :
    (1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) =
      ((2 * Real.sin (Real.pi * a) : ℝ) : ℂ) *
        (((Real.cos (Real.pi * a - Real.pi / 2) : ℝ) : ℂ) +
          ((Real.sin (Real.pi * a - Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
  let x : ℝ := 2 * Real.pi * a
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) =
      ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) =
        (x : ℂ) * Complex.I by
          dsimp [x]
          push_cast
          ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    dsimp [x]
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two,
      show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * a)]
  · simp only [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, add_zero, mul_one, zero_sub]
    dsimp [x]
    rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two,
      show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
      Real.sin_two_mul]
    ring

/-- Principal argument of the first additive-character boundary. -/
theorem arg_one_sub_stdAddChar
    {N : ℕ} [NeZero N] (j : ZMod N) (hj : j ≠ 0) :
    Complex.arg (1 - ZMod.stdAddChar j) =
      Real.pi * ((j.val : ℝ) / N - 1 / 2) := by
  let a : ℝ := j.val / N
  have hjval : 0 < j.val := ZMod.val_pos.mpr hj
  have hN : 0 < N := NeZero.pos N
  have ha0 : 0 < a := div_pos (Nat.cast_pos.mpr hjval) (Nat.cast_pos.mpr hN)
  have ha1 : a < 1 := (div_lt_one (Nat.cast_pos.mpr hN)).2 <|
    Nat.cast_lt.mpr j.val_lt
  have hapi0 : 0 < Real.pi * a := mul_pos Real.pi_pos ha0
  have hapilt : Real.pi * a < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * a) :=
    Real.sin_pos_of_pos_of_lt_pi hapi0 hapilt
  have hangle : Real.pi * a - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hchar : ZMod.stdAddChar j =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
    dsimp [a]
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
    push_cast
    congr 1
    ring
  rw [hchar, one_sub_exp_two_pi_mul_I_factor a]
  convert Complex.arg_mul_cos_add_sin_mul_I (mul_pos two_pos hsin) hangle using 1
  all_goals simp [a]
  all_goals ring

/-- The omitted first sine value, now proved at every nonzero rational point
needed by the character calculation. -/
theorem sinZeta_one_eq_neg_pi_mul_centeredSawtooth
    {N : ℕ} [NeZero N] (j : ZMod N) (hj : j ≠ 0) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle j) 1 =
      -(Real.pi : ℂ) * centeredSawtooth j := by
  have hneg : -j ≠ 0 := neg_ne_zero.mpr hj
  have hzNorm : ‖ZMod.stdAddChar j‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hInv : (ZMod.stdAddChar j)⁻¹ =
      starRingEnd ℂ (ZMod.stdAddChar j) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hzNorm, one_pow]
    norm_num
  have hnegChar : ZMod.stdAddChar (-j) =
      starRingEnd ℂ (ZMod.stdAddChar j) := by
    rw [AddChar.map_neg_eq_inv, hInv]
  have hargNe : Complex.arg (1 - ZMod.stdAddChar j) ≠ Real.pi := by
    rw [arg_one_sub_stdAddChar j hj]
    have hval : (j.val : ℝ) / N < 1 :=
      (div_lt_one (Nat.cast_pos.mpr (NeZero.pos N))).2 (Nat.cast_lt.mpr j.val_lt)
    nlinarith [Real.pi_pos]
  have hconjBoundary :
      1 - ZMod.stdAddChar (-j) =
        starRingEnd ℂ (1 - ZMod.stdAddChar j) := by
    rw [hnegChar, map_sub, map_one]
  have hconjValue :
      HurwitzZeta.expZeta (ZMod.toAddCircle (-j)) 1 =
        starRingEnd ℂ (HurwitzZeta.expZeta (ZMod.toAddCircle j) 1) := by
    rw [expZeta_one_eq_neg_log (-j) hneg,
      expZeta_one_eq_neg_log j hj, hconjBoundary,
      Complex.log_conj _ hargNe, map_neg]
  rw [HurwitzZeta.sinZeta_eq]
  rw [show -ZMod.toAddCircle j = ZMod.toAddCircle (-j) by
    exact (map_neg (ZMod.toAddCircle (N := N)) j).symm]
  rw [hconjValue]
  have him :
      (HurwitzZeta.expZeta (ZMod.toAddCircle j) 1 -
          starRingEnd ℂ (HurwitzZeta.expZeta (ZMod.toAddCircle j) 1)) /
            (2 * Complex.I) =
        ((HurwitzZeta.expZeta (ZMod.toAddCircle j) 1).im : ℂ) := by
    let E := HurwitzZeta.expZeta (ZMod.toAddCircle j) 1
    have hdiff : E - starRingEnd ℂ E = 2 * (E.im : ℂ) * Complex.I := by
      apply Complex.ext
      all_goals simp
      all_goals ring
    change (E - starRingEnd ℂ E) / (2 * Complex.I) = (E.im : ℂ)
    rw [hdiff]
    field_simp [Complex.I_ne_zero]
  rw [him, expZeta_one_eq_neg_log j hj]
  have hcenter : centeredSawtooth j =
      (j.val : ℂ) / (N : ℂ) - 1 / 2 := by
    simp [centeredSawtooth, hj]
  rw [hcenter]
  calc
    ((-Complex.log (1 - ZMod.stdAddChar j)).im : ℂ) =
        ((-(Real.pi * ((j.val : ℝ) / N - 1 / 2)) : ℝ) : ℂ) := by
          rw [Complex.neg_im, Complex.log_im, arg_one_sub_stdAddChar j hj]
    _ = -(Real.pi : ℂ) * ((j.val : ℂ) / (N : ℂ) - 1 / 2) := by
          push_cast
          ring

/-! ## Primitive odd Gauss and `L(1)` identities -/

/-- A primitive odd Dirichlet character modulo an arbitrary nontrivial level
has the exact classical Gauss mass.  This is proved from the finite DFT
involution, so no field assumption on `ZMod N` is used. -/
theorem primitiveOdd_gaussSum_normSq
    {N : ℕ} [NeZero N] (_hN : 2 ≤ N) {χ : Character N}
    (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by
  let τ : ℂ := gaussSum χ ZMod.stdAddChar
  let τinv : ℂ := gaussSum χ⁻¹ ZMod.stdAddChar
  have hχinv : (χ⁻¹).IsPrimitive := inverse_isPrimitive hχ
  have hoddInv : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have hdft : ZMod.dft (χ : ZMod N → ℂ) =
      fun k => χ⁻¹ (-k) * τ := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hdftInv : ZMod.dft ((χ⁻¹ : Character N) : ZMod N → ℂ) =
      fun k => χ (-k) * τinv := by
    funext k
    simpa [τinv] using hχinv.fourierTransform_eq_inv_mul_gaussSum k
  have hdouble := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (1 : ZMod N)
  rw [hdft, ZMod.dft_mul_const] at hdouble
  have hnegDft : ZMod.dft (fun j : ZMod N => χ⁻¹ (-j)) (1 : ZMod N) = τinv := by
    rw [ZMod.dft_comp_neg]
    change ZMod.dft ((χ⁻¹ : Character N) : ZMod N → ℂ) (-1) = τinv
    rw [hdftInv]
    simp [τinv]
  change (ZMod.dft (fun j : ZMod N => χ⁻¹ (-j)) 1) * τ =
    (N : ℂ) * χ (-1) at hdouble
  rw [hnegDft, hodd] at hdouble
  have hprod : τ * τinv = -(N : ℂ) := by
    calc
      τ * τinv = τinv * τ := mul_comm _ _
      _ = (N : ℂ) * (-1) := hdouble
      _ = -(N : ℂ) := by ring
  have hstar : starRingEnd ℂ τ = -τinv := by
    have hshift := gaussSum_mulShift χ⁻¹ ZMod.stdAddChar (-1 : (ZMod N)ˣ)
    have hunitVal : ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := by rfl
    rw [hunitVal] at hshift
    have hnegOne : χ⁻¹ ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := by
      rw [hunitVal]
      exact hoddInv
    rw [hoddInv] at hshift
    have hinvShift :
        ZMod.stdAddChar.mulShift (-1 : ZMod N) = ZMod.stdAddChar⁻¹ := by
      exact AddChar.inv_mulShift ZMod.stdAddChar |>.symm
    rw [hinvShift] at hshift
    have hstarRaw := star_gaussSum_eq χ ZMod.stdAddChar
    have hshift' : -(gaussSum χ⁻¹ ZMod.stdAddChar⁻¹) = τinv := by
      simpa only [neg_one_mul, τinv] using hshift
    calc
      starRingEnd ℂ τ = gaussSum χ⁻¹ ZMod.stdAddChar⁻¹ := by
        simpa [τ] using hstarRaw
      _ = -(-(gaussSum χ⁻¹ ZMod.stdAddChar⁻¹)) := by ring
      _ = -τinv := congrArg Neg.neg hshift'
  have hnormComplex : τ * starRingEnd ℂ τ = (N : ℂ) := by
    rw [hstar]
    calc
      τ * -τinv = -(τ * τinv) := by ring
      _ = -(-(N : ℂ)) := congrArg Neg.neg hprod
      _ = (N : ℂ) := by ring
  rw [Complex.mul_conj] at hnormComplex
  exact_mod_cast hnormComplex

private theorem LFunction_const_mul
    {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun x => c * Φ x) s = c * ZMod.LFunction Φ s := by
  unfold ZMod.LFunction
  have hsum :
      (∑ j : ZMod N,
          (c * Φ j) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s) =
        c * ∑ j : ZMod N,
          Φ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

/-- Exact phase-sensitive first special-value formula for primitive odd
characters.  The `LFunction` here is Mathlib's analytically continued
Dirichlet L-function. -/
theorem primitiveOdd_LFunction_bernoulliOne
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : Character N}
    (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    -(gaussSum χ ZMod.stdAddChar) *
        DirichletCharacter.LFunction χ⁻¹ 1 =
      (Real.pi : ℂ) * Complex.I * bernoulliOne χ := by
  let E : ZMod N → ℂ := fun j =>
    HurwitzZeta.expZeta (ZMod.toAddCircle j) 1
  let A : ℂ := ∑ j : ZMod N, χ j * E (-j)
  have hχ0 : χ (0 : ZMod N) = 0 := χ.map_zero' (by omega)
  have hχne : χ ≠ 1 := primitive_ne_one hN hχ
  have hAfromDFT :
      ZMod.LFunction (ZMod.dft (χ : ZMod N → ℂ)) 1 = A := by
    simpa [A, E] using ZMod.LFunction_dft (χ : ZMod N → ℂ)
      (s := (1 : ℂ)) (Or.inl hχ0)
  have hoddInv : (χ⁻¹).Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]
    norm_num
  have hdft : ZMod.dft (χ : ZMod N → ℂ) =
      fun k => -(gaussSum χ ZMod.stdAddChar) * χ⁻¹ k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
    rw [hoddInv.eval_neg]
    ring
  have hLHS :
      ZMod.LFunction (ZMod.dft (χ : ZMod N → ℂ)) 1 =
        -(gaussSum χ ZMod.stdAddChar) *
          DirichletCharacter.LFunction χ⁻¹ 1 := by
    rw [hdft, LFunction_const_mul]
    rfl
  have hAreflect : A = -∑ j : ZMod N, χ j * E j := by
    calc
      A = ∑ j : ZMod N, χ (-j) * E j := by
        unfold A
        exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun j => by
          rw [Equiv.neg_apply, neg_neg]
      _ = -∑ j : ZMod N, χ j * E j := by
        simp_rw [hodd.eval_neg, neg_mul, Finset.sum_neg_distrib]
  let B : ℂ := ∑ j : ZMod N, χ j * E j
  have hAreflect' : A = -B := by simpa [B] using hAreflect
  have hAasSine :
      A = -Complex.I * ∑ j : ZMod N,
        χ j * HurwitzZeta.sinZeta (ZMod.toAddCircle j) 1 := by
    calc
      A = (A - B) / 2 := by rw [hAreflect']; ring
      _ = (A - ∑ j : ZMod N, χ j * E j) / 2 := by rfl
      _ = (∑ j : ZMod N, χ j * (E (-j) - E j)) / 2 := by
        unfold A
        rw [← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -Complex.I * ∑ j : ZMod N,
          χ j * HurwitzZeta.sinZeta (ZMod.toAddCircle j) 1 := by
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        rw [HurwitzZeta.sinZeta_eq]
        rw [show -ZMod.toAddCircle j = ZMod.toAddCircle (-j) by
          exact (map_neg (ZMod.toAddCircle (N := N)) j).symm]
        field_simp [Complex.I_ne_zero]
        ring
  have hSawtooth :
      (∑ j : ZMod N, χ j * centeredSawtooth j) = bernoulliOne χ := by
    have h := centeredSawtooth_transform_eq_bernoulliOne (by omega) hχne
    simpa [twistedTransform, mul_comm] using h
  have hAvalue : A = (Real.pi : ℂ) * Complex.I * bernoulliOne χ := by
    rw [hAasSine]
    have hterm (j : ZMod N) :
        χ j * HurwitzZeta.sinZeta (ZMod.toAddCircle j) 1 =
          χ j * (-(Real.pi : ℂ) * centeredSawtooth j) := by
      by_cases hj : j = 0
      · subst j
        simp [hχ0]
      · rw [sinZeta_one_eq_neg_pi_mul_centeredSawtooth j hj]
    simp_rw [hterm]
    have hsum :
        (∑ j : ZMod N, χ j * (-(Real.pi : ℂ) * centeredSawtooth j)) =
          -(Real.pi : ℂ) * bernoulliOne χ := by
      calc
        _ = -(Real.pi : ℂ) *
            ∑ j : ZMod N, χ j * centeredSawtooth j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = -(Real.pi : ℂ) * bernoulliOne χ := by rw [hSawtooth]
    rw [hsum]
    ring
  rw [← hLHS, hAfromDFT, hAvalue]

/-- Squared-magnitude form used in the manuscript. -/
theorem bernoulliOne_normSq_eq_LFunction
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : Character N}
    (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    Complex.normSq (bernoulliOne χ) =
      (N : ℝ) / Real.pi ^ 2 *
        Complex.normSq (DirichletCharacter.LFunction χ⁻¹ 1) := by
  have hphase := primitiveOdd_LFunction_bernoulliOne hN hχ hodd
  have hnorm := congrArg Complex.normSq hphase
  rw [Complex.normSq_mul, Complex.normSq_neg,
    primitiveOdd_gaussSum_normSq hN hχ hodd,
    Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_I, mul_one] at hnorm
  have hpi2 : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  rw [div_mul_eq_mul_div, eq_div_iff hpi2]
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hnorm.symm

end NField.Alignment.SawtoothLValue
