/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPositiveConstants
import NField.Alignment.CollisionAmplitudeConstantsEnclosure
import NField.Alignment.CollisionFourierEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionDirichletRationalEnclosure
open scoped BigOperators
open Set CollisionDivisorSeries CollisionPositiveConstants
open CollisionAmplitudeConstantsEnclosure CollisionFourierEnclosure
open CollisionMobiusDeficit

def zetaPrefix (s : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N+1), zetaKernel s n

theorem zeta_tail_bound {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, zetaKernel s (n+N+1)) ≤ (N : ℝ)^(1-s)/(s-1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : AntitoneOn (fun x : ℝ => x^(-s)) (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNR.trans_le hx) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hNR
  have ht := ha.tsum_comp_add_le_integral N hi (fun x hx =>
    Real.rpow_nonneg (hNR.le.trans hx.le) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hNR] at ht
  have he : -(N : ℝ)^(-s+1)/(-s+1)=(N : ℝ)^(1-s)/(s-1) := by
    rw [show -s+1=1-s by ring]
    field_simp [show 1-s ≠ 0 by linarith, show s-1 ≠ 0 by linarith]
    ring
  rw [he] at ht
  convert! ht using 1

theorem zeta_prefix_enclosure {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    zetaPrefix s N ≤ realZeta s ∧ realZeta s ≤ zetaPrefix s N+(N : ℝ)^(1-s)/(s-1) := by
  have hs' := zetaKernel_summable hs
  have he := hs'.sum_add_tsum_nat_add (N+1)
  change zetaPrefix s N+(∑' n,zetaKernel s (n+(N+1)))=realZeta s at he
  simp only [← Nat.add_assoc] at he
  have ht := zeta_tail_bound hs hN
  have hn : 0 ≤ ∑' n : ℕ,zetaKernel s (n+N+1) := tsum_nonneg (fun n => zetaKernel_nonneg s _)
  constructor <;> linarith

theorem sqrt_enclosure {x l u : ℝ} (hx : 0 ≤ x) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hls : l^2 ≤ x) (hus : x ≤ u^2) : l ≤ Real.sqrt x ∧ Real.sqrt x ≤ u := by
  constructor
  · apply (sq_le_sq₀ hl (Real.sqrt_nonneg x)).mp
    rwa [Real.sq_sqrt hx]
  · apply (sq_le_sq₀ (Real.sqrt_nonneg x) hu).mp
    rwa [Real.sq_sqrt hx]

theorem half_integer_power {x : ℝ} (hx : 0 < x) (m : ℕ) :
    x^(-((m : ℝ)+1/2))=1/(x^m*Real.sqrt x) := by
  rw [Real.rpow_neg hx.le,Real.rpow_add hx,Real.rpow_natCast,← Real.sqrt_eq_rpow,one_div]

def positivePrefix (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, f (n+1)

theorem zetaPrefix_positivePrefix (s : ℝ) (N : ℕ) :
    zetaPrefix s N=positivePrefix (zetaKernel s) N := by
  simpa [zetaPrefix,positivePrefix] using Finset.sum_range_succ' (zetaKernel s) N

theorem zeta_computed_enclosure {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N)
    {lower upper : ℕ → ℝ} {tail : ℝ}
    (hp : ∀ n ∈ Finset.range N,
      lower (n+1) ≤ (n+1 : ℝ)^(-s) ∧ (n+1 : ℝ)^(-s) ≤ upper (n+1))
    (ht : (N : ℝ)^(-(s-1))/(s-1) ≤ tail) :
    positivePrefix lower N ≤ realZeta s ∧
      realZeta s ≤ positivePrefix upper N+tail := by
  have hb := zeta_prefix_enclosure hs hN
  rw [zetaPrefix_positivePrefix] at hb
  have hlo : positivePrefix lower N ≤ positivePrefix (zetaKernel s) N := by
    apply Finset.sum_le_sum
    intro n hn
    simpa only [zetaKernel_rpow (by linarith : s ≠ 0),Nat.cast_add,Nat.cast_one] using (hp n hn).1
  have hhi : positivePrefix (zetaKernel s) N ≤ positivePrefix upper N := by
    apply Finset.sum_le_sum
    intro n hn
    simpa only [zetaKernel_rpow (by linarith : s ≠ 0),Nat.cast_add,Nat.cast_one] using (hp n hn).2
  have he : -(s-1)=1-s := by ring
  rw [he] at ht
  constructor <;> linarith

def deficitPrefix (s : ℝ) (N : ℕ) : ℝ :=
  positivePrefix (fun n => divisorDeficit n*zetaKernel s n) N

theorem deficit_prefix_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    deficitPrefix s N ≤ deficitSeries s := by
  have h := (deficitSeries_summable hs).sum_le_tsum (Finset.range (N+1))
    (fun n _ => mul_nonneg (divisorDeficit_nonneg n) (zetaKernel_nonneg s n))
  rw [Finset.sum_range_succ'] at h
  simpa [deficitPrefix,positivePrefix,deficitSeries] using h

theorem deficit_prefix_enclosure {s : ℝ} (hs : 1 < s) {N : ℕ}
    {lower upper : ℕ → ℝ}
    (hp : ∀ n ∈ Finset.range N,
      lower (n+1) ≤ (n+1 : ℝ)^(-s) ∧ (n+1 : ℝ)^(-s) ≤ upper (n+1)) :
    positivePrefix (fun n => divisorDeficit n*lower n) N ≤ deficitPrefix s N ∧
      deficitPrefix s N ≤ positivePrefix (fun n => divisorDeficit n*upper n) N := by
  unfold deficitPrefix positivePrefix
  constructor
  · apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_left _ (divisorDeficit_nonneg _)
    simpa only [zetaKernel_rpow (by linarith : s ≠ 0),Nat.cast_add,Nat.cast_one] using (hp n hn).1
  · apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_left _ (divisorDeficit_nonneg _)
    simpa only [zetaKernel_rpow (by linarith : s ≠ 0),Nat.cast_add,Nat.cast_one] using (hp n hn).2

theorem deficit_formula_enclosure {s zl zh tl th : ℝ} (hs : 1 < s)
    (hz0 : 0 ≤ zl) (ht0 : 0 < tl)
    (hz : zl ≤ realZeta s ∧ realZeta s ≤ zh)
    (ht : tl ≤ realZeta (2*s) ∧ realZeta (2*s) ≤ th) :
    zl^2/(2*th)-zh+1/2 ≤ deficitSeries s ∧
      deficitSeries s ≤ zh^2/(2*tl)-zl+1/2 := by
  have hn : 0 ≤ realZeta s := (realZeta_pos hs).le
  have hsquare : zl^2 ≤ (realZeta s)^2 ∧ (realZeta s)^2 ≤ zh^2 :=
    ⟨(sq_le_sq₀ hz0 hn).mpr hz.1,(sq_le_sq₀ hn (hn.trans hz.2)).mpr hz.2⟩
  have hd : 2*tl ≤ 2*realZeta (2*s) ∧ 2*realZeta (2*s) ≤ 2*th := by
    constructor <;> linarith [ht.1,ht.2]
  have h := positive_division_enclosure (sq_nonneg zl) (by positivity : 0 < 2*tl)
    hsquare hd
  rw [deficitSeries_formula hs]
  constructor <;> linarith [h.1,h.2,hz.1,hz.2]

theorem deficit_final_enclosure {s lo hi prefixLower : ℝ} (hs : 1 < s) (N : ℕ)
    (hraw : lo ≤ deficitSeries s ∧ deficitSeries s ≤ hi)
    (hp : prefixLower ≤ deficitPrefix s N) :
    max 0 (max prefixLower lo) ≤ deficitSeries s ∧
      deficitSeries s ≤ hi ∧ 0 ≤ deficitSeries s-deficitPrefix s N ∧
      deficitSeries s-deficitPrefix s N ≤ hi-prefixLower := by
  have h := deficit_prefix_le hs N
  refine ⟨max_le (deficitSeries_nonneg s) (max_le (hp.trans h) hraw.1),hraw.2,?_,?_⟩
  · linarith
  · linarith [hraw.2]

theorem deficit_two_enclosure {zl zh : ℝ}
    (hz : zl ≤ realZeta 2 ∧ realZeta 2 ≤ zh) :
    7/4-zh ≤ deficitSeries 2 ∧ deficitSeries 2 ≤ 7/4-zl := by
  rw [deficitSeries_two_exact]
  constructor <;> linarith [hz.1,hz.2]

theorem deficit_special_intersection {s lo hi sl sh : ℝ}
    (h : lo ≤ deficitSeries s ∧ deficitSeries s ≤ hi)
    (hs : sl ≤ deficitSeries s ∧ deficitSeries s ≤ sh) :
    max lo sl ≤ deficitSeries s ∧ deficitSeries s ≤ min hi sh :=
  ⟨max_le h.1 hs.1,le_min h.2 hs.2⟩

theorem deficit_special_constants :
    0 ≤ deficitSeries 2 ∧ deficitSeries 2 ≤ 1/8 ∧
      0 ≤ deficitSeries (3/2) ∧ deficitSeries (3/2) ≤ 67/80 :=
  ⟨deficitSeries_nonneg 2,deficitSeries_two_upper.le,
    deficitSeries_nonneg (3/2),deficitSeries_threeHalves_upper.le⟩

theorem deficit_weighted_enclosure {l2 u2 l3 u3 : ℝ}
    (h2 : l2 ≤ deficitSeries 2 ∧ deficitSeries 2 ≤ u2)
    (h3 : l3 ≤ deficitSeries (3/2) ∧ deficitSeries (3/2) ≤ u3) :
    3/2*l2+37/100*l3 ≤ 3/2*deficitSeries 2+37/100*deficitSeries (3/2) ∧
      3/2*deficitSeries 2+37/100*deficitSeries (3/2) ≤ 3/2*u2+37/100*u3 := by
  constructor <;> linarith [h2.1,h2.2,h3.1,h3.2]

theorem deficit_literal_margin :
    1-(3/2*deficitSeries 2+37/100*deficitSeries (3/2)) > 4021/8000 ∧
      (4021 : ℝ)/8000 > 1/2 := by
  constructor
  · linarith [deficitSeries_combined_upper]
  · norm_num

end NField.Alignment.CollisionDirichletRationalEnclosure
