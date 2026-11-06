/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionAmplitudeConstantsEnclosure
import NField.Alignment.CollisionUniformAmplitude
import NField.Alignment.CollisionPrimePowerAmplitude
import NField.Alignment.CollisionFourierEnclosure

noncomputable section
set_option autoImplicit false
namespace NField.Alignment.CollisionUniformAmplitudeEnclosure
open scoped BigOperators
open CollisionAmplitudeArithmetic CollisionAmplitudeRefinement CollisionHarmonicSeed
open CollisionZetaMoments CollisionHarmonicSeedExpansion CollisionConductorArithmetic
open CollisionUniformAmplitude CollisionJordanVariance CollisionFourierEnclosure
open CollisionAmplitudeConstantsEnclosure CollisionHarmonicRemainder

def nuLower (q : ℕ) (L : ℕ → ℝ) : ℝ :=
  ∑ p ∈ q.primeFactors, L p / ((p : ℝ)-1)

theorem nu_enclosure (q : ℕ) (L U : ℕ → ℝ)
    (hlog : ∀ p ∈ q.primeFactors, L p ≤ Real.log p ∧ Real.log p ≤ U p) :
    nuLower q L ≤ nu q ∧ nu q ≤ nuLower q U := by
  have hp (p : ℕ) (h : p ∈ q.primeFactors) : 0 ≤ (p : ℝ)-1 := by
    have htwo := (Nat.prime_of_mem_primeFactors h).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast htwo
    linarith
  exact ⟨Finset.sum_le_sum (fun p h => div_le_div_of_nonneg_right (hlog p h).1 (hp p h)),
    Finset.sum_le_sum (fun p h => div_le_div_of_nonneg_right (hlog p h).2 (hp p h))⟩

theorem rho_nonneg (q : ℕ) : 0 ≤ rho q := by
  unfold rho totientRatio
  exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (deltaThree_pos q).le

theorem harmonic_error_enclosure {n : ℕ} (hn : 1 ≤ n) {ll lh gl gh : ℝ}
    (hl : ll ≤ Real.log n ∧ Real.log n ≤ lh)
    (hg : gl ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ gh) :
    max ((harmonic (n-1) : ℝ)-lh-gh+1/(2*(n : ℝ))) (-1/(12*(n : ℝ)^2)) ≤ harmonicError n ∧
    harmonicError n ≤ min ((harmonic (n-1) : ℝ)-ll-gl+1/(2*(n : ℝ))) 0 := by
  have hb := harmonicError_bounds hn
  unfold harmonicError
  constructor
  · apply max_le
    · linarith [hl.2,hg.2]
    · simpa only [harmonicError,neg_div] using hb.1.le
  · apply le_min
    · linarith [hl.1,hg.1]
    · exact hb.2.le

theorem seed_expansion_enclosure {q : ℕ} (hq : 0 < q)
    {z2l z2h z3l z3h z4h ll lh kl kh : ℝ}
    (hz2 : z2l ≤ zetaNat 2 ∧ zetaNat 2 ≤ z2h)
    (hz3 : z3l ≤ zetaThree ∧ zetaThree ≤ z3h) (hz4 : zetaNat 4 ≤ z4h)
    (hlog : ll ≤ Real.log q ∧ Real.log q ≤ lh)
    (hk : kl ≤ kappaZero ∧ kappaZero ≤ kh) :
    productLower z2l z2h (ll+kl) (lh+kh)/(q : ℝ)^2-z3h/(2*(q : ℝ)^3)-z4h/(12*(q : ℝ)^4) ≤ harmonicSeed q ∧
    harmonicSeed q ≤ productUpper z2l z2h (ll+kl) (lh+kh)/(q : ℝ)^2-z3l/(2*(q : ℝ)^3) := by
  have hm := product_interval hz2 ⟨add_le_add hlog.1 hk.1,add_le_add hlog.2 hk.2⟩
  have hml := div_le_div_of_nonneg_right hm.1 (sq_nonneg (q : ℝ))
  have hmh := div_le_div_of_nonneg_right hm.2 (sq_nonneg (q : ℝ))
  have hzl := div_le_div_of_nonneg_right hz3.1 (show 0 ≤ 2*(q : ℝ)^3 by positivity)
  have hzh := div_le_div_of_nonneg_right hz3.2 (show 0 ≤ 2*(q : ℝ)^3 by positivity)
  have he := seedError_bounds hq
  have heh := div_le_div_of_nonneg_right hz4 (show 0 ≤ 12*(q : ℝ)^4 by positivity)
  rw [harmonicSeed_expansion hq]
  constructor <;> linarith [he.1,he.2]

theorem amplitude_main_enclosure (q : ℕ) {al ah ll lh kl kh nl nh : ℝ}
    (ha : al ≤ amplitudeLeading ∧ amplitudeLeading ≤ ah)
    (hlog : ll ≤ Real.log q ∧ Real.log q ≤ lh)
    (hk : kl ≤ kappaZero ∧ kappaZero ≤ kh)
    (hn : nl ≤ nu q ∧ nu q ≤ nh) :
    productLower (al*rho q/(q : ℝ)^2) (ah*rho q/(q : ℝ)^2) (ll+kl+nl) (lh+kh+nh) ≤
      amplitudeLeading*rho q/(q : ℝ)^2*(Real.log q+kappaZero+nu q) ∧
    amplitudeLeading*rho q/(q : ℝ)^2*(Real.log q+kappaZero+nu q) ≤
      productUpper (al*rho q/(q : ℝ)^2) (ah*rho q/(q : ℝ)^2) (ll+kl+nl) (lh+kh+nh) := by
  have hl := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha.1 (rho_nonneg q)) (sq_nonneg (q : ℝ))
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha.2 (rho_nonneg q)) (sq_nonneg (q : ℝ))
  exact product_interval ⟨hl,hh⟩
    ⟨add_le_add (add_le_add hlog.1 hk.1) hn.1,add_le_add (add_le_add hlog.2 hk.2) hn.2⟩


def uniformErrorUpper (q : ℕ) (z4h z3l : ℝ) : ℝ :=
  z4h/(12*z3l*(q : ℝ)^4*deltaThree q)*∏ p ∈ q.primeFactors, ((p : ℝ)+1)

theorem uniform_error_upper {q : ℕ} (hq : 0 < q) {z4h z3l : ℝ}
    (hzl : 0 < z3l) (hz3 : z3l ≤ zetaThree) (hz4 : zetaNat 4 ≤ z4h) :
    |amplitudeError q| ≤ uniformErrorUpper q z4h z3l := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd := deltaThree_pos q
  have hlo : 0 < 12*z3l*(q : ℝ)^4*deltaThree q := by positivity
  have hden : 12*z3l*(q : ℝ)^4*deltaThree q ≤ 12*zetaThree*(q : ℝ)^4*deltaThree q := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz3 (by norm_num))
        (by positivity)) hd.le
  have h1 := div_le_div_of_nonneg_left (zetaNat_pos (by norm_num : 1<(4 : ℕ))).le hlo hden
  have h2 := div_le_div_of_nonneg_right hz4 hlo.le
  apply (amplitude_uniform_error hq).trans
  exact mul_le_mul_of_nonneg_right (h1.trans h2)
    (Finset.prod_nonneg (fun p _ => by positivity))

theorem uniform_amplitude_enclosure {q : ℕ} (hq : 2 ≤ q) {l u z4h z3l : ℝ}
    (hzl : 0 < z3l) (hz3 : z3l ≤ zetaThree) (hz4 : zetaNat 4 ≤ z4h)
    (hm : l ≤ amplitudeLeading*rho q/(q : ℝ)^2*(Real.log q+kappaZero+nu q) ∧
      amplitudeLeading*rho q/(q : ℝ)^2*(Real.log q+kappaZero+nu q) ≤ u) :
    l-uniformErrorUpper q z4h z3l ≤ amplitude q ∧ amplitude q ≤ u+uniformErrorUpper q z4h z3l := by
  have he := abs_le.mp (uniform_error_upper (by omega : 0<q) hzl hz3 hz4)
  rw [amplitude_uniform_formula hq]
  constructor <;> linarith [hm.1,hm.2,he.1,he.2]

theorem prime_power_main_enclosure {p a : ℕ} (hp : p.Prime)
    {al ah ll lh kl kh : ℝ}
    (ha : al ≤ amplitudeLeading ∧ amplitudeLeading ≤ ah)
    (hlog : ll ≤ Real.log p ∧ Real.log p ≤ lh)
    (hk : kl ≤ kappaZero ∧ kappaZero ≤ kh) :
    productLower (al*rho p/(p : ℝ)^(2*a)) (ah*rho p/(p : ℝ)^(2*a))
      ((a : ℝ)*ll+kl+ll/((p : ℝ)-1)) ((a : ℝ)*lh+kh+lh/((p : ℝ)-1)) ≤
      amplitudeLeading*rho p/(p : ℝ)^(2*a)*
        ((a : ℝ)*Real.log p+kappaZero+Real.log p/((p : ℝ)-1)) ∧
    amplitudeLeading*rho p/(p : ℝ)^(2*a)*
        ((a : ℝ)*Real.log p+kappaZero+Real.log p/((p : ℝ)-1)) ≤
      productUpper (al*rho p/(p : ℝ)^(2*a)) (ah*rho p/(p : ℝ)^(2*a))
        ((a : ℝ)*ll+kl+ll/((p : ℝ)-1)) ((a : ℝ)*lh+kh+lh/((p : ℝ)-1)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ha.1 (rho_nonneg p)) (by positivity : 0 ≤ (p : ℝ)^(2*a))
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ha.2 (rho_nonneg p)) (by positivity : 0 ≤ (p : ℝ)^(2*a))
  exact product_interval ⟨hl,hh⟩
    ⟨add_le_add (add_le_add (mul_le_mul_of_nonneg_left hlog.1 (Nat.cast_nonneg a)) hk.1)
        (div_le_div_of_nonneg_right hlog.1 (by linarith)),
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg a)) hk.2)
        (div_le_div_of_nonneg_right hlog.2 (by linarith))⟩

theorem prime_power_full_enclosure {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0)
    {l u z4h z3l : ℝ} (hzl : 0 < z3l) (hz3 : z3l ≤ zetaThree) (hz4 : zetaNat 4 ≤ z4h)
    (hm : l ≤ amplitudeLeading*rho p/(p : ℝ)^(2*a)*
      ((a : ℝ)*Real.log p+kappaZero+Real.log p/((p : ℝ)-1)) ∧
      amplitudeLeading*rho p/(p : ℝ)^(2*a)*
        ((a : ℝ)*Real.log p+kappaZero+Real.log p/((p : ℝ)-1)) ≤ u) :
    l-uniformErrorUpper (p^a) z4h z3l ≤ amplitude (p^a) ∧
      amplitude (p^a) ≤ u+uniformErrorUpper (p^a) z4h z3l := by
  have he := abs_le.mp (uniform_error_upper (q := p^a) (Nat.pow_pos hp.pos) hzl hz3 hz4)
  rw [CollisionPrimePowerAmplitude.amplitude_prime_power_formula hp ha]
  constructor <;> linarith [hm.1,hm.2,he.1,he.2]

theorem prime_leading_enclosure (p : ℕ) {al ah ll lh : ℝ}
    (ha : al ≤ amplitudeLeading ∧ amplitudeLeading ≤ ah)
    (hlog : ll ≤ Real.log p ∧ Real.log p ≤ lh) :
    productLower al ah ll lh/(p : ℝ)^2 ≤ amplitudeLeading*Real.log p/(p : ℝ)^2 ∧
      amplitudeLeading*Real.log p/(p : ℝ)^2 ≤ productUpper al ah ll lh/(p : ℝ)^2 := by
  have h := product_interval ha hlog
  exact ⟨div_le_div_of_nonneg_right h.1 (sq_nonneg _),div_le_div_of_nonneg_right h.2 (sq_nonneg _)⟩

end NField.Alignment.CollisionUniformAmplitudeEnclosure
