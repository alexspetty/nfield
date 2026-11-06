/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.RealSawtoothIntegralSymmetry

/-! # The literal real sawtooth pairing and gcd kernel -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.RealSawtoothPairIntegral
open scoped BigOperators Topology Classical
open MeasureTheory Set CollisionDedekindPairing RealSawtoothLimits
  RealSawtoothDistribution RealSawtoothIntegralSymmetry

def pairIntegral (r s : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, periodicSawtooth ((r:ℝ)*x)*periodicSawtooth ((s:ℝ)*x)

theorem pair_integral_symm (r s : ℕ) : pairIntegral r s=pairIntegral s r := by
  unfold pairIntegral
  congr 1
  funext x
  ring

theorem pair_integral_mul (r s : ℕ) {n : ℕ} (hn : 0<n) :
    pairIntegral (n*r) (n*s)=pairIntegral r s := by
  unfold pairIntegral
  have h := periodic_integral_mul (sawtooth_pair_periodic r s)
    (sawtooth_pair_integrable (r:ℝ) (s:ℝ)) hn
  convert h using 1
  congr 1
  funext x
  push_cast
  congr 1 <;> congr 1 <;> ring

theorem coprime_pair_averaging {r s : ℕ} (hr : 0<r) (hcop : s.Coprime r) :
    (r:ℝ)*pairIntegral r s=pairIntegral 1 s := by
  have hrR : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  let g := fun x : ℝ => periodicSawtooth ((r:ℝ)*x)*periodicSawtooth ((s:ℝ)*x)
  have hpoint (x : ℝ) : (∑ j ∈ Finset.range r, g (x+(j:ℝ)/r))=
      periodicSawtooth ((r:ℝ)*x)*periodicSawtooth ((s:ℝ)*((r:ℝ)*x)) := by
    have he (j : ℕ) : (r:ℝ)*(x+(j:ℝ)/r)=(r:ℝ)*x+j := by field_simp <;> ring
    change (∑ j ∈ Finset.range r, periodicSawtooth ((r:ℝ)*(x+(j:ℝ)/r))*
      periodicSawtooth ((s:ℝ)*(x+(j:ℝ)/r)))=_
    simp_rw [he,sawtooth_add_nat]
    simp_rw [show ∀ j : ℕ, (s:ℝ)*(x+(j:ℝ)/r)=(s:ℝ)*x+(s:ℝ)*j/r by intro j; ring]
    rw [← Finset.mul_sum,sawtooth_twisted_distribution hr hcop]
    congr 2
    ring
  have hgi (j : ℕ) : IntervalIntegrable (fun x => g (x+(j:ℝ)/r)) volume 0 1 := by
    apply (IntervalIntegrable.comp_add_right_iff).mpr
    exact sawtooth_pair_integrable (r:ℝ) (s:ℝ) _ _
  calc
    (r:ℝ)*pairIntegral r s = ∑ _j ∈ Finset.range r, pairIntegral r s := by simp
    _ = ∑ j ∈ Finset.range r, ∫ x in (0:ℝ)..1, g (x+(j:ℝ)/r) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (periodic_integral_shift (sawtooth_pair_periodic r s) _).symm
    _ = ∫ x in (0:ℝ)..1, ∑ j ∈ Finset.range r, g (x+(j:ℝ)/r) :=
      (intervalIntegral.integral_finsetSum (fun j hj => hgi j)).symm
    _ = ∫ x in (0:ℝ)..1, periodicSawtooth ((r:ℝ)*x)*periodicSawtooth ((s:ℝ)*((r:ℝ)*x)) := by
      simp only [hpoint]
    _ = pairIntegral 1 s := by
      have h := periodic_integral_mul (sawtooth_pair_periodic 1 s)
        (by simpa only [Nat.cast_one] using sawtooth_pair_integrable (1:ℝ) (s:ℝ)) hr
      simpa only [Nat.cast_one,one_mul,pairIntegral] using h

theorem sawtooth_square_integral : pairIntegral 1 1=(1/12:ℝ) := by
  unfold pairIntegral
  simp only [Nat.cast_one,one_mul]
  calc
    (∫ x in (0:ℝ)..1, periodicSawtooth x*periodicSawtooth x)=
        ∫ x in (0:ℝ)..1, (x-1/2)^2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      change periodicSawtooth x*periodicSawtooth x=(x-1/2)^2
      rw [sawtooth_affine (n := 0) (by simpa using hx.1) (by simpa using hx.2)]
      norm_num
      ring
    _ = 1/12 := by
      rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^2) (1/2),integral_pow]
      norm_num

theorem coprime_pair_integral {r s : ℕ} (hr : 0<r) (hs : 0<s) (hcop : r.Coprime s) :
    pairIntegral r s=1/(12*(r:ℝ)*s) := by
  have h1 := coprime_pair_averaging hr hcop.symm
  have h2 := coprime_pair_averaging hs (Nat.coprime_one_left s)
  rw [pair_integral_symm s 1,sawtooth_square_integral] at h2
  have hrR : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  have hsR : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  apply (eq_div_iff (by positivity : (12:ℝ)*r*s≠0)).mpr
  nlinarith

/-- Title: `Real sawtooth pairing and the gcd kernel`. -/
theorem sawtooth_pair_integral {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    (∫ x in (0:ℝ)..1, periodicSawtooth ((r:ℝ)*x)*periodicSawtooth ((s:ℝ)*x))=
      (r.gcd s:ℝ)^2/(12*(r:ℝ)*s) := by
  let d := r.gcd s
  have hd : 0<d := Nat.gcd_pos_of_pos_left s hr
  have hdr : d∣r := Nat.gcd_dvd_left r s
  have hds : d∣s := Nat.gcd_dvd_right r s
  have hr' : 0<r/d := Nat.div_pos (Nat.le_of_dvd hr hdr) hd
  have hs' : 0<s/d := Nat.div_pos (Nat.le_of_dvd hs hds) hd
  have hcop : (r/d).Coprime (s/d) := Nat.coprime_div_gcd_div_gcd hd
  have her : d*(r/d)=r := Nat.mul_div_cancel' hdr
  have hes : d*(s/d)=s := Nat.mul_div_cancel' hds
  have hi := pair_integral_mul (r/d) (s/d) hd
  rw [her,hes,coprime_pair_integral hr' hs' hcop] at hi
  change pairIntegral r s=_
  rw [hi]
  have herR : (d:ℝ)*(r/d:ℕ)=r := by exact_mod_cast her
  have hesR : (d:ℝ)*(s/d:ℕ)=s := by exact_mod_cast hes
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hrR : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  have hsR : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  have hr'R : ((r/d:ℕ):ℝ)≠0 := by exact_mod_cast hr'.ne'
  have hs'R : ((s/d:ℕ):ℝ)≠0 := by exact_mod_cast hs'.ne'
  change 1/(12*((r/d:ℕ):ℝ)*((s/d:ℕ):ℝ))=(d:ℝ)^2/(12*(r:ℝ)*s)
  field_simp
  nlinarith [mul_mul_mul_comm (d:ℝ) ((r/d:ℕ):ℝ) (d:ℝ) ((s/d:ℕ):ℝ)]

end NField.Alignment.RealSawtoothPairIntegral
