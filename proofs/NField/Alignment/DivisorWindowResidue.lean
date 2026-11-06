/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.DivisorWindowPairing

/-! # Short divisor windows and the exact centered displacement -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorWindowResidue
open scoped BigOperators Classical
open DivisorWindowPairing SquareLockCarrierMass

theorem interval_multiples_card_le_one {L U k : ℕ} (hwidth : U-L<k) :
    (intervalMultiples L U k).card≤1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨haI,haD⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI,hbD⟩ := Finset.mem_filter.mp hb
  obtain ⟨haL,haU⟩ := Finset.mem_Icc.mp haI
  obtain ⟨hbL,hbU⟩ := Finset.mem_Icc.mp hbI
  have haE := Nat.mul_div_cancel' haD
  have hbE := Nat.mul_div_cancel' hbD
  have hgap : ∀ x y : ℕ, L≤x → x≤U → L≤y → y≤U →
      k*(x/k)=x → k*(y/k)=y → x<y → False := by
    intro x y hxL hxU hyL hyU hxE hyE hxy
    have hq : x/k<y/k := by
      by_contra hn
      have hm := Nat.mul_le_mul_left k (show y/k≤x/k by omega)
      omega
    have hm := Nat.mul_le_mul_left k (show x/k+1≤y/k by omega)
    have hLU : L≤U := hxL.trans hxU
    have hsub := Nat.sub_add_cancel hLU
    nlinarith
  rcases lt_trichotomy a b with h|h|h
  · exact False.elim (hgap a b haL haU hbL hbU haE hbE h)
  · exact h
  · exact False.elim (hgap b a hbL hbU haL haU hbE haE h)

theorem centered_residue_le_of_near_multiple {n v k C : ℕ}
    (hC : C≤n) (hhalf : 2*C<k) (hv : v∈intervalMultiples (n-C) (n+C) k) :
    (centeredNaturalResidue n k).natAbs≤C := by
  obtain ⟨hvI,hvd⟩ := Finset.mem_filter.mp hv
  obtain ⟨hvL,hvU⟩ := Finset.mem_Icc.mp hvI
  have hk : 0<k := by omega
  have hvm : v%k=0 := Nat.mod_eq_zero_of_dvd hvd
  by_cases hvn : v≤n
  · let d := n-v
    have hd : d≤C := by dsimp [d]; omega
    have hdk : d<k := by omega
    have he : v+d=n := by dsimp [d]; omega
    have hr : n%k=d := calc
      _ = (v+d)%k := congrArg (fun a => a%k) he.symm
      _ = d := by rw [Nat.add_mod,hvm,zero_add,Nat.mod_eq_of_lt hdk,Nat.mod_eq_of_lt hdk]
    simp only [centeredNaturalResidue,hr,if_pos (show 2*d≤k by omega),Int.natAbs_natCast]
    exact hd
  · let d := v-n
    have hd : d≤C := by dsimp [d]; omega
    have hd0 : 0<d := by dsimp [d]; omega
    have hdk : d<k := by omega
    have he : n+d=v := by dsimp [d]; omega
    have hr : n%k<k := Nat.mod_lt _ hk
    have hz : (n%k+d)%k=0 := by
      have he' := congrArg (fun a => a%k) he
      rw [Nat.add_mod,Nat.mod_eq_of_lt hdk,hvm] at he'
      exact he'
    obtain ⟨j,hj⟩ := Nat.dvd_of_mod_eq_zero hz
    have hj1 : j=1 := by
      have hj0 : 0<j := by
        by_contra hh
        have hjz : j=0 := by omega
        rw [hjz,mul_zero] at hj
        omega
      have hj2 : j<2 := by
        by_contra hh
        have hjlarge : 2≤j := by omega
        nlinarith
      omega
    rw [hj1,mul_one] at hj
    have hnot : ¬2*(n%k)≤k := by omega
    have hval : ((n%k : ℕ) : ℤ)-(k : ℤ)=-(d : ℤ) := by omega
    simp only [centeredNaturalResidue,if_neg hnot,hval,Int.natAbs_neg,Int.natAbs_natCast]
    exact hd

theorem window_large_modulus_bound {p C k : ℕ} (hp : p.Prime) (hC : 1≤C)
    (hhalf : 2*C≤p) (hk : 2*C<k) (hkp : k≤p) :
    (intervalMultiples (p^2-C) (p^2+C) k).card ≤
      if k∈smallDisplacementCarriers p C ∨ k=p then 1 else 0 := by
  have hCp : C≤p := by omega
  have hCsq : C≤p^2 := hCp.trans (Nat.le_self_pow (by omega) p)
  have hwidth : (p^2+C)-(p^2-C)=2*C := by omega
  by_cases hmem : k∈smallDisplacementCarriers p C ∨ k=p
  · simp only [if_pos hmem]
    exact interval_multiples_card_le_one (by omega)
  · simp only [if_neg hmem]
    apply Nat.le_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hk2 : 2≤k := by omega
    have hkp' : k<p := by omega
    have hc := centered_residue_le_of_near_multiple hCsq hk hv
    have hz := centeredPrimeSquareResidue_natAbs_pos hp hk2 hkp'
    have hm : k∈smallDisplacementCarriers p C :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk2,by omega⟩,hz,hc⟩
    exact hmem (Or.inl hm)

end NField.Alignment.DivisorWindowResidue
