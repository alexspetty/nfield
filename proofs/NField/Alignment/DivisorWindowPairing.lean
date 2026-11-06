/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/
import NField.Alignment.SquareLockCountBound
import Mathlib.NumberTheory.Divisors

/-! # Divisor pairing and interval counts for the printed signed window -/
noncomputable section
set_option autoImplicit false
namespace NField.Alignment.DivisorWindowPairing
open scoped BigOperators

def smallDivisors (p n : ℕ) : Finset ℕ := n.divisors.filter (fun d => d≤p)
def intervalMultiples (L U k : ℕ) : Finset ℕ := (Finset.Icc L U).filter (fun n => k∣n)

theorem divisor_count_le_twice_small {p n : ℕ} (hn : 0<n) (hbound : n<(p+1)^2) :
    n.divisors.card ≤ 2*(smallDivisors p n).card := by
  have hsub : n.divisors ⊆ smallDivisors p n ∪ (smallDivisors p n).image (fun d => n/d) := by
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    by_cases hdp : d≤p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd,hdp⟩)
    · have he : d*(n/d)=n := Nat.mul_div_cancel' hdvd
      have hq : n/d≤p := by
        by_contra hq
        have hmul := Nat.mul_le_mul (by omega : p+1≤d) (by omega : p+1≤n/d)
        nlinarith
      have hq0 : 0<n/d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd0
      have hqmem : n/d ∈ smallDivisors p n := Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨⟨d,by nlinarith⟩,hn.ne'⟩,hq⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨n/d,hqmem,?_⟩
      calc
        n/(n/d) = (d*(n/d))/(n/d) := congrArg (fun a => a/(n/d)) he.symm
        _ = d := Nat.mul_div_cancel d hq0
  calc
    _ ≤ (smallDivisors p n ∪ (smallDivisors p n).image (fun d => n/d)).card := Finset.card_le_card hsub
    _ ≤ (smallDivisors p n).card+((smallDivisors p n).image (fun d => n/d)).card := Finset.card_union_le _ _
    _ ≤ (smallDivisors p n).card+(smallDivisors p n).card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = _ := by omega

theorem interval_multiples_card {L U k : ℕ} (hLU : L≤U) (hk : 0<k) :
    (intervalMultiples L U k).card*k ≤ U-L+2*k := by
  have hmap : ∀ n ∈ intervalMultiples L U k, n/k ∈ Finset.Icc (L/k) (U/k) := by
    intro n hn
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hi.1,Nat.div_le_div_right hi.2⟩
  have hinj : ∀ n ∈ intervalMultiples L U k, ∀ m ∈ intervalMultiples L U k,
      n/k=m/k → n=m := by
    intro n hn m hm he
    have hn' := Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
    have hm' := Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2
    rw [he] at hn'
    omega
  have hc : (intervalMultiples L U k).card ≤ (Finset.Icc (L/k) (U/k)).card :=
    Finset.card_le_card_of_injOn (fun n => n/k) hmap hinj
  have hdiv : L/k≤U/k := Nat.div_le_div_right hLU
  simp only [Nat.card_Icc] at hc
  have hmul := Nat.mul_le_mul_right k hc
  have hsplit : U/k+1-L/k+L/k=U/k+1 := by omega
  have hL := Nat.div_add_mod L k
  have hU := Nat.div_mul_le_self U k
  have hmod := Nat.mod_lt L hk
  have hsub : U-L+L=U := Nat.sub_add_cancel hLU
  nlinarith

theorem interval_multiples_real_bound {L U k : ℕ} (hLU : L≤U) (hk : 0<k) :
    ((intervalMultiples L U k).card : ℝ) ≤ ((U-L : ℕ) : ℝ)/(k : ℝ)+2 := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have h : ((intervalMultiples L U k).card : ℝ)*(k : ℝ) ≤ ((U-L : ℕ) : ℝ)+2*k := by
    exact_mod_cast interval_multiples_card hLU hk
  simpa [add_div,mul_div_cancel_right₀ _ hkR.ne'] using (le_div_iff₀ hkR).mpr h

end NField.Alignment.DivisorWindowPairing
