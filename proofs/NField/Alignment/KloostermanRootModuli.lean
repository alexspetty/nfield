/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.KloostermanRootPowerAggregate
import NField.Alignment.FinitePowerSumGrowth

/-!
# Individual Kloosterman root moduli for odd primes

Use the actual extensions of cardinality p^n to turn the Stepanov
aggregate bound into eventual exponential growth. Cesaro averaging then
bounds every member of the fixed root family, retaining multiplicities.
The exact product p forces both reciprocal roots onto the circle of
radius sqrt(p), and their sum gives the prime-field estimate.
-/

set_option autoImplicit false
namespace NField.Alignment.KloostermanRootModuli
open scoped BigOperators Classical Topology
open Filter KloostermanQuadraticLSeries KloostermanTraceSum KloostermanRootPowerAggregate

private theorem sqrt_nat_pow (p n : ℕ) :
    Real.sqrt ((p:ℝ)^n) = (Real.sqrt p)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) n),ih,pow_succ]

/-- The fixed reciprocal-root family has square-root exponential growth
through all sufficiently large extension degrees. -/
theorem eventual_root_power_growth (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    ∀ᶠ n : ℕ in atTop,
      ‖∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, (α m^n+β m^n)‖ ≤
        (16*p+1)*(Real.sqrt p)^n := by
  have hp2 := (Fact.out : p.Prime).two_le
  filter_upwards [eventually_ge_atTop (12*p)] with n hn
  have hn0 : n≠0 := by omega
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p n) = p^n := by
    rw [Fintype.card_eq_nat_card,GaloisField.card p n hn0]
  have hq : 12*p≤Fintype.card (GaloisField p n) := by
    rw [hcard]
    exact hn.trans (Nat.lt_pow_self (by omega : 1<p)).le
  have hodd : Odd (Fintype.card (GaloisField p n)) := by rw [hcard]; exact hp.pow
  have h := root_power_aggregate_bound (K := GaloisField p n) p a b ha hb hodd hq α β hf
  rw [GaloisField.finrank p hn0,hcard,Nat.cast_pow,sqrt_nat_pow] at h
  have hs : 1 ≤ (Real.sqrt p)^n := one_le_pow₀ (Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1≤p)))
  have hc := Nat.ceil_lt_add_one (pow_nonneg (Real.sqrt_nonneg (p:ℝ)) n)
  have ht : ‖∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, (α m^n+β m^n)‖ ≤
      ‖(∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, (α m^n+β m^n))+1‖+1 := by
    simpa using norm_sub_le
      ((∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, (α m^n+β m^n))+1) (1:ℂ)
  have hcp : (0:ℝ)≤8*p := by positivity
  have hceil := mul_le_mul_of_nonneg_left hc.le hcp
  nlinarith

/-- Every actual reciprocal root for nonzero frequency has modulus at
most sqrt(p), using all growing finite extensions of the same prime field. -/
theorem root_norm_le (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X)) :
    ∀ m : ZMod p, m≠0 → ‖α m‖≤Real.sqrt p ∧ ‖β m‖≤Real.sqrt p := by
  let z : {m : ZMod p // m≠0} ⊕ {m : ZMod p // m≠0} → ℂ :=
    Sum.elim (fun m => α m.val) (fun m => β m.val)
  have he (n : ℕ) : (∑ i, z i^n) =
      ∑ m ∈ (Finset.univ : Finset (ZMod p)).erase 0, (α m^n+β m^n) := by
    rw [Fintype.sum_sum_type,← Finset.sum_add_distrib]
    exact (Finset.sum_subtype (p := fun m : ZMod p => m≠0)
      (Finset.univ.erase 0) (fun m => by simp) (fun m => α m^n+β m^n)).symm
  have hg := eventual_root_power_growth p hp a b ha hb α β hf
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hz := FinitePowerSumGrowth.norm_le_of_power_sum_growth z (Real.sqrt p) (16*p+1)
    (Real.sqrt_pos.mpr hp0) (by simpa only [he] using hg)
  intro m hm
  exact ⟨hz (Sum.inl ⟨m,hm⟩),hz (Sum.inr ⟨m,hm⟩)⟩

/-- The exact product p upgrades both upper bounds to equality. -/
theorem root_norm_eq (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b : ZMod p) (ha : a≠0) (hb : b≠0) (α β : ZMod p → ℂ)
    (hf : ∀ m : ZMod p, m≠0 → formalLSeries p a b m =
      (1-PowerSeries.C (α m)*PowerSeries.X)*(1-PowerSeries.C (β m)*PowerSeries.X))
    (hprod : ∀ m : ZMod p, m≠0 → α m*β m=p) :
    ∀ m : ZMod p, m≠0 → ‖α m‖=Real.sqrt p ∧ ‖β m‖=Real.sqrt p := by
  intro m hm
  obtain ⟨hα,hβ⟩ := root_norm_le p hp a b ha hb α β hf m hm
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs := Real.sq_sqrt hp0.le
  have hsp := Real.sqrt_pos.mpr hp0
  have hmul : ‖α m‖*‖β m‖=(p:ℝ) := by rw [← norm_mul,hprod m hm,Complex.norm_natCast]
  have h1 := mul_le_mul_of_nonneg_left hβ (norm_nonneg (α m))
  have h2 := mul_le_mul_of_nonneg_right hα (norm_nonneg (β m))
  constructor <;> nlinarith

/-- The actual prime-field trace Kloosterman sum satisfies Weil's bound
for odd primes and nonzero a,b,m. -/
theorem prime_trace_sum_bound (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (a b m : ZMod p) (ha : a≠0) (hb : b≠0) (hm : m≠0) :
    ‖traceKloostermanSum p a b m‖ ≤ 2*Real.sqrt p := by
  obtain ⟨α,β,h⟩ := exists_root_families p a b ha hb
  obtain ⟨hα,hβ⟩ := root_norm_le p hp a b ha hb α β (fun k hk => (h k hk).2.2) m hm
  have hn : ‖traceKloostermanSum p a b m‖=‖α m+β m‖ := by
    rw [(h m hm).1,norm_neg]
  rw [hn]
  exact (norm_add_le _ _).trans (by linarith)

end NField.Alignment.KloostermanRootModuli
