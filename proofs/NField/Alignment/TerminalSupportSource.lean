/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.TerminalCarrySource

/-! # Actual terminal support and leading-lag pullbacks -/

noncomputable section
namespace NField.Alignment.TerminalSupportSource
open scoped BigOperators Classical
open CollisionCharacterStructure CarryBoundarySpectra TerminalCollisionBoundary
  TerminalCarrySource LiftedBoundaryInvisibility

def terminalDigitSupport (p N : ℕ) : Finset ℕ :=
  (Finset.range (p ^ N)).filter fun n => n / p ^ (N - 1) = n % p

/-- Title: `The digit-defined terminal support is the endpoint parametrization`. -/
theorem terminal_digit_support_eq {p N : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    terminalDigitSupport p N = terminalCollisionSupport p N := by
  letI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne'⟩
  ext n
  simp only [terminalDigitSupport, Finset.mem_filter, Finset.mem_range,
    terminalCollisionSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hn, heq⟩
    have hxval : (n : ZMod (p ^ N)).val = n := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]
    have hf := terminalCoordinateFacts hp hN (n : ZMod (p ^ N))
    rw [hxval] at hf
    obtain ⟨_, hy, hdecomp⟩ := hf
    let i : TerminalCellIndex p N :=
      (⟨n % p, Nat.mod_lt _ hp⟩, ⟨n % p ^ (N - 1) / p, hy⟩)
    refine ⟨i, ?_⟩
    unfold terminalCellNat
    change n % p * p ^ (N - 1) + p * (n % p ^ (N - 1) / p) + n % p = n
    simpa only [heq] using hdecomp.symm
  · rintro ⟨i, rfl⟩
    refine ⟨terminalCellNat_lt_modulus hN i, ?_⟩
    rw [terminalCellNat_mod_p hN]
    unfold terminalCellNat
    rw [terminal_top_power hN]
    exact block_digit_div hp (pow_pos hp _) i.2.isLt i.1.isLt

/-- Title: `Exact population of the first and last digit support`. -/
theorem terminal_digit_support_card {p N : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    (terminalDigitSupport p N).card = p ^ (N - 1) := by
  rw [terminal_digit_support_eq hp hN]
  exact terminalCollisionSupport_card hp hN

/-- Title: `The formal endpoint count is twice the actual support population`. -/
theorem terminal_formal_boundary_card {p N : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    terminalFormalBoundarySize p N = 2 * (terminalDigitSupport p N).card := by
  rw [terminal_digit_support_card hp hN]
  rfl

/-- The first and the `k`th digits of an ambient word of length `k+s`. -/
def leadingDigitWeight (p k s : ℕ) (x : ZMod (p ^ k * p ^ s)) : ℂ :=
  if x.val / p ^ (s + (k - 1)) = (x.val / p ^ s) % p then 1 else 0

/-- Title: `The actual leading-lag support is a block lift`. -/
theorem leading_digit_block_lift {p k s : ℕ} [NeZero (p ^ k)]
    [NeZero (p ^ k * p ^ s)] (hp : 0 < p) :
    leadingDigitWeight p k s = blockLiftWeight (L := p ^ s) (terminalDigitWeight p k) := by
  funext x
  have hlt : x.val / p ^ s < p ^ k := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp _)]
    exact x.val_lt
  simp only [leadingDigitWeight, blockLiftWeight, terminalDigitWeight,
    ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.div_div_eq_div_mul, ← pow_add]

/-- Title: `All ordinary higher-level fluxes of a leading-lag support vanish`. -/
theorem leading_digit_flux_zero {p k s : ℕ} [NeZero (p ^ k)]
    [NeZero (p ^ k * p ^ s)] (hp : p.Prime) (hk : 2 ≤ k) (hs : 0 < s)
    (χ : Character (p ^ k * p ^ s)) : cellBoundaryFlux (leadingDigitWeight p k s) χ = 0 := by
  rw [leading_digit_block_lift hp.pos, cellBoundaryFlux_eq_ordinaryBoundaryFlux]
  apply no_unit_boundary_flux
  intro u
  by_contra hn
  have hpL : p ∣ p ^ s := dvd_pow_self p hs.ne'
  exact blockLiftBoundary_nonunit_of_prime_dilation hp
    (hp.two_le.trans (Nat.le_pow (by omega : 0 < k))) (pow_pos hp.pos _) hpL
    (terminalDigitWeight p k) u.val hn (dvd_mul_of_dvd_right hpL _) u.isUnit

/-- Title: `Primitive higher-conductor carry transforms of leading-lag supports vanish`. -/
theorem leading_digit_primitive_transform_zero {p k s : ℕ} [NeZero (p ^ k)]
    [NeZero (p ^ k * p ^ s)] (hp : p.Prime) (hk : 2 ≤ k) (hs : 0 < s)
    {χ : Character (p ^ k * p ^ s)} (hχ : χ.IsPrimitive) :
    carryTransform (leadingDigitWeight p k s) χ = 0 := by
  rw [leading_digit_block_lift hp.pos]
  exact primitiveTransform_blockLift_zero hp
    (hp.two_le.trans (Nat.le_pow (by omega : 0 < k))) (pow_pos hp.pos _)
    (dvd_pow_self p hs.ne') _ hχ

end NField.Alignment.TerminalSupportSource
