/-
Copyright 2020-2026 Alexander S. Petty.
SPDX-License-Identifier: Apache-2.0
Author: Alexander S. Petty
-/

import NField.Alignment.CollisionPrimitivePairAmplitude

/-!
# The literal primitive-pair conservation and normalization displays

Both positive double series are summable. Their symmetrization is an
actual permutation of the address pair, before identifying total unit mass.
-/

noncomputable section
set_option autoImplicit false

namespace NField.Alignment.CollisionPrimitiveMassDisplays

open scoped BigOperators Classical
open CollisionPrimitivePairAmplitude CollisionMassReadout CollisionAmplitudeRefinement

def pairTreePotential (a b : ℕ) : ℝ :=
  ((a : ℝ)+(b : ℝ))/((a : ℝ)^2*(b : ℝ)^2)

def primitiveAddressMass (p : ℕ×ℕ) : ℝ :=
  if 0<p.1 ∧ 0<p.2 ∧ p.1.Coprime p.2 then
    1/((p.1 : ℝ)*((p.1+p.2 : ℕ) : ℝ)^2) else 0

def positiveAddressMass (p : ℕ×ℕ) : ℝ := primitiveAddressMass (p.1+1,p.2+1)
def positivePairMass (p : ℕ×ℕ) : ℝ := primitivePairMass (p.1+1,p.2+1)

theorem pairTreePotential_conservation {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    pairTreePotential a b-pairTreePotential a (a+b)-pairTreePotential (a+b) b=
      1/((a : ℝ)*(b : ℝ)*((a+b : ℕ) : ℝ)) := by
  have haR : (a : ℝ)≠0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ)≠0 := by exact_mod_cast hb.ne'
  have hab : (a : ℝ)+(b : ℝ)≠0 := by positivity
  unfold pairTreePotential
  push_cast
  field_simp
  ring

theorem primitiveAddressMass_nonneg (p : ℕ×ℕ) : 0 ≤ primitiveAddressMass p := by
  unfold primitiveAddressMass
  split_ifs <;> positivity

theorem primitivePairMass_symmetrization (p : ℕ×ℕ) :
    primitivePairMass p=primitiveAddressMass p+primitiveAddressMass p.swap := by
  rcases p with ⟨a,b⟩
  by_cases ha : a=0
  · subst a; simp [primitiveAddressMass]
  by_cases hb : b=0
  · subst b; simp [primitiveAddressMass]
  have ha0 : 0<a := Nat.pos_of_ne_zero ha
  have hb0 : 0<b := Nat.pos_of_ne_zero hb
  have haR : (a : ℝ)≠0 := by exact_mod_cast ha
  have hbR : (b : ℝ)≠0 := by exact_mod_cast hb
  have hab : (a : ℝ)+(b : ℝ)≠0 := by positivity
  by_cases hc : a.Coprime b
  · dsimp only [primitivePairMass,primitiveAddressMass,Prod.swap]
    rw [if_pos hc,if_pos (show 0<a ∧ 0<b ∧ a.Coprime b from ⟨ha0,hb0,hc⟩),
      if_pos (show 0<b ∧ 0<a ∧ b.Coprime a from ⟨hb0,ha0,hc.symm⟩)]
    push_cast
    field_simp
    ring
  · have hc' : ¬b.Coprime a := by simpa only [Nat.coprime_comm] using hc
    simp [primitivePairMass,primitiveAddressMass,ha0,hb0,hc,hc']

theorem primitiveAddressMass_summable : Summable primitiveAddressMass := by
  apply Summable.of_nonneg_of_le primitiveAddressMass_nonneg _ primitivePairMass_summable
  intro p
  rw [primitivePairMass_symmetrization]
  exact le_add_of_nonneg_right (primitiveAddressMass_nonneg p.swap)

theorem primitiveAddressMass_swap_summable : Summable (fun p : ℕ×ℕ => primitiveAddressMass p.swap) :=
  primitiveAddressMass_summable.comp_injective (Equiv.prodComm ℕ ℕ).injective

theorem primitiveAddressMass_swap_tsum :
    (∑' p : ℕ×ℕ, primitiveAddressMass p.swap)=∑' p : ℕ×ℕ, primitiveAddressMass p :=
  (Equiv.prodComm ℕ ℕ).tsum_eq primitiveAddressMass

theorem primitivePairMass_total : (∑' p : ℕ×ℕ, primitivePairMass p)=2 := by
  have h := amplitude_primitive_pair 1
  simp only [amplitude_one,primitivePairGate,one_dvd,if_true] at h
  linarith

theorem primitiveAddressMass_total : (∑' p : ℕ×ℕ, primitiveAddressMass p)=1 := by
  have h := primitivePairMass_total
  simp_rw [primitivePairMass_symmetrization] at h
  rw [primitiveAddressMass_summable.tsum_add primitiveAddressMass_swap_summable,
    primitiveAddressMass_swap_tsum] at h
  linarith

theorem positiveAddressMass_formula (p : ℕ×ℕ) : positiveAddressMass p=
    if (p.1+1).Coprime (p.2+1) then
      1/(((p.1+1 : ℕ) : ℝ)*((p.1+1+p.2+1 : ℕ) : ℝ)^2) else 0 := by
  simp [positiveAddressMass,primitiveAddressMass,Nat.add_assoc]

theorem positivePairMass_formula (p : ℕ×ℕ) : positivePairMass p=
    if (p.1+1).Coprime (p.2+1) then
      1/(((p.1+1 : ℕ) : ℝ)*((p.2+1 : ℕ) : ℝ)*((p.1+1+p.2+1 : ℕ) : ℝ)) else 0 := by
  simp [positivePairMass,primitivePairMass,Nat.add_assoc]

theorem positive_pair_shift_injective :
    Function.Injective (fun p : ℕ×ℕ => (p.1+1,p.2+1)) := by
  intro p r h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (by dsimp at h1; omega) (by dsimp at h2; omega)

theorem positiveAddressMass_summable : Summable positiveAddressMass :=
  primitiveAddressMass_summable.comp_injective positive_pair_shift_injective

theorem positivePairMass_summable : Summable positivePairMass :=
  primitivePairMass_summable.comp_injective positive_pair_shift_injective

theorem positiveAddressMass_tsum :
    (∑' p : ℕ×ℕ, positiveAddressMass p)=∑' p : ℕ×ℕ, primitiveAddressMass p := by
  apply positive_pair_shift_injective.tsum_eq
  intro p hp
  have hp1 : 0<p.1 := by
    by_contra h
    have hz : p.1=0 := by omega
    simp [Function.mem_support,primitiveAddressMass,hz] at hp
  have hp2 : 0<p.2 := by
    by_contra h
    have hz : p.2=0 := by omega
    simp [Function.mem_support,primitiveAddressMass,hz] at hp
  exact ⟨(p.1-1,p.2-1),Prod.ext (by dsimp; omega) (by dsimp; omega)⟩

theorem positivePairMass_tsum :
    (∑' p : ℕ×ℕ, positivePairMass p)=∑' p : ℕ×ℕ, primitivePairMass p := by
  have h := primitivePairGate_positive_series 1
  simpa only [primitivePairGate,one_dvd,if_true,positivePairMass] using h

theorem literal_primitive_mass_normalization :
    Summable positiveAddressMass ∧ Summable positivePairMass ∧
    (∑' k : ℕ, CollisionRemainderDynamics.collisionWeight k)=(∑' p : ℕ×ℕ, positiveAddressMass p) ∧
    (∑' p : ℕ×ℕ, positiveAddressMass p)=(1/2 : ℝ)*(∑' p : ℕ×ℕ, positivePairMass p) ∧
    (1/2 : ℝ)*(∑' p : ℕ×ℕ, positivePairMass p)=1 := by
  refine ⟨positiveAddressMass_summable,positivePairMass_summable,?_,?_,?_⟩ <;>
    norm_num [collisionWeight_tsum,positiveAddressMass_tsum,positivePairMass_tsum,
      primitiveAddressMass_total,primitivePairMass_total]

end NField.Alignment.CollisionPrimitiveMassDisplays
