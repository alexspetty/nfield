/-
Author: Alexander S. Petty
-/

/-!
Stable Lean definitions for the elementary digit-collision object.

This module starts upstream of the certificate layer.  It defines the digit bin
and the finite collision count directly from long division arithmetic.  The
first examples are intentionally tiny: they check that Lean is computing from
these definitions rather than trusting a precomputed table.
-/

namespace NField.CollisionDefinition

/-- The long-division digit bin: `floor(b*r/p)`. -/
def digitBin (b p r : Nat) : Nat :=
  (b * r) / p

/-- The image of a remainder under multiplication by `a`, reduced modulo `p`. -/
def transportedRemainder (p a r : Nat) : Nat :=
  (a * r) % p

/-- Transported remainders always land back inside the modulus. -/
theorem transportedRemainder_lt_of_pos (p a r : Nat) (hp : 0 < p) :
    transportedRemainder p a r < p := by
  unfold transportedRemainder
  exact Nat.mod_lt (a * r) hp

/-- Transport depends only on the residue class of the input remainder. -/
theorem transportedRemainder_mod_right (p a r : Nat) :
    transportedRemainder p a (r % p) = transportedRemainder p a r := by
  unfold transportedRemainder
  simp [Nat.mul_mod]

/-- Transport depends only on the residue class of the multiplier. -/
theorem transportedRemainder_mod_left (p a r : Nat) :
    transportedRemainder p (a % p) r = transportedRemainder p a r := by
  unfold transportedRemainder
  simp [Nat.mul_mod]

/-- Composing two transports is the same as transport by the product multiplier. -/
theorem transportedRemainder_compose (p a c r : Nat) :
    transportedRemainder p a (transportedRemainder p c r) =
      transportedRemainder p (a * c) r := by
  unfold transportedRemainder
  simp [Nat.mul_mod, Nat.mul_left_comm, Nat.mul_comm]

/-- Transport by the identity multiplier is reduction to the residue class. -/
theorem transportedRemainder_one (p r : Nat) :
    transportedRemainder p 1 r = r % p := by
  unfold transportedRemainder
  simp

/-- A multiplier with a modular inverse gives an inverse transport on residue classes. -/
theorem transportedRemainder_inverse_of_mul_mod_one (p a c r : Nat)
    (h : (a * c) % p = 1 % p) :
    transportedRemainder p a (transportedRemainder p c r) = r % p := by
  rw [transportedRemainder_compose]
  rw [← transportedRemainder_mod_left p (a * c) r]
  rw [h]
  rw [transportedRemainder_mod_left p 1 r]
  exact transportedRemainder_one p r

/-- A transport with a modular inverse is injective on representatives below the modulus. -/
theorem transportedRemainder_injective_of_inverse (p a c x y : Nat)
    (h : (c * a) % p = 1 % p) (hx : x < p) (hy : y < p)
    (heq : transportedRemainder p a x = transportedRemainder p a y) :
    x = y := by
  have hxinv := transportedRemainder_inverse_of_mul_mod_one p c a x h
  have hyinv := transportedRemainder_inverse_of_mul_mod_one p c a y h
  have htransport :
      transportedRemainder p c (transportedRemainder p a x) =
        transportedRemainder p c (transportedRemainder p a y) := by
    rw [heq]
  have hmod : x % p = y % p := by
    rw [← hxinv, htransport, hyinv]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod
  exact hmod

/-- Transport by a multiplier with an inverse preserves duplicate-free residue lists. -/
theorem transportedRemainder_map_nodup_of_inverse (p a c : Nat) (xs : List Nat)
    (h : (c * a) % p = 1 % p)
    (hxs : ∀ x, x ∈ xs → x < p)
    (hnodup : xs.Nodup) :
    (xs.map (transportedRemainder p a)).Nodup := by
  induction xs with
  | nil =>
      exact List.nodup_nil
  | cons x xs ih =>
      have hnodup_parts := List.nodup_cons.mp hnodup
      have hx_not_mem : ¬ x ∈ xs := hnodup_parts.left
      have hxs_tail : ∀ y, y ∈ xs → y < p := by
        intro y hy
        exact hxs y (by simp [hy])
      have hmapped_tail : (xs.map (transportedRemainder p a)).Nodup :=
        ih hxs_tail hnodup_parts.right
      exact List.nodup_cons.mpr ⟨by
        intro hmem
        have hw := List.mem_map.mp hmem
        rcases hw with ⟨y, hy, heq⟩
        have hxy : x = y := transportedRemainder_injective_of_inverse p a c x y h
          (hxs x (by simp)) (hxs_tail y hy) heq.symm
        exact hx_not_mem (by rw [hxy]; exact hy), hmapped_tail⟩

/-- Unit transport maps the canonical residue range to a duplicate-free list. -/
theorem transportedRemainder_range_nodup_of_inverse (p a c : Nat)
    (h : (c * a) % p = 1 % p) :
    ((List.range p).map (transportedRemainder p a)).Nodup := by
  exact transportedRemainder_map_nodup_of_inverse p a c (List.range p) h
    (by
      intro x hx
      exact List.mem_range.mp hx)
    List.nodup_range

/-- Unit transport of the canonical range hits every residue below the modulus. -/
theorem transportedRemainder_range_mem_of_inverse (p a c y : Nat)
    (h : (a * c) % p = 1 % p) (hy : y < p) :
    y ∈ (List.range p).map (transportedRemainder p a) := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le y) hy
  let x := transportedRemainder p c y
  have hx : x < p := transportedRemainder_lt_of_pos p c y hp
  have hxmem : x ∈ List.range p := List.mem_range.mpr hx
  have hxy : transportedRemainder p a x = y := by
    unfold x
    rw [transportedRemainder_inverse_of_mul_mod_one p a c y h]
    exact Nat.mod_eq_of_lt hy
  have hmem : transportedRemainder p a x ∈
      (List.range p).map (transportedRemainder p a) :=
    List.mem_map_of_mem hxmem
  rw [hxy] at hmem
  exact hmem

/-- Unit transport of the canonical range has exactly the residues below the modulus as image. -/
theorem transportedRemainder_range_mem_iff_of_inverse (p a c y : Nat)
    (h : (a * c) % p = 1 % p) :
    y ∈ (List.range p).map (transportedRemainder p a) ↔ y < p := by
  constructor
  · intro hy_mem
    have hw := List.mem_map.mp hy_mem
    rcases hw with ⟨x, hx, hy_eq⟩
    have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le x) (List.mem_range.mp hx)
    rw [← hy_eq]
    exact transportedRemainder_lt_of_pos p a x hp
  · intro hy
    exact transportedRemainder_range_mem_of_inverse p a c y h hy

/-- Duplicate-free lists with the same membership are permutations. -/
theorem nodup_perm_of_mem_iff (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  rw [hx.count, hy.count]
  by_cases hzx : z ∈ xs
  · have hzy : z ∈ ys := (hm z).mp hzx
    simp [hzx, hzy]
  · have hzy : z ∉ ys := by
      intro yy
      exact hzx ((hm z).mpr yy)
    simp [hzx, hzy]

/-- Sum an integer-valued function over a finite residue list. -/
def listSumInt (F : Nat → Int) (xs : List Nat) : Int :=
  xs.foldr (fun r acc => F r + acc) 0

/-- Finite integer sums are unchanged by permuting the list of representatives. -/
theorem listSumInt_perm (F : Nat → Int) {xs ys : List Nat} (h : xs.Perm ys) :
    listSumInt F xs = listSumInt F ys := by
  induction h with
  | nil => rfl
  | cons x h ih =>
      unfold listSumInt
      simp [List.foldr]
      unfold listSumInt at ih
      exact ih
  | swap x y l =>
      unfold listSumInt
      simp [List.foldr]
      omega
  | trans h1 h2 ih1 ih2 =>
      exact Eq.trans ih1 ih2

/-- Summing over a mapped list is the same as composing the summand with the map. -/
theorem listSumInt_map (F : Nat → Int) (g : Nat → Nat) (xs : List Nat) :
    listSumInt F (xs.map g) = listSumInt (fun x => F (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      unfold listSumInt
      simp [List.foldr]
      unfold listSumInt at ih
      exact ih

/-- Unit transport of the canonical range is a permutation of the canonical range. -/
theorem transportedRemainder_range_perm_of_inverse (p a c : Nat)
    (h : (a * c) % p = 1 % p) :
    ((List.range p).map (transportedRemainder p a)).Perm (List.range p) := by
  have hca : (c * a) % p = 1 % p := by
    simpa [Nat.mul_comm] using h
  exact nodup_perm_of_mem_iff
    ((List.range p).map (transportedRemainder p a))
    (List.range p)
    (transportedRemainder_range_nodup_of_inverse p a c hca)
    List.nodup_range
    (by
      intro z
      rw [transportedRemainder_range_mem_iff_of_inverse p a c z h]
      exact Iff.symm List.mem_range)

/-- Reindexing by unit transport does not change a finite sum over the residue range. -/
theorem listSumInt_transport_range_eq_range (p a c : Nat) (F : Nat → Int)
    (h : (a * c) % p = 1 % p) :
    listSumInt F ((List.range p).map (transportedRemainder p a)) =
      listSumInt F (List.range p) := by
  exact listSumInt_perm F (transportedRemainder_range_perm_of_inverse p a c h)

/-- Whether `r` and its transported image lie in the same digit bin. -/
def sameDigitBin (b p a r : Nat) : Bool :=
  digitBin b p r == digitBin b p (transportedRemainder p a r)

/-- Integer indicator for one digit-bin collision. -/
def collisionIndicator (b p a r : Nat) : Int :=
  if sameDigitBin b p a r then 1 else 0

/-- Opening `sameDigitBin` at a transported argument composes the transport multipliers. -/
theorem sameDigitBin_transport_argument_product (b p a d r : Nat) :
    sameDigitBin b p d (transportedRemainder p a r) =
      (digitBin b p (transportedRemainder p a r) ==
        digitBin b p (transportedRemainder p (d * a) r)) := by
  unfold sameDigitBin
  rw [transportedRemainder_compose]

/-- Opening the collision indicator at a transported argument composes the transport multipliers. -/
theorem collisionIndicator_transport_argument_product (b p a d r : Nat) :
    collisionIndicator b p d (transportedRemainder p a r) =
      if digitBin b p (transportedRemainder p a r) ==
          digitBin b p (transportedRemainder p (d * a) r) then 1 else 0 := by
  unfold collisionIndicator
  rw [sameDigitBin_transport_argument_product]

/-- Unit transport reindexing preserves finite sums of the collision indicator. -/
theorem collisionIndicator_sum_reindex_transport_range (b p a c d : Nat)
    (h : (a * c) % p = 1 % p) :
    listSumInt (fun r => collisionIndicator b p d r)
        ((List.range p).map (transportedRemainder p a)) =
      listSumInt (fun r => collisionIndicator b p d r) (List.range p) := by
  exact listSumInt_transport_range_eq_range p a c
    (fun r => collisionIndicator b p d r) h

/-- Unit transport can be moved inside the collision-indicator summand. -/
theorem collisionIndicator_sum_transport_argument_eq_range (b p a c d : Nat)
    (h : (a * c) % p = 1 % p) :
    listSumInt
        (fun r => collisionIndicator b p d (transportedRemainder p a r))
        (List.range p) =
      listSumInt (fun r => collisionIndicator b p d r) (List.range p) := by
  rw [← listSumInt_map (fun r => collisionIndicator b p d r)
    (transportedRemainder p a) (List.range p)]
  exact collisionIndicator_sum_reindex_transport_range b p a c d h

/-- Finite collision count over an explicit list of remainders. -/
def collisionCountOnList (b p a : Nat) (remainders : List Nat) : Int :=
  remainders.foldr (fun r acc => collisionIndicator b p a r + acc) 0

/-- Collision count over the canonical residue range. -/
def collisionCountRange (b p a : Nat) : Int :=
  listSumInt (fun r => collisionIndicator b p a r) (List.range p)

/-- Transported-argument reindexing, stated in collision-count vocabulary. -/
theorem collisionCountRange_reindex_transport_argument (b p a c d : Nat)
    (h : (a * c) % p = 1 % p) :
    listSumInt
        (fun r => collisionIndicator b p d (transportedRemainder p a r))
        (List.range p) =
      collisionCountRange b p d := by
  unfold collisionCountRange
  exact collisionIndicator_sum_transport_argument_eq_range b p a c d h

/-- Expanded transported-count form: the summand compares the two transported digit bins. -/
theorem collisionCountRange_transport_expanded_product (b p a c d : Nat)
    (h : (a * c) % p = 1 % p) :
    listSumInt
      (fun r =>
        if digitBin b p (transportedRemainder p a r) ==
            digitBin b p (transportedRemainder p (d * a) r) then 1 else 0)
      (List.range p) =
    collisionCountRange b p d := by
  rw [← collisionCountRange_reindex_transport_argument b p a c d h]
  have hfun :
      (fun r =>
        if digitBin b p (transportedRemainder p a r) ==
            digitBin b p (transportedRemainder p (d * a) r) then 1 else 0) =
      (fun r => collisionIndicator b p d (transportedRemainder p a r)) := by
    funext r
    exact (collisionIndicator_transport_argument_product b p a d r).symm
  rw [hfun]

/-- The identity multiplier preserves the digit bin of any remainder below the modulus. -/
theorem sameDigitBin_identity_of_lt (b p r : Nat) (hr : r < p) :
    sameDigitBin b p 1 r = true := by
  unfold sameDigitBin transportedRemainder
  have hmod : (1 * r) % p = r := by
    simpa using Nat.mod_eq_of_lt hr
  rw [hmod]
  simp

/-- The identity multiplier contributes one collision for any remainder below the modulus. -/
theorem collisionIndicator_identity_of_lt (b p r : Nat) (hr : r < p) :
    collisionIndicator b p 1 r = 1 := by
  unfold collisionIndicator
  rw [sameDigitBin_identity_of_lt b p r hr]
  simp

/-- On any list of remainders below `p`, the identity multiplier collides on every entry. -/
theorem collisionCount_identity_of_all_lt (b p : Nat) (remainders : List Nat)
    (h : ∀ r, r ∈ remainders → r < p) :
    collisionCountOnList b p 1 remainders = Int.ofNat remainders.length := by
  induction remainders with
  | nil => rfl
  | cons r rs ih =>
      unfold collisionCountOnList
      simp [List.foldr]
      rw [collisionIndicator_identity_of_lt b p r (h r (by simp))]
      have hrs : ∀ x, x ∈ rs → x < p := by
        intro x hx
        exact h x (by simp [hx])
      unfold collisionCountOnList at ih
      rw [ih hrs]
      rw [Int.add_comm]
      simp

/-- The zero multiplier sends every remainder to zero. -/
theorem transportedRemainder_zero (p r : Nat) :
    transportedRemainder p 0 r = 0 := by
  unfold transportedRemainder
  simp

/-- For multiplier zero, same-bin collision is the same as lying in digit bin zero. -/
theorem sameDigitBin_zero_eq (b p r : Nat) :
    sameDigitBin b p 0 r = (digitBin b p r == 0) := by
  unfold sameDigitBin
  rw [transportedRemainder_zero]
  unfold digitBin
  simp

/-- For multiplier zero, the collision indicator is exactly the bin-zero indicator. -/
theorem collisionIndicator_zero_eq (b p r : Nat) :
    collisionIndicator b p 0 r = if digitBin b p r == 0 then 1 else 0 := by
  unfold collisionIndicator
  rw [sameDigitBin_zero_eq]

/-- In base 10 modulo 7, remainder `1` lies in digit bin `1`. -/
theorem digitBin_10_7_1 : digitBin 10 7 1 = 1 := by
  rfl

/-- Multiplication by `2` sends remainder `1` modulo `7` to remainder `2`. -/
theorem transportedRemainder_7_2_1 : transportedRemainder 7 2 1 = 2 := by
  rfl

/-- The identity multiplier creates a collision for remainder `4`. -/
theorem collisionIndicator_identity_10_7_4 :
    collisionIndicator 10 7 1 4 = 1 := by
  rfl

/-- Multiplier `2` does not keep remainder `1` in the same base-10 digit bin modulo `7`. -/
theorem collisionIndicator_noncollision_10_7_2_1 :
    collisionIndicator 10 7 2 1 = 0 := by
  rfl

/-- The identity multiplier collides on every listed remainder in this tiny example. -/
theorem collisionCount_identity_10_7_first3 :
    collisionCountOnList 10 7 1 [1, 2, 3] = 3 := by
  rfl

/-- Multiplier `2` has no collisions on the first three nonzero remainders modulo `7`. -/
theorem collisionCount_multiplier2_10_7_first3 :
    collisionCountOnList 10 7 2 [1, 2, 3] = 0 := by
  rfl

end NField.CollisionDefinition
