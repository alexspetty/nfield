/-
Author: Alexander S. Petty
-/

import NField.Alignment.SupportedDenominators

/-!
# Canonical supported and rough decomposition

Every positive denominator has a unique factorization into its largest divisor
supported by the base and a complementary factor coprime to the base.  This is
the canonical arithmetic decomposition used by synchronized alignment.
-/

namespace NField.Alignment

/-- The largest divisor of `n` supported by `b`. -/
noncomputable def supportedPart (b n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => Supported b m ∧ m ∣ n) n

/-- The factor remaining after the supported part is removed. -/
noncomputable def roughPart (b n : ℕ) : ℕ :=
  n / supportedPart b n

theorem supportedPart_spec {b n : ℕ} (hn : 0 < n) :
    Supported b (supportedPart b n) ∧ supportedPart b n ∣ n := by
  classical
  unfold supportedPart
  exact Nat.findGreatest_spec (P := fun m => Supported b m ∧ m ∣ n)
    (m := 1) (n := n) hn ⟨supported_one b, one_dvd n⟩

theorem supportedPart_supported {b n : ℕ} (hn : 0 < n) :
    Supported b (supportedPart b n) :=
  (supportedPart_spec hn).1

theorem supportedPart_dvd {b n : ℕ} (hn : 0 < n) :
    supportedPart b n ∣ n :=
  (supportedPart_spec hn).2

theorem supportedPart_pos {b n : ℕ} (hn : 0 < n) :
    0 < supportedPart b n := by
  classical
  unfold supportedPart
  rw [Nat.findGreatest_pos]
  exact ⟨1, by omega, by omega, supported_one b, one_dvd n⟩

/-- Every supported divisor is bounded by the canonical supported part. -/
theorem supportedDivisor_le_supportedPart {b n d : ℕ} (hn : 0 < n)
    (hdSupported : Supported b d) (hdn : d ∣ n) :
    d ≤ supportedPart b n := by
  classical
  unfold supportedPart
  exact Nat.le_findGreatest (Nat.le_of_dvd hn hdn) ⟨hdSupported, hdn⟩

/-- The canonical factors multiply back to the original positive denominator. -/
theorem roughPart_mul_supportedPart {b n : ℕ} (hn : 0 < n) :
    roughPart b n * supportedPart b n = n := by
  unfold roughPart
  exact Nat.div_mul_cancel (supportedPart_dvd hn)

theorem roughPart_pos {b n : ℕ} (hn : 0 < n) :
    0 < roughPart b n := by
  rw [roughPart]
  exact Nat.div_pos (Nat.le_of_dvd hn (supportedPart_dvd hn))
    (supportedPart_pos hn)

/-- The rough part is coprime to the base.  Otherwise adjoining a common prime
to the supported part would produce a larger supported divisor of `n`. -/
theorem roughPart_coprime_base {b n : ℕ} (hn : 0 < n) :
    Nat.Coprime (roughPart b n) b := by
  by_contra hnot
  obtain ⟨p, hp, hpRough, hpBase⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  let m := supportedPart b n
  have hmPos : 0 < m := supportedPart_pos hn
  have hmSupported : Supported b m := supportedPart_supported hn
  have hpmSupported : Supported b (p * m) :=
    supported_mul (supported_of_dvd_base hpBase) hmSupported
  have hdecomp : roughPart b n * m = n := by
    simpa [m] using roughPart_mul_supportedPart (b := b) hn
  have hpmDvd : p * m ∣ n := by
    obtain ⟨c, hc⟩ := hpRough
    refine ⟨c, ?_⟩
    rw [← hdecomp, hc]
    ring
  have hle : p * m ≤ m := by
    simpa [m] using supportedDivisor_le_supportedPart hn hpmSupported hpmDvd
  have hpTwo : 2 ≤ p := hp.two_le
  nlinarith

/-- A positive denominator is supported exactly when its rough part is one. -/
theorem roughPart_eq_one_iff_supported {b n : ℕ} (hn : 0 < n) :
    roughPart b n = 1 ↔ Supported b n := by
  constructor
  · intro ht
    have hdecomp := roughPart_mul_supportedPart (b := b) hn
    rw [ht, one_mul] at hdecomp
    rw [← hdecomp]
    exact supportedPart_supported hn
  · intro hnSupported
    have hpart : supportedPart b n = n := by
      apply le_antisymm
      · exact Nat.le_of_dvd hn (supportedPart_dvd hn)
      · exact supportedDivisor_le_supportedPart hn hnSupported dvd_rfl
    rw [roughPart, hpart, Nat.div_self hn]

/-- A supplied supported-coprime product has the manuscript's canonical
supported part. -/
theorem supportedPart_mul_of_supported_coprime {b t m : ℕ}
    (ht : 0 < t) (hm : 0 < m) (hmSupported : Supported b m)
    (hcop : Nat.Coprime t b) :
    supportedPart b (t * m) = m := by
  have htm : 0 < t * m := Nat.mul_pos ht hm
  apply le_antisymm
  · have hpartSupported := supportedPart_supported (b := b) htm
    have hpartDvd := supportedPart_dvd (b := b) htm
    rcases hpartSupported with ⟨D, hD⟩
    have hcopPow : Nat.Coprime t (b ^ D) := hcop.pow_right D
    have hcopPart : Nat.Coprime (supportedPart b (t * m)) t :=
      (Nat.Coprime.of_dvd_right hD hcopPow).symm
    have hdivM : supportedPart b (t * m) ∣ m :=
      (hcopPart.dvd_mul_left).mp hpartDvd
    exact Nat.le_of_dvd hm hdivM
  · exact supportedDivisor_le_supportedPart htm hmSupported (dvd_mul_left m t)

/-- The complementary factor of a supplied supported-coprime product is the
supplied rough factor. -/
theorem roughPart_mul_of_supported_coprime {b t m : ℕ}
    (ht : 0 < t) (hm : 0 < m) (hmSupported : Supported b m)
    (hcop : Nat.Coprime t b) :
    roughPart b (t * m) = t := by
  rw [roughPart, supportedPart_mul_of_supported_coprime ht hm hmSupported hcop]
  exact Nat.mul_div_left t hm

/-- The supported-coprime representation of a positive denominator is unique. -/
theorem supported_coprime_decomposition_unique {b n t m : ℕ}
    (hn : n = t * m) (ht : 0 < t) (hm : 0 < m)
    (hmSupported : Supported b m) (hcop : Nat.Coprime t b) :
    supportedPart b n = m ∧ roughPart b n = t := by
  subst n
  exact ⟨supportedPart_mul_of_supported_coprime ht hm hmSupported hcop,
    roughPart_mul_of_supported_coprime ht hm hmSupported hcop⟩

/-- The multiplicative period of a base modulo an arbitrary coprime positive
modulus. -/
noncomputable def coprimeBasePeriod (b t : ℕ) (hcop : Nat.Coprime t b) : ℕ :=
  orderOf (ZMod.unitOfCoprime b hcop.symm)

theorem coprimeBasePeriod_pos {b t : ℕ} (hcop : Nat.Coprime t b) :
    0 < coprimeBasePeriod b t hcop := by
  unfold coprimeBasePeriod
  exact orderOf_pos (ZMod.unitOfCoprime b hcop.symm)

theorem pow_coprimeBasePeriod_mod_eq_one {b t : ℕ}
    (hcop : Nat.Coprime t b) :
    b ^ coprimeBasePeriod b t hcop % t = 1 % t := by
  let u : (ZMod t)ˣ := ZMod.unitOfCoprime b hcop.symm
  have hpow : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  have hcoe : ((u : ZMod t) ^ orderOf u) = 1 :=
    congrArg (fun z : (ZMod t)ˣ => (z : ZMod t)) hpow
  have hcast : ((b ^ orderOf u : ℕ) : ZMod t) = ((1 : ℕ) : ZMod t) := by
    simpa [u, ZMod.coe_unitOfCoprime] using hcoe
  have hmod := (ZMod.natCast_eq_natCast_iff' (b ^ orderOf u) 1 t).mp hcast
  simpa [coprimeBasePeriod, u] using hmod

/-- The multiplicative period modulo a divisor of the rough part divides the
full rough-part period. -/
theorem divisor_coprimeBasePeriod_dvd {b t d : ℕ}
    (hcop : Nat.Coprime t b) (hd : d ∣ t) :
    coprimeBasePeriod b d (Nat.Coprime.of_dvd_left hd hcop) ∣
      coprimeBasePeriod b t hcop := by
  let L := coprimeBasePeriod b t hcop
  let hcopD : Nat.Coprime d b := Nat.Coprime.of_dvd_left hd hcop
  let u : (ZMod d)ˣ := ZMod.unitOfCoprime b hcopD.symm
  change orderOf u ∣ L
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  have hmodT : b ^ L % t = 1 % t := by
    simpa [L] using pow_coprimeBasePeriod_mod_eq_one hcop
  have hmodeqT : b ^ L ≡ 1 [MOD t] := by
    exact hmodT
  have hmodeqD : b ^ L ≡ 1 [MOD d] := hmodeqT.of_dvd hd
  have hcast := (ZMod.natCast_eq_natCast_iff' (b ^ L) 1 d).mpr hmodeqD
  simpa [u, ZMod.coe_unitOfCoprime] using hcast

end NField.Alignment
