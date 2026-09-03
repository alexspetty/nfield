/-
Author: Alexander S. Petty
-/

import NField.Alignment.SecondaryCapacityLedger

/-!
# Reduced harmonic Möbius coordinates

The exact coprime-to-unrestricted harmonic conversion used by the continuous
secondary term.  The proof expands the coprimality indicator by the Möbius
function and evaluates the multiples of each divisor without asymptotics.
-/

namespace NField.Alignment.ReducedHarmonicMobius

open scoped BigOperators ArithmeticFunction.Moebius
open NField.Alignment.SecondaryCapacityLedger

theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  change (∑ d ∈ n.divisors,
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d) = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.coe_moebius_mul_coe_zeta]
  simp [ArithmeticFunction.one_apply]

theorem coprime_indicator_moebius {a k : ℕ} (hk : 0 < k) :
    (if a.Coprime k then (1 : ℝ) else 0) =
      ∑ d ∈ k.divisors,
        if d ∣ a then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  have hfilter :
      {d ∈ k.divisors | d ∣ a} = (a.gcd k).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro hd
      exact ⟨Nat.dvd_gcd hd.2 hd.1.1,
        ne_zero_of_dvd_ne_zero hk.ne' (Nat.gcd_dvd_right a k)⟩
    · intro hd
      exact ⟨⟨hd.1.trans (Nat.gcd_dvd_right a k), hk.ne'⟩,
        hd.1.trans (Nat.gcd_dvd_left a k)⟩
  rw [hfilter]
  rw [sum_moebius_divisors]

theorem Ico_one_eq_Icc_one_pred {q : ℕ} (hq : 0 < q) :
    Finset.Ico 1 q = Finset.Icc 1 (q - 1) := by
  ext n
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- Multiples of `d` below `k` contribute a scaled harmonic number. -/
theorem reciprocal_multiples_sum
    {d k : ℕ} (hk : 0 < k) (hdk : d ∣ k) :
    (∑ a ∈ Finset.Ico 1 k,
        if d ∣ a then (a : ℝ)⁻¹ else 0) =
      (d : ℝ)⁻¹ * (harmonic (k / d - 1) : ℝ) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdk hk
  have hqpos : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk hdk) hdpos
  have hkd : d * (k / d) = k := Nat.mul_div_cancel' hdk
  rw [← Finset.sum_filter]
  calc
    (∑ a ∈ (Finset.Ico 1 k).filter fun a ↦ d ∣ a, (a : ℝ)⁻¹) =
        ∑ n ∈ Finset.Ico 1 (k / d), ((d * n : ℕ) : ℝ)⁻¹ := by
          symm
          apply Finset.sum_bij (fun n _ ↦ d * n)
          · intro n hn
            have hnI := Finset.mem_Ico.mp hn
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_Ico.mpr ⟨Nat.mul_pos hdpos hnI.1, ?_⟩,
              dvd_mul_right d n⟩
            rw [← hkd]
            exact (Nat.mul_lt_mul_left hdpos).2 hnI.2
          · intro n hn m hm hnm
            exact Nat.eq_of_mul_eq_mul_left hdpos hnm
          · intro a ha
            have haI := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
            have hda := (Finset.mem_filter.mp ha).2
            let n := a / d
            have hdn : d * n = a := Nat.mul_div_cancel' hda
            have hnpos : 0 < n := Nat.div_pos
              (Nat.le_of_dvd haI.1 hda) hdpos
            have hnq : n < k / d := by
              apply (Nat.div_lt_div_right hdpos.ne' hda hdk).2
              exact haI.2
            exact ⟨n, Finset.mem_Ico.mpr ⟨hnpos, hnq⟩, hdn⟩
          · intro n hn
            push_cast
            rw [mul_inv]
    _ = (d : ℝ)⁻¹ *
          ∑ n ∈ Finset.Ico 1 (k / d), (n : ℝ)⁻¹ := by
            simp_rw [Nat.cast_mul, mul_inv]
            rw [Finset.mul_sum]
    _ = (d : ℝ)⁻¹ * (harmonic (k / d - 1) : ℝ) := by
          rw [Ico_one_eq_Icc_one_pred hqpos, harmonic_eq_sum_Icc]
          push_cast
          rfl

/-- The manuscript identity
`Hₖ* = Σ_{d|k} μ(d) h_{k/d-1}/d`. -/
theorem reducedHarmonicStar_moebius
    {k : ℕ} (hk : 0 < k) :
    reducedHarmonicStar k =
      ∑ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          (harmonic (k / d - 1) : ℝ) := by
  unfold reducedHarmonicStar
  calc
    (∑ a ∈ (Finset.Ico 1 k).filter fun a ↦ a.Coprime k,
        (a : ℝ)⁻¹) =
        ∑ a ∈ Finset.Ico 1 k,
          (a : ℝ)⁻¹ * (if a.Coprime k then (1 : ℝ) else 0) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro a _ha
            by_cases hcop : a.Coprime k <;> simp [hcop]
    _ = ∑ a ∈ Finset.Ico 1 k,
          (a : ℝ)⁻¹ *
            ∑ d ∈ k.divisors,
              if d ∣ a then (ArithmeticFunction.moebius d : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro a _ha
            rw [← coprime_indicator_moebius hk]
    _ = ∑ d ∈ k.divisors,
          (ArithmeticFunction.moebius d : ℝ) *
            ∑ a ∈ Finset.Ico 1 k,
              if d ∣ a then (a : ℝ)⁻¹ else 0 := by
            rw [show
              (∑ a ∈ Finset.Ico 1 k,
                (a : ℝ)⁻¹ *
                  ∑ d ∈ k.divisors,
                    if d ∣ a then (ArithmeticFunction.moebius d : ℝ) else 0) =
              ∑ a ∈ Finset.Ico 1 k, ∑ d ∈ k.divisors,
                (ArithmeticFunction.moebius d : ℝ) *
                  (if d ∣ a then (a : ℝ)⁻¹ else 0) by
                    apply Finset.sum_congr rfl
                    intro a _ha
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro d _hd
                    by_cases hda : d ∣ a <;> simp [hda]
                    ring]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro d _hd
            rw [Finset.mul_sum]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
          rw [reciprocal_multiples_sum hk hdk]
          ring

/-- Divisor coordinates `(k,d)` with `1 ≤ k ≤ N` and `d | k`. -/
def divisorTriangle (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun kd ↦
    kd.2 ∣ kd.1

/-- Product coordinates `(d,n)` with `d*n ≤ N`. -/
def factorTriangle (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun dn ↦
    dn.1 * dn.2 ≤ N

def divisorToFactor (kd : ℕ × ℕ) : ℕ × ℕ :=
  (kd.2, kd.1 / kd.2)

theorem divisorToFactor_mem {N : ℕ} {kd : ℕ × ℕ}
    (hkd : kd ∈ divisorTriangle N) :
    divisorToFactor kd ∈ factorTriangle N := by
  rcases kd with ⟨k,d⟩
  have hbase := (Finset.mem_filter.mp hkd).1
  have hdiv := (Finset.mem_filter.mp hkd).2
  have hkI := Finset.mem_Icc.mp (Finset.mem_product.mp hbase).1
  have hdI := Finset.mem_Icc.mp (Finset.mem_product.mp hbase).2
  have hnpos : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hkI.1 hdiv) hdI.1
  have hnle : k / d ≤ N := (Nat.div_le_self k d).trans hkI.2
  unfold divisorToFactor factorTriangle
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr hdI, Finset.mem_Icc.mpr ⟨hnpos, hnle⟩⟩, ?_⟩
  rw [Nat.mul_div_cancel' hdiv]
  exact hkI.2

theorem divisorToFactor_injective {N : ℕ} :
    Set.InjOn divisorToFactor (↑(divisorTriangle N) : Set (ℕ × ℕ)) := by
  intro kd hkd uv huv heq
  rcases kd with ⟨k,d⟩
  rcases uv with ⟨l,e⟩
  have hkdiv := (Finset.mem_filter.mp hkd).2
  have hldiv := (Finset.mem_filter.mp huv).2
  have hde : d = e := congrArg Prod.fst heq
  have hquot : k / d = l / e := congrArg Prod.snd heq
  have hquot' : k / e = l / e := by simpa [hde] using hquot
  apply Prod.ext
  · calc
      k = d * (k / d) := (Nat.mul_div_cancel' hkdiv).symm
      _ = e * (l / e) := by rw [hde, hquot']
      _ = l := Nat.mul_div_cancel' hldiv
  · exact hde

theorem divisorToFactor_surjective {N : ℕ} :
    ∀ dn ∈ factorTriangle N, ∃ kd, ∃ _ : kd ∈ divisorTriangle N,
      divisorToFactor kd = dn := by
  intro dn hdn
  rcases dn with ⟨d,n⟩
  have hbase := (Finset.mem_filter.mp hdn).1
  have hmul := (Finset.mem_filter.mp hdn).2
  have hdI := Finset.mem_Icc.mp (Finset.mem_product.mp hbase).1
  have hnI := Finset.mem_Icc.mp (Finset.mem_product.mp hbase).2
  let kd := (d*n,d)
  have hkd : kd ∈ divisorTriangle N := by
    unfold kd divisorTriangle
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hdI.1 hnI.1, hmul⟩,
        Finset.mem_Icc.mpr hdI⟩, dvd_mul_right d n⟩
  refine ⟨kd, hkd, ?_⟩
  unfold kd divisorToFactor
  change (d, (d * n) / d) = (d, n)
  rw [Nat.mul_div_cancel_left n hdI.1]

/-- Reindex a divisor sum by the exact factor pair `k=d*n`. -/
theorem sum_divisor_triangle
    {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, f d (k / d)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / d), f d n := by
  have hleft :
      (∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, f d (k / d)) =
        ∑ kd ∈ divisorTriangle N, f kd.2 (kd.1 / kd.2) := by
    calc
      _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          if d ∣ k then f d (k / d) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkI := Finset.mem_Icc.mp hk
            rw [← Finset.sum_filter]
            apply Finset.sum_congr
            · ext d
              simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
              constructor
              · intro hd
                exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hkI.1,
                  Nat.le_of_dvd hkI.1 hd.1 |>.trans hkI.2⟩, hd.1⟩
              · intro hd
                exact ⟨hd.2, by omega⟩
            · intro d _hd
              rfl
      _ = ∑ kd ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
          if kd.2 ∣ kd.1 then f kd.2 (kd.1 / kd.2) else 0 := by
            exact (Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
              (fun kd : ℕ × ℕ ↦
                if kd.2 ∣ kd.1 then f kd.2 (kd.1 / kd.2) else 0)).symm
      _ = _ := by
            unfold divisorTriangle
            rw [Finset.sum_filter]
  rw [hleft]
  calc
    (∑ kd ∈ divisorTriangle N, f kd.2 (kd.1 / kd.2)) =
        ∑ dn ∈ factorTriangle N, f dn.1 dn.2 := by
          apply Finset.sum_bij (fun kd _ ↦ divisorToFactor kd)
          · exact fun kd hkd ↦ divisorToFactor_mem hkd
          · intro kd hkd uv huv
            exact divisorToFactor_injective hkd huv
          · exact divisorToFactor_surjective
          · intro kd _hkd
            rfl
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / d), f d n := by
      unfold factorTriangle
      rw [Finset.sum_filter]
      rw [show
        (∑ dn ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
          if dn.1 * dn.2 ≤ N then f dn.1 dn.2 else 0) =
          ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            if d * n ≤ N then f d n else 0 by
              exact Finset.sum_product _ _ _]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro hn
          exact ⟨hn.1.1, (Nat.le_div_iff_mul_le hdpos).mpr
            (by simpa [Nat.mul_comm] using hn.2)⟩
        · intro hn
          exact ⟨⟨hn.1, hn.2.trans (Nat.div_le_self N d)⟩,
            (by simpa [Nat.mul_comm] using
              (Nat.le_div_iff_mul_le hdpos).mp hn.2)⟩
      · intro n _hn
        rfl

/-- The fractional part of the rational argument `N / (d*n)`. -/
noncomputable def quotientFractionalPart (N d n : ℕ) : ℝ :=
  ((N % (d * n) : ℕ) : ℝ) / ((d * n : ℕ) : ℝ)

/-- The manuscript's `W(N/d)` with its rational argument represented
exactly, rather than rounded by natural-number division. -/
noncomputable def weightedFractionalPartsAtQuotient (N d : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (N / d),
    (harmonic (n - 1) : ℝ) / (n : ℝ) *
      quotientFractionalPart N d n

/-- Exact Möbius transform of the rationally evaluated weighted
fractional-part sums. -/
noncomputable def exactMobiusFractionalTransform (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
      weightedFractionalPartsAtQuotient N d

/-- Manuscript Lemma `Möbius reduction`, now with the exact fractional
argument `N/d` and no assumed equality. -/
theorem mobius_reduction (N : ℕ) :
    fractionalFloorTerm N = exactMobiusFractionalTransform N := by
  by_cases hN : N = 0
  · subst N
    simp [fractionalFloorTerm, exactMobiusFractionalTransform]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hincludeOne :
      fractionalFloorTerm N =
        ∑ k ∈ Finset.Icc 1 N,
          (((N % k : ℕ) : ℝ) / (k : ℝ) ^ 2) *
            reducedHarmonicStar k := by
    unfold fractionalFloorTerm
    rw [hIcc, Finset.sum_insert (by simp)]
    simp [Nat.mod_one]
  rw [hincludeOne]
  calc
    (∑ k ∈ Finset.Icc 1 N,
        (((N % k : ℕ) : ℝ) / (k : ℝ) ^ 2) *
          reducedHarmonicStar k) =
        ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors,
          (((N % k : ℕ) : ℝ) / (k : ℝ) ^ 2) *
            ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
              (harmonic (k / d - 1) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
            rw [reducedHarmonicStar_moebius hkpos, Finset.mul_sum]
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors,
          (((N % (d * (k / d)) : ℕ) : ℝ) /
              ((d * (k / d) : ℕ) : ℝ) ^ 2) *
            ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
              (harmonic (k / d - 1) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro d hd
            have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
            rw [Nat.mul_div_cancel' hdk]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / d),
          (((N % (d * n) : ℕ) : ℝ) / ((d * n : ℕ) : ℝ) ^ 2) *
            ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
              (harmonic (n - 1) : ℝ)) := by
            exact sum_divisor_triangle N (fun d n ↦
              (((N % (d * n) : ℕ) : ℝ) /
                ((d * n : ℕ) : ℝ) ^ 2) *
                ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
                  (harmonic (n - 1) : ℝ)))
    _ = exactMobiusFractionalTransform N := by
      unfold exactMobiusFractionalTransform weightedFractionalPartsAtQuotient
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hdQ : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hnQ : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
      unfold quotientFractionalPart
      push_cast
      field_simp [hdQ, hnQ]

end NField.Alignment.ReducedHarmonicMobius
