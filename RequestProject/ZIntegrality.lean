import RequestProject.RivoalQ
import RequestProject.APValuation

/-!
# Integrality of the cleared Zudilin denominators

Zudilin's denominators satisfy `2^{4m} Q_m ∈ ℤ`.  This is Lemma 5.1 of the base note for the
row `X₂`, and it is proved here rather than imported.

The proof uses the closed form `Q_m = ∑_{k≤m} T(m,k)` of `RivoalQ.lean`.  Writing the three
falling/rising products of `T(m,k)` in terms of natural numbers,

`T(m,k) = C(m,k) · U(m,k) / (4^k (k!)^2)`,

where `U(m,k) = (2m-2k+1)(2m-2k+3) ⋯ (2m+2k-1)` is a run of `2k` consecutive odd numbers.
Legendre's bound along an arithmetic progression (`APValuation.lean`) shows that
`(k!)^2` divides `2^{2 v₂(k!)} U(m,k)`, and `2k + 2 v₂(k!) ≤ 4m` for `k ≤ m`, whence the claim.
-/

namespace Catalan

open Finset

/-- The product `c (c+2) ⋯ (c + 2(n-1))` of `n` terms of an odd arithmetic progression. -/
def oddRun (c n : ℕ) : ℕ := ∏ j ∈ range n, (c + 2 * j)

lemma oddRun_pos (c n : ℕ) (hc : 0 < c) : 0 < oddRun c n :=
  Finset.prod_pos (fun j _ => by omega)

lemma oddRun_split (c k : ℕ) : oddRun c (2 * k) = oddRun c k * oddRun (c + 2 * k) k := by
  unfold oddRun
  rw [two_mul, Finset.prod_range_add]
  refine congrArg _ (Finset.prod_congr rfl (fun j _ => by ring))

/-- Legendre's bound applied to a run of `2k` odd numbers: `(k!)²` divides
`2^{2 v₂(k!)} · U`. -/
theorem sq_factorial_dvd_oddRun (c k : ℕ) (hc : 0 < c) :
    (k.factorial) ^ 2 ∣ 2 ^ (2 * (k.factorial).factorization 2) * oddRun c (2 * k) := by
  have hUpos := oddRun_pos c (2 * k) hc
  have hFne : (k.factorial) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero k)
  have hRne : 2 ^ (2 * (k.factorial).factorization 2) * oddRun c (2 * k) ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hFne hRne, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hL : ((k.factorial) ^ 2).factorization p = 2 * (k.factorial).factorization p := by
      rw [Nat.factorization_pow]
      simp
    have hR : (2 ^ (2 * (k.factorial).factorization 2) * oddRun c (2 * k)).factorization p
        = (2 * (k.factorial).factorization 2) * (Nat.factorization 2 p)
          + (oddRun c (2 * k)).factorization p := by
      rw [Nat.factorization_mul (by positivity) hUpos.ne', Nat.factorization_pow]
      simp
    rcases eq_or_ne p 2 with rfl | hp2
    · rw [hL, hR, Nat.Prime.factorization_self Nat.prime_two]
      omega
    · have hzero : (Nat.factorization 2) p = 0 := by
        rw [Nat.Prime.factorization Nat.prime_two]
        simp [Ne.symm hp2]
      have hsq : (k.factorial) ^ 2 ∣ (2 * k).factorial := by
        have h := Nat.factorial_mul_factorial_dvd_factorial_add k k
        rw [two_mul, sq]
        exact h
      have hle1 : ((k.factorial) ^ 2).factorization p ≤ ((2 * k).factorial).factorization p := by
        have := (Nat.factorization_le_iff_dvd hFne (Nat.factorial_ne_zero _)).mpr hsq
        exact (Finsupp.le_def.mp this) p
      have hle2 : ((2 * k).factorial).factorization p ≤ (oddRun c (2 * k)).factorization p :=
        factorization_factorial_le_prod_ap hp hp2 c (2 * k) hc
      rw [hR, hzero]
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-! ### The three products of the closed form as natural numbers -/

lemma pdProd_nat (m k : ℕ) (hk : k ≤ m) : pdProd ((m : ℚ)) k = ((m.descFactorial k : ℕ) : ℚ) := by
  induction k with
  | zero => simp
  | succ i ih =>
      have hi : i ≤ m := by omega
      rw [pdProd_succ, ih hi, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hi]
      ring

lemma two_pow_mul_puProd (m k : ℕ) :
    (2 : ℚ) ^ k * puProd ((m : ℚ) + 1 / 2) k = (oddRun (2 * m + 1) k : ℚ) := by
  have h2 : (2 : ℚ) ^ k = ∏ _j ∈ range k, (2 : ℚ) := by simp
  rw [puProd, h2, ← Finset.prod_mul_distrib, oddRun, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun j _ => by push_cast; ring)

lemma two_pow_mul_pdProd_half (m k : ℕ) (hk : k ≤ m) :
    (2 : ℚ) ^ k * pdProd ((m : ℚ) - 1 / 2) k = (oddRun (2 * m - 2 * k + 1) k : ℚ) := by
  have h2 : (2 : ℚ) ^ k = ∏ _j ∈ range k, (2 : ℚ) := by simp
  rw [pdProd, h2, ← Finset.prod_mul_distrib, oddRun, Nat.cast_prod,
    ← Finset.prod_range_reflect (fun j => ((2 * m - 2 * k + 1 + 2 * j : ℕ) : ℚ)) k]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  have hnat : 2 * m - 2 * k + 1 + 2 * (k - 1 - j) = 2 * m - (1 + 2 * j) := by omega
  have hle : 1 + 2 * j ≤ 2 * m := by omega
  rw [hnat, Nat.cast_sub hle]
  push_cast
  ring

lemma four_pow_mul_halves (m k : ℕ) (hk : k ≤ m) :
    (4 : ℚ) ^ k * (pdProd ((m : ℚ) - 1 / 2) k * puProd ((m : ℚ) + 1 / 2) k)
      = (oddRun (2 * m - 2 * k + 1) (2 * k) : ℚ) := by
  have h1 := two_pow_mul_pdProd_half m k hk
  have h2 := two_pow_mul_puProd m k
  have hc : 2 * m - 2 * k + 1 + 2 * k = 2 * m + 1 := by omega
  have h4 : (4 : ℚ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [oddRun_split, hc, Nat.cast_mul, ← h1, ← h2, h4]
  ring

/-! ### Integrality of `2^{4m} Q_m` -/

theorem two_pow_mul_tZ_isNat (m k : ℕ) (hk : k ≤ m) :
    ∃ z : ℕ, (2 : ℚ) ^ (4 * m) * tZ (m : ℚ) k = (z : ℚ) := by
  set F := k.factorial with hF
  set v := F.factorization 2 with hv
  set U := oddRun (2 * m - 2 * k + 1) (2 * k) with hU
  obtain ⟨w, hw⟩ := sq_factorial_dvd_oddRun (2 * m - 2 * k + 1) k (by omega)
  have hvk : v ≤ k := by
    have : padicValNat 2 (Nat.factorial k) ≤ k :=
      @padicValNat_factorial_le 2 ⟨Nat.prime_two⟩ k
    rw [hv, hF, Nat.factorization_def _ Nat.prime_two]
    exact this
  have hr : 4 * m = (4 * m - 2 * k - 2 * v) + 2 * k + 2 * v := by omega
  set r := 4 * m - 2 * k - 2 * v with hrdef
  have hFne : (F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpd : pdProd ((m : ℚ)) k = (F : ℚ) * (m.choose k : ℚ) := by
    rw [pdProd_nat m k hk, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hhalf : pdProd ((m : ℚ) - 1 / 2) k * puProd ((m : ℚ) + 1 / 2) k = (U : ℚ) / 4 ^ k := by
    have h := four_pow_mul_halves m k hk
    have h4 : (4 : ℚ) ^ k ≠ 0 := by positivity
    field_simp at h ⊢
    linarith [h]
  have hwQ : (2 : ℚ) ^ (2 * v) * (U : ℚ) = (F : ℚ) ^ 2 * (w : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hw
  refine ⟨2 ^ r * (m.choose k) * w, ?_⟩
  have hnum : pdProd ((m : ℚ)) k * pdProd ((m : ℚ) - 1 / 2) k * puProd ((m : ℚ) + 1 / 2) k
      = (F : ℚ) * (m.choose k : ℚ) * ((U : ℚ) / 4 ^ k) := by
    rw [mul_assoc, hpd, hhalf]
  have h2k : (2 : ℚ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  rw [tZ, hnum, hr, pow_add, pow_add, h2k]
  push_cast
  field_simp
  rw [← hF]
  linear_combination ((F : ℚ) * (m.choose k : ℚ)) * hwQ

theorem two_pow_mul_Qz_isNat (m : ℕ) : ∃ z : ℤ, ((z : ℤ) : ℚ) = 2 ^ (4 * m) * Qz m := by
  have hsum : (2 : ℚ) ^ (4 * m) * Qz m = ∑ k ∈ range (m + 1), (2 : ℚ) ^ (4 * m) * tZ (m : ℚ) k := by
    rw [← dZsum_eq_Qz, dZsum, Finset.mul_sum]
  choose z hz using fun k : {k // k ∈ range (m + 1)} =>
    two_pow_mul_tZ_isNat m k.1 (by have := k.2; simp only [Finset.mem_range] at this; omega)
  classical
  refine ⟨∑ k ∈ (range (m + 1)).attach, (z k : ℤ), ?_⟩
  rw [hsum]
  push_cast
  rw [← Finset.sum_attach (range (m + 1)) (fun k => (2 : ℚ) ^ (4 * m) * tZ (m : ℚ) k)]
  exact Finset.sum_congr rfl (fun k _ => (hz k).symm)

/-- Lemma 5.1 for the second row: `2^{e} Q_m ∈ ℤ` for any clearing exponent `e ≥ 4m`. -/
theorem two_pow_mul_Qz_isInt (m e : ℕ) (he : 4 * m ≤ e) :
    ∃ z : ℤ, ((z : ℤ) : ℚ) = 2 ^ e * Qz m := by
  obtain ⟨z, hz⟩ := two_pow_mul_Qz_isNat m
  refine ⟨2 ^ (e - 4 * m) * z, ?_⟩
  have hsplit : (2 : ℚ) ^ e = 2 ^ (e - 4 * m) * 2 ^ (4 * m) := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  rw [hsplit, mul_assoc, ← hz]

end Catalan
