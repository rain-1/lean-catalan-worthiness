import Mathlib

/-!
# Legendre's bound for a product along an arithmetic progression

If a prime `p` does not divide the common difference `d` of an arithmetic progression, then the
product of `n` consecutive terms of the progression is divisible by at least as high a power of
`p` as `n !` is: among any `p^i` consecutive terms exactly one is divisible by `p^i`, so the
number of terms divisible by `p^i` is at least `⌊n / p^i⌋`, and Legendre's formula for `v_p(n !)`
is the sum of these quotients.

Only the difference `d = 2` (with `p` odd) is needed in this development, and that is the form in
which the results are stated.

The main results are

* `Catalan.card_ap_dvd_ge` : `n / q ≤ #{j < n | q ∣ c + 2 j}` for odd `q`;
* `Catalan.factorization_factorial_le_prod_ap` : `v_p(n !) ≤ v_p(∏_{j<n} (c + 2 j))` for odd `p`.
-/

namespace Catalan

open Finset

/-- If `q` is odd and positive, the congruence `c + 2 j ≡ 0 (mod q)` has a solution `j < q`. -/
lemma exists_ap_root (q c : ℕ) (hq : 0 < q) (hcop : Nat.Coprime 2 q) :
    ∃ j0 < q, q ∣ c + 2 * j0 := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, 2 * u + (q : ℤ) * v = 1 := by
    have hco : IsCoprime (2 : ℤ) (q : ℤ) := by
      simpa using Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨a, b, hab⟩ := hco
    exact ⟨a, b, by linarith [hab]⟩
  set x : ℤ := -(c : ℤ) * u with hx
  set jz : ℤ := x % (q : ℤ) with hjz
  have h1 : 0 ≤ jz := Int.emod_nonneg _ (by positivity)
  have h2 : jz < (q : ℤ) := Int.emod_lt_of_pos _ hq0
  obtain ⟨t, ht⟩ : ∃ t : ℤ, x - jz = (q : ℤ) * t :=
    ⟨x / (q : ℤ), by rw [hjz]; linarith [Int.emod_add_mul_ediv x (q : ℤ)]⟩
  refine ⟨jz.toNat, ?_, ?_⟩
  · have : (jz.toNat : ℤ) < (q : ℤ) := by rwa [Int.toNat_of_nonneg h1]
    exact_mod_cast this
  · have hcast : ((jz.toNat : ℕ) : ℤ) = jz := Int.toNat_of_nonneg h1
    have hdvd : (q : ℤ) ∣ ((c : ℤ) + 2 * jz) := by
      refine ⟨(c : ℤ) * v - 2 * t, ?_⟩
      have hxdef : x = -(c : ℤ) * u := hx
      linear_combination (-2 : ℤ) * ht - (c : ℤ) * huv - 2 * hxdef
    have : (q : ℤ) ∣ ((c + 2 * jz.toNat : ℕ) : ℤ) := by push_cast [hcast]; exact hdvd
    exact_mod_cast this

/-- At least `⌊n / q⌋` of the numbers `c, c + 2, …, c + 2(n-1)` are divisible by the odd
number `q`. -/
lemma card_ap_dvd_ge (q c n : ℕ) (hq : 0 < q) (hcop : Nat.Coprime 2 q) :
    n / q ≤ #{j ∈ range n | q ∣ c + 2 * j} := by
  obtain ⟨j0, hj0, hdvd⟩ := exists_ap_root q c hq hcop
  rw [← Finset.card_range (n / q)]
  refine Finset.card_le_card_of_injOn (fun t => j0 + t * q) ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    have hle : (t + 1) * q ≤ n := (Nat.le_div_iff_mul_le hq).mp ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨by nlinarith, ?_⟩
    have hrw : c + 2 * (j0 + t * q) = (c + 2 * j0) + q * (2 * t) := by ring
    rw [hrw]
    exact Nat.dvd_add hdvd ⟨2 * t, rfl⟩
  · intro a _ b _ hab
    have hab' : j0 + a * q = j0 + b * q := hab
    have hmul : a * q = b * q := by omega
    exact Nat.eq_of_mul_eq_mul_right hq hmul

/-- Legendre's bound along an arithmetic progression of difference `2`: for an odd prime `p`,
the product `∏_{j<n} (c + 2 j)` is divisible by at least as high a power of `p` as `n !`. -/
theorem factorization_factorial_le_prod_ap {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (c n : ℕ)
    (hc : 0 < c) :
    (n.factorial).factorization p ≤ (∏ j ∈ range n, (c + 2 * j)).factorization p := by
  classical
  set b : ℕ := c + 2 * n + 1 with hb
  have hple : 2 ≤ p := hp.two_le
  have hbpow : b < p ^ b := by
    calc b < 2 ^ b := Nat.lt_two_pow_self
      _ ≤ p ^ b := Nat.pow_le_pow_left hple b
  have hlogn : Nat.log p n < b := by
    have h1 : Nat.log p n ≤ n := Nat.log_le_self p n
    omega
  have hfac : (n.factorial).factorization p = ∑ i ∈ Ico 1 b, n / p ^ i :=
    Nat.factorization_factorial hp hlogn
  have hprodfac : (∏ j ∈ range n, (c + 2 * j)).factorization p
      = ∑ j ∈ range n, (c + 2 * j).factorization p := by
    rw [Nat.factorization_prod (fun j _ => by omega)]
    simp
  have hterm : ∀ j ∈ range n, (c + 2 * j).factorization p
      = ∑ i ∈ Ico 1 b, (if p ^ i ∣ c + 2 * j then 1 else 0) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hlt : c + 2 * j < p ^ b := by
      have : c + 2 * j < b := by omega
      omega
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega) hlt, Finset.card_filter]
  rw [hfac, hprodfac, Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_le_sum (fun i hi => ?_)
  simp only [Finset.mem_Ico] at hi
  have hq : 0 < p ^ i := pow_pos hp.pos i
  have hcop : Nat.Coprime 2 (p ^ i) := by
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hp2 h.symm)
    exact this.pow_right i
  have := card_ap_dvd_ge (p ^ i) c n hq hcop
  calc n / p ^ i ≤ #{j ∈ range n | p ^ i ∣ c + 2 * j} := this
    _ = ∑ j ∈ range n, (if p ^ i ∣ c + 2 * j then 1 else 0) := Finset.card_filter _ _

end Catalan
