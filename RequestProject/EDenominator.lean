import RequestProject.LcmRow

/-!
# The denominator estimate behind Imported Theorem E

The closed form of the modular `E`-family numerator `B_n` (see `EClosedForm.lean`) is

`B_n = ∑_{k ≤ n} C(2k,k)² c_k (-4)^{n-k} C(k, n-k)`,   `c_k = (1/4) ∑_{j<k} 4^j / (C(2j,j)(2j+1)²)`.

The only non-integral ingredient is the weight `c_k`.  This file proves the arithmetic fact
that makes `D_n² B_n` an integer, namely

`4 · C(2j,j) · (2j+1)² ∣ D_k² · C(2k,k)² · 4^j`   for `j < k`,      (`central_denom_dvd`)

where `D_k = lcm (1, …, k)`.

The proof is prime by prime.

*Odd `p`.*  Write `a = v_p(2j+1)` and `e = ⌊log_p (2j+1)⌋`.  Legendre's formula
(`Nat.factorization_choose`) expresses `v_p(C(2j,j))` as the number of levels `i` with
`p^i ≤ 2 (j mod p^i)`; no level `i ≤ a` qualifies, because `p^i ∣ 2j+1` forces
`2 (j mod p^i) = p^i - 1`.  Hence `v_p(C(2j,j)) ≤ ⌊log_p 2j⌋ - a`, and therefore

`v_p(C(2j,j)) + 2a ≤ 2e`.

On the other side `p^e ≤ 2j + 1 < 2k`.  If `p^e ≤ k` then `p^e ∣ D_k`, so
`v_p(D_k) ≥ e`.  Otherwise `k < p^e < 2k`, and then Legendre's formula at level `e` gives
`v_p(C(2k,k)) ≥ 1`, while `3 p^{e-1} ≤ p^e < 2k` gives `v_p(D_k) ≥ e - 1`; either way
`v_p(D_k) + v_p(C(2k,k)) ≥ e`.

*`p = 2`.*  Here `v_2(2j+1) = 0`, `v_2(C(2j,j)) ≤ 2j` and `v_2(C(2k,k)) ≥ 1`, so the factor
`4^j` alone does the job.
-/

namespace Catalan

open Nat Finset

lemma Dlcm_ne_zero (N : ℕ) : Dlcm N ≠ 0 := by
  simp [Dlcm, Finset.lcm_eq_zero_iff]

/-- If `p ^ i ≤ k` (and `1 ≤ k`) then `p ^ i` divides `D_k`, hence `i ≤ v_p(D_k)`. -/
lemma le_factorization_Dlcm {p i k : ℕ} (hp : p.Prime) (h : p ^ i ≤ k) :
    i ≤ (Dlcm k).factorization p := by
  refine (hp.pow_dvd_iff_le_factorization (Dlcm_ne_zero k)).1 ?_
  exact dvd_Dlcm (Nat.one_le_pow _ _ hp.pos) h

/-- Legendre's formula for the central binomial coefficient. -/
lemma factorization_centralBinom_eq {p : ℕ} (hp : p.Prime) (k b : ℕ) (hb : Nat.log p (2 * k) < b) :
    (Nat.centralBinom k).factorization p =
      #{i ∈ Ico 1 b | p ^ i ≤ 2 * (k % p ^ i)} := by
  have h := Nat.factorization_choose (p := p) (n := 2 * k) (k := k) (b := b) hp (by omega) hb
  rw [Nat.centralBinom, h]
  congr 1
  refine Finset.filter_congr ?_
  intro i _
  have hkk : 2 * k - k = k := by omega
  rw [hkk]
  omega

/-- If `k < p ^ e ≤ 2 k` then `p` divides the central binomial coefficient `C(2k,k)`. -/
lemma one_le_factorization_centralBinom {p e k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (h1 : k < p ^ e) (h2 : p ^ e ≤ 2 * k) : 1 ≤ (Nat.centralBinom k).factorization p := by
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · rw [pow_zero] at h1; omega
    · exact h
  have hlog : e ≤ Nat.log p (2 * k) :=
    (Nat.le_log_iff_pow_le hp.one_lt (by omega)).2 h2
  rw [factorization_centralBinom_eq hp k (Nat.log p (2 * k) + 1) (by omega)]
  have hmem : e ∈ {i ∈ Ico 1 (Nat.log p (2 * k) + 1) | p ^ i ≤ 2 * (k % p ^ i)} := by
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨he1, by omega⟩, ?_⟩
    rw [Nat.mod_eq_of_lt h1]
    exact h2
  exact Finset.card_pos.2 ⟨e, hmem⟩

/-- If `p ^ i` divides `2j+1` then `2 (j mod p^i) + 1 = p ^ i`. -/
lemma two_mul_mod_add_one {p i j : ℕ} (hp : 0 < p) (hdvd : p ^ i ∣ 2 * j + 1) :
    2 * (j % p ^ i) + 1 = p ^ i := by
  have hP : 0 < p ^ i := pow_pos hp i
  have hr : j % p ^ i < p ^ i := Nat.mod_lt _ hP
  have hsplit : 2 * j + 1 = 2 * (p ^ i * (j / p ^ i)) + (2 * (j % p ^ i) + 1) := by
    have := Nat.div_add_mod j (p ^ i)
    omega
  have hmul : p ^ i ∣ 2 * (p ^ i * (j / p ^ i)) := ⟨2 * (j / p ^ i), by ring⟩
  have hdvd2 : p ^ i ∣ 2 * (j % p ^ i) + 1 :=
    (Nat.dvd_add_right hmul).mp (by rw [← hsplit]; exact hdvd)
  obtain ⟨m, hm⟩ := hdvd2
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · omega
      · rfl
    · exfalso
      have h3 : p ^ i * 2 ≤ p ^ i * m := Nat.mul_le_mul_left _ hge
      rw [← hm] at h3
      omega
  rw [hm1, mul_one] at hm
  omega

/-- The key refinement of Legendre's bound: the `p`-adic levels below `v_p(2j+1)` contribute
no carry to `C(2j,j)`. -/
lemma factorization_centralBinom_le_log_sub {p j : ℕ} (hp : p.Prime) :
    (Nat.centralBinom j).factorization p ≤
      Nat.log p (2 * j) - (2 * j + 1).factorization p := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Nat.centralBinom]
  set a := (2 * j + 1).factorization p with ha
  rw [factorization_centralBinom_eq hp j (Nat.log p (2 * j) + 1) (by omega)]
  have hsub : {i ∈ Ico 1 (Nat.log p (2 * j) + 1) | p ^ i ≤ 2 * (j % p ^ i)} ⊆
      Ico (a + 1) (Nat.log p (2 * j) + 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    obtain ⟨⟨hi1, hi2⟩, hcond⟩ := hi
    refine Finset.mem_Ico.2 ⟨?_, hi2⟩
    by_contra hcon
    push_neg at hcon
    have hle : i ≤ a := by omega
    have hdvd : p ^ i ∣ 2 * j + 1 :=
      (hp.pow_dvd_iff_le_factorization (by omega)).2 hle
    have := two_mul_mod_add_one hp.pos hdvd
    omega
  calc #{i ∈ Ico 1 (Nat.log p (2 * j) + 1) | p ^ i ≤ 2 * (j % p ^ i)}
      ≤ #(Ico (a + 1) (Nat.log p (2 * j) + 1)) := Finset.card_le_card hsub
    _ = Nat.log p (2 * j) - a := by rw [Nat.card_Ico]; omega

/-- The odd-prime half of the estimate: `v_p(C(2j,j)) + 2 v_p(2j+1) ≤ 2 ⌊log_p (2j+1)⌋`. -/
lemma odd_prime_left_bound {p j : ℕ} (hp : p.Prime) :
    (Nat.centralBinom j).factorization p + 2 * (2 * j + 1).factorization p ≤
      2 * Nat.log p (2 * j + 1) := by
  have h1 := factorization_centralBinom_le_log_sub (p := p) (j := j) hp
  have h2 : (2 * j + 1).factorization p ≤ Nat.log p (2 * j + 1) := by
    refine (Nat.le_log_iff_pow_le hp.one_lt (by omega)).2 ?_
    exact Nat.le_of_dvd (by omega)
      ((hp.pow_dvd_iff_le_factorization (by omega)).2 le_rfl)
  have h3 : Nat.log p (2 * j) ≤ Nat.log p (2 * j + 1) := Nat.log_mono_right (by omega)
  omega

/-- The odd-prime half of the estimate, right-hand side. -/
lemma odd_prime_right_bound {p e k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (he : p ^ e < 2 * k) :
    e ≤ (Dlcm k).factorization p + (Nat.centralBinom k).factorization p := by
  rcases le_or_gt (p ^ e) k with h | h
  · exact le_trans (le_factorization_Dlcm hp h) (Nat.le_add_right _ _)
  · have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h'
      · rw [pow_zero] at h; omega
      · exact h'
    have hc : 1 ≤ (Nat.centralBinom k).factorization p :=
      one_le_factorization_centralBinom hp hk h (by omega)
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      rcases Nat.lt_or_ge p 3 with h' | h'
      · interval_cases p
        · exact absurd rfl hp2
      · exact h'
    have hstep : 3 * p ^ (e - 1) ≤ p ^ e := by
      have hmul : p ^ (e - 1) * 3 ≤ p ^ (e - 1) * p := Nat.mul_le_mul_left _ hp3
      calc 3 * p ^ (e - 1) = p ^ (e - 1) * 3 := by ring
        _ ≤ p ^ (e - 1) * p := hmul
        _ = p ^ e := by rw [← pow_succ]; congr 1; omega
    have hle : p ^ (e - 1) ≤ k := by omega
    have := le_factorization_Dlcm hp hle
    omega

/-- The `p = 2` half of the estimate. -/
lemma two_adic_bound {j k : ℕ} (hk : 1 ≤ k) :
    2 + (Nat.centralBinom j).factorization 2 + 2 * (2 * j + 1).factorization 2 ≤
      2 * (Dlcm k).factorization 2 + 2 * (Nat.centralBinom k).factorization 2 + 2 * j := by
  have hodd : (2 * j + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega)
  have hcj : (Nat.centralBinom j).factorization 2 ≤ 2 * j := by
    have hle : 2 ^ ((Nat.centralBinom j).factorization 2) ≤ 2 * j + 1 := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [Nat.centralBinom]
      · have := Nat.pow_factorization_choose_le (p := 2) (n := 2 * j) (k := j) (by omega)
        rw [← Nat.centralBinom] at this
        omega
    have hlt : 2 * j + 1 < 2 ^ (2 * j + 1) := Nat.lt_two_pow_self
    have hcmp : (2 : ℕ) ^ ((Nat.centralBinom j).factorization 2) < 2 ^ (2 * j + 1) :=
      lt_of_le_of_lt hle hlt
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 hcmp
    omega
  have hck : 1 ≤ (Nat.centralBinom k).factorization 2 := by
    have hlog2 : Nat.log 2 (2 * k) = Nat.log 2 k + 1 := by
      rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    have hklt : k < 2 ^ Nat.log 2 (2 * k) := by
      rw [hlog2]
      exact Nat.lt_pow_succ_log_self (by norm_num) k
    exact one_le_factorization_centralBinom (p := 2) (e := Nat.log 2 (2 * k)) Nat.prime_two hk
      hklt (Nat.pow_log_le_self 2 (by omega))
  omega

/-- The arithmetic heart of Imported Theorem E:
`4 C(2j,j) (2j+1)² ∣ D_k² C(2k,k)² 4^j` whenever `j < k`. -/
theorem central_denom_dvd {j k : ℕ} (hjk : j < k) :
    4 * Nat.centralBinom j * (2 * j + 1) ^ 2 ∣
      (Dlcm k) ^ 2 * (Nat.centralBinom k) ^ 2 * 4 ^ j := by
  have hk : 1 ≤ k := by omega
  have hcbj : Nat.centralBinom j ≠ 0 := (Nat.centralBinom_pos j).ne'
  have hcbk : Nat.centralBinom k ≠ 0 := (Nat.centralBinom_pos k).ne'
  have hDk : Dlcm k ≠ 0 := Dlcm_ne_zero k
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hodd : (2 * j + 1 : ℕ) ≠ 0 := by omega
  have hL : (4 * Nat.centralBinom j * (2 * j + 1) ^ 2 : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero h4 hcbj) (pow_ne_zero _ hodd)
  have hR : ((Dlcm k) ^ 2 * (Nat.centralBinom k) ^ 2 * 4 ^ j : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ hDk) (pow_ne_zero _ hcbk)) (pow_ne_zero _ h4)
  rw [← Nat.factorization_le_iff_dvd hL hR, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hfL : (4 * Nat.centralBinom j * (2 * j + 1) ^ 2 : ℕ).factorization p =
      (4 : ℕ).factorization p + (Nat.centralBinom j).factorization p
        + 2 * (2 * j + 1).factorization p := by
    rw [Nat.factorization_mul (Nat.mul_ne_zero h4 hcbj) (pow_ne_zero _ hodd),
      Nat.factorization_mul h4 hcbj, Nat.factorization_pow]
    simp
  have hfR : ((Dlcm k) ^ 2 * (Nat.centralBinom k) ^ 2 * 4 ^ j : ℕ).factorization p =
      2 * (Dlcm k).factorization p + 2 * (Nat.centralBinom k).factorization p
        + j * (4 : ℕ).factorization p := by
    rw [Nat.factorization_mul (Nat.mul_ne_zero (pow_ne_zero _ hDk) (pow_ne_zero _ hcbk))
        (pow_ne_zero _ h4),
      Nat.factorization_mul (pow_ne_zero _ hDk) (pow_ne_zero _ hcbk),
      Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow]
    simp
  rw [hfL, hfR]
  by_cases hp2 : p = 2
  · subst hp2
    have hv4 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [hv4]
    have := two_adic_bound (j := j) (k := k) hk
    omega
  · have hv4 : (4 : ℕ).factorization p = 0 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp [Ne.symm hp2]
    rw [hv4]
    have hleft := odd_prime_left_bound (p := p) (j := j) hp
    have hright : Nat.log p (2 * j + 1) ≤
        (Dlcm k).factorization p + (Nat.centralBinom k).factorization p := by
      refine odd_prime_right_bound hp hp2 hk ?_
      have : p ^ Nat.log p (2 * j + 1) ≤ 2 * j + 1 := Nat.pow_log_le_self p (by omega)
      omega
    omega

end Catalan
