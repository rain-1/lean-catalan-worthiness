import Mathlib

/-!
# The common LCM-square at index `3n` and `6n`

Section 14 of the base note.  With `D N = lcm(1, …, N)` we prove Lemma 14.1,

`D (6n) = D (6n - 1)` for `n ≥ 1`,

which is what makes the single integral factor `S n = D (6n) ^ 2` work simultaneously for the
modular `E`-row at index `6n` and for the Zudilin row at index `3n`.
-/

namespace Catalan

/-- `D N = lcm (1, 2, …, N)`. -/
def Dlcm (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

@[simp] lemma Dlcm_zero : Dlcm 0 = 1 := by decide

lemma dvd_Dlcm {d N : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ N) : d ∣ Dlcm N :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)

lemma Dlcm_succ (N : ℕ) : Dlcm (N + 1) = Nat.lcm (Dlcm N) (N + 1) := by
  unfold Dlcm
  rw [show Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.lcm_insert]
  simp only [id]
  exact Nat.lcm_comm _ _

lemma Dlcm_eq_of_dvd {N : ℕ} (h : (N + 1) ∣ Dlcm N) : Dlcm (N + 1) = Dlcm N := by
  rw [Dlcm_succ, Nat.lcm_comm]
  exact Nat.lcm_eq_right h

/-- If `N = u * v` with `u, v` coprime and both `< N`, then `N` divides `lcm(1,…,N-1)`. -/
lemma dvd_Dlcm_of_coprime_factorization {N u v : ℕ} (hN : N = u * v) (hcop : Nat.Coprime u v)
    (hu1 : 1 ≤ u) (hv1 : 1 ≤ v) (hu : u < N) (hv : v < N) : N ∣ Dlcm (N - 1) := by
  have hu' : u ∣ Dlcm (N - 1) := dvd_Dlcm hu1 (by omega)
  have hv' : v ∣ Dlcm (N - 1) := dvd_Dlcm hv1 (by omega)
  nth_rewrite 1 [hN]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hu' hv'

/-- Lemma 14.1: `D (6n) = D (6n - 1)` for `n ≥ 1`. -/
theorem Dlcm_six_mul (n : ℕ) (hn : 1 ≤ n) : Dlcm (6 * n) = Dlcm (6 * n - 1) := by
  set N := 6 * n with hN
  have hN6 : 6 ≤ N := by omega
  -- split off the exact power of two
  set a := N.factorization 2 with ha
  set u := 2 ^ a with hu
  set v := N / u with hv
  have hNpos : 0 < N := by omega
  have hudvd : u ∣ N := Nat.ordProj_dvd N 2
  have hNuv : N = u * v := (Nat.mul_div_cancel' hudvd).symm
  have hvpos : 0 < v := Nat.pos_of_ne_zero (by
    intro h
    rw [h, mul_zero] at hNuv
    omega)
  have hcop : Nat.Coprime u v := by
    have : ¬ (2 ∣ v) := by
      intro h2
      have : u * 2 ∣ N := by
        rw [hNuv]
        exact mul_dvd_mul_left u h2
      have hnot := Nat.pow_succ_factorization_not_dvd (by omega : N ≠ 0) (by norm_num : Nat.Prime 2)
      rw [pow_succ] at hnot
      exact hnot this
    have hprime : Nat.Prime 2 := by norm_num
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hprime).mpr this)
  -- `u` is a power of two, so `3 ∣ v`, forcing `v ≥ 3` and `u ≤ N / 3 < N`
  have h3v : 3 ∣ v := by
    have h3N : 3 ∣ N := ⟨2 * n, by omega⟩
    have h3u : ¬ (3 ∣ u) := by
      intro h
      have := Nat.Prime.dvd_of_dvd_pow (p := 3) (by norm_num) h
      omega
    have hcop3u : Nat.Coprime 3 u := by
      rw [hu]
      exact Nat.Coprime.pow_right a
        ((Nat.coprime_primes (by norm_num) (by norm_num)).mpr (by norm_num))
    have h3uv : 3 ∣ u * v := by rw [← hNuv]; exact h3N
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop3u h3uv)
  have hv3 : 3 ≤ v := Nat.le_of_dvd hvpos h3v
  have hu2 : 2 ∣ N := ⟨3 * n, by omega⟩
  have hua : 1 ≤ a := by
    rw [ha]
    exact (Nat.Prime.factorization_pos_of_dvd (by norm_num) (by omega) hu2)
  have hupos : 1 ≤ u := Nat.one_le_two_pow
  have hult : u < N := by
    have : u * 3 ≤ u * v := Nat.mul_le_mul_left u hv3
    nlinarith [hNuv, hupos]
  have hvlt : v < N := by
    have hu2' : 2 ≤ u := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hua
    nlinarith [hNuv, hvpos]
  have hdvd : N ∣ Dlcm (N - 1) :=
    dvd_Dlcm_of_coprime_factorization hNuv hcop hupos hvpos hult hvlt
  have hNsucc : N - 1 + 1 = N := by omega
  calc Dlcm N = Dlcm ((N - 1) + 1) := by rw [hNsucc]
    _ = Dlcm (N - 1) := Dlcm_eq_of_dvd (by rw [hNsucc]; exact hdvd)

/-- `S n = D (6n) ^ 2`, the common integral factor of the two rows. -/
def Sfac (n : ℕ) : ℕ := (Dlcm (6 * n)) ^ 2

lemma Sfac_eq (n : ℕ) (hn : 1 ≤ n) : Sfac n = (Dlcm (6 * n - 1)) ^ 2 := by
  rw [Sfac, Dlcm_six_mul n hn]

end Catalan
