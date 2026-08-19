import RequestProject.EIntegrality
import RequestProject.RateTools

/-!
# The archimedean growth rate of the modular `E`-family denominators

The base note imports the archimedean estimate `(1/n) log A_n → log 8` for the modular
`E`-family denominators (equation (9.2) of the base note).  Using the closed form

`A_n = ∑_{k ≤ n} C(n,k) C(2k,k) C(2(n-k), n-k)`

of `RequestProject/EIntegrality.lean`, this estimate becomes elementary and is proved here,
so it no longer has to be assumed.

The two ingredients are the crude bounds

`8 ^ n ≤ 16 (n+1)^3 A_n`   and   `A_n ≤ (n+1) 8 ^ n`,

which follow from `C(n,k) ≤ 2^n`, `C(2k,k) ≤ 4^k` and Mathlib's lower bound
`4 ^ m ≤ 2 m C(2m,m)`, applied to the single middle term `k = ⌊n/2⌋` of the sum.
A polynomial two-sided bound of that shape forces the logarithmic rate
(`logRate_of_sandwich`).
-/

namespace Catalan

open Finset Filter Topology

/-! ### Elementary two-sided bounds for the closed form -/

lemma centralBinom_le_four_pow (n : ℕ) : Nat.centralBinom n ≤ 4 ^ n := by
  have h := Nat.choose_le_two_pow (n := 2 * n) (k := n)
  simpa [Nat.centralBinom, pow_mul] using h

lemma eT_le_eight_pow (n k : ℕ) (hk : k ≤ n) : eT n k ≤ 8 ^ n := by
  have h1 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
  have h2 := centralBinom_le_four_pow k
  have h3 := centralBinom_le_four_pow (n - k)
  calc eT n k ≤ 2 ^ n * 4 ^ k * 4 ^ (n - k) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    _ = 8 ^ n := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hk,
          show (8 : ℕ) = 2 * 4 by norm_num, mul_pow]

/-- Upper bound: `A_n ≤ (n+1) 8^n`. -/
lemma eSum_le (n : ℕ) : eSum n ≤ (n + 1) * 8 ^ n := by
  have h : eSum n ≤ ∑ _k ∈ range (n + 1), 8 ^ n :=
    Finset.sum_le_sum fun k hk =>
      eT_le_eight_pow n k (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk)
  simpa [mul_comm] using h

lemma eT_le_eSum (n k : ℕ) (hk : k ≤ n) : eT n k ≤ eSum n :=
  Finset.single_le_sum (f := fun k => eT n k) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

/-- Lower bound: `8^n ≤ 16 (n+1)^3 A_n`, obtained from the middle term of the sum. -/
lemma eight_pow_le_eSum (n : ℕ) : 8 ^ n ≤ 16 * (n + 1) ^ 3 * eSum n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp [eSum, eT, Nat.centralBinom]
    · have hb := Nat.four_pow_le_two_mul_self_mul_centralBinom m hmpos
      have hsub : m + m - m = m := by omega
      have hterm : eT (m + m) m = Nat.centralBinom m ^ 3 := by
        simp [eT, hsub, Nat.centralBinom, two_mul]; ring
      have h1 : (8 : ℕ) ^ (m + m) = (4 ^ m) ^ 3 := by
        rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num, show (4 : ℕ) = 2 ^ 2 by norm_num,
          ← pow_mul, ← pow_mul]
        ring_nf
      have h3 : eT (m + m) m ≤ eSum (m + m) := eT_le_eSum _ _ (by omega)
      calc (8 : ℕ) ^ (m + m) = (4 ^ m) ^ 3 := h1
        _ ≤ (2 * m * Nat.centralBinom m) ^ 3 := Nat.pow_le_pow_left hb 3
        _ = 8 * m ^ 3 * Nat.centralBinom m ^ 3 := by ring
        _ = 8 * m ^ 3 * eT (m + m) m := by rw [hterm]
        _ ≤ 16 * (m + m + 1) ^ 3 * eSum (m + m) :=
            Nat.mul_le_mul
              (by nlinarith [Nat.pow_le_pow_left (show m ≤ m + m + 1 by omega) 3]) h3
  · subst hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · norm_num [eSum, eT, Nat.centralBinom, Finset.sum_range_succ]
    · have hb := Nat.four_pow_le_two_mul_self_mul_centralBinom m hmpos
      have hb1 := Nat.four_pow_le_two_mul_self_mul_centralBinom (m + 1) (by omega)
      have hsub : 2 * m + 1 - m = m + 1 := by omega
      have hch : Nat.centralBinom m ≤ (2 * m + 1).choose m := by
        have h := Nat.choose_mono (b := m) (show 2 * m ≤ 2 * m + 1 by omega)
        simpa [Nat.centralBinom] using h
      have hterm : Nat.centralBinom m * Nat.centralBinom m * Nat.centralBinom (m + 1)
          ≤ eT (2 * m + 1) m := by
        rw [eT, hsub]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hch)
      have r1 : (4 : ℕ) ^ m * 4 ^ m * 4 ^ m = 64 ^ m := by rw [← mul_pow, ← mul_pow]; norm_num
      have r2 : (8 : ℕ) ^ (2 * m + 1) = 64 ^ m * 8 := by rw [pow_succ, pow_mul]; norm_num
      have h1 : (8 : ℕ) ^ (2 * m + 1) = 2 * (4 ^ m * 4 ^ m * 4 ^ (m + 1)) := by
        rw [r2, pow_succ, ← r1]; ring
      have h3 : eT (2 * m + 1) m ≤ eSum (2 * m + 1) := eT_le_eSum _ _ (by omega)
      calc (8 : ℕ) ^ (2 * m + 1) = 2 * (4 ^ m * 4 ^ m * 4 ^ (m + 1)) := h1
        _ ≤ 2 * ((2 * m * Nat.centralBinom m) * (2 * m * Nat.centralBinom m)
              * (2 * (m + 1) * Nat.centralBinom (m + 1))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hb hb) hb1)
        _ = 16 * (m * m * (m + 1)) * (Nat.centralBinom m * Nat.centralBinom m
              * Nat.centralBinom (m + 1)) := by ring
        _ ≤ 16 * (2 * m + 1 + 1) ^ 3 * eT (2 * m + 1) m :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by nlinarith)) hterm
        _ ≤ 16 * (2 * m + 1 + 1) ^ 3 * eSum (2 * m + 1) := Nat.mul_le_mul_left _ h3

lemma eSum_pos (n : ℕ) : 0 < eSum n := by
  have h : eT n 0 ≤ eSum n := eT_le_eSum n 0 (Nat.zero_le _)
  have h0 : 0 < eT n 0 := by
    have := Nat.centralBinom_pos n
    simpa [eT, Nat.centralBinom] using this
  omega

/-! ### From polynomial two-sided bounds to a logarithmic rate -/

private lemma tendsto_log_succ_div : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hA : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := h.comp hA
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have h3 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have h4 := h1.mul h2
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h5 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- If `f` is squeezed between `e^{an}` and `e^{an}` up to a polynomial factor, then
`(1/n) log |f n| → a`. -/
lemma logRate_of_sandwich {f : ℕ → ℝ} {a C : ℝ} (d : ℕ) (hC : 0 < C)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < f n)
    (hlb : ∀ᶠ n : ℕ in atTop, Real.exp (a * n) ≤ C * ((n : ℝ) + 1) ^ d * f n)
    (hub : ∀ᶠ n : ℕ in atTop, f n ≤ C * ((n : ℝ) + 1) ^ d * Real.exp (a * n)) :
    LogRate f a := by
  set L : ℕ → ℝ := fun n => |Real.log C| + d * Real.log ((n : ℝ) + 1) with hL
  have hLdiv : Tendsto (fun n : ℕ => L n / n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => |Real.log C| / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 : Tendsto (fun n : ℕ => (d : ℝ) * (Real.log ((n : ℝ) + 1) / n)) atTop (𝓝 ((d : ℝ) * 0)) :=
      tendsto_const_nhds.mul tendsto_log_succ_div
    rw [mul_zero] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr ?_
    intro n; simp only [hL]; ring
  have hlo : Tendsto (fun n : ℕ => a - L n / n) atTop (𝓝 a) := by
    have := tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ)) |>.sub hLdiv
    simpa using this
  have hhi : Tendsto (fun n : ℕ => a + L n / n) atTop (𝓝 a) := by
    have := tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ)) |>.add hLdiv
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hpos, hlb, eventually_gt_atTop 0] with n hp hl hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have habs : |f n| = f n := abs_of_pos hp
    have h := Real.log_le_log (Real.exp_pos (a * n)) hl
    rw [Real.log_exp, Real.log_mul (by positivity) hp.ne', Real.log_mul hC.ne' (by positivity),
      Real.log_pow] at h
    have hle : Real.log C ≤ |Real.log C| := le_abs_self _
    have hmul : (a - L n / n) * n = a * n - L n := by field_simp
    rw [habs, le_div_iff₀ hn0, hmul]
    simp only [hL] at hmul ⊢
    linarith
  · filter_upwards [hpos, hub, eventually_gt_atTop 0] with n hp hu hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have habs : |f n| = f n := abs_of_pos hp
    have h := Real.log_le_log hp hu
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hC.ne' (by positivity),
      Real.log_pow, Real.log_exp] at h
    have hle : Real.log C ≤ |Real.log C| := le_abs_self _
    have hmul : (a + L n / n) * n = a * n + L n := by field_simp
    rw [habs, div_le_iff₀ hn0, hmul]
    simp only [hL] at hmul ⊢
    linarith

/-! ### The rate of `A_n` -/

private lemma exp_log_eight_mul (n : ℕ) : Real.exp (Real.log 8 * n) = (8 : ℝ) ^ n := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log]
  norm_num

/-- Equation (9.2) of the base note, now proved: `(1/n) log A_n → log 8`. -/
theorem rate_Ae : LogRate (fun n => ((Ae n : ℚ) : ℝ)) (Real.log 8) := by
  have hcast : ∀ n : ℕ, ((Ae n : ℚ) : ℝ) = (eSum n : ℝ) := by
    intro n; rw [Ae_eq_eSum]; push_cast; ring
  refine logRate_of_sandwich (f := fun n => ((Ae n : ℚ) : ℝ)) (a := Real.log 8) (C := 16) 3
    (by norm_num) ?_ ?_ ?_
  · filter_upwards with n
    rw [hcast]
    exact_mod_cast eSum_pos n
  · filter_upwards with n
    rw [hcast, exp_log_eight_mul]
    have h := eight_pow_le_eSum n
    have h' : ((8 : ℕ) ^ n : ℝ) ≤ ((16 * (n + 1) ^ 3 * eSum n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  · filter_upwards with n
    rw [hcast, exp_log_eight_mul]
    have h := eSum_le n
    have h' : ((eSum n : ℕ) : ℝ) ≤ (((n + 1) * 8 ^ n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have hn1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp8 : (0 : ℝ) < 8 ^ n := pow_pos (by norm_num) n
    have hsq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have hcube : ((n : ℝ) + 1) * 1 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    have hpoly : ((n : ℝ) + 1) ≤ 16 * ((n : ℝ) + 1) ^ 3 := by nlinarith
    have := mul_le_mul_of_nonneg_right hpoly hp8.le
    linarith

end Catalan
