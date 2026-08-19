import RequestProject.Zudilin
import RequestProject.RateTools
import RequestProject.Constant

/-!
# The archimedean growth rate of the Zudilin denominators

The base note imports the archimedean estimate `(1/m) log Q_m → 5 log φ` (Imported Theorem Z).
It is proved here, so that it no longer has to be assumed.

The argument is elementary.  Zudilin's recurrence

`L_m Q_{m+1} = C_m Q_m + R_m Q_{m-1}`

has *positive* coefficients, so all `Q_m` are positive and the ratios
`ρ_m = Q_{m+1}/Q_m` satisfy the scalar recursion

`ρ_{m+1} = a_{m+1} + b_{m+1} / ρ_m`,   `a_m = C_m/L_m → 11`,  `b_m = R_m/L_m → 1`.

Since `ρ_m ≥ a_m ≥ 10` for large `m`, the map `ρ ↦ a + b/ρ` is a contraction with factor
`b/ρ² ≤ 1/100` there, and `ρ_m` converges to the positive root of `λ = 11 + 1/λ`, which is
`λ = φ⁵ = (11 + 5√5)/2`.  Cesàro summation of `log Q_m = ∑_{j<m} log ρ_j` then gives
`(1/m) log Q_m → log φ⁵ = 5 log φ`.
-/

namespace Catalan

open Filter Topology

/-! ### Positivity of the coefficients and of `Q_m` -/

lemma phiZ_pos (m : ℕ) : 0 < phiZ m := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  rcases eq_or_lt_of_le hm with h | h
  · simp [phiZ, ← h]
  · unfold phiZ; nlinarith

lemma LZ_pos (m : ℕ) : 0 < LZ m := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have h1 : (0 : ℤ) < (2 * (m : ℤ) + 1) ^ 2 := by positivity
  have h2 : (0 : ℤ) < (2 * (m : ℤ) + 2) ^ 2 := by positivity
  exact mul_pos (mul_pos h1 h2) (phiZ_pos m)

lemma CZ_pos (m : ℕ) : 0 < CZ m := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  rcases eq_or_lt_of_le hm with h | h
  · simp [CZ, ← h]
  · have h1 : (1 : ℤ) ≤ (m : ℤ) := h
    unfold CZ
    nlinarith [pow_le_pow_right₀ h1 (show 3 ≤ 6 by norm_num),
      pow_le_pow_right₀ h1 (show 2 ≤ 6 by norm_num),
      pow_le_pow_right₀ h1 (show 0 ≤ 6 by norm_num),
      pow_pos (lt_of_lt_of_le one_pos h1) 6]

lemma RZ_nonneg (m : ℕ) : 0 ≤ RZ m := by
  have h1 : (0 : ℤ) ≤ (2 * (m : ℤ) - 1) ^ 2 := sq_nonneg _
  have h2 : (0 : ℤ) ≤ (2 * (m : ℤ)) ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg h1 h2) (phiZ_pos (m + 1)).le

/-- All the Zudilin denominators are positive. -/
theorem Qz_pos (m : ℕ) : 0 < Qz m := by
  have key : ∀ m, 0 < Qz m ∧ 0 < Qz (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨by norm_num, by norm_num⟩
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have hrec := Qz_rec k
        have hL : (0 : ℚ) < (LZ (k + 1) : ℚ) := by exact_mod_cast LZ_pos (k + 1)
        have hC : (0 : ℚ) < (CZ (k + 1) : ℚ) := by exact_mod_cast CZ_pos (k + 1)
        have hR : (0 : ℚ) ≤ (RZ (k + 1) : ℚ) := by exact_mod_cast RZ_nonneg (k + 1)
        have hpos : (0 : ℚ) < (CZ (k + 1) : ℚ) * Qz (k + 1) + (RZ (k + 1) : ℚ) * Qz k :=
          add_pos_of_pos_of_nonneg (mul_pos hC ih.2) (mul_nonneg hR ih.1.le)
        have hmul : (0 : ℚ) < (LZ (k + 1) : ℚ) * Qz (k + 1 + 1) := by rw [hrec]; exact hpos
        by_contra hcon
        push_neg at hcon
        nlinarith [hmul, hL, hcon]
  exact (key m).1

/-! ### The ratio recursion -/

/-- The Zudilin denominators as a real sequence. -/
noncomputable def qR (m : ℕ) : ℝ := ((Qz m : ℚ) : ℝ)

lemma qR_pos (m : ℕ) : 0 < qR m := by
  have := Qz_pos m
  simpa [qR] using (by exact_mod_cast this : (0:ℝ) < ((Qz m : ℚ) : ℝ))

/-- `ρ_m = Q_{m+1}/Q_m`. -/
noncomputable def rhoZ (m : ℕ) : ℝ := qR (m + 1) / qR m

/-- `a_m = C_m/L_m`. -/
noncomputable def aZ (m : ℕ) : ℝ := (CZ m : ℝ) / (LZ m : ℝ)

/-- `b_m = R_m/L_m`. -/
noncomputable def bZ (m : ℕ) : ℝ := (RZ m : ℝ) / (LZ m : ℝ)

lemma LZ_real_pos (m : ℕ) : (0 : ℝ) < (LZ m : ℝ) := by exact_mod_cast LZ_pos m

lemma aZ_pos (m : ℕ) : 0 < aZ m := div_pos (by exact_mod_cast CZ_pos m) (LZ_real_pos m)

lemma bZ_nonneg (m : ℕ) : 0 ≤ bZ m :=
  div_nonneg (by exact_mod_cast RZ_nonneg m) (LZ_real_pos m).le

lemma rhoZ_pos (m : ℕ) : 0 < rhoZ m := div_pos (qR_pos (m + 1)) (qR_pos m)

lemma rhoZ_rec (m : ℕ) : rhoZ (m + 1) = aZ (m + 1) + bZ (m + 1) / rhoZ m := by
  have hrec : (LZ (m + 1) : ℝ) * qR (m + 2) = (CZ (m + 1) : ℝ) * qR (m + 1)
      + (RZ (m + 1) : ℝ) * qR m := by
    have h := Qz_rec m
    have := congrArg (fun z : ℚ => (z : ℝ)) h
    push_cast at this
    simpa [qR] using this
  have hL := (LZ_real_pos (m + 1)).ne'
  have hq0 := (qR_pos m).ne'
  have hq1 := (qR_pos (m + 1)).ne'
  unfold rhoZ aZ bZ
  field_simp
  nlinarith [hrec]

/-! ### The coefficients of the recursion -/

lemma LZ_real (m : ℕ) : (LZ m : ℝ)
    = 320 * (m : ℝ) ^ 6 + 832 * (m : ℝ) ^ 5 + 672 * (m : ℝ) ^ 4 + 112 * (m : ℝ) ^ 3
      - 60 * (m : ℝ) ^ 2 - 8 * (m : ℝ) + 4 := by
  unfold LZ phiZ
  push_cast
  ring

lemma CZ_real (m : ℕ) : (CZ m : ℝ)
    = 3520 * (m : ℝ) ^ 6 + 5632 * (m : ℝ) ^ 5 + 2064 * (m : ℝ) ^ 4 - 384 * (m : ℝ) ^ 3
      - 156 * (m : ℝ) ^ 2 + 16 * (m : ℝ) + 7 := by
  unfold CZ
  push_cast
  ring

lemma RZ_real (m : ℕ) : (RZ m : ℝ)
    = 320 * (m : ℝ) ^ 6 + 192 * (m : ℝ) ^ 5 - 224 * (m : ℝ) ^ 4 - 80 * (m : ℝ) ^ 3
      + 52 * (m : ℝ) ^ 2 := by
  unfold RZ phiZ
  push_cast
  ring

lemma LZ_ge (m : ℕ) (hm : 1 ≤ m) : 320 * (m : ℝ) ^ 6 ≤ (LZ m : ℝ) := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [LZ_real]
  nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 3 by norm_num),
    pow_le_pow_right₀ h1 (show 1 ≤ 2 by norm_num), pow_pos (lt_of_lt_of_le one_pos h1) 3]

/-- `|a_m - 11| ≤ 35/m`. -/
lemma aZ_approx (m : ℕ) (hm : 1 ≤ m) : |aZ m - 11| ≤ 35 / (m : ℝ) := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL := LZ_real_pos m
  have hLge := LZ_ge m hm
  have hnum : |(CZ m : ℝ) - 11 * (LZ m : ℝ)| ≤ 11000 * (m : ℝ) ^ 5 := by
    rw [CZ_real, LZ_real, abs_le]
    constructor <;> nlinarith [pow_le_pow_right₀ h1 (show 4 ≤ 5 by norm_num),
      pow_le_pow_right₀ h1 (show 3 ≤ 5 by norm_num), pow_le_pow_right₀ h1 (show 2 ≤ 5 by norm_num),
      pow_le_pow_right₀ h1 (show 1 ≤ 5 by norm_num), pow_le_pow_right₀ h1 (show 0 ≤ 5 by norm_num),
      pow_pos (lt_of_lt_of_le one_pos h1) 5, pow_pos (lt_of_lt_of_le one_pos h1) 6]
  have hkey : aZ m - 11 = ((CZ m : ℝ) - 11 * (LZ m : ℝ)) / (LZ m : ℝ) := by
    unfold aZ; field_simp
  rw [hkey, abs_div, abs_of_pos hL, div_le_div_iff₀ hL (by positivity)]
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le one_pos h1
  calc |(CZ m : ℝ) - 11 * (LZ m : ℝ)| * (m : ℝ) ≤ 11000 * (m : ℝ) ^ 5 * (m : ℝ) := by
        exact mul_le_mul_of_nonneg_right hnum hm0.le
    _ = 11000 * (m : ℝ) ^ 6 := by ring
    _ ≤ 35 * (320 * (m : ℝ) ^ 6) := by nlinarith [pow_pos hm0 6]
    _ ≤ 35 * (LZ m : ℝ) := by nlinarith

/-- `|b_m - 1| ≤ 7/m`. -/
lemma bZ_approx (m : ℕ) (hm : 1 ≤ m) : |bZ m - 1| ≤ 7 / (m : ℝ) := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL := LZ_real_pos m
  have hLge := LZ_ge m hm
  have hnum : |(RZ m : ℝ) - (LZ m : ℝ)| ≤ 2000 * (m : ℝ) ^ 5 := by
    rw [RZ_real, LZ_real, abs_le]
    constructor <;> nlinarith [pow_le_pow_right₀ h1 (show 4 ≤ 5 by norm_num),
      pow_le_pow_right₀ h1 (show 3 ≤ 5 by norm_num), pow_le_pow_right₀ h1 (show 2 ≤ 5 by norm_num),
      pow_le_pow_right₀ h1 (show 1 ≤ 5 by norm_num), pow_le_pow_right₀ h1 (show 0 ≤ 5 by norm_num),
      pow_pos (lt_of_lt_of_le one_pos h1) 5, pow_pos (lt_of_lt_of_le one_pos h1) 6]
  have hkey : bZ m - 1 = ((RZ m : ℝ) - (LZ m : ℝ)) / (LZ m : ℝ) := by
    unfold bZ; field_simp
  rw [hkey, abs_div, abs_of_pos hL, div_le_div_iff₀ hL (by positivity)]
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le one_pos h1
  calc |(RZ m : ℝ) - (LZ m : ℝ)| * (m : ℝ) ≤ 2000 * (m : ℝ) ^ 5 * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hnum hm0.le
    _ = 2000 * (m : ℝ) ^ 6 := by ring
    _ ≤ 7 * (320 * (m : ℝ) ^ 6) := by nlinarith [pow_pos hm0 6]
    _ ≤ 7 * (LZ m : ℝ) := by nlinarith

/-! ### Bounds for the ratios -/

lemma rhoZ_ge_ten (m : ℕ) (hm : 35 ≤ m) : 10 ≤ rhoZ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k + 1 := by omega
  have ha := aZ_approx (k + 1) hk
  have hm1 : (35 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hm
  have hb : 0 ≤ bZ (k + 1) / rhoZ k := div_nonneg (bZ_nonneg _) (rhoZ_pos k).le
  have haa : 10 ≤ aZ (k + 1) := by
    have h := abs_le.mp ha
    have : 35 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith [h.1]
  rw [rhoZ_rec k]
  linarith

lemma rhoZ_le_thirteen (m : ℕ) (hm : 36 ≤ m) : rhoZ m ≤ 13 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k + 1 := by omega
  have ha := abs_le.mp (aZ_approx (k + 1) hk)
  have hb := abs_le.mp (bZ_approx (k + 1) hk)
  have hm1 : (36 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hm
  have hrho : 10 ≤ rhoZ k := rhoZ_ge_ten k (by omega)
  have h35 : 35 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h7 : 7 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hble : bZ (k + 1) ≤ 2 := by linarith [hb.2]
  have hdiv : bZ (k + 1) / rhoZ k ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  rw [rhoZ_rec k]
  linarith [ha.2]

/-! ### The limit `φ⁵` -/

lemma gold_pow_five : Real.goldenRatio ^ 5 = 5 * Real.goldenRatio + 3 := by
  have h := Real.goldenRatio_sq
  linear_combination (Real.goldenRatio ^ 3 + Real.goldenRatio ^ 2 + 2 * Real.goldenRatio + 3) * h

lemma gold_pow_five_sq : (Real.goldenRatio ^ 5) ^ 2 = 11 * Real.goldenRatio ^ 5 + 1 := by
  have h := Real.goldenRatio_sq
  rw [gold_pow_five]
  linear_combination 25 * h

lemma gold_pow_five_gt : (11 : ℝ) < Real.goldenRatio ^ 5 := by
  have h : (1.618 : ℝ) < Real.goldenRatio := by
    rw [Real.goldenRatio]
    have h5 : (2.236 : ℝ) < Real.sqrt 5 := by
      have : (2.236 : ℝ) = Real.sqrt (2.236 ^ 2) := by
        rw [Real.sqrt_sq (by norm_num)]
      rw [this]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  rw [gold_pow_five]
  linarith

lemma fix_of_sq {y : ℝ} (hy : 0 < y) (h : y ^ 2 = 11 * y + 1) : y = 11 + 1 / y := by
  have hne : y ≠ 0 := ne_of_gt hy
  field_simp
  nlinarith [h]

lemma gold_pow_five_lt : Real.goldenRatio ^ 5 < 11.2 := by
  have h : Real.goldenRatio < 1.6181 := by
    rw [Real.goldenRatio]
    have h5 : Real.sqrt 5 < 2.2361 := by
      have h1 : Real.sqrt 5 < Real.sqrt (2.2361 ^ 2) :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rwa [Real.sqrt_sq (by norm_num)] at h1
    linarith
  rw [gold_pow_five]
  linarith

lemma gold_pow_five_fix : Real.goldenRatio ^ 5 = 11 + 1 / Real.goldenRatio ^ 5 :=
  fix_of_sq (by linarith [gold_pow_five_gt]) gold_pow_five_sq

/-! ### Convergence of the ratios -/

/-- A contraction estimate with a vanishing inhomogeneity forces convergence to zero. -/
lemma tendsto_zero_of_contraction {e c : ℕ → ℝ} {q E : ℝ} {N : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (he : ∀ m, 0 ≤ e m)
    (hbd : ∀ m, N ≤ m → e m ≤ E)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ m, N ≤ m → e (m + 1) ≤ c m + q * e m) :
    Tendsto e atTop (𝓝 0) := by
  have hE : 0 ≤ E := le_trans (he N) (hbd N le_rfl)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcsmall : ∀ᶠ m in atTop, c m ≤ ε * (1 - q) / 2 := by
    have := hc.eventually (eventually_le_nhds (show (0:ℝ) < ε * (1 - q) / 2 by
      have : 0 < 1 - q := by linarith
      positivity))
    filter_upwards [this] with m hm using hm
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hcsmall
  set K := max K0 N with hK
  have hKN : N ≤ K := le_max_right _ _
  have hKK0 : K0 ≤ K := le_max_left _ _
  have key : ∀ j, e (K + j) ≤ ε / 2 + q ^ j * E := by
    intro j
    induction j with
    | zero =>
        have hb := hbd K hKN
        simp only [Nat.add_zero, pow_zero, one_mul]
        linarith
    | succ i ih =>
        have h1 : e (K + i + 1) ≤ c (K + i) + q * e (K + i) :=
          hstep (K + i) (le_trans hKN (Nat.le_add_right _ _))
        have h2 : c (K + i) ≤ ε * (1 - q) / 2 := hK0 (K + i) (le_trans hKK0 (Nat.le_add_right _ _))
        have h3 : q * e (K + i) ≤ q * (ε / 2 + q ^ i * E) := mul_le_mul_of_nonneg_left ih hq0
        have h4 : e (K + i + 1) ≤ ε * (1 - q) / 2 + q * (ε / 2 + q ^ i * E) := by linarith
        calc e (K + (i + 1)) = e (K + i + 1) := by ring_nf
          _ ≤ ε * (1 - q) / 2 + q * (ε / 2 + q ^ i * E) := h4
          _ = ε / 2 + q ^ (i + 1) * E := by ring
  have hpow : Tendsto (fun j : ℕ => q ^ j * E) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const E
    simpa using this
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hpow.eventually (eventually_le_nhds
    (show (0:ℝ) < ε / 4 by linarith)))
  refine ⟨K + J, fun m hm => ?_⟩
  have hj : m = K + (m - K) := by omega
  have hJm : J ≤ m - K := by omega
  have h1 := key (m - K)
  have h2 : q ^ (m - K) * E ≤ ε / 4 := hJ (m - K) hJm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he m)]
  calc e m = e (K + (m - K)) := by rw [← hj]
    _ ≤ ε / 2 + q ^ (m - K) * E := h1
    _ ≤ ε / 2 + ε / 4 := by linarith
    _ < ε := by linarith

/-- One contraction step for the ratios `ρ_m`, around the fixed point `λ = 11 + 1/λ`. -/
lemma rhoZ_contract (lam : ℝ) (hfix : lam = 11 + 1 / lam) (hlo : 11 < lam) (hhi : lam < 12)
    (m : ℕ) (hm : 36 ≤ m) :
    |rhoZ (m + 1) - lam| ≤ 36 / ((m : ℝ) + 1) + 1 / 110 * |rhoZ m - lam| := by
  have hk : 1 ≤ m + 1 := by omega
  have hrho : 10 ≤ rhoZ m := rhoZ_ge_ten m (by omega)
  have hrhopos : 0 < rhoZ m := rhoZ_pos m
  have hlampos : (0 : ℝ) < lam := by linarith
  have hmR : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have expand : (aZ (m + 1) - 11) + (bZ (m + 1) - 1) / rhoZ m + (1 / rhoZ m - 1 / lam)
      = aZ (m + 1) + bZ (m + 1) / rhoZ m - (11 + 1 / lam) := by
    field_simp
    ring
  have hsplit : rhoZ (m + 1) - lam
      = (aZ (m + 1) - 11) + (bZ (m + 1) - 1) / rhoZ m + (1 / rhoZ m - 1 / lam) := by
    rw [expand, ← hfix, rhoZ_rec m]
  have h1 : |aZ (m + 1) - 11| ≤ 35 / ((m : ℝ) + 1) := by
    rw [hmR]; exact aZ_approx (m + 1) hk
  have h2 : |(bZ (m + 1) - 1) / rhoZ m| ≤ 1 / ((m : ℝ) + 1) := by
    have hb7 : |bZ (m + 1) - 1| ≤ 7 / ((m : ℝ) + 1) := by
      rw [hmR]; exact bZ_approx (m + 1) hk
    have hb7' : |bZ (m + 1) - 1| * ((m : ℝ) + 1) ≤ 7 := (le_div_iff₀ hpos).mp hb7
    rw [abs_div, abs_of_pos hrhopos, div_le_div_iff₀ hrhopos hpos]
    linarith
  have h3 : |1 / rhoZ m - 1 / lam| ≤ 1 / 110 * |rhoZ m - lam| := by
    have heq : 1 / rhoZ m - 1 / lam = (lam - rhoZ m) / (rhoZ m * lam) := by
      field_simp
    have hprod : (110 : ℝ) ≤ rhoZ m * lam := by nlinarith
    rw [heq, abs_div, abs_of_pos (mul_pos hrhopos hlampos), abs_sub_comm,
      div_le_iff₀ (mul_pos hrhopos hlampos)]
    nlinarith [abs_nonneg (rhoZ m - lam), hprod]
  calc |rhoZ (m + 1) - lam|
      = |(aZ (m + 1) - 11) + (bZ (m + 1) - 1) / rhoZ m + (1 / rhoZ m - 1 / lam)| := by rw [hsplit]
    _ ≤ |(aZ (m + 1) - 11) + (bZ (m + 1) - 1) / rhoZ m| + |1 / rhoZ m - 1 / lam| :=
        abs_add_le _ _
    _ ≤ |aZ (m + 1) - 11| + |(bZ (m + 1) - 1) / rhoZ m| + |1 / rhoZ m - 1 / lam| := by
        linarith [abs_add_le (aZ (m + 1) - 11) ((bZ (m + 1) - 1) / rhoZ m)]
    _ ≤ 35 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) + 1 / 110 * |rhoZ m - lam| := by
        linarith
    _ = 36 / ((m : ℝ) + 1) + 1 / 110 * |rhoZ m - lam| := by ring

theorem tendsto_rhoZ : Tendsto rhoZ atTop (𝓝 (Real.goldenRatio ^ 5)) := by
  have hlo := gold_pow_five_gt
  have hhi : Real.goldenRatio ^ 5 < 12 := by linarith [gold_pow_five_lt]
  have hzero : Tendsto (fun m => |rhoZ m - Real.goldenRatio ^ 5|) atTop (𝓝 0) := by
    refine tendsto_zero_of_contraction (q := 1 / 110) (E := 2) (N := 36)
      (c := fun m => 36 / ((m : ℝ) + 1)) (by norm_num) (by norm_num)
      (fun m => abs_nonneg _) ?_ ?_ ?_
    · intro m hm
      have h1 := rhoZ_ge_ten m (by omega)
      have h2 := rhoZ_le_thirteen m hm
      have h3 := gold_pow_five_lt
      rw [abs_le]
      constructor <;> [linarith; linarith]
    · have h : Tendsto (fun m : ℕ => ((m : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
      exact Filter.Tendsto.div_atTop tendsto_const_nhds h
    · intro m hm
      exact rhoZ_contract (Real.goldenRatio ^ 5) gold_pow_five_fix hlo hhi m hm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using hzero

/-! ### The growth rate -/

lemma log_qR_eq_sum (m : ℕ) : Real.log (qR m) = ∑ j ∈ Finset.range m, Real.log (rhoZ j) := by
  induction m with
  | zero => simp [qR, Qz_zero]
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      have h : qR (k + 1) = rhoZ k * qR k := by
        unfold rhoZ
        rw [div_mul_cancel₀ _ (qR_pos k).ne']
      rw [h, Real.log_mul (rhoZ_pos k).ne' (qR_pos k).ne']
      ring

/-- Imported Theorem Z, now proved: `(1/m) log Q_m → 5 log φ`. -/
theorem rate_Qz : LogRate qR (5 * Real.log Real.goldenRatio) := by
  have hlog : Tendsto (fun m => Real.log (rhoZ m)) atTop
      (𝓝 (Real.log (Real.goldenRatio ^ 5))) := by
    refine (Real.continuousAt_log ?_).tendsto.comp tendsto_rhoZ
    have := gold_pow_five_gt
    linarith
  have hces := hlog.cesaro
  have hval : Real.log (Real.goldenRatio ^ 5) = 5 * Real.log Real.goldenRatio := by
    rw [Real.log_pow]; push_cast; ring
  rw [hval] at hces
  unfold LogRate
  refine hces.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← log_qR_eq_sum m, abs_of_pos (qR_pos m)]
  field_simp

end Catalan
