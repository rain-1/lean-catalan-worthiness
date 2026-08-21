import RequestProject.Constant58
import RequestProject.Final

/-!
# The near-critical constants

This file sets up, and certifies numerically, the constants of the *near-critical*
(Zudilin × Nesterenko) construction.

The two Nesterenko characteristic values are

`T± = (3303 ± 437 √57)/144`,

with `T⁺ T⁻ = 32/27`, and the associated archimedean rates of the Nesterenko `(4,7)` row are

`A_N = 12 + 14 log 2 + 2 log T⁺`,  `E_N = 12 + 14 log 2 + 2 log T⁻`.

Paired with the Zudilin rates `A_Z = 12 + 12 log 2 + 15 log φ`, `E_Z = 12 + 12 log 2 - 15 log φ`
already used in the project (`Final.lean`) and with the division modulus of exponential rate
`σ(k) = 12 + k log 2`, the balanced two-row selection produces the linear-form rate

`F(k) = (E_Z + E_N - 12 - k log 2)/2 = (log 2 / 2)(k_* - k)`,  `k_* = (E_Z + E_N - 12)/log 2`,

the denominator rate `H(k) = D + F(k)` with `D = A_N - E_N`, and hence the quality

`δ(k) = D / (D + F(k))`.

Everything in this file is proved unconditionally.  The certificates are:

* `TplusNC_mul_TminusNC` : `T⁺ T⁻ = 32/27`;
* `crossed_gap_NC` : `30 log φ < D`, i.e. the crossed gap `A_Z + E_N < A_N + E_Z`;
* `kstarNC_gt_22`, `kstarNC_lt_24` : `22 < k_* < 24`;
* `deltaNC_gt_of_lt_kstar`, `deltaNC_22_gt` : `δ(22) > 0.99`;
* `exists_k_deltaNC_gt_one_sub` : for every `ε > 0` there is an admissible modulus exponent
  `0 ≤ k < k_*` with `δ(k) > 1 - ε`.
-/

namespace Catalan

open Real

/-! ### The Nesterenko characteristic values -/

/-- `T⁺ = (3303 + 437 √57)/144`. -/
noncomputable def TplusNC : ℝ := (3303 + 437 * Real.sqrt 57) / 144

/-- `T⁻ = (3303 - 437 √57)/144`. -/
noncomputable def TminusNC : ℝ := (3303 - 437 * Real.sqrt 57) / 144

lemma sqrt57_lt : Real.sqrt 57 < 7.54983444 := by
  have h : (57:ℝ) < 7.54983444 ^ 2 := by norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 57), Real.sqrt_nonneg 57]

lemma sqrt57_gt : (7.54983443 : ℝ) < Real.sqrt 57 := by
  have h : ((7.54983443:ℝ)) ^ 2 < 57 := by norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 57), Real.sqrt_nonneg 57]

lemma TminusNC_lt : TminusNC < 0.02584969 := by
  rw [TminusNC]; have := sqrt57_gt; nlinarith

lemma TminusNC_gt : (0.02584965 : ℝ) < TminusNC := by
  rw [TminusNC]; have := sqrt57_lt; nlinarith

lemma TminusNC_pos : 0 < TminusNC := lt_trans (by norm_num) TminusNC_gt

lemma TplusNC_pos : 0 < TplusNC := by
  rw [TplusNC]
  have := Real.sqrt_nonneg 57
  positivity

/-- `T⁺ T⁻ = 32/27`. -/
theorem TplusNC_mul_TminusNC : TplusNC * TminusNC = 32 / 27 := by
  rw [TplusNC, TminusNC]
  have h : Real.sqrt 57 ^ 2 = 57 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- `log T⁺ = log (32/27) - log T⁻`. -/
theorem log_TplusNC_eq : Real.log TplusNC = Real.log (32/27) - Real.log TminusNC := by
  have h := congrArg Real.log TplusNC_mul_TminusNC
  rw [Real.log_mul (ne_of_gt TplusNC_pos) (ne_of_gt TminusNC_pos)] at h
  linarith

/-! ### Certified bounds on `log T⁻` -/

private lemma log_upper_point : Real.log (0.8271901) < -0.18971 := by
  have hx : |(1728099/10000000 : ℝ)| < 1 := by rw [abs_of_pos] <;> norm_num
  have hz := Real.abs_log_sub_add_sum_range_le hx 8
  rw [abs_of_pos (by norm_num : (0:ℝ) < 1728099/10000000)] at hz
  have h1x : (1 : ℝ) - 1728099/10000000 = 0.8271901 := by norm_num
  rw [h1x] at hz
  simp_rw [Finset.sum_range_succ] at hz
  norm_num at hz
  rcases abs_le.mp hz with ⟨h1, h2⟩
  linarith

private lemma log_lower_point : (-0.18973 : ℝ) < Real.log (0.827188) := by
  have hx : |(172812/1000000 : ℝ)| < 1 := by rw [abs_of_pos] <;> norm_num
  have hz := Real.abs_log_sub_add_sum_range_le hx 8
  rw [abs_of_pos (by norm_num : (0:ℝ) < 172812/1000000)] at hz
  have h1x : (1 : ℝ) - 172812/1000000 = 0.827188 := by norm_num
  rw [h1x] at hz
  simp_rw [Finset.sum_range_succ] at hz
  norm_num at hz
  rcases abs_le.mp hz with ⟨h1, h2⟩
  linarith

private lemma log_32_eq : Real.log 32 = 5 * Real.log 2 := by
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; push_cast; ring

/-- `log T⁻ < -3.65544`. -/
theorem log_TminusNC_lt : Real.log TminusNC < -3.65544 := by
  have h32 : Real.log (32 * TminusNC) = 5 * Real.log 2 + Real.log TminusNC := by
    rw [Real.log_mul (by norm_num) (ne_of_gt TminusNC_pos), log_32_eq]
  have hlt : 32 * TminusNC < 0.8271901 := by
    have := TminusNC_lt; linarith
  have hmono : Real.log (32 * TminusNC) < Real.log (0.8271901) :=
    Real.log_lt_log (by have := TminusNC_pos; linarith) hlt
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have := log_upper_point
  linarith

/-- `-3.65547 < log T⁻`. -/
theorem log_TminusNC_gt : (-3.65547 : ℝ) < Real.log TminusNC := by
  have h32 : Real.log (32 * TminusNC) = 5 * Real.log 2 + Real.log TminusNC := by
    rw [Real.log_mul (by norm_num) (ne_of_gt TminusNC_pos), log_32_eq]
  have hgt : (0.827188 : ℝ) < 32 * TminusNC := by
    have := TminusNC_gt; linarith
  have hmono : Real.log (0.827188) < Real.log (32 * TminusNC) :=
    Real.log_lt_log (by norm_num) hgt
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have := log_lower_point
  linarith

/-! ### A sharper upper bound for `log φ` -/

/-- `log φ < 0.4844`, from `φ¹⁵ < 4096/3`. -/
theorem log_golden_lt_tight : Real.log Real.goldenRatio < 0.4844 := by
  have hpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hpow : Real.goldenRatio ^ 15 < (1.618034 : ℝ) ^ 15 :=
    pow_lt_pow_left₀ golden_lt hpos.le (by norm_num)
  have h15 : Real.goldenRatio ^ 15 < 4096 / 3 := by
    have : (1.618034 : ℝ) ^ 15 < 4096 / 3 := by norm_num
    linarith
  have hlog : 15 * Real.log Real.goldenRatio < Real.log (4096 / 3) := by
    have hp : Real.log (Real.goldenRatio ^ 15) = 15 * Real.log Real.goldenRatio := by
      rw [Real.log_pow]; push_cast; ring
    rw [← hp]
    exact Real.log_lt_log (by positivity) h15
  have hsplit : Real.log (4096 / 3) = 10 * Real.log 2 + Real.log (4 / 3) := by
    rw [show (4096 / 3 : ℝ) = 1024 * (4 / 3) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    push_cast; ring
  have h43 : Real.log (4 / 3) ≤ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4/3 by norm_num)
    linarith
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [hsplit] at hlog
  linarith

/-! ### The near-critical rates -/

/-- `A_N = 12 + 14 log 2 + 2 log T⁺`, the archimedean rate of the Nesterenko denominator row. -/
noncomputable def ANrate : ℝ := 12 + 14 * Real.log 2 + 2 * Real.log TplusNC

/-- `E_N = 12 + 14 log 2 + 2 log T⁻`, the rate of the Nesterenko linear form. -/
noncomputable def ENrate : ℝ := 12 + 14 * Real.log 2 + 2 * Real.log TminusNC

/-- `D = A_N - E_N = 2 log (T⁺/T⁻)`, the Nesterenko gap. -/
noncomputable def DgapNC : ℝ := ANrate - ENrate

theorem DgapNC_eq : DgapNC = 2 * Real.log (32/27) - 4 * Real.log TminusNC := by
  rw [DgapNC, ANrate, ENrate, log_TplusNC_eq]; ring

private lemma log_32_27_le : Real.log (32/27) ≤ 5 / 27 := by
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 32/27 by norm_num)
  linarith

private lemma log_32_27_ge : (5 : ℝ) / 32 ≤ Real.log (32/27) := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 27/32 by norm_num)
  have hinv : Real.log (27/32) = -Real.log (32/27) := by
    rw [show (27/32 : ℝ) = (32/27)⁻¹ by norm_num, Real.log_inv]
  rw [hinv] at h
  linarith

theorem DgapNC_gt : (14.934 : ℝ) < DgapNC := by
  rw [DgapNC_eq]
  have h1 := log_32_27_ge
  have h2 := log_TminusNC_lt
  linarith

theorem DgapNC_lt : DgapNC < 14.993 := by
  rw [DgapNC_eq]
  have h1 := log_32_27_le
  have h2 := log_TminusNC_gt
  linarith

theorem DgapNC_pos : 0 < DgapNC := lt_trans (by norm_num) DgapNC_gt

/-- **The crossed gap.**  `A_Z + E_N < A_N + E_Z`, equivalently `30 log φ < D`. -/
theorem crossed_gap_NC : AZrate + ENrate < ANrate + EZrate := by
  have hphi := log_golden_lt_tight
  have hD := DgapNC_gt
  rw [AZrate, EZrate]
  rw [DgapNC] at hD
  linarith

/-! ### The critical modulus `k_*` -/

/-- `k_* = (E_Z + E_N - 12)/log 2`. -/
noncomputable def kstarNC : ℝ := (EZrate + ENrate - 12) / Real.log 2

/-- `σ(k) = 12 + k log 2`, the rate of the division modulus `D_{6n}² 2^{⌊kn⌋}`. -/
noncomputable def sigmaNC (k : ℝ) : ℝ := 12 + k * Real.log 2

/-- `F(k) = (E_Z + E_N - σ(k))/2`, the linear-form rate of the selected sequence. -/
noncomputable def FrateNC (k : ℝ) : ℝ := (EZrate + ENrate - 12 - k * Real.log 2) / 2

/-- `H(k) = D + F(k)`, the denominator rate of the selected sequence. -/
noncomputable def HrateNC (k : ℝ) : ℝ := DgapNC + FrateNC k

/-- `δ(k) = D / (D + F(k)) = 1 - F(k)/H(k)`, the resulting worthiness. -/
noncomputable def deltaNC (k : ℝ) : ℝ := DgapNC / (DgapNC + FrateNC k)

lemma log_two_pos' : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem FrateNC_eq (k : ℝ) : FrateNC k = Real.log 2 / 2 * (kstarNC - k) := by
  rw [FrateNC, kstarNC]
  field_simp

theorem FrateNC_pos {k : ℝ} (hk : k < kstarNC) : 0 < FrateNC k := by
  rw [FrateNC_eq]
  have := log_two_pos'
  have : 0 < kstarNC - k := by linarith
  positivity

theorem HrateNC_pos {k : ℝ} (hk : k < kstarNC) : 0 < HrateNC k := by
  have := FrateNC_pos hk
  have := DgapNC_pos
  rw [HrateNC]
  linarith

/-- `22 < k_*`. -/
theorem kstarNC_gt_22 : 22 < kstarNC := by
  have hl2l : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hphiU := log_golden_lt_tight
  have hLl := log_TminusNC_gt
  have hnum : 22 * Real.log 2 < EZrate + ENrate - 12 := by
    rw [EZrate, ENrate]
    linarith
  rw [kstarNC, lt_div_iff₀ log_two_pos']
  linarith

/-- `k_* < 24`. -/
theorem kstarNC_lt_24 : kstarNC < 24 := by
  have hl2l : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hphiL := log_golden_gt
  have hLu := log_TminusNC_lt
  have hnum : EZrate + ENrate - 12 < 24 * Real.log 2 := by
    rw [EZrate, ENrate]
    linarith
  rw [kstarNC, div_lt_iff₀ log_two_pos']
  linarith

theorem kstarNC_pos : 0 < kstarNC := lt_trans (by norm_num) kstarNC_gt_22

/-! ### The quality function -/

theorem deltaNC_eq_one_sub {k : ℝ} (hk : k < kstarNC) :
    deltaNC k = 1 - FrateNC k / HrateNC k := by
  have hH : HrateNC k ≠ 0 := ne_of_gt (HrateNC_pos hk)
  rw [deltaNC, HrateNC] at *
  field_simp
  ring

theorem deltaNC_pos {k : ℝ} (hk : k < kstarNC) : 0 < deltaNC k := by
  have := HrateNC_pos hk
  rw [deltaNC]
  rw [HrateNC] at this
  exact div_pos DgapNC_pos this

/-- The explicit `k = 22` quality bound: `δ(22) > 0.99`. -/
theorem deltaNC_22_gt : (0.99 : ℝ) < deltaNC 22 := by
  have hk : (22 : ℝ) < kstarNC := kstarNC_gt_22
  have hF := FrateNC_pos hk
  have hD := DgapNC_gt
  have hDp := DgapNC_pos
  have hden : 0 < DgapNC + FrateNC 22 := by linarith
  have hl2l : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hphiL := log_golden_gt
  have hLu := log_TminusNC_lt
  have hFup : FrateNC 22 < 0.1218 := by
    rw [FrateNC, EZrate, ENrate]
    linarith
  rw [deltaNC, lt_div_iff₀ hden]
  linarith

/-- For every `ε > 0` there is a modulus exponent `0 ≤ k < k_*` whose quality exceeds `1 - ε`. -/
theorem exists_k_deltaNC_gt_one_sub {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℝ, 0 ≤ k ∧ k < kstarNC ∧ 1 - ε < deltaNC k := by
  rcases le_or_gt 1 ε with hε1 | hε1
  · refine ⟨22, by norm_num, kstarNC_gt_22, ?_⟩
    have := deltaNC_pos kstarNC_gt_22
    have h99 := deltaNC_22_gt
    linarith
  · have hDp := DgapNC_pos
    have hl2 := log_two_pos'
    set t : ℝ := min 1 (ε * DgapNC / ((1 - ε) * Real.log 2)) with ht
    have h1ε : 0 < 1 - ε := by linarith
    have htpos : 0 < t := by
      rw [ht]
      have : 0 < ε * DgapNC / ((1 - ε) * Real.log 2) := by positivity
      exact lt_min (by norm_num) this
    have htle : t ≤ 1 := min_le_left _ _
    have htle2 : t ≤ ε * DgapNC / ((1 - ε) * Real.log 2) := min_le_right _ _
    refine ⟨kstarNC - t, ?_, by linarith, ?_⟩
    · have := kstarNC_gt_22
      linarith
    · have hk : kstarNC - t < kstarNC := by linarith
      have hF : FrateNC (kstarNC - t) = Real.log 2 / 2 * t := by
        rw [FrateNC_eq]; ring_nf
      have hFpos := FrateNC_pos hk
      have hden : 0 < DgapNC + FrateNC (kstarNC - t) := by linarith
      have hkey : (1 - ε) * FrateNC (kstarNC - t) < ε * DgapNC := by
        rw [hF]
        have hmul : (1 - ε) * Real.log 2 * t ≤ ε * DgapNC := by
          rw [le_div_iff₀ (by positivity)] at htle2
          linarith [htle2]
        nlinarith [htpos, hl2, hε]
      rw [deltaNC, lt_div_iff₀ hden]
      nlinarith

end Catalan
