import RequestProject.Constant

/-!
# The numerical value of the improved worthiness constant

The `5 : 8` construction produces the exponents

`H = 10 - 2 log 2 + (75/2) log φ`,  `F = 10 - 2 log 2 - (25/2) log φ`,

whose associated worthiness `1 - F/H = 50 log φ / H` is

`0.9025266028569714694…`.

Here we certify that this constant exceeds `0.9` (indeed `0.9025`) and stays below `1`.
-/

namespace Catalan

open Real

/-- The constant `50 log φ / (10 - 2 log 2 + (75/2) log φ)` of the `5 : 8` theorem. -/
noncomputable def worthinessConstant58 : ℝ :=
  50 * Real.log Real.goldenRatio /
    (10 - 2 * Real.log 2 + 75 / 2 * Real.log Real.goldenRatio)

lemma worthinessConstant58_den_pos :
    (0 : ℝ) < 10 - 2 * Real.log 2 + 75 / 2 * Real.log Real.goldenRatio := by
  have h1 := log_golden_pos
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- The improved worthiness constant exceeds `0.9025`. -/
theorem worthinessConstant58_gt : (0.9025 : ℝ) < worthinessConstant58 := by
  have hL := log_golden_gt
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [worthinessConstant58, lt_div_iff₀ worthinessConstant58_den_pos]
  linarith

/-- In particular the improved worthiness constant exceeds `0.9`. -/
theorem worthinessConstant58_gt_nine_tenths : (0.9 : ℝ) < worthinessConstant58 :=
  lt_trans (by norm_num) worthinessConstant58_gt

lemma golden_lt : Real.goldenRatio < 1.618034 := by
  rw [Real.goldenRatio]
  have h5 : Real.sqrt 5 < 2.236068 := by
    have hsq : (5 : ℝ) < (2.236068 : ℝ) ^ 2 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  linarith

/-- A sharper upper bound for `log φ`, from `φ⁵ < 16`. -/
lemma log_golden_lt_sharp : Real.log Real.goldenRatio < 0.5546 := by
  have hpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hpow : Real.goldenRatio ^ 5 < (1.618034 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ golden_lt hpos.le (by norm_num)
  have h5 : Real.goldenRatio ^ 5 < 16 := by
    have : (1.618034 : ℝ) ^ 5 < 16 := by norm_num
    linarith
  have hlog : 5 * Real.log Real.goldenRatio < Real.log 16 := by
    have hp : Real.log (Real.goldenRatio ^ 5) = 5 * Real.log Real.goldenRatio := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [← hp]
    exact Real.log_lt_log (by positivity) h5
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h16] at hlog
  linarith

/-- The improved worthiness constant is still below the irrationality threshold `1`. -/
theorem worthinessConstant58_lt_one : worthinessConstant58 < 1 := by
  have hpos := log_golden_pos
  have hup := log_golden_lt_sharp
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [worthinessConstant58, div_lt_one worthinessConstant58_den_pos]
  linarith

end Catalan
