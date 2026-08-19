import Mathlib

/-!
# The numerical value of the worthiness constant

Section 10 of the unconditional note.  The headline bound is

`δ ≥ 30 log φ / (6 + (45/2) log φ) = 0.8579144524…`,

and we certify here that this constant is `> 0.857914` and `< 1` (so the theorem stays below the
irrationality threshold).
-/

namespace Catalan

open Real

/-- The constant `30 log φ / (6 + (45/2) log φ)` of Theorem 10.1. -/
noncomputable def worthinessConstant : ℝ :=
  30 * Real.log Real.goldenRatio / (6 + 45 / 2 * Real.log Real.goldenRatio)

lemma golden_gt : (17711 / 10946 : ℝ) < Real.goldenRatio := by
  rw [Real.goldenRatio]
  have h5 : (24476 / 10946 : ℝ) < Real.sqrt 5 := by
    have hsq : ((24476 / 10946 : ℝ)) ^ 2 < 5 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  linarith

/-- A certified lower bound for `log φ`, via the Taylor series of `log (1 - x)` at
`x = 6765/17711`. -/
lemma log_golden_gt : (0.4812117 : ℝ) < Real.log Real.goldenRatio := by
  have hstep : (0.4812117 : ℝ) < Real.log (17711 / 10946) := by
    have hx : |(6765 / 17711 : ℝ)| < 1 := by rw [abs_of_pos] <;> norm_num
    have hz := Real.abs_log_sub_add_sum_range_le hx 17
    rw [abs_of_pos (by norm_num : (0:ℝ) < 6765 / 17711)] at hz
    have h1x : (1 : ℝ) - 6765 / 17711 = (17711 / 10946)⁻¹ := by norm_num
    rw [h1x, Real.log_inv] at hz
    simp_rw [Finset.sum_range_succ] at hz
    norm_num at hz
    rcases abs_le.mp hz with ⟨h1, h2⟩
    linarith
  exact hstep.trans_le (Real.log_le_log (by norm_num) golden_gt.le)

lemma log_golden_lt : Real.log Real.goldenRatio < 0.8 := by
  have h1 : Real.log Real.goldenRatio < Real.log 2 :=
    Real.log_lt_log Real.goldenRatio_pos Real.goldenRatio_lt_two
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

lemma log_golden_pos : 0 < Real.log Real.goldenRatio := by
  have := log_golden_gt
  linarith

/-- The worthiness constant exceeds `0.857914`. -/
theorem worthinessConstant_gt : (0.857914 : ℝ) < worthinessConstant := by
  have hL := log_golden_gt
  have hden : (0 : ℝ) < 6 + 45 / 2 * Real.log Real.goldenRatio := by
    have := log_golden_pos
    linarith
  rw [worthinessConstant, lt_div_iff₀ hden]
  nlinarith

/-- The worthiness constant is below the irrationality threshold `1`. -/
theorem worthinessConstant_lt_one : worthinessConstant < 1 := by
  have hL := log_golden_lt
  have hpos := log_golden_pos
  have hden : (0 : ℝ) < 6 + 45 / 2 * Real.log Real.goldenRatio := by linarith
  rw [worthinessConstant, div_lt_one hden]
  linarith

end Catalan
