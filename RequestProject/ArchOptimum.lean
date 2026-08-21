import RequestProject.Constant58

/-!
# Optimality of the `5 : 8` index ratio inside this architecture

Section 13 of the blueprint.  Sampling the Zudilin row at index `a n` and the modular `E`-row at
index `c n`, the architecture used here (a common lcm square `D_{max(2a,c)n}²`, the dyadic cross
modulus of exponent `min(8a,5c) n log 2`, and the two-successive-minima selection) produces the
denominator exponent

`H(a,c) = max(2a,c) + (2a+c) log 2 - (1/2) min(8a,5c) log 2 + (15/2) a log φ`

and the worthiness `δ(a,c) = 10 a log φ / H(a,c)`.  By homogeneity only the ratio `r = c/a`
matters, and we normalize `a = 1`:

`Harch r = max(2,r) + (2+r) log 2 - (1/2) min(8,5r) log 2 + (15/2) log φ`,
`deltaArch r = 10 log φ / Harch r`.

The unique maximum of `deltaArch` over `r > 0` is at `r = 8/5`, i.e. at the index ratio `5 : 8`,
and its value is exactly the constant `worthinessConstant58` of the main theorem.

This is a statement *about this architecture only*; it says nothing about other constructions.
-/

namespace Catalan

open Real

/-- The normalized denominator exponent of the architecture, as a function of the index ratio
`r = c/a`. -/
noncomputable def Harch (r : ℝ) : ℝ :=
  max 2 r + (2 + r) * Real.log 2 - (1 / 2) * min 8 (5 * r) * Real.log 2
    + (15 / 2) * Real.log Real.goldenRatio

/-- The worthiness supplied by the architecture at index ratio `r`. -/
noncomputable def deltaArch (r : ℝ) : ℝ := 10 * Real.log Real.goldenRatio / Harch r

lemma Harch_eight_fifths :
    Harch (8 / 5) = 2 - 2 / 5 * Real.log 2 + (15 / 2) * Real.log Real.goldenRatio := by
  unfold Harch
  rw [max_eq_left (by norm_num), min_eq_left (by norm_num)]
  ring

lemma Harch_eight_fifths_pos : 0 < Harch (8 / 5) := by
  rw [Harch_eight_fifths]
  have h1 := log_golden_pos
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- The unique minimum of the denominator exponent is at `r = 8/5`. -/
theorem Harch_lt_of_ne (r : ℝ) (hne : r ≠ 8 / 5) : Harch (8 / 5) < Harch r := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Harch_eight_fifths]
  unfold Harch
  rcases le_total r (8 / 5) with h1 | h1
  · have hlt : r < 8 / 5 := lt_of_le_of_ne h1 hne
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
    nlinarith
  · rcases le_total r 2 with h2 | h2
    · have hlt : 8 / 5 < r := lt_of_le_of_ne h1 (Ne.symm hne)
      rw [max_eq_left (by linarith), min_eq_left (by linarith)]
      nlinarith
    · rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      nlinarith

theorem Harch_pos (r : ℝ) : 0 < Harch r := by
  rcases eq_or_ne r (8 / 5) with rfl | hne
  · exact Harch_eight_fifths_pos
  · exact lt_trans Harch_eight_fifths_pos (Harch_lt_of_ne r hne)

/-- At the optimal ratio the architecture yields exactly the constant of the main theorem. -/
theorem deltaArch_eight_fifths : deltaArch (8 / 5) = worthinessConstant58 := by
  have hpos := Harch_eight_fifths_pos
  rw [deltaArch, Harch_eight_fifths, worthinessConstant58]
  rw [Harch_eight_fifths] at hpos
  rw [div_eq_div_iff (by linarith) worthinessConstant58_den_pos.ne']
  ring

/-- The optimum is *strict*: any other ratio does strictly worse. -/
theorem deltaArch_lt_of_ne (r : ℝ) (hne : r ≠ 8 / 5) :
    deltaArch r < deltaArch (8 / 5) := by
  have hL := log_golden_pos
  have hr8 := Harch_eight_fifths_pos
  have hlt := Harch_lt_of_ne r hne
  exact div_lt_div_of_pos_left (by linarith) hr8 hlt

/-- **Optimality of the `5 : 8` ratio**: no index ratio does better inside this architecture. -/
theorem deltaArch_le (r : ℝ) : deltaArch r ≤ deltaArch (8 / 5) := by
  rcases eq_or_ne r (8 / 5) with rfl | hne
  · exact le_rfl
  · exact (deltaArch_lt_of_ne r hne).le

end Catalan
